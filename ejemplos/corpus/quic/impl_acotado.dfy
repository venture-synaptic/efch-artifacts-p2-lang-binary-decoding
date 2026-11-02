// Entero de longitud variable de QUIC (RFC 9000, §16), con tipos acotados para compilar a
// código eficiente. EXP-005 (sensibilidad).

newtype u8 = x: int | 0 <= x < 0x100
newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000
datatype Option<T> = None | Some(value: T)

ghost function BE(s: seq<u8>): nat {
  if |s| == 0 then 0 else BE(s[..|s| - 1]) * 256 + s[|s| - 1] as nat
}

ghost function Spec(buf: seq<u8>): Option<(nat, nat)> {
  if |buf| == 0 then None
  else
    var n := if buf[0] < 64 then 1 else if buf[0] < 128 then 2 else if buf[0] < 192 then 4 else 8;
    if |buf| < n then None else Some((BE([buf[0] % 64] + buf[1..n]), n))
}

lemma BEBound(s: seq<u8>)
  ensures BE(s) < Pow256(|s|)
{
  if |s| > 0 { BEBound(s[..|s| - 1]); }
}

ghost function Pow256(n: nat): nat { if n == 0 then 1 else 256 * Pow256(n - 1) }

method Decode(buf: seq<u8>) returns (r: Option<(u64, u8)>)
  requires |buf| <= 8
  ensures match Spec(buf)
            case None => r.None?
            case Some(t) => r.Some? && r.value.0 as nat == t.0 && r.value.1 as nat == t.1
{
  if |buf| == 0 { return None; }
  var n: u8 := if buf[0] < 64 then 1 else if buf[0] < 128 then 2 else if buf[0] < 192 then 4 else 8;
  if (|buf| as u8) < n { return None; }
  var v: u64 := (buf[0] % 64) as u64;
  var i: u8 := 1;
  while i < n
    invariant 1 <= i <= n
    invariant v as nat == BE([buf[0] % 64] + buf[1..i])
  {
    assert ([buf[0] % 64] + buf[1..i + 1])[..i] == [buf[0] % 64] + buf[1..i];
    BEBound([buf[0] % 64] + buf[1..i + 1]);
    assert Pow256(i as nat + 1) <= 0x1_0000_0000_0000_0000 by { PowMono(i as nat + 1, 8); }
    v := v * 256 + buf[i] as u64;
    i := i + 1;
  }
  return Some((v, n));
}

lemma PowMono(a: nat, b: nat)
  requires a <= b
  ensures Pow256(a) <= Pow256(b)
{
  if a < b { PowMono(a, b - 1); }
}
