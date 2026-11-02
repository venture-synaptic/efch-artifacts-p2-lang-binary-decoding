// Entero de longitud variable de QUIC (RFC 9000, §16). EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

function BE(s: seq<u8>): nat {
  if |s| == 0 then 0 else BE(s[..|s| - 1]) * 256 + s[|s| - 1] as nat
}

function Spec(buf: seq<u8>): Option<(nat, nat)> {
  if |buf| == 0 then None
  else
    var n := if buf[0] < 64 then 1 else if buf[0] < 128 then 2 else if buf[0] < 192 then 4 else 8;
    if |buf| < n then None else Some((BE([buf[0] % 64] + buf[1..n]), n))
}

method Decode(buf: seq<u8>) returns (r: Option<(nat, nat)>)
  ensures r == Spec(buf)
{
  if |buf| == 0 { return None; }
  var n := if buf[0] < 64 then 1 else if buf[0] < 128 then 2 else if buf[0] < 192 then 4 else 8;
  if |buf| < n { return None; }
  var v: nat := (buf[0] % 64) as nat;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant v == BE([buf[0] % 64] + buf[1..i])
  {
    assert ([buf[0] % 64] + buf[1..i + 1])[..i] == [buf[0] % 64] + buf[1..i];
    v := v * 256 + buf[i] as nat;
    i := i + 1;
  }
  return Some((v, n));
}
