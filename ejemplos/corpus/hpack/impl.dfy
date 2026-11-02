// Entero de HPACK con prefijo de N bits (RFC 7541, §5.1), valor ≤ 2^32-1 y ≤ 6 bytes. EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

function Pow(b: nat, e: nat): nat
  ensures b > 0 ==> Pow(b, e) > 0
{
  if e == 0 then 1 else b * Pow(b, e - 1)
}

// Suma de los grupos de 7 bits en little-endian.
function LE7(s: seq<u8>): nat {
  if |s| == 0 then 0 else LE7(s[..|s| - 1]) + (s[|s| - 1] % 128) as nat * Pow(128, |s| - 1)
}

// Primer t' ≥ t, con t' < min(|buf|, 6), cuyo byte no tiene el bit de continuación.
function Term(buf: seq<u8>, t: nat): Option<nat>
  decreases 6 - t
{
  if t >= 6 || t >= |buf| then None else if buf[t] < 128 then Some(t) else Term(buf, t + 1)
}

function Spec(n: nat, buf: seq<u8>): Option<(nat, nat)> {
  if n < 1 || n > 8 || |buf| == 0 then None
  else
    var mask := Pow(2, n) - 1;
    var p := buf[0] as nat % Pow(2, n);
    if p < mask then Some((p, 1))
    else match Term(buf, 1)
         case None => None
         case Some(t) =>
           var v := mask + LE7(buf[1..t + 1]);
           if v > 0xffff_ffff then None else Some((v, t + 1))
}

method Decode(n: nat, buf: seq<u8>) returns (r: Option<(nat, nat)>)
  ensures r == Spec(n, buf)
{
  if n < 1 || n > 8 || |buf| == 0 { return None; }
  var mask := Pow(2, n) - 1;
  var v := buf[0] as nat % Pow(2, n);
  if v < mask { return Some((v, 1)); }
  var i := 1;
  var m: nat := 1;
  while i < |buf| && i < 6
    invariant 1 <= i <= |buf| && i <= 6
    invariant Term(buf, 1) == Term(buf, i)
    invariant m == Pow(128, i - 1)
    invariant v == mask + LE7(buf[1..i])
  {
    assert buf[1..i + 1][..i - 1] == buf[1..i];
    v := v + (buf[i] % 128) as nat * m;
    if buf[i] < 128 {
      if v > 0xffff_ffff { return None; }
      return Some((v, i + 1));
    }
    m := m * 128;
    i := i + 1;
  }
  return None;
}
