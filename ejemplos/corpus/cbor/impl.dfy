// Cabecera de un elemento CBOR (RFC 8949, §3); información adicional 28..31 es error. EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

function BE(s: seq<u8>): nat {
  if |s| == 0 then 0 else BE(s[..|s| - 1]) * 256 + s[|s| - 1] as nat
}

function Spec(buf: seq<u8>): Option<(nat, nat, nat)> {
  if |buf| == 0 then None
  else
    var mt := buf[0] as nat / 32;
    var ai := buf[0] as nat % 32;
    if ai < 24 then Some((mt, ai, 1))
    else if ai > 27 then None
    else
      var k := if ai == 24 then 1 else if ai == 25 then 2 else if ai == 26 then 4 else 8;
      if |buf| < k + 1 then None
      else if mt == 7 && ai == 24 && BE(buf[1..k + 1]) < 32 then None
      else Some((mt, BE(buf[1..k + 1]), k + 1))
}

method Decode(buf: seq<u8>) returns (r: Option<(nat, nat, nat)>)
  ensures r == Spec(buf)
{
  if |buf| == 0 { return None; }
  var major := buf[0] as nat / 32;
  var info := buf[0] as nat % 32;
  if info < 24 { return Some((major, info, 1)); }
  if info > 27 { return None; }
  var k := if info == 24 then 1 else if info == 25 then 2 else if info == 26 then 4 else 8;
  if |buf| < k + 1 { return None; }
  var arg: nat := 0;
  var i := 1;
  while i <= k
    invariant 1 <= i <= k + 1
    invariant arg == BE(buf[1..i])
  {
    assert buf[1..i + 1][..i - 1] == buf[1..i];
    arg := arg * 256 + buf[i] as nat;
    i := i + 1;
  }
  if major == 7 && info == 24 && arg < 32 { return None; }
  return Some((major, arg, k + 1));
}
