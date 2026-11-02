// CompactSize de Bitcoin, solo en forma canónica. EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

function LE(s: seq<u8>): nat {
  if |s| == 0 then 0 else s[0] as nat + 256 * LE(s[1..])
}

function Spec(buf: seq<u8>): Option<(nat, nat)> {
  if |buf| == 0 then None
  else if buf[0] < 0xfd then Some((buf[0] as nat, 1))
  else
    var k := if buf[0] == 0xfd then 2 else if buf[0] == 0xfe then 4 else 8;
    var min := if k == 2 then 0xfd else if k == 4 then 0x1_0000 else 0x1_0000_0000;
    if |buf| < k + 1 then None
    else
      var v := LE(buf[1..k + 1]);
      if v < min then None else Some((v, k + 1))
}

method Decode(buf: seq<u8>) returns (r: Option<(nat, nat)>)
  ensures r == Spec(buf)
{
  if |buf| == 0 { return None; }
  if buf[0] < 0xfd { return Some((buf[0] as nat, 1)); }
  var k, min;
  if buf[0] == 0xfd { k, min := 2, 0xfd; }
  else if buf[0] == 0xfe { k, min := 4, 0x1_0000; }
  else { k, min := 8, 0x1_0000_0000; }
  if |buf| < k + 1 { return None; }
  var v: nat := 0;
  var i := k;
  while i >= 1
    invariant 0 <= i <= k
    invariant v == LE(buf[i + 1..k + 1])
  {
    assert buf[i..k + 1][1..] == buf[i + 1..k + 1];
    v := buf[i] as nat + 256 * v;
    i := i - 1;
  }
  return if v < min then None else Some((v, k + 1));
}
