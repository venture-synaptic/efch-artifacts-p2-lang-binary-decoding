// Primer punto de código UTF-8 (RFC 3629, §3 y §4). EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

// Añade a acc los 6 bits bajos de cada byte de continuación.
function Cont(acc: nat, s: seq<u8>): nat {
  if |s| == 0 then acc else Cont(acc, s[..|s| - 1]) * 64 + (s[|s| - 1] % 64) as nat
}

function Spec(buf: seq<u8>): Option<(nat, nat)> {
  if |buf| == 0 then None
  else
    var b0 := buf[0] as nat;
    var n := if b0 < 0x80 then 1 else if b0 < 0xc0 then 0 else if b0 < 0xe0 then 2
             else if b0 < 0xf0 then 3 else if b0 < 0xf8 then 4 else 0;
    if n == 0 || |buf| < n || exists j :: 1 <= j < n && buf[j] / 64 != 2 then None
    else
      var lead := if n == 1 then b0 else if n == 2 then b0 % 32 else if n == 3 then b0 % 16 else b0 % 8;
      var cp := Cont(lead, buf[1..n]);
      var min := if n == 1 then 0 else if n == 2 then 0x80 else if n == 3 then 0x800 else 0x10000;
      if cp < min || (0xd800 <= cp <= 0xdfff) || cp > 0x10ffff then None else Some((cp, n))
}

method Decode(buf: seq<u8>) returns (r: Option<(nat, nat)>)
  ensures r == Spec(buf)
{
  if |buf| == 0 { return None; }
  var b0 := buf[0] as nat;
  var n, min, cp;
  if b0 < 0x80 { return Some((b0, 1)); }
  else if b0 < 0xc0 { return None; }
  else if b0 < 0xe0 { n, min, cp := 2, 0x80, b0 % 32; }
  else if b0 < 0xf0 { n, min, cp := 3, 0x800, b0 % 16; }
  else if b0 < 0xf8 { n, min, cp := 4, 0x10000, b0 % 8; }
  else { return None; }
  if |buf| < n { return None; }
  ghost var lead := cp;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall j :: 1 <= j < i ==> buf[j] / 64 == 2
    invariant cp == Cont(lead, buf[1..i])
  {
    if buf[i] / 64 != 2 { return None; }
    assert buf[1..i + 1][..i - 1] == buf[1..i];
    cp := cp * 64 + (buf[i] % 64) as nat;
    i := i + 1;
  }
  if cp < min || (0xd800 <= cp <= 0xdfff) || cp > 0x10ffff { return None; }
  return Some((cp, n));
}
