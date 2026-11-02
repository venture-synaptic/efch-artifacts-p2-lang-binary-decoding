// Entero de MessagePack: fixint positivo y negativo, uint8..64 e int8..64. EXP-005.
// Los negativos se devuelven en complemento a dos de 64 bits.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

function BE(s: seq<u8>): nat {
  if |s| == 0 then 0 else BE(s[..|s| - 1]) * 256 + s[|s| - 1] as nat
}

function Len(tag: nat): nat { if tag % 4 == 0 then 1 else if tag % 4 == 1 then 2 else if tag % 4 == 2 then 4 else 8 }

// 2^(8k) para k = 1, 2, 4, 8.
function Range(k: nat): nat {
  if k == 1 then 0x100 else if k == 2 then 0x1_0000 else if k == 4 then 0x1_0000_0000 else 0x1_0000_0000_0000_0000
}

function Spec(buf: seq<u8>): Option<(nat, bool, nat)> {
  if |buf| == 0 then None
  else
    var b0 := buf[0] as nat;
    if b0 < 0x80 then Some((b0, false, 1))
    else if b0 >= 0xe0 then Some((b0 + 0x1_0000_0000_0000_0000 - 256, true, 1))
    else if b0 < 0xcc || b0 > 0xd3 then None
    else
      var sg := b0 >= 0xd0;
      var k := Len(b0);
      if |buf| < k + 1 then None
      else
        var u := BE(buf[1..k + 1]);
        var v := if sg && u >= Range(k) / 2 then u + 0x1_0000_0000_0000_0000 - Range(k) else u;
        Some((v, sg, k + 1))
}

method Decode(buf: seq<u8>) returns (r: Option<(nat, bool, nat)>)
  ensures r == Spec(buf)
{
  if |buf| == 0 { return None; }
  var tag := buf[0] as nat;
  if tag < 0x80 { return Some((tag, false, 1)); }
  if tag >= 0xe0 { return Some((tag + 0x1_0000_0000_0000_0000 - 256, true, 1)); }
  if tag < 0xcc || tag > 0xd3 { return None; }
  var signed := tag >= 0xd0;
  var k := Len(tag);
  if |buf| < k + 1 { return None; }
  var u: nat := 0;
  var i := 1;
  while i <= k
    invariant 1 <= i <= k + 1
    invariant u == BE(buf[1..i])
  {
    assert buf[1..i + 1][..i - 1] == buf[1..i];
    u := u * 256 + buf[i] as nat;
    i := i + 1;
  }
  if signed && u >= Range(k) / 2 { u := u + 0x1_0000_0000_0000_0000 - Range(k); }
  return Some((u, signed, k + 1));
}
