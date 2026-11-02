// Nombre de host (RFC 1123 §2.1, RFC 952) en formato de cable DNS (RFC 1035 §3.1 y §4.1.4). EXP-007.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

predicate IsLdh(c: u8) {
  (0x61 <= c <= 0x7a) || (0x41 <= c <= 0x5a) || (0x30 <= c <= 0x39) || c == 0x2d
}

// La etiqueta de longitud l que empieza tras el octeto p es LDH y no empieza ni termina por guion.
predicate ValidLabel(b: seq<u8>, p: nat, l: nat)
  requires 1 <= l && p + l < |b|
{
  b[p + 1] != 0x2d && b[p + l] != 0x2d && forall j :: p < j <= p + l ==> IsLdh(b[j])
}

function Spec(b: seq<u8>, p: nat, labels: nat): Option<(nat, nat, nat)>
  decreases |b| - p
{
  if p >= |b| then None
  else if b[p] == 0 then Some((p + 1, labels, 0xffff))
  else if b[p] >= 0xc0 then
    if p + 1 < |b| then Some((p + 2, labels, (b[p] as nat - 0xc0) * 256 + b[p + 1] as nat)) else None
  else if b[p] >= 0x40 then None
  else if p + b[p] as nat < |b| && ValidLabel(b, p, b[p] as nat) then Spec(b, p + 1 + b[p] as nat, labels + 1)
  else None
}

method Parse(b: seq<u8>) returns (r: Option<(nat, nat, nat)>)
  ensures r == Spec(b, 0, 0)
{
  var pos, labels := 0, 0;
  while pos < |b|
    invariant Spec(b, pos, labels) == Spec(b, 0, 0)
    decreases |b| - pos
  {
    var n := b[pos] as nat;
    if n == 0 { return Some((pos + 1, labels, 0xffff)); }
    if n >= 0xc0 {
      if pos + 1 >= |b| { return None; }
      return Some((pos + 2, labels, (n - 0xc0) * 256 + b[pos + 1] as nat));
    }
    if n >= 0x40 || pos + n >= |b| || b[pos + 1] == 0x2d || b[pos + n] == 0x2d { return None; }
    var j := pos + 1;
    while j <= pos + n
      invariant pos + 1 <= j <= pos + n + 1
      invariant forall k :: pos < k < j ==> IsLdh(b[k])
    {
      if !IsLdh(b[j]) { return None; }
      j := j + 1;
    }
    labels := labels + 1;
    pos := pos + 1 + n;
  }
  return None;
}
