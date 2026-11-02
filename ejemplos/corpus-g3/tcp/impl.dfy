// Opciones de la cabecera TCP (RFC 9293 §3.1 y §3.2; RFC 7323 §2.2–2.3; RFC 2018 §2). EXP-010.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

// Recorrido de opciones desde p. mss y ws valen -1 mientras la opción no ha aparecido.
function Walk(b: seq<u8>, hl: nat, p: nat, mss: int, ws: int, sack: bool): Option<(nat, nat, nat, bool)>
  requires 20 <= p <= hl <= |b|
  decreases hl - p
{
  var done := Some((hl, if mss < 0 then 0xffff else mss as nat, if ws < 0 then 0xff else ws as nat, sack));
  if p == hl || b[p] == 0 then done
  else if b[p] == 1 then Walk(b, hl, p + 1, mss, ws, sack)
  else if p + 1 >= hl then None
  else
    var l := b[p + 1] as nat;
    if l < 2 || p + l > hl then None
    else if b[p] == 2 then
      if l != 4 || mss >= 0 then None
      else Walk(b, hl, p + l, b[p + 2] as int * 256 + b[p + 3] as int, ws, sack)
    else if b[p] == 3 then
      if l != 3 || ws >= 0 then None
      else Walk(b, hl, p + l, mss, if b[p + 2] > 14 then 14 else b[p + 2] as int, sack)
    else if b[p] == 4 then
      if l != 2 || sack then None
      else Walk(b, hl, p + l, mss, ws, true)
    else Walk(b, hl, p + l, mss, ws, sack)
}

function Spec(b: seq<u8>): Option<(nat, nat, nat, bool)>
{
  if |b| < 20 then None
  else if b[12] < 0x50 || 4 * (b[12] as nat / 16) > |b| then None
  else Walk(b, 4 * (b[12] as nat / 16), 20, -1, -1, false)
}

method Parse(b: seq<u8>) returns (r: Option<(nat, nat, nat, bool)>)
  ensures r == Spec(b)
{
  if |b| < 20 { return None; }
  var hl := 4 * (b[12] as nat / 16);
  if b[12] < 0x50 || hl > |b| { return None; }
  var p, mss, ws, sack := 20, -1, -1, false;
  while p < hl
    invariant 20 <= p <= hl
    invariant Walk(b, hl, p, mss, ws, sack) == Spec(b)
    decreases hl - p
  {
    if b[p] == 0 { break; }
    if b[p] == 1 { p := p + 1; continue; }
    if p + 1 >= hl { return None; }
    var l := b[p + 1] as nat;
    if l < 2 || p + l > hl { return None; }
    if b[p] == 2 {
      if l != 4 || mss >= 0 { return None; }
      mss := b[p + 2] as int * 256 + b[p + 3] as int;
    } else if b[p] == 3 {
      if l != 3 || ws >= 0 { return None; }
      ws := if b[p + 2] > 14 then 14 else b[p + 2] as int;
    } else if b[p] == 4 {
      if l != 2 || sack { return None; }
      sack := true;
    }
    p := p + l;
  }
  return Some((hl, if mss < 0 then 0xffff else mss as nat, if ws < 0 then 0xff else ws as nat, sack));
}
