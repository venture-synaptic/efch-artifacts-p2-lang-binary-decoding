// Bloque base64 de 4 caracteres (RFC 4648, §4); bits de relleno no nulos rechazados. EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

// Valor de un carácter del alfabeto estándar; 64 si no pertenece a él.
function Sextet(c: u8): nat {
  if 65 <= c <= 90 then (c - 65) as nat
  else if 97 <= c <= 122 then (c - 71) as nat
  else if 48 <= c <= 57 then (c + 4) as nat
  else if c == 43 then 62 else if c == 47 then 63 else 64
}

function Spec(s: seq<u8>): Option<(nat, nat)> {
  if |s| != 4 then None
  else
    var v0, v1, v2, v3 := Sextet(s[0]), Sextet(s[1]), Sextet(s[2]), Sextet(s[3]);
    var p2, p3 := s[2] == 61, s[3] == 61;
    if v0 == 64 || v1 == 64 || (p2 && !p3) || (!p2 && v2 == 64) || (!p3 && v3 == 64) then None
    else
      var w := v0 * 262144 + v1 * 4096 + (if p2 then 0 else v2) * 64 + (if p3 then 0 else v3);
      if p2 then (if w % 65536 != 0 then None else Some((w / 65536, 1)))
      else if p3 then (if w % 256 != 0 then None else Some((w / 256, 2)))
      else Some((w, 3))
}

method Decode(s: seq<u8>) returns (r: Option<(nat, nat)>)
  ensures r == Spec(s)
{
  if |s| != 4 { return None; }
  var a, b := Sextet(s[0]), Sextet(s[1]);
  if a == 64 || b == 64 { return None; }
  var w := a * 262144 + b * 4096;
  if s[2] == 61 && s[3] == 61 {
    return if w % 65536 == 0 then Some((w / 65536, 1)) else None;
  }
  var c := Sextet(s[2]);
  if c == 64 { return None; }
  w := w + c * 64;
  if s[3] == 61 {
    return if w % 256 == 0 then Some((w / 256, 2)) else None;
  }
  var d := Sextet(s[3]);
  if d == 64 { return None; }
  return Some((w + d, 3));
}
