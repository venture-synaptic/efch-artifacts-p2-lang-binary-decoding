// Validación de cabecera IPv4 (RFC 791, §3.1) con suma de comprobación (RFC 1071). EXP-005.

newtype u8 = x: int | 0 <= x < 256
datatype Option<T> = None | Some(value: T)

// Suma de las k primeras palabras de 16 bits en big-endian.
function Sum(h: seq<u8>, k: nat): nat
  requires 2 * k <= |h|
{
  if k == 0 then 0 else Sum(h, k - 1) + h[2 * k - 2] as nat * 256 + h[2 * k - 1] as nat
}

function Fold(s: nat): nat { s % 65536 + s / 65536 }

function Spec(h: seq<u8>): Option<(nat, nat)> {
  if |h| < 20 then None
  else
    var ver, ihl := h[0] as nat / 16, h[0] as nat % 16;
    var tot := h[2] as nat * 256 + h[3] as nat;
    if ver != 4 || ihl < 5 || |h| < 4 * ihl || tot < 4 * ihl then None
    else if Fold(Fold(Sum(h, 2 * ihl))) == 0xffff then Some((ihl, tot))
    else None
}

method Check(h: seq<u8>) returns (r: Option<(nat, nat)>)
  ensures r == Spec(h)
{
  if |h| < 20 { return None; }
  var version, ihl := h[0] as nat / 16, h[0] as nat % 16;
  var total := h[2] as nat * 256 + h[3] as nat;
  if version != 4 || ihl < 5 || |h| < 4 * ihl || total < 4 * ihl { return None; }
  var sum := 0;
  var i := 0;
  while i < 2 * ihl
    invariant 0 <= i <= 2 * ihl
    invariant sum == Sum(h, i)
  {
    sum := sum + h[2 * i] as nat * 256 + h[2 * i + 1] as nat;
    i := i + 1;
  }
  sum := Fold(Fold(sum));
  return if sum == 0xffff then Some((ihl, total)) else None;
}
