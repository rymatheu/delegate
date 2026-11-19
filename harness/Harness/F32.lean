/-! binary32 values as bit patterns: hexadecimal text (the form records take in files), the
shortest decimal that reads back to the same value (the form people read; never parsed back
into a record), and the neighbors of a value. -/

namespace Harness.F32

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `0x` and eight hexadecimal digits. -/
def hex (w : UInt32) : String := Id.run do
  let mut s := "0x"
  for k in [0:8] do
    s := s.push (hexDigit ((w >>> (UInt32.ofNat (28 - 4 * k))) &&& 0xf).toNat)
  return s

def parseHex? (s : String) : Option UInt32 := do
  let t ← if s.startsWith "0x" then some (s.drop 2).toString else none
  if t.isEmpty || t.length > 8 then none
  let mut v : Nat := 0
  for c in t.toList do
    let d ← if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
            else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
            else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
            else none
    v := v * 16 + d
  return UInt32.ofNat v

def signBit : UInt32 := 0x80000000
def isNaNBits (w : UInt32) : Bool := (w &&& 0x7f800000) == 0x7f800000 && (w &&& 0x007fffff) != 0

/-- The next binary32 value toward +∞ (NaN stays, +∞ stays). -/
def nextUp (w : UInt32) : UInt32 :=
  if isNaNBits w || w == 0x7f800000 then w
  else if w == 0 || w == signBit then 1
  else if w &&& signBit == 0 then w + 1
  else w - 1

/-- The next binary32 value toward −∞. -/
def nextDown (w : UInt32) : UInt32 := (nextUp (w ^^^ signBit)) ^^^ signBit

/-- Round-half-even of num/den. -/
private def roundDiv (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1 else if 2 * r < den then q else if q % 2 == 0 then q else q + 1

/-- n rounded to the nearest multiple of 10^(-k) scaled: round(m·2^e / 10^k). -/
private def scaled (m : Nat) (e : Int) (k : Int) : Nat :=
  let (num, den) :=
    if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  if k ≥ 0 then roundDiv num (den * 10 ^ k.toNat) else roundDiv (num * 10 ^ (-k).toNat) den

private def digitsLen (n : Nat) : Nat := (toString n).length

/-- The shortest decimal (digits n, power k: n·10^k) that reads back to the positive finite
binary32 with bits w. -/
private def shortest (w : UInt32) : Nat × Int := Id.run do
  let ex := ((w >>> 23) &&& 0xff).toNat
  let fr := (w &&& 0x7fffff).toNat
  let (m, e) : Nat × Int := if ex == 0 then (fr, -149) else (fr + 2 ^ 23, (ex : Int) - 150)
  let x := (Float32.ofBits w).toFloat
  let p : Int := (Float.floor (Float.log10 x)).toInt64.toInt
  for d in [1:10] do
    let mut k : Int := p - (d - 1 : Nat)
    let mut n := scaled m e k
    if n ≥ 10 ^ d then
      k := k + 1
      n := scaled m e k
    if n < 10 ^ (d - 1) then
      k := k - 1
      n := scaled m e k
    let back : Float32 :=
      if k ≥ 0 then Float32.ofScientific n false k.toNat else Float32.ofScientific n true (-k).toNat
    if back.toBits == w then
      -- drop trailing zeros
      let mut n' := n
      let mut k' := k
      while n' > 0 && n' % 10 == 0 do
        n' := n' / 10
        k' := k' + 1
      return (n', k')
  return (m, e)  -- not reached: nine digits always suffice for binary32

/-- Decimal text of the digits `ds` times 10^k: plain notation for decimal exponents in
[-5, 10), scientific otherwise. -/
def decimalText (ds : String) (k : Int) : String :=
  let l : Int := ds.length
  let sci := l - 1 + k
  if sci < -5 || sci ≥ 10 then
    let rest := (ds.drop 1).toString
    let mant := if rest.isEmpty then ds else s!"{ds.take 1}.{rest}"
    s!"{mant}e{sci}"
  else if k ≥ 0 then ds ++ "".pushn '0' k.toNat
  else if l + k > 0 then
    let i := (l + k).toNat
    s!"{ds.take i}.{(ds.drop i).toString}"
  else "0." ++ "".pushn '0' (-(l + k)).toNat ++ ds

/-- Readable text of a binary32 bit pattern: the shortest decimal that reads back to the same bits. -/
def text (w : UInt32) : String :=
  let neg := w &&& signBit != 0
  let a := w &&& 0x7fffffff
  let sgn := if neg then "-" else ""
  if isNaNBits w then (if w == 0x7fc00000 then "nan" else s!"nan({hex w})")
  else if a == 0x7f800000 then sgn ++ "inf"
  else if a == 0 then sgn ++ "0"
  else
    let (n, k) := shortest a
    let body := decimalText (toString n) k
    sgn ++ body

end Harness.F32

namespace Harness.F32

/-- A finite nonzero binary64 value to seven significant digits: `(negative, n, k)` with
x ≈ ±n·10^k and no trailing zeros in n. -/
def sig7 (x : Float) : Bool × Nat × Int :=
  let a := x.abs
  let e0 : Int := (Float.floor (Float.log10 a)).toInt64.toInt
  let scale (e : Int) : Float :=
    if e ≥ 0 then a / (10.0 ^ e.toNat.toFloat) else a * (10.0 ^ (-e).toNat.toFloat)
  let (n, e) :=
    let n := (scale e0 * 1e6).round.toUInt64.toNat
    if n ≥ 10000000 then ((scale (e0 + 1) * 1e6).round.toUInt64.toNat, e0 + 1) else (n, e0)
  Id.run do
    let mut n := n
    let mut k : Int := e - 6
    while n > 0 && n % 10 == 0 do
      n := n / 10
      k := k + 1
    return (x < 0, n, k)

/-- A binary64 value with seven significant digits, for reports (margins, ranges). -/
def fmt (x : Float) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x > 0 then "inf" else "-inf")
  else if x == 0 then (if 1.0 / x < 0 then "-0" else "0")
  else
    let (neg, n, k) := sig7 x
    (if neg then "-" else "") ++ decimalText (toString n) k

end Harness.F32
