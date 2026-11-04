/-!
# Text helpers for the `copter` executable

Splitting lines into words, reading decimal numbers, and printing binary floating-point values
exactly. Rewritten from the helpers of `Flight/Main.lean` (`Flight.Cli.words`, `parseFloat?`,
`exactDecimal`), with one change: a number is read into an exact decimal record and rounded once,
directly to the target format (`Float32.ofScientific` or `Float.ofScientific`), so a `float`
parameter or input is the correctly rounded `float` of the decimal text, as `strtof` gives, not a
`double` rounded again to `float`.

Not ArduPilot code.
-/

namespace Copter.Text

/-- Split a line into its whitespace-separated words. -/
def words (line : String) : List String :=
  let step := fun (acc : List String × List Char) (c : Char) =>
    if c.isWhitespace then
      (if acc.2.isEmpty then acc.1 else String.ofList acc.2.reverse :: acc.1, [])
    else (acc.1, c :: acc.2)
  let (ws, cur) := line.toList.foldl step ([], [])
  (if cur.isEmpty then ws else String.ofList cur.reverse :: ws).reverse

/-- Read a non-empty string of decimal digits as a natural number. -/
def digits? (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldl (fun acc c => acc.bind fun n =>
    if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

/-- Read an optional sign, returning whether it was a minus and the remaining characters. -/
def sign (cs : List Char) : Bool × List Char :=
  match cs with
  | '-' :: rest => (true, rest)
  | '+' :: rest => (false, rest)
  | _ => (false, cs)

/-- An exact decimal number `(-1)^neg · m · 10^e`. -/
structure Decimal where
  neg : Bool
  m : Nat
  e : Int
deriving Repr

/-- Parse a decimal number such as `-12`, `0.5`, `.25` or `1.5e-3`. -/
def parseDecimal? (s : String) : Option Decimal := do
  let (neg, body) := sign s.toList
  let (mant, expPart) := body.span (fun c => c != 'e' && c != 'E')
  let (intPart, fracPart) := mant.span (· != '.')
  let fracDigits := fracPart.drop 1
  if intPart.isEmpty && fracDigits.isEmpty then none
  let m ← digits? (intPart ++ fracDigits)
  let e : Int ← match expPart with
    | [] => pure 0
    | _ :: rest =>
      let (eneg, edigits) := sign rest
      let n ← digits? edigits
      pure (if eneg then -(n : Int) else n)
  pure ⟨neg, m, e - fracDigits.length⟩

/-- The `float` nearest to the decimal (one rounding). -/
def Decimal.toFloat32 (d : Decimal) : Float32 :=
  let mag := if d.e < 0 then Float32.ofScientific d.m true d.e.natAbs
    else Float32.ofScientific d.m false d.e.toNat
  if d.neg then -mag else mag

/-- The `double` nearest to the decimal (one rounding). -/
def Decimal.toFloat (d : Decimal) : Float :=
  let mag := if d.e < 0 then Float.ofScientific d.m true d.e.natAbs
    else Float.ofScientific d.m false d.e.toNat
  if d.neg then -mag else mag

/-- The decimal as an integer, if it is one. -/
def Decimal.toInt? (d : Decimal) : Option Int :=
  let mag : Option Nat :=
    if 0 ≤ d.e then some (d.m * 10 ^ d.e.toNat)
    else
      let q := 10 ^ d.e.natAbs
      if d.m % q == 0 then some (d.m / q) else none
  mag.map fun n => if d.neg then -(n : Int) else n

/-- The exact decimal expansion of a finite binary64 value (`nan`, `inf`, `-inf` otherwise);
trailing fractional zeros are dropped. Same as `Flight.Cli.exactDecimal`. -/
def exactDecimal (x : Float) : String :=
  if x.isNaN then "nan"
  else if x.isInf then (if x < 0 then "-inf" else "inf")
  else
    let bits : Nat := x.toBits.toNat
    let neg := bits / 2 ^ 63 == 1
    let expField : Nat := (bits / 2 ^ 52) % 2048
    let frac : Nat := bits % 2 ^ 52
    -- value = m * 2^e
    let (m, e) : Nat × Int :=
      if expField == 0 then (frac, -1074) else (frac + 2 ^ 52, Int.ofNat expField - 1075)
    let body :=
      if 0 ≤ e then toString (m * 2 ^ e.toNat)
      else
        let k := e.natAbs
        -- m / 2^k = m * 5^k / 10^k
        let ds := (toString (m * 5 ^ k)).toList
        let ds := List.replicate (k + 1 - ds.length) '0' ++ ds
        let intPart := ds.take (ds.length - k)
        let fracPart := ((ds.drop (ds.length - k)).reverse.dropWhile (· == '0')).reverse
        if fracPart.isEmpty then String.ofList intPart
        else String.ofList intPart ++ "." ++ String.ofList fracPart
    if neg && m != 0 then "-" ++ body else body

/-- The exact decimal expansion of a `float` (widening to `double` is exact). -/
def exactDecimal32 (x : Float32) : String := exactDecimal x.toFloat

/-- A `float` printed exactly if `exact`, else by `Float32.toString` (six decimals). -/
def fmt32 (exact : Bool) (x : Float32) : String := if exact then exactDecimal32 x else toString x

/-- A `double` printed exactly if `exact`, else by `Float.toString`. -/
def fmt64 (exact : Bool) (x : Float) : String := if exact then exactDecimal x else toString x

end Copter.Text
