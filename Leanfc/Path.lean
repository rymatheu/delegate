import Leanfc.Vec3

/-!
# Path

One leg of the navigator's path: the cubic Hermite curve from `p0` to `p1` with end tangents `m0`,
`m1` (derivatives with respect to the path parameter τ ∈ [0, 1]):

  p(τ) = h00·p0 + h01·p1 + h10·m0 + h11·m1,
  h00 = 2τ³ − 3τ² + 1,  h01 = −2τ³ + 3τ²,  h10 = τ³ − 2τ² + τ,  h11 = τ³ − τ².

A straight leg is the Hermite leg with m0 = m1 = p1 − p0 (`line`), which is p0 + τ(p1 − p0); the
same evaluator serves both kinds of leg.

**Ends are exact in binary32.** At τ = 0 and τ = 1 every basis value is computed exactly (products
and sums of 0, 1, 2, 3), so h00 = 1 and the others 0 at τ = 0, h01 = 1 and the others 0 at τ = 1.
The sum is grouped (h00·p0 + h01·p1) + (h10·m0 + h11·m1): at τ = 0 it is (p0 + ±0) + (±0 + ±0),
which is p0 bit for bit unless a coordinate of p0 is −0 (then +0 may come out). `Navigator.make`
stores every end point as w + 0, which turns −0 into +0 and changes nothing else, so `eval h 0`
is `h.p0` and `eval h 1` is `h.p1` bit for bit (`Checks` confirms it on every shipped leg).

`deriv` is p′(τ) = 6(τ − τ²)(p1 − p0) + h10′·m0 + h11′·m1 (h00′ = −h01′ = 6τ² − 6τ), `deriv2` is
p″(τ) = (6 − 12τ)(p1 − p0) + (6τ − 4)·m0 + (6τ − 2)·m1, and `curvature` is
κ = ‖p′ × p″‖ / ‖p′‖³ (0 where ‖p′‖ = 0).
-/

structure Hermite where
  p0 : Vec3
  m0 : Vec3
  p1 : Vec3
  m1 : Vec3
  deriving Inhabited, Repr

namespace Path

/-- The straight leg from `a` to `b`: tangents b − a at both ends. -/
def line (a b : Vec3) : Hermite := let d := b - a; ⟨a, d, b, d⟩

/-- p(τ). -/
def eval (h : Hermite) (τ : R) : Vec3 :=
  let t2 := τ * τ
  let t3 := t2 * τ
  let h00 := 2 * t3 - 3 * t2 + 1
  let h01 := 3 * t2 - 2 * t3
  let h10 := t3 - 2 * t2 + τ
  let h11 := t3 - t2
  (Vec3.scale h00 h.p0 + Vec3.scale h01 h.p1) + (Vec3.scale h10 h.m0 + Vec3.scale h11 h.m1)

/-- p′(τ). -/
def deriv (h : Hermite) (τ : R) : Vec3 :=
  let t2 := τ * τ
  Vec3.scale (6 * (τ - t2)) (h.p1 - h.p0) + Vec3.scale (3 * t2 - 4 * τ + 1) h.m0 +
    Vec3.scale (3 * t2 - 2 * τ) h.m1

/-- p″(τ). -/
def deriv2 (h : Hermite) (τ : R) : Vec3 :=
  Vec3.scale (6 - 12 * τ) (h.p1 - h.p0) + Vec3.scale (6 * τ - 4) h.m0 + Vec3.scale (6 * τ - 2) h.m1

/-- Curvature κ = ‖p′ × p″‖ / ‖p′‖³ (1/m); 0 where p′ = 0. -/
def curvature (h : Hermite) (τ : R) : R :=
  let d1 := deriv h τ
  let n := Vec3.norm d1
  if n > 0 then Vec3.norm (Vec3.cross d1 (deriv2 h τ)) / (n * n * n) else 0

end Path
