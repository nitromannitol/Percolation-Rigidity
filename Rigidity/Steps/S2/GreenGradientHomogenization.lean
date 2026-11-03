import Rigidity.Draft.Section2Statements
import Rigidity.External.CorrectorQuantitative
import LatticeProb.External.GreenQuantitative
import LatticeProb.Prob.Percolation.LatticeClusterL2

/-!
# Proposition 2.6: the steps of the homogenization of the gradient of the Green function

Proposition 2.6 (paper L463-476 statement, L497-655 proof of the corrected draft), in the
forward-difference reading [C4]: beyond a minimal scale `M(y) ≤ O_s(C)`,
`|D⁺G(x, y) - ∑ᵢ D⁺ℓ_{eᵢ}(x) ∂ᵢḠ(x - y)| ≤ C |x - y|^{-1/2 + δ} |x - y|^{1 - d}`.

Notation: `R = |x - y|₂ / 2`, `u = G(·, y) - K(y) - Ḡ(x - y)` (`K(y)` the constant at infinity of
Dario–Gu in `d = 2`, zero in `d ≥ 3`), and `ℓ_{eᵢ} = xᵢ + χ_{eᵢ}` the corrected planes.

## Local properties at a vertex `x` and a scale `X` (deterministic)

* `GreenCloseAt` (H1, eq. (green-homogenziation)): `|G(z, y) - Ḡ(z - y) - K| ≤ C |z - y|^{1-d+η}`
  beyond `X`.
* `RegularityAt` (H2, eq. (large scale-regularity)): Theorem 2.4 at order one, with the element of
  `𝒜₁` written as `∑ᵢ ξᵢ ℓ_{eᵢ} + a` (Theorem 2.5).
* `CorrectorBoundAt` (H3, eq. (corrector-sublinearity-and-lipschitz)): oscillation and gradient
  of the corrector `χ_q` on `B_r(x)` at most `C |q|₁ r^η` for `r ≥ X`.
* `DenseAt` (H4, the density estimate of Penrose–Pisztora): every ball of radius `r/100` centred
  in `B_r(x)` has at least `c r^d` vertices of the cluster, for `r ≥ X`.

## Steps

* `step:2.6-inputs`.
  - `RegularityScaleStep`: (H2) beyond a minimal scale `M_reg(x) ≤ O_s(C)`. Its proof combines
    Theorem 2.4 at order one (proposed literature input `ArmstrongDarioOrderOne`, [C34])
    with the classification of `𝒜₁` (`LatticeProb.External.SupercriticalBondCorrectorInput`).
  - `DensityScaleStep`: (H4) beyond a minimal scale `M_dense(x) ≤ O_s(C)`. This is the density
    estimate the paper cites from Penrose–Pisztora, Theorem 1 (proposed literature input
    `ClusterDensityInput`; for bond percolation, Dario–Gu, Proposition A.1 [C35]).
  - `TailOfOsStep`: `X ≤ O_s(θ)` gives a stretched exponential tail (Markov's inequality).
  - (H1) and (H3) come from `SupercriticalBondGreenQuantitative` (`greenClose_scales` below) and
    `CorrectorQuantitativeInput` (with `α = δ/4`).
* `step:2.6-continuum`. `ContinuumGreenStep`: `|∇Ḡ(v)| ≤ C |v|^{1-d}` and the Taylor bound
  `|Ḡ(v + w) - Ḡ(v) - ∇Ḡ(v)·w| ≤ C |w|² |v|^{-d}` for `|w| ≤ |v|/2`
  (eqs. (green-gradient-estimate), (green-hessian-estimate), (green-taylor-expansion)).
* `step:2.6-reduction` (Step 2). `MinimalScaleStep`: the union bound turning the pointwise scales
  `A X(x, y)^N` into `M(y) := sup {|x - y| : A X(x, y)^N ≥ |x - y|} ≤ O_s(C)`.
* `step:2.6-expansion` (Step 3).
  - `GreenOscillationStep`: `|u| ≤ C R^{2-d}` on `B_R(x)` (H1 and `ContinuumGreenStep`); this
    replaces eq. (decay-estimate), which fails in `d = 2`.
  - `AffineMajorizationStep`: under (H4), the `L̲²(𝒞_∞ ∩ B_r(x))` norm of an affine function
    majorizes `r` times its slope.
  - `SlopeEstimateStep`: the slope `ξ` of the regularity estimate satisfies
    `|ξ - ∇Ḡ(x - y)|₁ ≤ C R^{1/2 - d + δ/4}` (choice `r = R^{1/2}`; uses `ContinuumGreenStep`,
    `AffineMajorizationStep`).
  - `GreenGradientCoreStep`: the deterministic pointwise bound at `x` from (H1)-(H4) when
    `|x - y| ≥ A X^N` (uses `GreenOscillationStep`, `SlopeEstimateStep`). The paper's passage
    through Caccioppoli's inequality and the `L²` gradient bound is replaced by the pointwise
    bound `|D⁺v(x)| ≤ 2 |𝒞_∞ ∩ B_X(x)|^{1/2} ‖v‖_{L̲²(B_X(x))}` for
    `v = u - ∑ᵢ ξᵢ ℓ_{eᵢ} - a`.

`greenGradientHomogenization_of_steps` proves Proposition 2.6 from the top-level steps
`RegularityScaleStep`, `DensityScaleStep`, `TailOfOsStep`, `MinimalScaleStep`,
`GreenGradientCoreStep` and the inputs `SupercriticalBondGreenQuantitative`,
`CorrectorQuantitativeInput`.
-/

namespace Rigidity.Steps.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Section2

variable {d : ℕ}

/-- The `ℓ¹` distance `|x - y|` of two vertices, the norm of the statement of Proposition 2.6. -/
def latticeL1Dist (x y : Vertex d) : ℝ := ∑ i, |((x i - y i : ℤ) : ℝ)|

/-- `X` has a stretched exponential tail, `P[X ≥ R] ≤ C exp(-R^s / C)` for `R ≥ 0` (the form of
the minimal scales of `SupercriticalBondGreenQuantitative`). -/
def HasStretchedExpTail (d : ℕ) (p : unitInterval) (X : Configuration d → ℝ) (s C : ℝ) : Prop :=
  ∀ R : ℝ, 0 ≤ R →
    latticeBondLaw d p {ω | R ≤ X ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))

/-! ### Local properties at a vertex and a scale -/

/-- (H1) Homogenization of the Green function beyond the scale `X`: for `z` with
`|z - y| ≥ X`, `|G(z, y) - Ḡ(z - y) - K| ≤ C₀ / (|z - y|^{1-η} |z - y|^{d-2})`. -/
def GreenCloseAt (hd : 2 ≤ d) (κ : {a : ℝ // 0 < a}) {ω : Configuration d} (C : OpenComponent ω)
    (y : C) (g : C → ℝ) (K C₀ η X : ℝ) : Prop :=
  ∀ z : C, ∀ v : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
    v.val = latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding y.val → X ≤ ‖v.val‖ →
      |g z - continuumGreen d hd κ v - K| ≤ C₀ / (Real.rpow ‖v.val‖ (1 - η) * ‖v.val‖ ^ (d - 2))

/-- (H2) Large-scale `C^{1,1}` regularity at `x` beyond the scale `X` (eq. (large
scale-regularity)): for `R ≥ 2X` and `u` harmonic in the interior of `𝒞 ∩ B_R(x)` there are a
slope `ξ` and a constant `a` with `‖u - ∑ᵢ ξᵢ ℓᵢ - a‖_{L̲²(B_r(x))} ≤ C₀ (r/R)² ‖u‖_{L̲²(B_R(x))}`
for every `r ∈ [X, R/2]`. -/
def RegularityAt {ω : Configuration d} (C : OpenComponent ω) (ℓ : Fin d → C → ℝ) (x : Vertex d)
    (C₀ X : ℝ) : Prop :=
  ∀ R : ℝ, 2 * X ≤ R → ∀ u : C → ℝ,
    (∀ z ∈ componentEuclideanBall C x R,
      (∀ w : C, (componentGraph C).Adj z w → w ∈ componentEuclideanBall C x R) →
        componentLaplacian C u z = 0) →
    ∃ (ξ : Fin d → ℝ) (a : ℝ), ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
      componentBallL2 C x r (fun z => u z - ∑ i, ξ i * ℓ i z - a) ≤
        C₀ * (r / R) ^ 2 * componentBallL2 C x R u

/-- (H3) Sublinearity and Lipschitz bound of the correctors at `x` beyond the scale `X`, in the
form of `CorrectorQuantitativeInput`. -/
def CorrectorBoundAt {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d) (C₀ η X : ℝ) :
    Prop :=
  ∀ (q : Fin d → ℝ) (ℓ : C → ℝ), IsCorrectedPlane C q ℓ → ∀ r : ℝ, X ≤ r →
    ∀ a b a' b' : C,
      ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
      ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
      ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
      ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
      (componentGraph C).Adj a' b' →
      |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
          |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
        ≤ C₀ * (∑ i, |q i|) * r ^ η

/-- (H4) Density of the cluster at `x` beyond the scale `X`: for `r ≥ X`, every ball of radius
`r/100` centred at a vertex of `B̄_r(x)` contains at least `c r^d` vertices of `𝒞`. -/
def DenseAt {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d) (c X : ℝ) : Prop :=
  ∀ r : ℝ, X ≤ r → ∀ z : Vertex d,
    dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) ≤ r →
      c * r ^ d ≤ ((componentEuclideanBall C z (r / 100)).card : ℝ)

theorem GreenCloseAt.mono {hd : 2 ≤ d} {κ : {a : ℝ // 0 < a}} {ω : Configuration d}
    {C : OpenComponent ω} {y : C} {g : C → ℝ} {K C₀ η X Y : ℝ}
    (h : GreenCloseAt hd κ C y g K C₀ η X) (hXY : X ≤ Y) : GreenCloseAt hd κ C y g K C₀ η Y :=
  fun z v hv hY => h z v hv (hXY.trans hY)

theorem RegularityAt.mono {ω : Configuration d} {C : OpenComponent ω} {ℓ : Fin d → C → ℝ}
    {x : Vertex d} {C₀ X Y : ℝ} (h : RegularityAt C ℓ x C₀ X) (hXY : X ≤ Y) :
    RegularityAt C ℓ x C₀ Y := by
  intro R hR u hu
  obtain ⟨ξ, a, hξ⟩ := h R (by linarith) u hu
  exact ⟨ξ, a, fun r hr hrR => hξ r (hXY.trans hr) hrR⟩

theorem DenseAt.mono {ω : Configuration d} {C : OpenComponent ω} {x : Vertex d} {c X Y : ℝ}
    (h : DenseAt C x c X) (hXY : X ≤ Y) : DenseAt C x c Y :=
  fun r hr => h r (hXY.trans hr)

/-! ### step:2.6-inputs -/

/-- step:2.6-inputs, regularity (paper L513-519): Theorems 2.4 and 2.5 combine into (H2) beyond a
minimal scale `M_reg(x) ≤ O_s(C)`, for every family of corrected planes `ℓ_{eᵢ}`. Its proof needs
Theorem 2.4 at order one (proposed input `ArmstrongDarioOrderOne`) and the classification of `𝒜₁`
of `SupercriticalBondCorrectorInput`. -/
def RegularityScaleStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C₀ : ℝ, 0 < s ∧ 0 < C₀ ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
        Rigidity.External.IsOsBond d p M s C₀ ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ ℓ : Fin d → uniqueInfiniteComponent h → ℝ,
            (∀ i, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) (ℓ i)) →
            RegularityAt (uniqueInfiniteComponent h) ℓ x C₀ (M ω)

/-- step:2.6-inputs, density (paper L508-511): (H4) beyond a minimal scale
`M_dense(x) ≤ O_s(C)`. This is the density estimate cited from Penrose–Pisztora, Theorem 1
(proposed input `ClusterDensityInput`). -/
def DensityScaleStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C c : ℝ, 0 < s ∧ 0 < C ∧ 0 < c ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
        Rigidity.External.IsOsBond d p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          DenseAt (uniqueInfiniteComponent h) x c (M ω)

/-- step:2.6-inputs, tails: `X ≤ O_s(θ)` gives `P[X ≥ R] ≤ C exp(-R^s / C)`, with `C` depending
only on `s` and `θ` (Markov's inequality applied to `exp((X/θ ∨ 0)^s)`). -/
def TailOfOsStep (d : ℕ) (p : unitInterval) : Prop :=
  ∀ s θ : ℝ, 0 < s → 0 < θ → ∃ C : ℝ, 0 < C ∧ ∀ X : Configuration d → ℝ, Measurable X →
    Rigidity.External.IsOsBond d p X s θ → HasStretchedExpTail d p X s C

/-! ### step:2.6-continuum -/

/-- step:2.6-continuum (eqs. (green-gradient-estimate), (green-hessian-estimate),
(green-taylor-expansion)): `‖∇Ḡ(v)‖ ≤ C |v|^{1-d}` and, for `|w| ≤ |v|/2`,
`|Ḡ(v + w) - Ḡ(v) - ∇Ḡ(v)·w| ≤ C |w|² |v|^{-d}`, from the explicit formula of `Ḡ`. -/
def ContinuumGreenStep (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ κ : {a : ℝ // 0 < a}, ∃ Cg : ℝ, 0 < Cg ∧ ∀ v : EuclideanSpace ℝ (Fin d), v ≠ 0 →
    ‖fderiv ℝ (greenBar d hd κ) v‖ ≤ Cg * ‖v‖ ^ (1 - (d : ℝ)) ∧
    ∀ w : EuclideanSpace ℝ (Fin d), 2 * ‖w‖ ≤ ‖v‖ →
      |greenBar d hd κ (v + w) - greenBar d hd κ v - fderiv ℝ (greenBar d hd κ) v w| ≤
        Cg * ‖w‖ ^ 2 * ‖v‖ ^ (-(d : ℝ))

/-! ### step:2.6-reduction -/

/-- step:2.6-reduction (paper L563-576): the union bound. For families `X i x` (`i < k`, `x ∈ ℤ^d`)
of scales with uniform stretched exponential tails, there is `M(y) ≤ O_{s'}(C')` such that almost
surely `A (X i x ∨ 2)^N < |x - y|` for every `i` and every `x` with `|x - y| ≥ M(y)`. The constant
`C'` may be taken at least `A`. -/
def MinimalScaleStep (d : ℕ) (p : unitInterval) : Prop :=
  ∀ (k : ℕ) (s C : Fin k → ℝ) (A : ℝ) (N : ℕ), (∀ i, 0 < s i) → (∀ i, 0 < C i) → 0 < A →
    ∃ s' C' : ℝ, 0 < s' ∧ A ≤ C' ∧
      ∀ (y : Vertex d) (X : Fin k → Vertex d → Configuration d → ℝ),
        (∀ i x, Measurable (X i x)) → (∀ i x, HasStretchedExpTail d p (X i x) (s i) (C i)) →
        ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOs d p M s' C' ∧
          ∀ᵐ ω ∂latticeBondLaw d p, ∀ x : Vertex d, M ω ≤ latticeL1Dist x y →
            ∀ i, A * max (X i x ω) 2 ^ N < latticeL1Dist x y

/-! ### step:2.6-expansion -/

/-- step:2.6-expansion, size of `u` (replacing eq. (decay-estimate)): under (H1), on the ball
`B_{|x-y|/2}(x)`, `|G(z, y) - K - Ḡ(x - y)| ≤ A₂ |x - y|^{2-d}` (uses `ContinuumGreenStep`). -/
def GreenOscillationStep (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ (κ : {a : ℝ // 0 < a}) (δ Ch : ℝ), 0 < δ → δ ≤ 1 → 0 < Ch → ∃ A₂ : ℝ, 0 < A₂ ∧
    ∀ {ω : Configuration d} (C : OpenComponent ω) (y : C) (g : C → ℝ) (K : ℝ) (x : C) (X : ℝ),
      GreenCloseAt hd κ C y g K Ch (δ / 4) X →
      X ≤ dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) / 2 →
      ∀ z : C, dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val) <
          dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) / 2 →
        |g z - K - greenBar d hd κ (toReal x.val - toReal y.val)| ≤
          A₂ * dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) ^
            (2 - (d : ℝ))

/-- step:2.6-expansion, affine majorization (paper L617-620): under (H4) at scale `X`, for
`r ≥ X ∨ R₀`, `c₁ r |η|₁ ≤ ‖b + η · (· - x)‖_{L̲²(𝒞 ∩ B_r(x))}`. -/
def AffineMajorizationStep (d : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ c₁ R₀ : ℝ, 0 < c₁ ∧ 0 < R₀ ∧
    ∀ {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d) (X r : ℝ),
      DenseAt C x c X → X ≤ r → R₀ ≤ r → ∀ (b : ℝ) (η : Fin d → ℝ),
        c₁ * r * ∑ i, |η i| ≤
          componentBallL2 C x r (fun z => b + ∑ i, η i * ((z.val i : ℝ) - (x i : ℝ)))

/-- step:2.6-expansion, slope (paper L601-640): if the regularity estimate at scale
`R = |x - y|₂ / 2` gives `‖u - ∑ᵢ ξᵢ ℓᵢ - a‖_{L̲²(B_r(x))} ≤ B r² R^{-d}` for `r ∈ [X, R/2]`, then
under (H1), (H3), (H4) the slope satisfies `|ξ - ∇Ḡ(x - y)|₁ ≤ A₁ R^{1/2 - d + δ/4}` once
`R ≥ R₁ ∨ X²` (the choice `r = R^{1/2}`; uses `ContinuumGreenStep` and
`AffineMajorizationStep`). -/
def SlopeEstimateStep (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ (κ : {a : ℝ // 0 < a}) (δ Ch Cc cD B : ℝ), 0 < δ → δ ≤ 1 → 0 < Ch → 0 < Cc → 0 < cD →
    0 < B → ∃ A₁ R₁ : ℝ, 0 < A₁ ∧ 0 < R₁ ∧
    ∀ {ω : Configuration d} (C : OpenComponent ω) (y : C) (g : C → ℝ) (K : ℝ)
      (ℓ : Fin d → C → ℝ) (x : C) (X : ℝ), 1 ≤ X →
      (∀ i, IsCorrectedPlane C (Pi.single i 1) (ℓ i)) →
      GreenCloseAt hd κ C y g K Ch (δ / 4) X → CorrectorBoundAt C x.val Cc (δ / 4) X →
      DenseAt C x.val cD X →
      ∀ R : ℝ, R = dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) / 2 →
        R₁ ≤ R → X ^ 2 ≤ R →
      ∀ (ξ : Fin d → ℝ) (a : ℝ),
        (∀ r : ℝ, X ≤ r → r ≤ R / 2 →
          componentBallL2 C x.val r (fun z => g z - K - greenBar d hd κ
              (toReal x.val - toReal y.val) - ∑ i, ξ i * ℓ i z - a) ≤
            B * r ^ 2 * R ^ (-(d : ℝ))) →
        ∑ i, |ξ i - fderiv ℝ (greenBar d hd κ) (toReal x.val - toReal y.val)
            (EuclideanSpace.single i 1)| ≤ A₁ * R ^ ((1 : ℝ) / 2 - d + δ / 4)

/-- step:2.6-expansion, the deterministic core (paper L554-655): under (H1)-(H4) at a scale
`X ≥ 2`, with `G(·, y)` harmonic off `y`, the forward-difference bound of Proposition 2.6 holds at
`x` once `|x - y| ≥ A X^N` (uses `GreenOscillationStep` and `SlopeEstimateStep`). -/
def GreenGradientCoreStep (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ (κ : {a : ℝ // 0 < a}) (δ Ch Cc Cr cD : ℝ), 0 < δ → δ ≤ 1 → 0 < Ch → 0 < Cc → 0 < Cr →
    0 < cD → ∃ (A : ℝ) (N : ℕ), 1 ≤ A ∧
    ∀ {ω : Configuration d} (C : OpenComponent ω) (y : C) (g : C → ℝ) (K : ℝ)
      (ℓ : Fin d → C → ℝ) (x : C) (X : ℝ), 2 ≤ X →
      (∀ z, z ≠ y → componentLaplacian C g z = 0) →
      (∀ i, IsCorrectedPlane C (Pi.single i 1) (ℓ i)) →
      GreenCloseAt hd κ C y g K Ch (δ / 4) X → RegularityAt C ℓ x.val Cr X →
      CorrectorBoundAt C x.val Cc (δ / 4) X → DenseAt C x.val cD X →
      A * X ^ N ≤ latticeL1Dist x.val y.val →
      (∑ j, |forwardDiff C g x j
          - fderiv ℝ (greenBar d hd κ) (toReal x.val - toReal y.val) (EuclideanSpace.single j 1)
          - ∑ i, (forwardDiff C (ℓ i) x j - if i = j then 1 else 0)
              * fderiv ℝ (greenBar d hd κ) (toReal x.val - toReal y.val)
                  (EuclideanSpace.single i 1)|)
        ≤ A * Real.rpow (latticeL1Dist x.val y.val) (-1 / 2 + δ)
            * Real.rpow (latticeL1Dist x.val y.val) (1 - (d : ℝ))

/-! ### Composition -/

/-- (H1) from `SupercriticalBondGreenQuantitative`, uniformly in `d ≥ 2` (`K = 0` in `d ≥ 3`). -/
theorem greenClose_scales [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∀ η : ℝ, 0 < η → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
      ∃ M K : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
        HasStretchedExpTail d p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ hy : y ∈ (uniqueInfiniteComponent h).supp, ∀ g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
            GreenCloseAt hd ⟨κ, hκ⟩ (uniqueInfiniteComponent h) ⟨y, hy⟩ g (K ω) C η (M ω) := by
  obtain ⟨κ, hκ, h2, h3⟩ := hGQ d hd p hpc hp1
  refine ⟨κ, hκ, fun η hη => ?_⟩
  rcases eq_or_lt_of_le hd with hd2 | hd3
  · obtain ⟨K, -, hK⟩ := h2 hd2.symm
    obtain ⟨C, s, hC, hs, hy⟩ := hK η hη
    refine ⟨C, s, hC, hs, fun y => ?_⟩
    obtain ⟨-, M, hMm, hM0, hMt, hMae⟩ := hy y
    refine ⟨M, K y, hMm, hM0, hMt, ?_⟩
    filter_upwards [hMae] with ω hω h hy g hg z v hv hMv
    have hpow : ‖v.val‖ ^ (d - 2) = 1 := by rw [show d - 2 = 0 by omega, pow_zero]
    rw [hpow, mul_one]
    exact (hω h hy g hg).2 z v hv hMv
  · obtain ⟨C, s, hC, hs, hy⟩ := h3 (by omega) η hη
    refine ⟨C, s, hC, hs, fun y => ?_⟩
    obtain ⟨M, hMm, hM0, hMt, hMae⟩ := hy y
    refine ⟨M, fun _ => 0, hMm, hM0, hMt, ?_⟩
    filter_upwards [hMae] with ω hω h hy g hg z v hv hMv
    rw [sub_zero]
    exact hω h hy g hg z v hv hMv

theorem mul_pow_max_lt {A t a b : ℝ} {N : ℕ} (ha : A * a ^ N < t) (hb : A * b ^ N < t) :
    A * max a b ^ N < t := by
  rcases le_total a b with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- The common scale `X = (X₁ ∨ 2) ∨ (X₂ ∨ 2) ∨ (X₃ ∨ 2) ∨ (X₄ ∨ 2)`. -/
theorem exists_scale_max {A t a b c e : ℝ} {N : ℕ} (ha : A * max a 2 ^ N < t)
    (hb : A * max b 2 ^ N < t) (hc : A * max c 2 ^ N < t) (he : A * max e 2 ^ N < t) :
    ∃ X : ℝ, 2 ≤ X ∧ a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ e ≤ X ∧ A * X ^ N < t :=
  ⟨max (max a 2) (max (max b 2) (max (max c 2) (max e 2))),
    (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    mul_pow_max_lt ha (mul_pow_max_lt hb (mul_pow_max_lt hc he))⟩

/-- **Proposition 2.6** from its steps and the inputs `SupercriticalBondGreenQuantitative` and
`CorrectorQuantitativeInput`. -/
theorem greenGradientHomogenization_of_steps [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hReg : RegularityScaleStep d p) (hDense : DensityScaleStep d p)
    (hTail : TailOfOsStep d p) (hScale : MinimalScaleStep d p)
    (hCore : GreenGradientCoreStep d hd) :
    GreenGradientHomogenizationStmt d hd p := by
  obtain ⟨κ, hκ, hH⟩ := greenClose_scales hd p hpc hp1 hGQ
  refine ⟨⟨κ, hκ⟩, fun δ hδ => ?_⟩
  have hδ' : 0 < min δ 1 := lt_min hδ one_pos
  have hη : 0 < min δ 1 / 4 := by positivity
  obtain ⟨Ch, sh, hCh, hsh, hHy⟩ := hH _ hη
  obtain ⟨sc, Cc, hsc, hCc, hCx⟩ := hCQ d hd p hpc hp1 _ hη
  obtain ⟨sr, Cr, hsr, hCr, hRx⟩ := hReg hpc hp1
  obtain ⟨sd, Cd, cD, hsd, hCd, hcD, hDx⟩ := hDense hpc hp1
  obtain ⟨A, N, hA, hcore⟩ :=
    hCore ⟨κ, hκ⟩ (min δ 1) Ch Cc Cr cD hδ' (min_le_right _ _) hCh hCc hCr hcD
  obtain ⟨Tc, hTc, hTcX⟩ := hTail sc Cc hsc hCc
  obtain ⟨Tr, hTr, hTrX⟩ := hTail sr Cr hsr hCr
  obtain ⟨Td, hTd, hTdX⟩ := hTail sd Cd hsd hCd
  choose Mc hMcm hMc0 hMcO hMcae using hCx
  choose Mr hMrm hMr0 hMrO hMrae using hRx
  choose Md hMdm hMd0 hMdO hMdae using hDx
  obtain ⟨s', C', hs', hAC', hS⟩ := hScale 4 ![sh, sc, sr, sd] ![Ch, Tc, Tr, Td] A N
    (by intro i; fin_cases i <;> simp [hsh, hsc, hsr, hsd])
    (by intro i; fin_cases i <;> simp [hCh, hTc, hTr, hTd]) (by linarith)
  refine ⟨s', C', hs', by linarith, fun y => ?_⟩
  obtain ⟨Mh, K, hMhm, hMh0, hMht, hMhae⟩ := hHy y
  obtain ⟨M, hMm, hM0, hMO, hMae⟩ := hS y (fun i x => ![Mh, Mc x, Mr x, Md x] i)
    (by intro i x; fin_cases i; exacts [hMhm, hMcm x, hMrm x, hMdm x])
    (by
      intro i x; fin_cases i
      exacts [hMht, hTcX _ (hMcm x) (hMcO x), hTrX _ (hMrm x) (hMrO x),
        hTdX _ (hMdm x) (hMdO x)])
  refine ⟨M, hMm, hM0, hMO, ?_⟩
  filter_upwards [hMhae, ae_all_iff.2 hMcae, ae_all_iff.2 hMrae, ae_all_iff.2 hMdae, hMae]
    with ω h1 h2 h3 h4 h5
  intro h hy g hg ℓ hℓ x hx
  have e := h5 x.val hx
  obtain ⟨X, hX2, hhX, hcX, hrX, hdX, hAX⟩ :=
    exists_scale_max (a := Mh ω) (b := Mc x.val ω) (c := Mr x.val ω) (e := Md x.val ω)
      (e 0) (e 1) (e 2) (e 3)
  have hD1 : 1 ≤ latticeL1Dist x.val y := by
    have : 1 ≤ A * X ^ N := one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ (by linarith))
    linarith
  have hbound := hcore (uniqueInfiniteComponent h) ⟨y, hy⟩ g (K ω) ℓ x X hX2
    (fun z hz => by have := hg.1 z; rw [if_neg hz] at this; linarith)
    hℓ ((h1 h hy g hg).mono hhX) ((h3 x.val h ℓ hℓ).mono hrX)
    (fun q ℓ' hq r hr => h2 x.val h q ℓ' hq r (hcX.trans hr)) ((h4 x.val h).mono hdX) hAX.le
  unfold latticeL1Dist at hbound hD1
  refine hbound.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by linarith) _))
  exact mul_le_mul hAC' (Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [min_le_left δ 1]))
    (Real.rpow_nonneg (by linarith) _) (by linarith)

end Rigidity.Steps.S2
