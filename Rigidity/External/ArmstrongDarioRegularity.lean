import Rigidity.External.CorrectorQuantitative
import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth

/-! Large-scale regularity on the infinite cluster at order one (literature input): Theorem 2.4 of
the corrected draft, item (iii) at `k = 1` (correction C34), at the origin.

Source: S. Armstrong and P. Dario, *Elliptic regularity and quantitative homogenization on
percolation clusters*, Comm. Pure Appl. Math. 71 (2018), arXiv:1609.09431v2, **Theorem 2
(Regularity theory), part (iii)**, with the scale bound (1.16). Verbatim (arXiv v2 numbering):

> There exist `s(d,𝔭,λ) > 0`, `δ(d,𝔭,λ) > 0` and a nonnegative random variable `𝒳` satisfying
> (1.16) `𝒳 ≤ O_s(C(d,𝔭,λ))` such that the following hold: [...] (iii) For each `k ∈ ℕ`, there
> exists `C(k,d,𝔭,λ) < ∞` such that, for every `R ≥ 2𝒳` and `u ∈ 𝒜(𝒞_∞ ∩ B_R)`, there exists
> `φ ∈ 𝒜_k(𝒞_∞)` such that, for every `r ∈ [𝒳, R/2]`, we have
> `‖u - φ‖_{L̲²(𝒞_∞ ∩ B_r)} ≤ C (r/R)^{k+1} ‖u‖_{L̲²(𝒞_∞ ∩ B_R)}`.

Specialization: bond percolation (`a = 𝟙{e open} ∈ {0, 1}`, the case singled out in §1.1 of the
source), `k = 1`. The two constants `C(d,𝔭,λ)` (in `O_s`) and `C(1,d,𝔭,λ)` (in the estimate) are
kept separate.

Conventions: `B_R` is the open Euclidean ball centred at the origin; `𝒜(𝒞_∞ ∩ B_R)`, the
functions harmonic at every vertex of `𝒞_∞ ∩ B_R` all of whose open-edge neighbours lie in
`B_R` (the `a`-interior of the source; `componentLaplacian` has the opposite sign
convention to the source); `𝒜₁`
is `harmonicGrowthSpace _ 1` (harmonic on `𝒞_∞` with `R⁻² ‖u‖_{L̲²(𝒞_∞ ∩ B_R)} → 0`); the norm
`L̲²` is the average over `𝒞_∞ ∩ B_r` (`componentBallL2`); `X ≤ O_s(θ)` means
`E[exp((X/θ ∨ 0)^s)] ≤ 2` (`IsOsBond`). The statement at every centre `x` (by stationarity) is
`Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin`. -/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.External

/-- **Theorem 2.4 (iii) at `k = 1`, at the origin** (Armstrong–Dario 2018, Theorem 2(iii),
arXiv:1609.09431v2; literature input). There are `s, C₀ > 0` and a nonnegative random variable
`𝒳 ≤ O_s(C₀)`, and a constant `C`, such that for every `R ≥ 2𝒳` and every `u` harmonic in
`𝒞_∞ ∩ B_R` there is `φ ∈ 𝒜₁(𝒞_∞)` with
`‖u - φ‖_{L̲²(𝒞_∞ ∩ B_r)} ≤ C (r/R)² ‖u‖_{L̲²(𝒞_∞ ∩ B_R)}` for every `r ∈ [𝒳, R/2]`. -/
def ArmstrongDarioOrderOneOrigin : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C₀ : ℝ, 0 < s ∧ 0 < C₀ ∧
      ∃ X : Configuration d → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond d p X s C₀ ∧
      ∃ C : ℝ, ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * X ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R,
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) 0 R) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ φ ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1,
            ∀ r : ℝ, X ω ≤ r → r ≤ R / 2 →
              componentBallL2 (uniqueInfiniteComponent h) 0 r (u - φ) ≤
                C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) 0 R u

end Rigidity.External
