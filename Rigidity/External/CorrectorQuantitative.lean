import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeClusterBall
import LatticeProb.Prob.Percolation.LatticeBondCritical

/-! The quantitative part of Theorem 2.5 of the corrected draft (literature input): quantitative
sublinearity and Lipschitz bound of the first-order corrector `χ_p = ℓ_p - p·x` on the infinite
cluster, beyond a minimal scale with stretched exponential moments.

Source: P. Dario and C. Gu, *Quantitative homogenization of the parabolic and elliptic Green's
functions on percolation clusters*, Ann. Probab. 49 (2021); arXiv:1909.10439v4, Proposition 2.12
(p. 22): for every exponent `α > 0` there are `s(d, 𝔭, λ, α) > 0` and `C(d, 𝔭, λ, α) < ∞` such
that every `y ∈ ℤ^d` has a non-negative random variable `M_corr,α(y) ≤ O_s(C)` with
`osc_{𝒞_∞ ∩ B_r(y)} χ_p ≤ C |p| r^α` for every `r ≥ M_corr,α(y)` and every `p ∈ ℝ^d` (the setting
of §1.6.1 of the source, with `a(e) ∈ {0, 1}` for bond percolation). The gradient term of the
statement below is bounded by the same oscillation, since both endpoints of an open edge in `B_r(x)`
lie in `B_r(x)`; the constant `C` is twice that of the source (`O_s(θ)` is monotone in `θ`), and the
`ℓ¹` norm of `p` bounds its Euclidean norm. The fixed-scale bound
`‖χ_p‖_{L^∞(𝒞_∞ ∩ B_r)} ≤ O_s(C |p| r^{1-δ/2})` of S. Armstrong and P. Dario, *Elliptic regularity
and quantitative homogenization on percolation clusters*, Comm. Pure Appl. Math. 71 (2018),
equation (1.22), does not give this minimal-scale form for every `α > 0`. The qualitative part
(existence, uniqueness and the classification of `𝒜₁`) is
`LatticeProb.External.SupercriticalBondCorrectorInput`.

Conventions: `B_r(x)` is the open Euclidean ball (contained in the discrete ball `B_r(x)` of the
source); `|p|` is the `ℓ¹` norm; the oscillation and the gradient bound are over vertices,
respectively open edges, of `𝒞_∞` in `B_r(x)`; `X ≤ O_s(θ)` means `E[exp((X/θ ∨ 0)^s)] ≤ 2`, as in
the source (p. 13). -/

open MeasureTheory LatticeProb.Percolation Classical

namespace Rigidity.External

/-- `X ≤ O_s(θ)` for the bond law of parameter `p`. -/
def IsOsBond (d : ℕ) (p : unitInterval) (X : Configuration d → ℝ) (s θ : ℝ) : Prop :=
  Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) (latticeBondLaw d p) ∧
  (∫ ω, Real.exp (Real.rpow (max (X ω / θ) 0) s) ∂latticeBondLaw d p) ≤ 2

/-- **Theorem 2.5, quantitative sublinearity and Lipschitz bound** (literature input; Dario-Gu,
Proposition 2.12). For every
`α > 0` there are `s, C > 0` and, for every vertex `x`, a minimal scale `M ≤ O_s(C)` such that for
every `r ≥ M`, every slope `p` and every corrected plane `ℓ_p`, with `χ_p = ℓ_p - p·x`,
`osc_{𝒞_∞ ∩ B_r(x)} χ_p + ‖∇χ_p‖_{L^∞(𝒞_∞ ∩ B_r(x))} ≤ C |p| r^α`. -/
def CorrectorQuantitativeInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∀ α : ℝ, 0 < α → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (q : Fin d → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
        ∀ r : ℝ, M ω ≤ r →
        ∀ a b a' b' : uniqueInfiniteComponent h,
          ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding a'.val - latticeEuclideanEmbedding x‖ < r →
          ‖latticeEuclideanEmbedding b'.val - latticeEuclideanEmbedding x‖ < r →
          (componentGraph (uniqueInfiniteComponent h)).Adj a' b' →
          |(ℓ a - ∑ i, q i * a.val i) - (ℓ b - ∑ i, q i * b.val i)| +
              |(ℓ a' - ∑ i, q i * a'.val i) - (ℓ b' - ∑ i, q i * b'.val i)|
            ≤ C * (∑ i, |q i|) * r ^ α

end Rigidity.External
