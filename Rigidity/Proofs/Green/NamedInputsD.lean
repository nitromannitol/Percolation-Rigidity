import Rigidity.Proofs.Green.NormalizedGaussianD
import Rigidity.Proofs.Green.GreenQuantitativeThree

/-!
# Two inputs of Theorem 1 of Dario–Gu on `ℤ^d`, stated for the route given here

* `DarioGuDensityGaussianD d p σ`: **Proposition A.7** of Dario–Gu (lines 2911-2920), second part,
  on `ℤ^d`: for every `α > 0` there is `T_dense,α(y) ≤ O_s(C)` such that for `t > T_dense,α(y)` the
  Gaussian mass of the infinite cluster `Σ_{x ∈ 𝒞_∞} p̄(t, x - y)` (`clusterGaussMass`) is within
  `C t^{-(1/2 - α)}` of `θ(p)`. The planar statement is `DarioGuDensityGaussianTwo`.
* `DarioGuGaussianFlowD d p σ`: the **whole-cluster estimate** of Dario–Gu, Proposition 4.3,
  Step 5, (4.40), with initial time `τ` and final time `3τ`, combined with the initial error of
  Proposition 2.12 by the triangle inequality: for `H_τ = θ^{-1} p̄(τ, · - y)` on `𝒞_∞` and
  `τ ≥ M(y)`, `‖P_{2τ} H_τ - H_{3τ}‖_{ℓ²} ≤ C τ^{α - d/4 - 1/2}`.
-/

open LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

variable (d : ℕ) [NeZero d]

/-- **Dario–Gu, Proposition A.7**, second part, on `ℤ^d`. -/
def DarioGuDensityGaussianD (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
    ∃ T : Configuration d → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧ IsOsBond d p T s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ t : ℝ, T ω < t →
        |clusterGaussMass (uniqueInfiniteComponent h) σ t y - theta d p| ≤
          C * t ^ (-(1 / 2 - α))

/-- **The whole-cluster estimate** of Dario–Gu, (4.40) with Proposition 2.12, on `ℤ^d`. -/
def DarioGuGaussianFlowD (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
    ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ τ : ℝ, M ω ≤ τ →
          l2norm (fun x => heatFlowG (openGraph ω) (2 * d) (2 * τ)
              (fun z => (theta d p)⁻¹ * clusterInd (uniqueInfiniteComponent h) σ τ y z) x -
            (theta d p)⁻¹ * clusterInd (uniqueInfiniteComponent h) σ (3 * τ) y x) ≤
            C * τ ^ (α - (d : ℝ) / 4 - 1 / 2)

end Rigidity.Green
