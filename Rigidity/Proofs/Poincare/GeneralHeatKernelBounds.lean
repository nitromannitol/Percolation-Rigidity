import Rigidity.Proofs.Poincare.HeatKernelBounds
import Rigidity.Proofs.Poincare.GeneralLatticeHeatKernel

/-!
# Upper bounds for the tilted heat kernel of `ℤ^d`

The extension of `HeatKernelBounds.lean` from `ℤ²` to `ℤ^d`: with `σ = max(√s, 1)`, the product
form of the heat kernel (`zdHeat_eq_prod_lineKernel`) and the bound of the tilted one-dimensional
kernel (`exists_lineKernel_mul_exp_le`) give
`Φ_s(x, y) e^{a|y - x|₁} ≤ (C^d/σ^d) e^{-|y - x|₁/σ}` for `0 ≤ a ≤ 1/6` with `a σ ≤ 1`
(`exists_zdHeat_mul_exp_le`).
-/

open LatticeProb LatticeProb.Percolation Rigidity.Green LatticeProb.ContinuousTime Finset

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- **The tilted heat kernel of `ℤ^d`**: `Φ_s(x, y) e^{a|y - x|₁} ≤ (C^d/σ^d) e^{-|y - x|₁/σ}` for
`0 ≤ a ≤ 1/6`, `a max(√s, 1) ≤ 1`, `σ = max(√s, 1)`. -/
theorem exists_zdHeat_mul_exp_le [NeZero d] : ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → ∀ a : ℝ,
    0 ≤ a → a ≤ 1 / 6 → a * max (Real.sqrt s) 1 ≤ 1 → ∀ x y : Vertex d,
      zdHeat d s x y * Real.exp (a * ∑ i, |(((y - x) i : ℤ) : ℝ)|) ≤
        C ^ d / max (Real.sqrt s) 1 ^ d *
          Real.exp (-(∑ i, |(((y - x) i : ℤ) : ℝ)|) / max (Real.sqrt s) 1) := by
  obtain ⟨C, hC, h⟩ := Rigidity.Poincare.exists_lineKernel_mul_exp_le
  refine ⟨C, hC, fun s hs a ha0 ha6 haσ x y => ?_⟩
  set σ := max (Real.sqrt s) 1 with hσ
  have hσ0 : 0 < σ := lt_of_lt_of_le one_pos (le_max_right _ _)
  rw [zdHeat_eq_prod_lineKernel, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  calc ∏ i, (lineKernel (2 * s) ((y - x) i) * Real.exp (a * |(((y - x) i : ℤ) : ℝ)|))
      ≤ ∏ i, (C / σ * Real.exp (-|(((y - x) i : ℤ) : ℝ)| / σ)) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => h s hs a ha0 ha6 haσ _)
        exact mul_nonneg (lineKernel_nonneg (by linarith) _) (Real.exp_pos _).le
    _ = C ^ d / σ ^ d * Real.exp (-(∑ i, |(((y - x) i : ℤ) : ℝ)|) / σ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          div_pow, ← Real.exp_sum, neg_div, ← Finset.sum_div, Finset.sum_neg_distrib, neg_div]

end Rigidity.Poincare.GeneralDim
