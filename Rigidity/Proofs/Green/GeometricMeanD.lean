import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The geometric mean of two bounds

`a ≤ A^{1-λ} B^λ` for `0 ≤ a ≤ A`, `a ≤ B` and `λ ∈ [0, 1]` (`le_rpow_mul_rpow`). With
`A = C₁ t^{-d/2-1/2+ε}` (the error of the heat kernel against the Gaussian in `ℓ^∞`) and
`B = C₂ t^{-d/2} e^{-D²/(C₃ t)}` (the Gaussian upper bound of the heat kernel and of the Gaussian),
this gives `C₁^{1-λ} C₂^λ t^{-d/2 - (1-λ)(1/2-ε)} e^{-λD²/(C₃ t)}` (`le_of_two_bounds`).
-/

namespace Rigidity.Green

theorem le_rpow_mul_rpow {a A B lam : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) (hB : a ≤ B) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) : a ≤ A ^ (1 - lam) * B ^ lam := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]
    exact mul_nonneg (Real.rpow_nonneg (ha.trans hA) _) (Real.rpow_nonneg (ha.trans hB) _)
  · have e : a = a ^ (1 - lam) * a ^ lam := by
      rw [← Real.rpow_add h]; simp
    rw [e]
    exact mul_le_mul (Real.rpow_le_rpow ha hA (by linarith)) (Real.rpow_le_rpow ha hB hl0)
      (Real.rpow_nonneg ha _) (Real.rpow_nonneg (ha.trans hA) _)

/-- **Two bounds combined.** -/
theorem le_of_two_bounds {a t C₁ C₂ C₃ D eps lam : ℝ} (d : ℕ) (ha : 0 ≤ a) (ht : 0 < t)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hA : a ≤ C₁ * t ^ (-((d : ℝ) / 2) - 1 / 2 + eps))
    (hB : a ≤ C₂ * t ^ (-((d : ℝ) / 2)) * Real.exp (-(D ^ 2 / (C₃ * t)))) :
    a ≤ C₁ ^ (1 - lam) * C₂ ^ lam * t ^ (-((d : ℝ) / 2) - (1 - lam) * (1 / 2 - eps)) *
      Real.exp (-(lam * D ^ 2 / (C₃ * t))) := by
  have h := le_rpow_mul_rpow ha hA hB hl0 hl1
  refine h.trans_eq ?_
  rw [Real.mul_rpow hC₁ (Real.rpow_nonneg ht.le _), Real.mul_rpow (by positivity)
    (Real.exp_pos _).le, Real.mul_rpow hC₂ (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le,
    ← Real.rpow_mul ht.le, ← Real.exp_mul]
  have e1 : t ^ ((-((d : ℝ) / 2) - 1 / 2 + eps) * (1 - lam)) * t ^ (-((d : ℝ) / 2) * lam) =
      t ^ (-((d : ℝ) / 2) - (1 - lam) * (1 / 2 - eps)) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [← e1]
  have e2 : -(D ^ 2 / (C₃ * t)) * lam = -(lam * D ^ 2 / (C₃ * t)) := by ring
  rw [e2]
  ring

end Rigidity.Green
