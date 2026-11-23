import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The integration in time in the proof of Proposition 4.3 of Dario–Gu

Step 5 of the proof of Proposition 4.3 of Dario–Gu (lines 2448-2490 of the source) integrates the
differential inequality `∂_s ∫ w² ≤ s^{-1} ∫ w² + C s^{-d/2 - 2 + α}` over `[τ, t]` with
`w(τ) = 0`, which gives (4.40): `∫ w²(t) ≤ C (t/τ) τ^{-d/2 - 1 + α}`. In dimension two the
exponent is `α - 3`. The function `s ↦ E(s)/s + A/(3 - α) s^{α - 3}` is nonincreasing
(`le_of_hasDerivAt_le_div_add`).
-/

namespace Rigidity.Green

/-- **Dario–Gu, (4.40)** (the integration of Step 5 of the proof of Proposition 4.3, `d = 2`):
if `E(τ) = 0`, `E` is continuous on `[τ, t]` and `E'(s) ≤ E(s)/s + A s^{α - 3}` on `(τ, t)`, then
`E(t) ≤ A/(3 - α) (t/τ) τ^{α - 2}`. -/
theorem le_of_hasDerivAt_le_div_add {E E' : ℝ → ℝ} {τ t A α : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t)
    (hA : 0 ≤ A) (hα : α < 3) (hE : ContinuousOn E (Set.Icc τ t))
    (hd : ∀ s ∈ Set.Ioo τ t, HasDerivAt E (E' s) s)
    (hle : ∀ s ∈ Set.Ioo τ t, E' s ≤ E s / s + A * s ^ (α - 3)) (h0 : E τ = 0) :
    E t ≤ A / (3 - α) * (t / τ) * τ ^ (α - 2) := by
  have h3 : 0 < 3 - α := by linarith
  let g : ℝ → ℝ := fun s => E s / s + A / (3 - α) * s ^ (α - 3)
  have hgc : ContinuousOn g (Set.Icc τ t) := by
    refine (hE.div continuousOn_id fun s hs => (hτ.trans_le hs.1).ne').add ?_
    exact continuousOn_const.mul
      (continuousOn_id.rpow_const fun s hs => Or.inl (hτ.trans_le hs.1).ne')
  have hgd : ∀ s ∈ interior (Set.Icc τ t), HasDerivWithinAt g
      ((E' s * s - E s * 1) / s ^ 2 + A / (3 - α) * ((α - 3) * s ^ (α - 3 - 1)))
      (interior (Set.Icc τ t)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have hs0 : s ≠ 0 := (hτ.trans hs.1).ne'
    exact (((hd s hs).div (hasDerivAt_id s) hs0).add
      ((Real.hasDerivAt_rpow_const (Or.inl hs0)).const_mul _)).hasDerivWithinAt
  have hgn : ∀ s ∈ interior (Set.Icc τ t),
      (E' s * s - E s * 1) / s ^ 2 + A / (3 - α) * ((α - 3) * s ^ (α - 3 - 1)) ≤ 0 := by
    intro s hs
    rw [interior_Icc] at hs
    have hs0 : 0 < s := hτ.trans hs.1
    have hu : s ^ (α - 3 - 1) = s ^ (α - 3) / s := Real.rpow_sub_one hs0.ne' _
    have hk : E' s * s ≤ E s + A * s ^ (α - 3) * s := by
      have := mul_le_mul_of_nonneg_right (hle s hs) hs0.le
      rwa [add_mul, div_mul_cancel₀ _ hs0.ne'] at this
    have e : (E' s * s - E s * 1) / s ^ 2 + A / (3 - α) * ((α - 3) * s ^ (α - 3 - 1)) =
        (E' s * s - E s - A * s ^ (α - 3) * s) / s ^ 2 := by
      rw [hu]
      field_simp
      ring
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc τ t) hgc hgd hgn
  have hgt : g t ≤ g τ := hanti ⟨le_rfl, hτt⟩ ⟨hτt, le_rfl⟩ hτt
  have ht0 : 0 < t := hτ.trans_le hτt
  have hgτ : g τ = A / (3 - α) * τ ^ (α - 3) := by
    simp only [g, h0, zero_div, zero_add]
  have hgt' : E t / t ≤ g t := by
    have : 0 ≤ A / (3 - α) * t ^ (α - 3) := by positivity
    simp only [g]
    linarith
  have hEt : E t / t ≤ A / (3 - α) * τ ^ (α - 3) := by linarith
  have hτ2 : τ ^ (α - 2) = τ ^ (α - 3) * τ := by
    rw [show α - 2 = α - 3 + 1 by ring, Real.rpow_add_one hτ.ne']
  calc E t = E t / t * t := by field_simp
    _ ≤ A / (3 - α) * τ ^ (α - 3) * t := mul_le_mul_of_nonneg_right hEt ht0.le
    _ = A / (3 - α) * (t / τ) * τ ^ (α - 2) := by
        rw [hτ2]
        field_simp

end Rigidity.Green
