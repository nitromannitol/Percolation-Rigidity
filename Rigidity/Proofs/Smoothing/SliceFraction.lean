import Mathlib.Tactic

/-!
# Relative mass of nonzero slices

A bound on nonzero slices relative to the zero slice converts to a bound relative to the full mass.
This is the rearrangement in Micciancio and Regev, *Worst-case to average-case reductions based on
Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- A geometric zero-slice bound controls the nonzero-slice fraction of the total mass. -/
theorem le_two_mul_ratio_of_zero_slice {q T Z M : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hT : 0 ≤ T) (hcover : Z + T ≤ M) (hbound : T ≤ (2 * q / (1 - q)) * Z) :
    T ≤ (2 * q) * M := by
  have hden : 0 < 1 - q := by linarith
  have hmul := mul_le_mul_of_nonneg_right hbound hden.le
  have hid : (2 * q / (1 - q)) * Z * (1 - q) = 2 * q * Z := by
    field_simp
  rw [hid] at hmul
  have hcover' := mul_nonneg (show 0 ≤ 2 * q by positivity) (sub_nonneg.mpr hcover)
  have hqT := mul_nonneg hq hT
  nlinarith

end Rigidity.Smoothing
