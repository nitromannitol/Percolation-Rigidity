import Rigidity.Proofs.Smoothing.Scale
import Mathlib.Tactic

/-!
# Geometric decay at the smoothing scale

The lower bound on the scale in Micciancio and Regev, *Worst-case to average-case reductions based
on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3, bounds the total geometric tail
coefficient by `ε / (1 + ε)`.
-/

namespace Rigidity.Smoothing

/-- The smoothing scale controls the geometric ratio appearing in the slice bound. -/
theorem geometric_ratio_of_scale {k : ℕ} (hk : 0 < k) {r ε s : ℝ} (hr : 0 < r)
    (hε : 0 < ε)
    (hs : Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) * r ≤ s) :
    let q := Real.exp (-Real.pi * (s / r) ^ 2)
    0 < q ∧ q < 1 ∧ 2 * k * q ≤ ε / (1 + ε) := by
  let A : ℝ := 2 * k * (1 + 1 / ε)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkin : (k : ℝ) ≠ 0 := by positivity
  have hinv : 0 < 1 / ε := one_div_pos.mpr hε
  have hA : 1 < A := by dsimp [A]; nlinarith
  have hlog : 0 < Real.log A / Real.pi := div_pos (Real.log_pos hA) Real.pi_pos
  have hroot : 0 < Real.sqrt (Real.log A / Real.pi) := Real.sqrt_pos.2 hlog
  have hsr : Real.sqrt (Real.log A / Real.pi) ≤ s / r := by
    apply (le_div_iff₀ hr).2
    exact hs
  have hsrpos : 0 < s / r := hroot.trans_le hsr
  have hsq : Real.log A / Real.pi ≤ (s / r) ^ 2 := by
    have h := (sq_le_sq₀ hroot.le hsrpos.le).2 hsr
    simpa only [Real.sq_sqrt hlog.le] using h
  have hlogle : Real.log A ≤ Real.pi * (s / r) ^ 2 := by
    simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).1 hsq
  have hq : Real.exp (-Real.pi * (s / r) ^ 2) ≤ A⁻¹ := by
    calc
      Real.exp (-Real.pi * (s / r) ^ 2) ≤ Real.exp (-Real.log A) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = A⁻¹ := by rw [Real.exp_neg, Real.exp_log (lt_trans zero_lt_one hA)]
  have hratio : (2 * (k : ℝ)) * A⁻¹ = ε / (1 + ε) := by
    dsimp only [A]
    field_simp
    ring
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · apply Real.exp_lt_one_iff.mpr
    have : 0 < Real.pi * (s / r) ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hsrpos)
    linarith
  · calc
      2 * (k : ℝ) * Real.exp (-Real.pi * (s / r) ^ 2) ≤ 2 * (k : ℝ) * A⁻¹ :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = ε / (1 + ε) := hratio

end Rigidity.Smoothing
