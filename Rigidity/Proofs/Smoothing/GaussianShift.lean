import Rigidity.Proofs.Smoothing.GaussianSummable
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Bounds for shifted Gaussians

A Gaussian shifted by a bounded vector is controlled by a wider unshifted Gaussian. This supplies a
summable majorant for the lattice periodization in Micciancio and Regev, *Worst-case to average-case
reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- A uniformly bounded shift is dominated by a wider Gaussian. -/
theorem exp_neg_norm_add_sq_le {E : Type*} [NormedAddCommGroup E] {a R : ℝ}
    (ha : 0 ≤ a) (hR : 0 ≤ R) (z x : E) (hx : ‖x‖ ≤ R) :
    Real.exp (-a * ‖z + x‖ ^ 2) ≤ Real.exp (a * R ^ 2) *
      Real.exp (-(a / 2) * ‖z‖ ^ 2) := by
  have htri : ‖z‖ ≤ ‖z + x‖ + ‖x‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (z + x) x
  have hsq : ‖z‖ ^ 2 ≤ 2 * ‖z + x‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z + x‖ - ‖x‖), norm_nonneg z, norm_nonneg (z + x), norm_nonneg x]
  have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x]
  have hmul := mul_nonneg ha (sub_nonneg.mpr hsq)
  have hmul' := mul_nonneg ha (sub_nonneg.mpr hx2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Lattice Gaussian periodization is continuous. -/
theorem continuous_tsum_gaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Continuous (fun x : E => ∑' z : L, Real.exp (-a * ‖(z : E) + x‖ ^ 2)) := by
  rw [continuous_iff_continuousAt]
  intro x
  let R : ℝ := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsum : Summable (fun z : L => Real.exp (a * R ^ 2) *
      Real.exp (-(a / 2) * ‖z‖ ^ 2)) :=
    (summable_gaussian L (show 0 < a / 2 by positivity)).mul_left _
  have hc : ContinuousOn (fun y : E => ∑' z : L, Real.exp (-a * ‖(z : E) + y‖ ^ 2))
      (Metric.closedBall 0 R) := by
    apply continuousOn_tsum (u := fun z : L => Real.exp (a * R ^ 2) *
      Real.exp (-(a / 2) * ‖z‖ ^ 2))
    · intro z
      fun_prop
    · exact hsum
    · intro z y hy
      have hyR : ‖y‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Submodule.coe_norm] using
        exp_neg_norm_add_sq_le ha.le hR (z : E) y hyR
  apply hc.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  simp only [Metric.mem_ball, dist_zero_right, R]
  linarith

end Rigidity.Smoothing
