import Rigidity.Proofs.Smoothing.OrthogonalSlice

/-!
# Geometry of an integer lattice slice

In a slice with integer coordinate `n`, the squared norm splits into `n² / ‖b‖²` and the squared
norm of a translated vector orthogonal to `b`. This is the geometric step in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- The squared norm on an integer slice separates into parallel and orthogonal terms. -/
theorem norm_sq_zsmul_add_of_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b v k : E) (hb : b ≠ 0) (hv : inner ℝ v b = 1)
    (hk : inner ℝ k b = 0) (n : ℤ) :
    ‖n • v + k‖ ^ 2 =
      ‖k + (n : ℝ) • (v - (1 / ‖b‖ ^ 2) • b)‖ ^ 2 + (n : ℝ) ^ 2 / ‖b‖ ^ 2 := by
  have hi : inner ℝ (n • v + k) b = (n : ℝ) := by
    rw [inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hv, hk]
    simp only [mul_one, add_zero]
  have hvec : (n • v + k) - ((n : ℝ) / ‖b‖ ^ 2) • b =
      k + (n : ℝ) • (v - (1 / ‖b‖ ^ 2) • b) := by
    simp only [smul_sub, smul_smul, mul_one_div, Int.cast_smul_eq_zsmul]
    abel
  have h := (inner_sub_projection_and_norm_sq b (n • v + k) hb).2
  rw [hi, hvec] at h
  exact h

end Rigidity.Smoothing
