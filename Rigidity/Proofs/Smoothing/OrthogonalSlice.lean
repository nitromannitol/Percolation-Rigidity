import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Orthogonal decomposition of a coordinate slice

The squared norm separates into the part parallel to a nonzero vector and the squared norm of the
orthogonal remainder. This is the geometric decomposition used by Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- Orthogonal projection onto the line through a nonzero vector separates squared norms. -/
theorem inner_sub_projection_and_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b y : E) (hb : b ≠ 0) :
    let t := inner ℝ y b / ‖b‖ ^ 2
    inner ℝ (y - t • b) b = 0 ∧
      ‖y‖ ^ 2 = ‖y - t • b‖ ^ 2 + (inner ℝ y b) ^ 2 / ‖b‖ ^ 2 := by
  let t : ℝ := inner ℝ y b / ‖b‖ ^ 2
  have hden : ‖b‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hb)
  have hortho : inner ℝ (y - t • b) b = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp only [t]
    field_simp
    ring
  have horthop : inner ℝ (y - t • b) (t • b) = 0 := by
    rw [real_inner_smul_right, hortho, mul_zero]
  have hnorm : ‖t • b‖ ^ 2 = (inner ℝ y b) ^ 2 / ‖b‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    dsimp only [t]
    field_simp
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (y - t • b) (t • b) horthop
  have hpyth' : ‖y‖ ^ 2 = ‖y - t • b‖ ^ 2 + ‖t • b‖ ^ 2 := by
    simpa only [sub_add_cancel, pow_two] using hpyth
  exact ⟨hortho, hpyth'.trans (congrArg (fun r => ‖y - t • b‖ ^ 2 + r) hnorm)⟩

end Rigidity.Smoothing
