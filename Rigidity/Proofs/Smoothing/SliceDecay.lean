import Rigidity.Proofs.Smoothing.GaussianSlice
import Rigidity.Proofs.Smoothing.IntegerTail

/-!
# Geometric domination of Gaussian slice factors

A bound on the generator length makes each integer slice factor at most the corresponding power of
a common Gaussian ratio. This is the geometric comparison in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- A Gaussian slice factor is bounded by a quadratic power of a common ratio. -/
theorem exp_integer_slice_le_pow {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hr : 0 < r)
    (hbr : b ≤ r) (n : ℤ) :
    Real.exp (-a * ((n : ℝ) ^ 2 / b ^ 2)) ≤
      (Real.exp (-a / r ^ 2)) ^ (n.natAbs ^ 2) := by
  have hsq : (((n.natAbs ^ 2 : ℕ) : ℝ)) = (n : ℝ) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hden : b ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hb.le hr.le).2 hbr
  have hdiv : (n : ℝ) ^ 2 / r ^ 2 ≤ (n : ℝ) ^ 2 / b ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hb) hden
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [hsq]
  calc
    -a * ((n : ℝ) ^ 2 / b ^ 2) = -(a * ((n : ℝ) ^ 2 / b ^ 2)) := by ring
    _ ≤ -(a * ((n : ℝ) ^ 2 / r ^ 2)) := neg_le_neg (mul_le_mul_of_nonneg_left hdiv ha)
    _ = (n : ℝ) ^ 2 * (-a / r ^ 2) := by ring

end Rigidity.Smoothing
