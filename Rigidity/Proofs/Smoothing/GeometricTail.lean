import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A geometric bound for a quadratic tail

This is the one-sided geometric estimate used in the proof of Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- A quadratic power series is dominated by the corresponding geometric tail. -/
theorem summable_pow_sq_add_one_and_tsum_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => q ^ ((n + 1) ^ 2)) ∧
      (∑' n : ℕ, q ^ ((n + 1) ^ 2)) ≤ q / (1 - q) := by
  have hgeom : Summable (fun n : ℕ => q ^ (n + 1)) := by
    simpa only [pow_succ'] using (summable_geometric_of_lt_one hq hq1).mul_left q
  have hle (n : ℕ) : q ^ ((n + 1) ^ 2) ≤ q ^ (n + 1) := by
    apply pow_le_pow_of_le_one hq hq1.le
    simpa only [sq] using (n + 1).le_mul_self
  have hsum : Summable (fun n : ℕ => q ^ ((n + 1) ^ 2)) :=
    hgeom.of_nonneg_of_le (fun _ => pow_nonneg hq _) hle
  refine ⟨hsum, ?_⟩
  calc
    (∑' n : ℕ, q ^ ((n + 1) ^ 2)) ≤ ∑' n : ℕ, q ^ (n + 1) :=
      hsum.tsum_le_tsum hle hgeom
    _ = q / (1 - q) := by
      simp only [pow_succ', tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]

end Rigidity.Smoothing
