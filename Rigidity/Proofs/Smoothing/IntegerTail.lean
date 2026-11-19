import Rigidity.Proofs.Smoothing.GeometricTail
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# A two-sided quadratic tail

The nonzero integer quadratic series is bounded by twice the positive geometric tail, as in the
proof of Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*,
SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- A nonzero integer quadratic series is summable and has a geometric upper bound. -/
theorem summable_int_pow_sq_and_tsum_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun z : ℤ => if z = 0 then 0 else q ^ (z.natAbs ^ 2)) ∧
      (∑' z : ℤ, if z = 0 then 0 else q ^ (z.natAbs ^ 2)) ≤ 2 * (q / (1 - q)) := by
  let f : ℤ → ℝ := fun z => if z = 0 then 0 else q ^ (z.natAbs ^ 2)
  have htail := summable_pow_sq_add_one_and_tsum_le hq hq1
  have hp (n : ℕ) : f ((n : ℤ) + 1) = q ^ ((n + 1) ^ 2) := by
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hn]
    simp only [f, Int.natCast_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Int.natAbs_natCast]
  have hm (n : ℕ) : f (-((n : ℤ) + 1)) = q ^ ((n + 1) ^ 2) := by
    have hn : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; rfl
    rw [hn]
    simp only [f, neg_eq_zero, Int.natCast_eq_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Int.natAbs_neg, Int.natAbs_natCast]
  have hpos : Summable (fun n : ℕ => f n) := by
    apply Summable.comp_nat_add (k := 1)
    simpa only [Nat.cast_add, Nat.cast_one, hp] using htail.1
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    simpa only [hm] using htail.1
  have hsum : Summable f := hpos.of_nat_of_neg_add_one hneg
  have hpos_sum : (∑' n : ℕ, f n) = ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
    rw [hpos.tsum_eq_zero_add]
    simp only [Nat.cast_zero, f, if_true, zero_add, Nat.cast_add, Nat.cast_one, hp]
  have hneg_sum : (∑' n : ℕ, f (-(n + 1))) = ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
    simp only [hm]
  refine ⟨hsum, ?_⟩
  change (∑' z : ℤ, f z) ≤ _
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hpos_sum, hneg_sum]
  linarith [htail.2]

end Rigidity.Smoothing
