import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Covering a Gaussian tail by coordinate slices

A summable nonnegative mass away from a distinguished point is bounded by the sum of masses of
finite families of slices that cover it. This is the union bound in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

open Classical

namespace Rigidity.Smoothing

/-- A finite cover bounds the mass away from a point by the sum of slice bounds. -/
theorem tsum_off_point_le_of_cover {α ι : Type*} [Fintype ι] (f : α → ℝ)
    (hf : Summable f) (hnonneg : ∀ y, 0 ≤ f y) (o : α) (P : ι → α → Prop)
    (hcover : ∀ y, y ≠ o → ∃ i, P i y) (p : ι → ℝ)
    (hslice : ∀ i, Summable (fun y => if P i y then f y else 0) ∧
      (∑' y, if P i y then f y else 0) ≤ p i * ∑' y, f y) :
    Summable (fun y => if y = o then 0 else f y) ∧
    (∑' y, if y = o then 0 else f y) ≤ (∑ i, p i) * ∑' y, f y := by
  have hoff : Summable (fun y => if y = o then 0 else f y) := by
    apply hf.of_nonneg_of_le
    · intro y
      split_ifs
      · exact le_rfl
      · exact hnonneg y
    · intro y
      split_ifs
      · exact hnonneg y
      · exact le_rfl
  have hsum : Summable (fun y => ∑ i, if P i y then f y else 0) :=
    summable_sum (fun i _ => (hslice i).1)
  have hpoint (y : α) : (if y = o then 0 else f y) ≤
      ∑ i, if P i y then f y else 0 := by
    have hnn (i : ι) : 0 ≤ (if P i y then f y else 0) := by
      split_ifs
      · exact hnonneg y
      · exact le_rfl
    by_cases hy : y = o
    · rw [if_pos hy]
      exact Finset.sum_nonneg fun i _ => hnn i
    · obtain ⟨i, hi⟩ := hcover y hy
      have h : (if P i y then f y else 0) ≤ ∑ j, if P j y then f y else 0 :=
        Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
      simpa only [hy, hi, if_true, if_false] using h
  refine ⟨hoff, ?_⟩
  calc
    (∑' y, if y = o then 0 else f y) ≤ ∑' y, ∑ i, if P i y then f y else 0 :=
      hoff.tsum_le_tsum hpoint hsum
    _ = ∑ i, ∑' y, if P i y then f y else 0 :=
      Summable.tsum_finsetSum (fun i _ => (hslice i).1)
    _ ≤ ∑ i, p i * ∑' y, f y := Finset.sum_le_sum fun i _ => (hslice i).2
    _ = (∑ i, p i) * ∑' y, f y := (Finset.sum_mul _ _ _).symm

end Rigidity.Smoothing
