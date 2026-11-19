import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Summing over fibers

A summable nonnegative family may be summed over the fibers of an integer-valued coordinate, with
the zero fiber removed on both sides. This is the summation step in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

open Classical

namespace Rigidity.Smoothing

/-- Total mass and mass off the zero fiber can be computed by summing over coordinate fibers. -/
theorem summable_and_tsum_fibers {α : Type*} (c : α → ℤ) (f : α → ℝ)
    (hf : Summable f) (hnonneg : ∀ y, 0 ≤ f y) :
    let S : ℤ → ℝ := fun n => ∑' y : {y // c y = n}, f y.1
    (∀ n, Summable (fun y : {y // c y = n} => f y.1)) ∧
    Summable S ∧ Summable (fun n => if n = 0 then 0 else S n) ∧
    Summable (fun y => if c y = 0 then 0 else f y) ∧
    (∑' y, f y) = (∑' n, S n) ∧
    (∑' y, if c y = 0 then 0 else f y) = ∑' n, if n = 0 then 0 else S n := by
  let S : ℤ → ℝ := fun n => ∑' y : {y // c y = n}, f y.1
  let e := Equiv.sigmaFiberEquiv c
  have hfib (n : ℤ) : Summable (fun y : {y // c y = n} => f y.1) :=
    hf.comp_injective Subtype.val_injective
  have hσ : Summable (fun p : Σ n : ℤ, {y // c y = n} => f p.2.1) :=
    hf.comp_injective e.injective
  have hS : Summable S := hσ.sigma' hfib
  have hSnonneg (n : ℤ) : 0 ≤ S n := tsum_nonneg fun _ => hnonneg _
  have hSoff : Summable (fun n => if n = 0 then 0 else S n) := by
    apply hS.of_nonneg_of_le
    · intro n
      split_ifs
      · exact le_rfl
      · exact hSnonneg n
    · intro n
      split_ifs
      · exact hSnonneg n
      · exact le_rfl
  let F : α → ℝ := fun y => if c y = 0 then 0 else f y
  have hF : Summable F := by
    apply hf.of_nonneg_of_le
    · intro y
      dsimp only [F]
      split_ifs
      · exact le_rfl
      · exact hnonneg y
    · intro y
      dsimp only [F]
      split_ifs
      · exact hnonneg y
      · exact le_rfl
  have hFσ : Summable (fun p : Σ n : ℤ, {y // c y = n} => F p.2.1) :=
    hF.comp_injective e.injective
  have hFfib (n : ℤ) : Summable (fun y : {y // c y = n} => F y.1) :=
    hF.comp_injective Subtype.val_injective
  refine ⟨hfib, hS, hSoff, hF, ?_, ?_⟩
  · calc
      (∑' y, f y) = ∑' p : Σ n : ℤ, {y // c y = n}, f p.2.1 := (e.tsum_eq f).symm
      _ = ∑' n, S n := hσ.tsum_sigma' hfib
  · calc
      (∑' y, F y) = ∑' p : Σ n : ℤ, {y // c y = n}, F p.2.1 := (e.tsum_eq F).symm
      _ = ∑' n, ∑' y : {y // c y = n}, F y.1 := hFσ.tsum_sigma' hFfib
      _ = ∑' n, if n = 0 then 0 else S n := by
        apply tsum_congr
        intro n
        by_cases hn : n = 0
        · simp only [hn, if_true]
          have hz : (fun y : {y // c y = n} => F y.1) = fun _ => 0 := by
            funext y
            simp only [F, y.2, hn, if_true]
          rw [hz, tsum_zero]
        · simp only [hn, if_false, S]
          apply tsum_congr
          intro y
          simp only [F, y.2, hn, if_false]

end Rigidity.Smoothing
