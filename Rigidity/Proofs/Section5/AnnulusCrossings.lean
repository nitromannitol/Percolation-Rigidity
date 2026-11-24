import Rigidity.Steps.Section5.LoopsAroundAnnuli
import PercolationClusterHomogenization.Proofs.Planar.AnnulusCrossings

/-!
# Lemma 5.14: the crossing probability and Borel-Cantelli steps

* `crossingProbabilityStep`: each of the five rectangles in `AnnulusCrossings ω R` has long side
  `m ≤ 4R` and short side `n ≥ R - 1`, so the failure of its crossing has probability at most
  `C (m + 1) e^{-cn} ≤ 4 C e^c (R + 1) e^{-cR}`; a union bound over the five gives `C' = 20 C e^c`
  and `c' = c`.
* `borelCantelliStep`: `(R + 1) e^{-cR}` is summable, and the Borel-Cantelli lemma applies.
-/

open MeasureTheory LatticeProb.Percolation Filter

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.External Rigidity.Steps.Section5

/-- Step `step:5.14-borel-cantelli`. -/
theorem borelCantelliStep : BorelCantelliStep := by
  intro p C c hC hc hbound
  set f : ℕ → ℝ := fun R => C * (R + 1) * Real.exp (-(c * R))
  have hf0 : ∀ R, 0 ≤ f R := fun R => by positivity
  have hfs : Summable f := by
    have h := ((Real.summable_pow_mul_exp_neg_nat_mul 1 hc).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 hc)).mul_left C
    refine h.congr fun R => ?_
    simp only [f, pow_one, pow_zero, neg_mul]
    ring
  have hsum : ∑' R, latticeBondLaw 2 p {ω | ¬ AnnulusCrossings ω R} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨M, hM⟩ := eventually_atTop.mp hω
  exact ⟨M, fun R hR => not_not.mp (hM R hR)⟩

end Rigidity.Proofs.Section5
