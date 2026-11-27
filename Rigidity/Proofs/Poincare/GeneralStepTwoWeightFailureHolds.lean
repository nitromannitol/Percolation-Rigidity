import Rigidity.Proofs.Poincare.GeneralStepTwoHolds
import Rigidity.Proofs.Corrector.GeneralStepTwoWeightFailure

/-!
# The failure bound of the weight bound of the Step 2 sum on `ℤᵈ`, `d ≥ 3`

The weight bound of a triadic cube fails with stretched exponential probability in its side
(`stepTwoWeightFailure_holds`, from `exists_measure_not_weightGood_le`), so the bound of the
Step 2 sum of Lemma 3.3 of Dario in dimension `d ≥ 3` follows from the reduction to a partition
alone (`darioStepTwoSumBoundThree_of_reduce`).
-/

namespace Rigidity.Corrector.GeneralDim

/-- **The failure bound of the weight bound holds** on `ℤᵈ`, `d ≥ 3`. -/
theorem stepTwoWeightFailure_holds : StepTwoWeightFailure := by
  intro _ _ hd _ hpc hp1 _ hG hGv hGae _ hκ _ hq
  exact exists_measure_not_weightGood_le hG hGv hd hpc hp1 hGae hκ hq

/-- **The bound of the Step 2 sum in dimension `d ≥ 3`, from the reduction to a partition.** -/
theorem darioStepTwoSumBoundThree_of_reduce (hred : StepTwoReduceBound) :
    DarioStepTwoSumBoundThree :=
  darioStepTwoSumBoundThree_of_reduce_of_weightFailure hred stepTwoWeightFailure_holds

end Rigidity.Corrector.GeneralDim
