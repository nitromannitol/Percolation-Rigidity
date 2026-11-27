import Rigidity.Proofs.Corrector.GeneralStepTwoReduce
import Rigidity.Proofs.Poincare.GeneralStepTwoHolds

/-!
# The probabilistic part of Step 2 of Lemma 3.3 of Dario on `ℤᵈ`, `d ≥ 3`

For `d ≥ 3` the good cubes of the summation of estimate (2) partition `ℤᵈ` almost surely, and the
weight of the Step 2 sum plus the path weight of the partition has a majorant with moments of
polynomial growth uniformly in the point (`exists_stepTwo_weight_data`): this is the named
hypothesis `DarioStepTwoWeightThree` of `GeneralStepTwoReduce` (`darioStepTwoWeightThree_holds`).
With Lemma 3.5 for the partition into good cubes it gives the bound of the Step 2 sum
(`darioStepTwoSumBoundThree_of_resample`).
-/

namespace Rigidity.Corrector.GeneralDim

/-- **The probabilistic part of Step 2 of Lemma 3.3 of Dario holds** on `ℤᵈ`, `d ≥ 3`. -/
theorem darioStepTwoWeightThree_holds : DarioStepTwoWeightThree := by
  intro _ _ hd _ hpc hp1 _ hG hGv hGae _ hκ
  exact exists_stepTwo_weight_data hG hGv hd hpc hp1 hGae hκ

/-- **The bound of the Step 2 sum in dimension `d ≥ 3`**, from Lemma 3.5 for the partition into
good cubes. -/
theorem darioStepTwoSumBoundThree_of_resample (h35 : DarioResamplePartitionThree) :
    DarioStepTwoSumBoundThree :=
  darioStepTwoSumBoundThree_of_weight h35 darioStepTwoWeightThree_holds

end Rigidity.Corrector.GeneralDim
