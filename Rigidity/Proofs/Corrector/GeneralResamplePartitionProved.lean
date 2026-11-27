import Rigidity.Proofs.Corrector.GeneralResamplePartitionHolds
import Rigidity.Proofs.Corrector.GeneralStepTwoReduce

/-!
# The corrected Lemma 3.5 of Dario on `ℤᵈ`, and Lemma 3.3 in dimension `d ≥ 3` from Step 2

The corrected Lemma 3.5 (`ResamplePartitionBound C₀ C`, with the scale `S` of both configurations
at the endpoint) holds with `C₀ = 81` and `C = 243` (`resamplePartitionBound_holds`, from
`resamplePartition_max_bound`), in every dimension (`darioResamplePartitionThree_holds`). Hence the
bound of the Step 1 sum of Lemma 3.3 holds in dimension `d ≥ 3` with no hypothesis
(`darioStepOneSumBoundThree_holds`), and Lemma 3.3 in dimension `d ≥ 3` follows from the
probabilistic part of Step 2 alone (`darioVarianceBoundThree_of_stepTwoWeight`).
-/

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Percolation

variable {d : ℕ}

/-- **Dario, Lemma 3.5, in corrected form**, for the partition into good cubes of `ℤᵈ`, with the
constants `C₀ = 81` and `C = 243`. -/
theorem resamplePartitionBound_holds : ResamplePartitionBound (d := d) 81 243 :=
  fun _ _ _ h hP hP' _ hx z => resamplePartition_max_bound h hP hP' hx z

/-- **Dario, Lemma 3.5, in corrected form, in dimension `d ≥ 3`.** -/
theorem darioResamplePartitionThree_holds : DarioResamplePartitionThree :=
  fun _ _ _ => ⟨81, 243, by norm_num, resamplePartitionBound_holds⟩

/-- **The bound of the Step 1 sum of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`.** -/
theorem darioStepOneSumBoundThree_holds : DarioStepOneSumBoundThree :=
  darioStepOneSumBoundThree_of_resample darioResamplePartitionThree_holds

/-- **Dario, Lemma 3.3 in dimension `d ≥ 3`, from the probabilistic part of Step 2.** -/
theorem darioVarianceBoundThree_of_stepTwoWeight (hW : DarioStepTwoWeightThree) :
    DarioVarianceBoundThree :=
  darioVarianceBoundThree_of_weight darioResamplePartitionThree_holds hW

end Rigidity.Corrector.GeneralDim
