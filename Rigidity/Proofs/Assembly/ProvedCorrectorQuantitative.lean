import Rigidity.Proofs.Assembly.EveryDimension
import Rigidity.Proofs.Poincare.GeneralStepTwoWeightThreeHolds

/-!
# The quantitative corrector input proved in every dimension

The probabilistic part of Step 2 of the proof of Lemma 3.3 of Dario (*Optimal corrector estimates
on percolation clusters*) in dimension `d ≥ 3` is proved
(`Rigidity.Corrector.GeneralDim.darioStepTwoWeightThree_holds`). With Lemma 3.5 in its corrected
form and Step 1, which are proved, it gives Lemma 3.3 in dimension `d ≥ 3`
(`Rigidity.Corrector.GeneralDim.darioVarianceBoundThree_holds`); with Lemma 3.2, which is proved in
every dimension, Theorem 1 of Dario in dimension `d ≥ 3`
(`Rigidity.Corrector.GeneralDim.darioOptimalCorrectorThree_holds`); and so the quantitative
corrector input of Theorem 1.1 (Theorem 2.5, quantitative part; Proposition 2.12 of Dario and Gu)
in every dimension, with no hypothesis
(`Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds`).
-/

namespace Rigidity.Corrector.GeneralDim

/-- **Dario, Lemma 3.3, in dimension `d ≥ 3`**, with no hypothesis. -/
theorem darioVarianceBoundThree_holds : DarioVarianceBoundThree :=
  darioVarianceBoundThree_of_stepTwoWeight darioStepTwoWeightThree_holds

/-- **Dario, Theorem 1, in dimension `d ≥ 3`**, with no hypothesis. -/
theorem darioOptimalCorrectorThree_holds : DarioOptimalCorrectorThree :=
  darioOptimalCorrectorThree_of_varianceBound darioVarianceBoundThree_holds

end Rigidity.Corrector.GeneralDim

namespace Rigidity.Assembly.EveryDimension

/-- **Theorem 2.5, quantitative part, in every dimension** (Proposition 2.12 of Dario and Gu, the
quantitative corrector estimate), with no hypothesis. -/
theorem correctorQuantitativeInput_holds : Rigidity.External.CorrectorQuantitativeInput :=
  correctorQuantitativeInput_of_stepTwoWeight
    Rigidity.Corrector.GeneralDim.darioStepTwoWeightThree_holds

end Rigidity.Assembly.EveryDimension
