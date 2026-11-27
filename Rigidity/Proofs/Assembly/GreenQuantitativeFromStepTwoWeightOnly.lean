import Rigidity.Proofs.Assembly.GreenQuantitativeFromStepTwoWeight
import Rigidity.Proofs.Green.GeneralFluxFlipWeight

/-!
# The quantitative Green estimate in every dimension from Proposition 2.12 and the Step 2 weight

The bound of each squared flip difference of the heat average of the flux by the Step 2 factor,
`FluxFlipWeightBoundD d p`, is proved for every `d ≥ 2` and supercritical `p < 1`
(`Rigidity.Green.GeneralFlux.fluxFlipWeightBoundD_holds`). So the variance bound (3.4) of Gu's
proof of his Proposition 1.1 (*An efficient algorithm for solving elliptic problems on percolation
clusters*) in every dimension `d ≥ 3` follows from the probabilistic part of Step 2 of the proof of
Lemma 3.3 of Dario (*Optimal corrector estimates on percolation clusters*) in dimension `d ≥ 3`
alone (`Rigidity.Green.GeneralFlux.fluxVarianceBoundThree_of_stepTwoWeight`), and the input
`LatticeProb.External.SupercriticalBondGreenQuantitative` (Dario and Gu, Theorem 2), the Green
input of Theorem 1.1 in every dimension, rests only on Proposition 2.12 of Dario and Gu
(`CorrectorQuantitativeInput`) and `DarioStepTwoWeightThree`
(`Rigidity.Assembly.ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_corrector_weight`).
-/

open LatticeProb.Percolation

namespace Rigidity.Green.GeneralFlux

/-- **The variance bound (3.4) of Gu's proof of Proposition 1.1 in dimension `d ≥ 3`** from the
probabilistic part of Step 2 of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`
(`DarioStepTwoWeightThree`) alone. -/
theorem fluxVarianceBoundThree_of_stepTwoWeight
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree) : FluxVarianceBoundThree :=
  fluxVarianceBoundThree_of_weightBound hW fun _ _ hd _ hpc hp1 =>
    fluxFlipWeightBoundD_holds (by omega) hpc hp1

end Rigidity.Green.GeneralFlux

namespace Rigidity.Assembly.ProvedFluxWeakNorm

/-- **Dario–Gu, Theorem 2, in every dimension**, from Proposition 2.12 (the quantitative
corrector estimate, `CorrectorQuantitativeInput`) and the probabilistic part of Step 2 of the proof
of Lemma 3.3 of Dario in dimension `d ≥ 3` (`DarioStepTwoWeightThree`): the Green input of
Theorem 1.1 in every dimension rests on these two statements and nothing else. -/
theorem supercriticalBondGreenQuantitative_of_corrector_weight
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_corrector_fluxVariance hCQ
    (Rigidity.Green.GeneralFlux.fluxVarianceBoundThree_of_stepTwoWeight hW)

end Rigidity.Assembly.ProvedFluxWeakNorm
