import Rigidity.Proofs.Assembly.GreenQuantitativeFromFluxVariance
import Rigidity.Proofs.Green.GeneralFluxFlipMoments

/-!
# The quantitative Green estimate in every dimension from the Step 2 weight and the flip bound

The input `LatticeProb.External.SupercriticalBondGreenQuantitative` (Dario and Gu, Theorem 2), the
Green input of Theorem 1.1 in every dimension, follows from Proposition 2.12 of Dario and Gu
(`CorrectorQuantitativeInput`) and the variance bound (3.4) of Gu's proof of his Proposition 1.1
(*An efficient algorithm for solving elliptic problems on percolation clusters*) in every dimension
`d ≥ 3` (`supercriticalBondGreenQuantitative_of_corrector_fluxVariance`). That variance bound
follows from the probabilistic part of Step 2 of the proof of Lemma 3.3 of Dario (*Optimal
corrector estimates on percolation clusters*) in dimension `d ≥ 3` (`DarioStepTwoWeightThree`) and
the bound of each squared flip difference of the heat average of the flux by the Step 2 factor
(`FluxFlipWeightBoundD`) (`Rigidity.Green.GeneralFlux.fluxVarianceBoundThree_of_weightBound`).
Hence the Green input of Theorem 1.1 in every dimension follows from Proposition 2.12,
`DarioStepTwoWeightThree` and `FluxFlipWeightBoundD`
(`supercriticalBondGreenQuantitative_of_corrector_stepTwoWeight`). Since `FluxFlipWeightBoundD` is
proved (`Rigidity.Green.GeneralFlux.fluxFlipWeightBoundD_holds`), it rests on Proposition 2.12 and
`DarioStepTwoWeightThree` alone (`supercriticalBondGreenQuantitative_of_corrector_weight`).
-/

namespace Rigidity.Assembly.ProvedFluxWeakNorm

open LatticeProb.Percolation

/-- **Dario–Gu, Theorem 2, in every dimension**, from Proposition 2.12 (the quantitative
corrector estimate, `CorrectorQuantitativeInput`), the probabilistic part of Step 2 of the proof of
Lemma 3.3 of Dario in dimension `d ≥ 3` (`DarioStepTwoWeightThree`) and the bound of each squared
flip difference of the heat average of the flux by the Step 2 factor (`FluxFlipWeightBoundD`, for
`d ≥ 3` and supercritical `p < 1`). The third is proved (`fluxFlipWeightBoundD_holds`), which gives
`supercriticalBondGreenQuantitative_of_corrector_weight`. -/
theorem supercriticalBondGreenQuantitative_of_corrector_stepTwoWeight
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree)
    (h2 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → Rigidity.Green.GeneralFlux.FluxFlipWeightBoundD d p) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_corrector_fluxVariance hCQ
    (Rigidity.Green.GeneralFlux.fluxVarianceBoundThree_of_weightBound hW h2)

end Rigidity.Assembly.ProvedFluxWeakNorm
