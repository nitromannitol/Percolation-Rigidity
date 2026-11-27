import Rigidity.Proofs.Assembly.GreenQuantitativeFromFlux
import Rigidity.Proofs.Green.GeneralFluxHolds
import Rigidity.Proofs.Green.GeneralFluxStepTwoInput

/-!
# The quantitative Green estimate in every dimension from Proposition 2.12 and Gu's variance bound

The input `LatticeProb.External.SupercriticalBondGreenQuantitative` follows from Proposition 2.12
of Dario and Gu (`CorrectorQuantitativeInput`) and their Proposition 2.13 in every dimension `d ≥ 3`
(`supercriticalBondGreenQuantitative_of_corrector_flux`). Proposition 2.13 on `ℤ^d` follows from
the variance bound (3.4) of Gu's proof of his Proposition 1.1 (*An efficient algorithm for solving
elliptic problems on percolation clusters*), `FluxVarianceBoundD d p`
(`Rigidity.Green.GeneralFlux.darioGuFluxWeakNormD_of_variance`). Hence the input follows from the
quantitative corrector estimate and the variance bound in every dimension `d ≥ 3`
(`supercriticalBondGreenQuantitative_of_corrector_fluxVariance`); the variance bound is the target
`FluxVarianceBoundThree` of the port of the flip chain of the flux to `ℤ^d`
(`Rigidity.Green.GeneralFlux`, `GeneralFluxStepTwoInput.lean`).
-/

namespace Rigidity.Assembly.ProvedFluxWeakNorm

open LatticeProb.Percolation

/-- **Dario–Gu, Theorem 2, in every dimension**, from Proposition 2.12 (the quantitative
corrector estimate) and the variance bound (3.4) of Gu for the heat averages of the flux in every
dimension `d ≥ 3`. -/
theorem supercriticalBondGreenQuantitative_of_corrector_fluxVariance
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hV : Rigidity.Green.GeneralFlux.FluxVarianceBoundThree) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_corrector_flux hCQ fun d _ hd p hpc hp1 =>
    Rigidity.Green.GeneralFlux.darioGuFluxWeakNormD_of_variance (by omega) p hpc hp1
      (hV d hd p hpc hp1)

end Rigidity.Assembly.ProvedFluxWeakNorm
