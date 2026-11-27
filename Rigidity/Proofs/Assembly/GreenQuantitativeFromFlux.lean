import Rigidity.Proofs.Assembly.GreenQuantitativeEveryDim
import Rigidity.Proofs.Green.GeneralTwoScaleFlow

/-!
# The quantitative Green estimate in every dimension from Propositions 2.12 and 2.13

The input `LatticeProb.External.SupercriticalBondGreenQuantitative` follows from the whole-cluster
estimate of Dario and Gu in every dimension `d ≥ 3`
(`ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_gaussianFlow`), and the whole-cluster
estimate on `ℤ^d` follows from Proposition 2.12 (`CorrectorQuantitativeInput`) and Proposition 2.13
on `ℤ^d` (`DarioGuFluxWeakNormD`; `Rigidity.Green.GeneralDim.exists_darioGuGaussianFlowD_of_inputs`).
Hence the input follows from the quantitative corrector estimate and Proposition 2.13 in every
dimension `d ≥ 3`.
-/

namespace Rigidity.Assembly.ProvedFluxWeakNorm

open LatticeProb.Percolation Rigidity.Green

/-- **Dario–Gu, Theorem 2, in every dimension**, from Proposition 2.12 (the quantitative
corrector estimate) and Proposition 2.13 (the weak norm of the centered flux) in every dimension
`d ≥ 3`. -/
theorem supercriticalBondGreenQuantitative_of_corrector_flux
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hflux : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval,
      criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
        ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormD d p σ) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_gaussianFlow fun d _ hd =>
    Rigidity.Green.GeneralDim.exists_darioGuGaussianFlowD_of_inputs hCQ (by omega) (hflux d hd)

end Rigidity.Assembly.ProvedFluxWeakNorm
