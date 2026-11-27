import Rigidity.Proofs.Assembly.ProvedCorrector
import Rigidity.Proofs.Assembly.ProvedGreenColumn
import Rigidity.Proofs.Assembly.GreenQuantitativeFromStepTwoWeight
import Rigidity.Proofs.Corrector.GeneralResamplePartitionProved
import Rigidity.Proofs.Green.GeneralFluxStepTwoInput

/-!
# Theorem 1.1 and Proposition 3.2 in every dimension from two statements of dimension `d ≥ 3`

The quantitative corrector input (Theorem 2.5 of the paper, Proposition 2.12 of Dario and Gu;
`Rigidity.External.CorrectorQuantitativeInput`) follows from Lemma 3.3 of Dario in dimension
`d ≥ 3`, which follows from the probabilistic part of Step 2 of its proof
(`Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree`; Lemma 3.5 in corrected form and Step 1
are proved). The quantitative Green estimate of Dario and Gu
(`LatticeProb.External.SupercriticalBondGreenQuantitative`) follows from it, from the same
statement and from the flip bound of the flux on `ℤᵈ`
(`Rigidity.Green.GeneralFlux.FluxFlipWeightBoundD`) in every dimension `d ≥ 3`. The other
literature inputs of Theorem 1.1 and Proposition 3.2 are proved. Hence Theorem 1.1 and
Proposition 3.2 hold in every dimension `d ≥ 2` from these two statements. Both are proved
(`Rigidity.Corrector.GeneralDim.darioStepTwoWeightThree_holds`,
`Rigidity.Green.GeneralFlux.fluxFlipWeightBoundD_holds`), and Theorem 1.1 and Proposition 3.2 with
the regime as their only hypothesis are `Rigidity.Assembly.Unconditional.lipschitz` and
`Rigidity.Assembly.Unconditional.notLipschitz`.
-/

namespace Rigidity.Assembly.EveryDimension

open LatticeProb.Percolation

/-- **Theorem 2.5** (Proposition 2.12 of Dario and Gu, quantitative corrector estimate) from the
probabilistic part of Step 2 of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3`. -/
theorem correctorQuantitativeInput_of_stepTwoWeight
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree) :
    Rigidity.External.CorrectorQuantitativeInput :=
  Rigidity.Assembly.WithProvedCorrector.correctorQuantitativeInput_of_darioVarianceBoundThree
    (Rigidity.Corrector.GeneralDim.darioVarianceBoundThree_of_stepTwoWeight hW)

/-- **Dario–Gu, Theorem 2, in every dimension**, from the probabilistic part of Step 2 of the proof
of Lemma 3.3 of Dario in dimension `d ≥ 3` and the flip bound of the flux on `ℤᵈ`
(`FluxFlipWeightBoundD`, for `d ≥ 3` and supercritical `p < 1`). -/
theorem supercriticalBondGreenQuantitative_of_stepTwoWeight
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree)
    (h2 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → Rigidity.Green.GeneralFlux.FluxFlipWeightBoundD d p) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  Rigidity.Assembly.ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_corrector_stepTwoWeight
    (correctorQuantitativeInput_of_stepTwoWeight hW) hW h2

/-- **Theorem 1.1** (`theorem:lipschitz`) in every dimension `d ≥ 2`, from the probabilistic part
of Step 2 of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3` and the flip bound of the flux
on `ℤᵈ` in dimension `d ≥ 3`. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree)
    (h2 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → Rigidity.Green.GeneralFlux.FluxFlipWeightBoundD d p) :
    Rigidity.Section3.LipschitzStmt d p :=
  Rigidity.Assembly.WithProvedGreenColumn.lipschitz d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    (correctorQuantitativeInput_of_stepTwoWeight hW)
    (supercriticalBondGreenQuantitative_of_stepTwoWeight hW h2)

/-- **Proposition 3.2** (`prop:not-lipschitz`) in every dimension `d ≥ 2`, from the probabilistic
part of Step 2 of the proof of Lemma 3.3 of Dario in dimension `d ≥ 3` and the flip bound of the
flux on `ℤᵈ` in dimension `d ≥ 3`. -/
theorem notLipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree)
    (h2 : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval, criticalProbability d < (p : ℝ) →
      (p : ℝ) < 1 → Rigidity.Green.GeneralFlux.FluxFlipWeightBoundD d p) :
    Rigidity.Section3.NotLipschitzStmt d p :=
  Rigidity.Assembly.WithProvedGreenColumn.notLipschitz d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    (correctorQuantitativeInput_of_stepTwoWeight hW)
    (supercriticalBondGreenQuantitative_of_stepTwoWeight hW h2)

end Rigidity.Assembly.EveryDimension
