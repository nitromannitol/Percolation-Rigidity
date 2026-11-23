import Rigidity.Proofs.Green.DarioGuTheoremOne
import Rigidity.Proofs.Green.DarioGuTwoScaleInitial

/-!
# Theorem 1 of Dario–Gu in dimension two with the two-scale initial error proved

The estimate of `h - θ^{-1} p̄` in §4.3 (`DarioGuTwoScaleInitialTwo`) follows from Proposition 2.12
(`CorrectorQuantitativeInputTwo`, R5; `darioGuTwoScaleInitialTwo_of_correctorQuantitative`), and
Proposition 2.12 follows from Dario's Theorem 1 (`DarioOptimalCorrectorTwo`) and the qualitative
corrector input (rigr57's `correctorQuantitativeInputTwo_of_dario`). The remaining hypotheses of
Theorem 1 are Lemma 4.1, Lemma 4.2, Proposition 4.3, Proposition A.7, Theorem 4 (Barlow) and
Proposition 2.15 (Carne–Varopoulos).
-/

namespace Rigidity.Green

open LatticeProb.Percolation Rigidity.External

/-- **Dario–Gu, Theorem 1** in dimension two from Lemma 4.1, Lemma 4.2, Proposition 4.3 and
Proposition A.7 (for some `σ > 0`), Theorem 4, Proposition 2.15, Proposition 2.12 and the
qualitative corrector input. -/
theorem darioGuHeatKernelTwo_of_correctorQuantitative
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuCorrectorLemmaTwo p σ ∧
        DarioGuTwoScaleErrorTwo p σ ∧ DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hCorr : SupercriticalBondCorrectorInputTwo) (hR5 : CorrectorQuantitativeInputTwo) :
    DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_sections (fun p hpc hp1 => by
    obtain ⟨σ, hσ, hA, hV, hP, hD⟩ := hSec p hpc hp1
    exact ⟨σ, hσ, hA, hV, hP, darioGuTwoScaleInitialTwo_of_correctorQuantitative hR5 hpc hp1 hσ,
      hD⟩) hBar hCV hCorr

/-- **Dario–Gu, Theorem 1** in dimension two, with Proposition 2.12 from Dario's Theorem 1. -/
theorem darioGuHeatKernelTwo_of_dario
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuCorrectorLemmaTwo p σ ∧
        DarioGuTwoScaleErrorTwo p σ ∧ DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hCorr : SupercriticalBondCorrectorInputTwo)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_correctorQuantitative hSec hBar hCV hCorr
    (Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario hD hCorr)

end Rigidity.Green
