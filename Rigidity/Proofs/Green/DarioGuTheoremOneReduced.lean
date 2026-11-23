import Rigidity.Proofs.Green.DarioGuTheoremOneCorrector
import Rigidity.Proofs.Green.DarioGuCorrectorLemma

/-!
# Theorem 1 of Dario–Gu in dimension two: the remaining hypotheses

With the estimate of the two-scale initial error and Lemma 4.2 proved from Proposition 2.12,
Theorem 4 and Proposition 2.15, Theorem 1 of Dario–Gu in dimension two (`DarioGuHeatKernelTwo`)
holds under:

* Lemma 4.1 (in the form of the iteration step), Proposition 4.3 and Proposition A.7 of the source
  for some diffusivity `σ > 0` (proved in the source from §3, §4.1–§4.2 and Appendix A; not
  formalized here);
* Theorem 4 (Barlow 2004, cited), Proposition 2.15 (Davies 1993, cited);
* the qualitative corrector input and Proposition 2.12 (R5), or Dario's Theorem 1.
-/

namespace Rigidity.Green

open LatticeProb.Percolation Rigidity.External

/-- **Dario–Gu, Theorem 1** in dimension two from Lemma 4.1, Proposition 4.3, Proposition A.7,
Theorem 4, Proposition 2.15, Proposition 2.12 and the qualitative corrector input. -/
theorem darioGuHeatKernelTwo_of_reduced
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hCorr : SupercriticalBondCorrectorInputTwo) (hR5 : CorrectorQuantitativeInputTwo) :
    DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_correctorQuantitative (fun p hpc hp1 => by
    obtain ⟨σ, hσ, hA, hP, hD⟩ := hSec p hpc hp1
    exact ⟨σ, hσ, hA, darioGuCorrectorLemmaTwo_of_inputs hR5 hBar hCV hpc hp1 hσ, hP, hD⟩)
    hBar hCV hCorr hR5

/-- **Dario–Gu, Theorem 1** in dimension two, with Proposition 2.12 from Dario's Theorem 1. -/
theorem darioGuHeatKernelTwo_of_reduced_dario
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hCorr : SupercriticalBondCorrectorInputTwo)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_reduced hSec hBar hCV hCorr
    (Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario hD hCorr)

end Rigidity.Green
