import Rigidity.Proofs.Green.DarioGuTheoremOneReduced
import Rigidity.Proofs.Green.DarioGuDensityGaussian
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds

/-!
# Theorem 1 of Dario–Gu in dimension two with Proposition A.7 proved

Proposition A.7 holds for every diffusivity `σ > 0` (`darioGuDensityGaussianTwo_holds`) and the
qualitative corrector input holds (`supercriticalBondCorrectorInputTwo_holds`), so Theorem 1 of
Dario–Gu in dimension two (`DarioGuHeatKernelTwo`) holds under Lemma 4.1 (in the form of the
iteration step) and Proposition 4.3 for some `σ > 0`, Theorem 4 (Barlow 2004, cited),
Proposition 2.15 (Davies 1993, cited) and Proposition 2.12 (R5), or Dario's Theorem 1.
-/

namespace Rigidity.Green

open LatticeProb.Percolation Rigidity.External

/-- **Dario–Gu, Theorem 1** in dimension two from Lemma 4.1 and Proposition 4.3 (for some
`σ > 0`), Theorem 4, Proposition 2.15 and Proposition 2.12. -/
theorem darioGuHeatKernelTwo_of_approx_twoScale
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hR5 : CorrectorQuantitativeInputTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_reduced (fun p hpc hp1 => by
    obtain ⟨σ, hσ, hA, hP⟩ := hSec p hpc hp1
    exact ⟨σ, hσ, hA, hP, darioGuDensityGaussianTwo_holds hpc hp1 hσ⟩)
    hBar hCV Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds hR5

/-- **Dario–Gu, Theorem 1** in dimension two, with Proposition 2.12 from Dario's Theorem 1. -/
theorem darioGuHeatKernelTwo_of_approx_twoScale_dario
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_approx_twoScale hSec hBar hCV
    (Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario hD
      Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds)

end Rigidity.Green
