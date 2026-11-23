import Rigidity.Proofs.Green.DarioGuTheoremOneDensity
import Rigidity.Proofs.Green.DarioGuApproxLemma

/-!
# Theorem 1 of Dario–Gu in dimension two with Lemma 4.1 reduced to Theorem 3

Lemma 4.1 holds for every diffusivity `σ > 0` from Theorem 3 (Remark 1.3), the Poincaré inequality
(Proposition 2.7), Theorem 4 and Proposition 2.15 (`darioGuApproxLemmaTwo_of_inputs`); with
Proposition A.7 proved, Theorem 1 of Dario–Gu in dimension two (`DarioGuHeatKernelTwo`) holds under
Proposition 4.3 for some `σ > 0`, Theorem 3, Proposition 2.7, Theorem 4, Proposition 2.15 and
Proposition 2.12 (or Dario's Theorem 1).
-/

namespace Rigidity.Green

open LatticeProb.Percolation Rigidity.External

/-- **Dario–Gu, Theorem 1** in dimension two from Proposition 4.3 (for some `σ > 0`), Theorem 3,
Proposition 2.7, Theorem 4, Proposition 2.15 and Proposition 2.12. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hPo : ClusterPoincareTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hR5 : CorrectorQuantitativeInputTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_approx_twoScale (fun p hpc hp1 => by
    obtain ⟨σ, hσ, hP⟩ := hP43 p hpc hp1
    exact ⟨σ, hσ, darioGuApproxLemmaTwo_of_inputs hG3 hPo hBar hCV hpc hp1 hσ, hP⟩)
    hBar hCV hR5

/-- **Dario–Gu, Theorem 1** in dimension two, with Proposition 2.12 from Dario's Theorem 1. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_dario
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hPo : ClusterPoincareTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_approx_twoScale_dario (fun p hpc hp1 => by
    obtain ⟨σ, hσ, hP⟩ := hP43 p hpc hp1
    exact ⟨σ, hσ, darioGuApproxLemmaTwo_of_inputs hG3 hPo hBar hCV hpc hp1 hσ, hP⟩)
    hBar hCV hD

end Rigidity.Green
