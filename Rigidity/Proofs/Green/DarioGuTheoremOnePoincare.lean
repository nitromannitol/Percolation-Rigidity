import Rigidity.Proofs.Green.DarioGuTheoremOneCarne
import Rigidity.Proofs.Green.DarioGuPoincareHolds

/-!
# Theorem 1 of Dario–Gu in dimension two with the Poincaré inequality proved

With the weak Poincaré inequality on balls of the cluster proved (`clusterPoincareTwo_holds`),
Lemma 4.1 holds from Theorem 3 (Remark 1.3), Theorem 4 and the Carne–Varopoulos bound
(`darioGuApproxLemmaTwo_of_gradient`), and Theorem 1 of Dario–Gu in dimension two
(`DarioGuHeatKernelTwo`) holds under Proposition 4.3 for some `σ > 0`, Theorem 3, Theorem 4
(Barlow, cited) and Proposition 2.12 (R5), or Dario's Theorem 1.
-/

namespace Rigidity.Green

open LatticeProb.Percolation Rigidity.External

/-- **Dario–Gu, Lemma 4.1** in dimension two from Theorem 3 and Theorem 4. -/
theorem darioGuApproxLemmaTwo_of_gradient (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ} (hσ : 0 < σ) :
    DarioGuApproxLemmaTwo p σ :=
  darioGuApproxLemmaTwo_of_inputs hG3 clusterPoincareTwo_holds hBar carneVaropoulosTwo_holds hpc
    hp1 hσ

/-- **Dario–Gu, Theorem 1** in dimension two from Proposition 4.3 (for some `σ > 0`), Theorem 3,
Theorem 4 and Proposition 2.12. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_barlow_poincare
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (hR5 : CorrectorQuantitativeInputTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient_barlow hP43 hG3 clusterPoincareTwo_holds hBar hR5

/-- **Dario–Gu, Theorem 1** in dimension two, with Proposition 2.12 from Dario's Theorem 1. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_barlow_poincare_dario
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient_barlow_dario hP43 hG3 clusterPoincareTwo_holds hBar hD

end Rigidity.Green
