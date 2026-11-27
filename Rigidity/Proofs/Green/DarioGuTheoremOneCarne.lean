import Rigidity.Proofs.Green.DarioGuTheoremOneApprox
import Rigidity.Proofs.Green.PlanarCarneVaropoulos

/-!
# Theorem 1 of Dario–Gu in dimension two with Proposition 2.15 proved

With the Carne–Varopoulos bound proved (`carneVaropoulosTwo_holds`), Proposition A.7 proved and
Lemma 4.1 reduced to Theorem 3 and the Poincaré inequality, Theorem 1 of Dario–Gu in dimension two
(`DarioGuHeatKernelTwo`) holds under Proposition 4.3 for some `σ > 0`, Theorem 3 (Remark 1.3),
the Poincaré inequality (Proposition 2.7), Theorem 4 (Barlow) and Proposition 2.12
(`CorrectorQuantitativeInputTwo`), or Dario's Theorem 1; Theorem 4 is proved
(`barlowGaussianUpperBoundTwo_holds`).
-/

namespace Rigidity.Green

open LatticeProb.Percolation Rigidity.External

/-- **Dario–Gu, Theorem 1** in dimension two from Proposition 4.3 (for some `σ > 0`), Theorem 3,
Proposition 2.7, Theorem 4 and Proposition 2.12. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_barlow
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hPo : ClusterPoincareTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hR5 : CorrectorQuantitativeInputTwo) :
    DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient hP43 hG3 hPo hBar carneVaropoulosTwo_holds hR5

/-- **Dario–Gu, Theorem 1** in dimension two, with Proposition 2.12 from Dario's Theorem 1. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_barlow_dario
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hPo : ClusterPoincareTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) :
    DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient_dario hP43 hG3 hPo hBar carneVaropoulosTwo_holds hD

end Rigidity.Green
