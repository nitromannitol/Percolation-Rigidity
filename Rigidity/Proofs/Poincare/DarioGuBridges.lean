import Rigidity.Proofs.Poincare.DarioCorrectorBridges
import Rigidity.Proofs.Green.DarioGuTheoremOnePoincare

/-!
# Theorem 1 of Dario and Gu in dimension two with Proposition A.7, Proposition 2.15, Lemma 4.1 and
# the weak Poincaré inequality proved

Proposition A.7 (`darioGuDensityGaussianTwo_holds`), the Carne–Varopoulos bound
(`carneVaropoulosTwo_holds`), the weak form of Proposition 2.7 (`clusterPoincareTwo_holds`) and,
from Theorem 3 and Theorem 4, Lemma 4.1 (`darioGuApproxLemmaTwo_of_gradient`) are proved. With
Theorem 1 of Dario available from Lemma 3.3 (or from its flip form (3.13)), Theorem 1 of Dario and
Gu in dimension two (`DarioGuHeatKernelTwo`) follows from the four statements
`DarioGuTwoScaleErrorTwo` (Proposition 4.3, for some `σ > 0` at every supercritical `p < 1`),
`DarioGuGradientBoundTwo` (Theorem 3 in the form of Remark 1.3), `BarlowGaussianUpperBoundTwo`
(Theorem 4) and `DarioLemmaThreeThree` (Lemma 3.3), or `DarioFlipSumBound` in place of the last.
Each of the four is proved: `exists_darioGuTwoScaleErrorTwo_holds`, `darioGuGradientBoundTwo_holds`,
`barlowGaussianUpperBoundTwo_holds`, and Lemma 3.3 through `darioStepTwoSumBound_holds`,
`darioFlipSumBound_of_stepTwo` and `darioLemmaThreeThree_of_flipSum`; hence
`Rigidity.Assembly.ProvedFluxWeakNorm.darioGuHeatKernelTwo_holds`.
-/

namespace Rigidity.Poincare

open LatticeProb.Percolation Rigidity.Corrector Rigidity.External Rigidity.Green

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 4.3, Theorem 3, Theorem 4 and
Lemma 3.3; Proposition 2.15, Proposition A.7, Lemma 4.1 and the weak Poincaré inequality are
proved. -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_barlow_threeThree
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (h33 : DarioLemmaThreeThree) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient_barlow_poincare_dario hP43 hG3 hBar
    (darioOptimalCorrectorTwo_of_threeThree h33)

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 4.3, Theorem 3, Theorem 4 and
the flip form of (3.13). -/
theorem darioGuHeatKernelTwo_of_twoScale_gradient_barlow_flipSum
    (hP43 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (hflip : DarioFlipSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient_barlow_threeThree hP43 hG3 hBar
    (darioLemmaThreeThree_of_flipSum hflip)

end Rigidity.Poincare
