import Rigidity.Proofs.Poincare.MultiscalePoincareHolds
import Rigidity.Proofs.Corrector.DarioLemmaThreeThreeFlip
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoHolds
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import Rigidity.Proofs.Green.DarioGuTheoremOneReduced

/-!
# Theorem 1 of Dario and its consequences from the concentration inequality and Lemma 3.3 alone

With the multiscale Poincaré inequality (`multiscalePoincareTwo_holds`), the qualitative corrector
input, the order-zero regularity and the quantitative sublinearity (1.22) proved, Theorem 1 of Dario
in dimension two follows from the concentration inequality `ConcentrationTwo` (Proposition 2.17) and
Lemma 3.3 (`DarioLemmaThreeThree`), or from `ConcentrationTwo` and the flip form `DarioFlipSumBound`
of (3.13). The same inputs give `CorrectorQuantitativeInputTwo`, `ArmstrongDarioOrderOneOriginTwo`
and, with the further named inputs of `darioGuHeatKernelTwo_of_reduced_dario`, Theorem 1 of Dario and
Gu.
-/

namespace Rigidity.Poincare

open Rigidity.Corrector Rigidity.External

/-- **Dario, Theorem 1, in dimension two**, from the concentration inequality and Lemma 3.3. -/
theorem darioOptimalCorrectorTwo_of_concentration_lemmaThreeThree (hconc : ConcentrationTwo)
    (h33 : DarioLemmaThreeThree) : DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_lemmaThreeThree multiscalePoincareTwo_holds hconc h33

/-- **Dario, Theorem 1, in dimension two**, from the concentration inequality and the flip form
of (3.13). -/
theorem darioOptimalCorrectorTwo_of_concentration_flipSum (hconc : ConcentrationTwo)
    (hflip : DarioFlipSumBound) : DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_concentration_lemmaThreeThree hconc
    (darioLemmaThreeThree_of_flipSum hflip)

/-- **Dario and Gu, Proposition 2.12, in dimension two**, from the concentration inequality and
the flip form of (3.13). -/
theorem correctorQuantitativeInputTwo_of_concentration_flipSum (hconc : ConcentrationTwo)
    (hflip : DarioFlipSumBound) : CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_lemmaThreeThree multiscalePoincareTwo_holds hconc
    (darioLemmaThreeThree_of_flipSum hflip)

/-- **Armstrong and Dario, Theorem 2 (iii) at `k = 1`, at the origin, in dimension two**, from the
concentration inequality and the flip form of (3.13). -/
theorem armstrongDarioOrderOneOriginTwo_of_concentration_flipSum (hconc : ConcentrationTwo)
    (hflip : DarioFlipSumBound) : ArmstrongDarioOrderOneOriginTwo :=
  Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector
    (darioOptimalCorrectorTwo_of_concentration_flipSum hconc hflip)

/-- **Dario and Gu, Theorem 1, in dimension two**, from the concentration inequality, the flip
form of (3.13) and the further inputs of `darioGuHeatKernelTwo_of_reduced_dario`. -/
theorem darioGuHeatKernelTwo_of_reduced_concentration_flipSum
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hconc : ConcentrationTwo) (hflip : DarioFlipSumBound) : DarioGuHeatKernelTwo :=
  Rigidity.Green.darioGuHeatKernelTwo_of_reduced_dario hSec hBar hCV
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds
    (darioOptimalCorrectorTwo_of_concentration_flipSum hconc hflip)

end Rigidity.Poincare
