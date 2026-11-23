import Rigidity.Proofs.Poincare.MultiscalePoincareHolds
import Rigidity.Proofs.Corrector.DarioLemmaThreeThreeFlip
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoHolds
import Rigidity.Proofs.Corrector.DarioCorrectorConcentration
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import Rigidity.Proofs.Green.DarioGuTheoremOneReduced

/-!
# Theorem 1 of Dario and its consequences from Lemma 3.3 alone

The multiscale Poincaré inequality (`multiscalePoincareTwo_holds`), the concentration inequality
(`concentrationTwo_holds`), the qualitative corrector input, the order-zero regularity and the
quantitative sublinearity (1.22) (`correctorOscSublinearTwo_holds`) are proved. Theorem 1 of Dario in
dimension two (`DarioOptimalCorrectorTwo`) therefore follows from Lemma 3.3 (`DarioLemmaThreeThree`)
alone (`darioOptimalCorrectorTwo_of_threeThree`), or from the flip form `DarioFlipSumBound` of (3.13)
alone (`darioOptimalCorrectorTwo_of_flipSum`). The same inputs give
`CorrectorQuantitativeInputTwo` and `ArmstrongDarioOrderOneOriginTwo`, and, with the further named
inputs of `darioGuHeatKernelTwo_of_reduced_dario`, Theorem 1 of Dario and Gu.
-/

namespace Rigidity.Poincare

open Rigidity.Corrector Rigidity.External

/-- **Dario, Theorem 1, in dimension two**, from Lemma 3.3. -/
theorem darioOptimalCorrectorTwo_of_threeThree (h33 : DarioLemmaThreeThree) :
    DarioOptimalCorrectorTwo := by
  obtain ⟨A₀, hA₀, hMSP⟩ := multiscalePoincareTwo_holds
  exact darioOptimalCorrectorTwo_of_poincare_osc hA₀ hMSP correctorOscSublinearTwo_holds h33

/-- **Dario, Theorem 1, in dimension two**, from the flip form of (3.13). -/
theorem darioOptimalCorrectorTwo_of_flipSum (hflip : DarioFlipSumBound) :
    DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_threeThree (darioLemmaThreeThree_of_flipSum hflip)

/-- **Dario and Gu, Proposition 2.12, in dimension two**, from Lemma 3.3. -/
theorem correctorQuantitativeInputTwo_of_threeThree (h33 : DarioLemmaThreeThree) :
    CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_dario (darioOptimalCorrectorTwo_of_threeThree h33)
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds

/-- **Dario and Gu, Proposition 2.12, in dimension two**, from the flip form of (3.13). -/
theorem correctorQuantitativeInputTwo_of_flipSum (hflip : DarioFlipSumBound) :
    CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_threeThree (darioLemmaThreeThree_of_flipSum hflip)

/-- **Armstrong and Dario, Theorem 2 (iii) at `k = 1`, at the origin, in dimension two**, from
Lemma 3.3. -/
theorem armstrongDarioOrderOneOriginTwo_of_threeThree (h33 : DarioLemmaThreeThree) :
    ArmstrongDarioOrderOneOriginTwo :=
  Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector
    (darioOptimalCorrectorTwo_of_threeThree h33)

/-- **Armstrong and Dario, Theorem 2 (iii) at `k = 1`, at the origin, in dimension two**, from the
flip form of (3.13). -/
theorem armstrongDarioOrderOneOriginTwo_of_flipSum (hflip : DarioFlipSumBound) :
    ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_threeThree (darioLemmaThreeThree_of_flipSum hflip)

/-- **Dario and Gu, Theorem 1, in dimension two**, from Lemma 3.3 and the further inputs of
`darioGuHeatKernelTwo_of_reduced_dario`. -/
theorem darioGuHeatKernelTwo_of_reduced_threeThree
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (h33 : DarioLemmaThreeThree) : DarioGuHeatKernelTwo :=
  Rigidity.Green.darioGuHeatKernelTwo_of_reduced_dario hSec hBar hCV
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds
    (darioOptimalCorrectorTwo_of_threeThree h33)

/-- **Dario and Gu, Theorem 1, in dimension two**, from the flip form of (3.13) and the further
inputs of `darioGuHeatKernelTwo_of_reduced_dario`. -/
theorem darioGuHeatKernelTwo_of_reduced_flipSum
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hflip : DarioFlipSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_reduced_threeThree hSec hBar hCV (darioLemmaThreeThree_of_flipSum hflip)

end Rigidity.Poincare
