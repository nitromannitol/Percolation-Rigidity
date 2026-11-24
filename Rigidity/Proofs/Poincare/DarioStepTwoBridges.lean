import Rigidity.Proofs.Poincare.DarioCorrectorBridges
import Rigidity.Proofs.Poincare.DarioGuFluxBridges
import Rigidity.Proofs.Corrector.DarioResamplePartitionHolds

/-!
# Theorem 1 of Dario and its consequences from the bound of the Step 2 sum

With Lemma 3.5 for the planar partition proved (`darioResamplePartitionTwo_holds`), the flip form
`DarioFlipSumBound` of (3.13), hence Lemma 3.3 of Dario, follows from the bound of the Step 2 sum
`Σ_e T₂(e)²` of the proof of Lemma 3.3 alone (`DarioStepTwoSumBound`, the hypothesis `hTwo` of
`darioFlipSumBound_of_resample`). So do Theorem 1 of Dario in dimension two, Proposition 2.12 of
Dario and Gu, Theorem 2 (iii) of Armstrong and Dario at `k = 1` at the origin, and, with their
further named inputs, Theorem 1 of Dario and Gu.
-/

namespace Rigidity.Poincare

open MeasureTheory LatticeProb.Percolation Rigidity.Corrector Rigidity.External Rigidity.Green
open scoped ENNReal

/-- The bound of the Step 2 sum of the proof of Lemma 3.3 of Dario: for every supercritical
`p < 1` and every almost sure event `G` of valid correctors, `Σ_e T₂(e)²` is almost surely finite
and `O_s(C / r²)`. -/
def DarioStepTwoSumBound : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
      (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
        ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
          (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
          IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)

/-- **The flip form (3.13) of Lemma 3.3 of Dario from the Step 2 sum.** -/
theorem darioFlipSumBound_of_stepTwo (hTwo : DarioStepTwoSumBound) : DarioFlipSumBound :=
  darioFlipSumBound_of_resample darioResamplePartitionTwo_holds hTwo

/-- **Dario, Theorem 1, in dimension two**, from the bound of the Step 2 sum. -/
theorem darioOptimalCorrectorTwo_of_stepTwo (hTwo : DarioStepTwoSumBound) :
    DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_flipSum (darioFlipSumBound_of_stepTwo hTwo)

/-- **Dario and Gu, Proposition 2.12, in dimension two**, from the bound of the Step 2 sum. -/
theorem correctorQuantitativeInputTwo_of_stepTwo (hTwo : DarioStepTwoSumBound) :
    CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_flipSum (darioFlipSumBound_of_stepTwo hTwo)

/-- **Armstrong and Dario, Theorem 2 (iii) at `k = 1`, at the origin, in dimension two**, from the
bound of the Step 2 sum. -/
theorem armstrongDarioOrderOneOriginTwo_of_stepTwo (hTwo : DarioStepTwoSumBound) :
    ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_flipSum (darioFlipSumBound_of_stepTwo hTwo)

/-- **Dario and Gu, Theorem 1, in dimension two**, from the bound of the Step 2 sum and the further
inputs of `darioGuHeatKernelTwo_of_reduced_dario`. -/
theorem darioGuHeatKernelTwo_of_reduced_stepTwo
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hTwo : DarioStepTwoSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_reduced_flipSum hSec hBar hCV (darioFlipSumBound_of_stepTwo hTwo)

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 2.13, Theorem 3, Theorem 4 and
the bound of the Step 2 sum. -/
theorem darioGuHeatKernelTwo_of_flux_gradient_barlow_stepTwo
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (hTwo : DarioStepTwoSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum hflux hG3 hBar
    (darioFlipSumBound_of_stepTwo hTwo)

end Rigidity.Poincare
