import Rigidity.Proofs.Poincare.DarioGuBridges
import Rigidity.Proofs.Green.DarioGuTwoScaleFluxTerm
import Rigidity.Proofs.Corrector.DarioStepOneHolds

/-!
# Theorem 1 of Dario and Gu in dimension two from the weak norm of the flux

Proposition 4.3 of Dario and Gu is proved from the weak norm estimate of the centered flux
(Proposition 2.13, `DarioGuFluxWeakNormTwo`) and the quantitative corrector estimate
(`exists_darioGuTwoScaleErrorTwo_of_inputs`), and the quantitative corrector estimate follows from
Lemma 3.3 of Dario. Theorem 1 of Dario and Gu in dimension two (`DarioGuHeatKernelTwo`) is
therefore reduced to the following named inputs:

* `DarioGuFluxWeakNormTwo p σ` for some `σ > 0` at every supercritical `p < 1` (Proposition 2.13);
* `DarioGuGradientBoundTwo` (Theorem 3 in the form of Remark 1.3);
* `BarlowGaussianUpperBoundTwo` (Theorem 4);
* one of `DarioLemmaThreeThree` (Lemma 3.3), `DarioFlipSumBound` (the flip form of (3.13)), or
  `DarioResamplePartitionTwo` (Lemma 3.5 for the planar partition) together with the bound of the
  Step 2 sum.
-/

namespace Rigidity.Poincare

open MeasureTheory LatticeProb.Percolation Rigidity.Corrector Rigidity.External Rigidity.Green
open scoped ENNReal

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 2.13, Theorem 3, Theorem 4 and
Lemma 3.3. -/
theorem darioGuHeatKernelTwo_of_flux_gradient_barlow_threeThree
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (h33 : DarioLemmaThreeThree) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_twoScale_gradient_barlow_threeThree
    (exists_darioGuTwoScaleErrorTwo_of_inputs (correctorQuantitativeInputTwo_of_threeThree h33)
      hflux) hG3 hBar h33

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 2.13, Theorem 3, Theorem 4 and
the flip form of (3.13). -/
theorem darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (hflip : DarioFlipSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_threeThree hflux hG3 hBar
    (darioLemmaThreeThree_of_flipSum hflip)

/-- **Dario and Gu, Theorem 1, in dimension two**, from Proposition 2.13, Theorem 3, Theorem 4,
Lemma 3.5 for the planar partition and the bound of the Step 2 sum. -/
theorem darioGuHeatKernelTwo_of_flux_gradient_barlow_resample
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo)
    (h35 : DarioResamplePartitionTwo)
    (hTwo : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
        (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
          ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
            IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)) :
    DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum hflux hG3 hBar
    (darioFlipSumBound_of_resample h35 hTwo)

end Rigidity.Poincare
