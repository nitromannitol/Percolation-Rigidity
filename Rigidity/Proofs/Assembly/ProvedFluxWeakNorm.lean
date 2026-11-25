import Rigidity.Proofs.Green.DarioGuFluxWeakNormHolds
import Rigidity.Proofs.Green.DarioGuFluxTranslateHolds
import Rigidity.Proofs.Poincare.DarioGuFluxBridges
import Rigidity.Proofs.Poincare.DarioStepTwoBridges
import Rigidity.Proofs.Assembly.PlanarDarioGu
import Rigidity.Proofs.Assembly.ProvedBarlow
import Rigidity.Proofs.Assembly.PlanarDarioGuVeryGood
import Rigidity.Proofs.Assembly.ProvedGradient

/-!
# The results that use Proposition 2.13 of Dario–Gu, with Proposition 2.13 proved

Proposition 2.13 of Dario–Gu in dimension two is proved (`darioGuFluxWeakNormTwo_holds`). The
results that took it as the hypothesis `hflux` are restated without it:

* Proposition 4.3 (`exists_darioGuTwoScaleErrorTwo_holds`) and Remark B.3
  (`exists_darioGuTranslatedFluxTwo_holds`), with the quantitative corrector estimate
  (`correctorQuantitativeInputTwo_holds`), now with no hypothesis;
* Theorem 1 of Dario and Gu in dimension two from Theorem 3 (Remark 1.3) and the Gaussian upper
  bound of Barlow (`darioGuHeatKernelTwo_of_gradient_barlow`), and its variants with Lemma 3.3 of
  Dario, the flip form of (3.13), Lemma 3.5 for the planar partition or the Step 2 sum;
* the quantitative Green function estimate `SupercriticalBondGreenQuantitativeTwo` from these two
  inputs (`supercriticalBondGreenQuantitativeTwo_of_gradient_barlow`);
* Theorem 1.3 of the paper in dimension two from these two inputs
  (`fast_decay_of_gradient_barlow`), or from Theorem 3 and the very good balls of the cluster
  (`fast_decay_of_gradient_veryGood`);
* with the Gaussian upper bound of Barlow proved (`barlowGaussianUpperBoundTwo_holds`), Theorem 1
  and Theorem 2 of Dario and Gu and Theorem 1.3 in dimension two from Theorem 3 alone
  (`darioGuHeatKernelTwo_of_gradient`, `supercriticalBondGreenQuantitativeTwo_of_gradient`,
  `fast_decay_of_gradient`);
* with Theorem 3 of Dario and Gu proved too (`darioGuGradientBoundTwo_holds`), Theorem 1 and
  Theorem 2 of Dario and Gu and Theorem 1.3 in dimension two with no hypothesis
  (`darioGuHeatKernelTwo_holds`, `supercriticalBondGreenQuantitativeTwo_holds`,
  `fast_decay_holds`).
-/

namespace Rigidity.Assembly.ProvedFluxWeakNorm

open MeasureTheory LatticeProb.Percolation Rigidity.Corrector Rigidity.External Rigidity.Green
  Rigidity.Poincare
open scoped ENNReal

/-- **Proposition 4.3 of Dario–Gu in dimension two**, with no hypothesis. -/
theorem exists_darioGuTwoScaleErrorTwo_holds :
    ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuTwoScaleErrorTwo p σ :=
  exists_darioGuTwoScaleErrorTwo_of_inputs correctorQuantitativeInputTwo_holds
    darioGuFluxWeakNormTwo_holds

/-- **Remark B.3 of Dario–Gu in dimension two**, with no hypothesis, for the diffusivity of
Proposition 2.13. -/
theorem exists_darioGuTranslatedFluxTwo_holds :
    ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ ∧ DarioGuTranslatedFluxTwo p σ := by
  intro p hpc hp1
  obtain ⟨σ, hσ, hf⟩ := darioGuFluxWeakNormTwo_holds p hpc hp1
  exact ⟨σ, hσ, hf, darioGuTranslatedFluxTwo_of_inputs correctorQuantitativeInputTwo_holds hpc hp1 hf⟩

/-- **Theorem 1 of Dario–Gu in dimension two** from Theorem 3, Theorem 4 and Lemma 3.3 of Dario. -/
theorem darioGuHeatKernelTwo_of_gradient_barlow_threeThree (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (h33 : DarioLemmaThreeThree) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_threeThree darioGuFluxWeakNormTwo_holds hG3 hBar h33

/-- **Theorem 1 of Dario–Gu in dimension two** from Theorem 3, Theorem 4 and the flip form of
(3.13). -/
theorem darioGuHeatKernelTwo_of_gradient_barlow_flipSum (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hflip : DarioFlipSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum darioGuFluxWeakNormTwo_holds hG3 hBar hflip

/-- **Theorem 1 of Dario–Gu in dimension two** from Theorem 3, Theorem 4, Lemma 3.5 for the planar
partition and the bound of the Step 2 sum. -/
theorem darioGuHeatKernelTwo_of_gradient_barlow_resample (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (h35 : DarioResamplePartitionTwo)
    (hTwo : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ (G : Set (Configuration 2)) (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2),
        (∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) → ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
          ∀ (i j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
            (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumTwo hG hGv i j r x ω < ∞) ∧
            IsOsBond 2 p (fun ω => (flipSumTwo hG hGv i j r x ω).toReal) s (C / r ^ 2)) :
    DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_resample darioGuFluxWeakNormTwo_holds hG3 hBar h35
    hTwo

/-- **Theorem 1 of Dario–Gu in dimension two** from Theorem 3, Theorem 4 and the bound of the
Step 2 sum. -/
theorem darioGuHeatKernelTwo_of_gradient_barlow_stepTwo (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hTwo : DarioStepTwoSumBound) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow_stepTwo darioGuFluxWeakNormTwo_holds hG3 hBar hTwo

/-- **Theorem 1 of Dario–Gu in dimension two** from Theorem 3 (Remark 1.3) and the Gaussian upper
bound of Barlow (Theorem 4). -/
theorem darioGuHeatKernelTwo_of_gradient_barlow (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_flux_gradient_barlow darioGuFluxWeakNormTwo_holds hG3 hBar

/-- **Theorem 2 of Dario–Gu in dimension two** (`SupercriticalBondGreenQuantitativeTwo`) from
Theorem 3 (Remark 1.3) and the Gaussian upper bound of Barlow. -/
theorem supercriticalBondGreenQuantitativeTwo_of_gradient_barlow (hG3 : DarioGuGradientBoundTwo)
    (hBar : BarlowGaussianUpperBoundTwo) : SupercriticalBondGreenQuantitativeTwo :=
  supercriticalBondGreenQuantitativeTwo_of_darioGu_of_orderZero
    (darioGuHeatKernelTwo_of_gradient_barlow hG3 hBar)
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds

/-- **Theorem 1.3** of the paper in dimension two from Theorem 3 of Dario and Gu and the Gaussian
upper bound of Barlow. -/
theorem fast_decay_of_gradient_barlow (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithPlanarInputs.fast_decay_of_flux_gradient_barlow p hpc hp1
    darioGuFluxWeakNormTwo_holds hG3 hBar

/-- **Theorem 1.3** of the paper in dimension two from Theorem 3 of Dario and Gu and the very good
balls of the cluster. -/
theorem fast_decay_of_gradient_veryGood (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hG3 : DarioGuGradientBoundTwo)
    (hVG : Rigidity.Barlow.ClusterVeryGoodBallsTwo) : Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithPlanarInputs.fast_decay_of_flux_gradient_veryGood p hpc hp1
    darioGuFluxWeakNormTwo_holds hG3 hVG

/-- **Theorem 1 of Dario–Gu in dimension two** from Theorem 3 (Remark 1.3) alone. -/
theorem darioGuHeatKernelTwo_of_gradient (hG3 : DarioGuGradientBoundTwo) : DarioGuHeatKernelTwo :=
  darioGuHeatKernelTwo_of_gradient_barlow hG3 Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

/-- **Theorem 2 of Dario–Gu in dimension two** (`SupercriticalBondGreenQuantitativeTwo`) from
Theorem 3 (Remark 1.3) alone. -/
theorem supercriticalBondGreenQuantitativeTwo_of_gradient (hG3 : DarioGuGradientBoundTwo) :
    SupercriticalBondGreenQuantitativeTwo :=
  supercriticalBondGreenQuantitativeTwo_of_gradient_barlow hG3
    Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

/-- **Theorem 1.3** of the paper in dimension two from Theorem 3 of Dario and Gu alone. -/
theorem fast_decay_of_gradient (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hG3 : DarioGuGradientBoundTwo) : Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedBarlow.fast_decay_of_flux_gradient p hpc hp1
    darioGuFluxWeakNormTwo_holds hG3

/-- **Theorem 1 of Dario–Gu in dimension two**, with no hypothesis. -/
theorem darioGuHeatKernelTwo_holds : DarioGuHeatKernelTwo :=
  Rigidity.Assembly.WithProvedBarlow.darioGuHeatKernelTwo_of_flux darioGuFluxWeakNormTwo_holds

/-- **Theorem 2 of Dario–Gu in dimension two** (`SupercriticalBondGreenQuantitativeTwo`, the
quantitative Green estimate with the random additive constant of the plane), with no hypothesis. -/
theorem supercriticalBondGreenQuantitativeTwo_holds : SupercriticalBondGreenQuantitativeTwo :=
  Rigidity.Assembly.WithProvedBarlow.supercriticalBondGreenQuantitativeTwo_of_flux
    darioGuFluxWeakNormTwo_holds

/-- **Theorem 1.3** of the paper (fast decay on the planar cluster), with no literature
hypothesis: for `p_c(2) < p < 1`. -/
theorem fast_decay_holds (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedBarlow.fast_decay_of_flux p hpc hp1 darioGuFluxWeakNormTwo_holds

end Rigidity.Assembly.ProvedFluxWeakNorm
