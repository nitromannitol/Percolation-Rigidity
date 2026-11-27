import Rigidity.Proofs.Assembly.PlanarGreenInputs
import Rigidity.Proofs.Poincare.DarioStepTwoHolds
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import Rigidity.Proofs.Green.LazyCarneVaropoulos

/-!
# Theorem 1.3 from the quantitative Green estimate of Dario and Gu

In dimension two four of the five planar inputs of `fast_decay_of_planar_estimates` are proved:
the qualitative corrector input (`supercriticalBondCorrectorInputTwo_holds`), the quantitative
corrector input (`correctorQuantitativeInputTwo_holds`, from Theorem 1 of Dario), and the
regularity of orders zero and one (`armstrongDarioOrderZeroTwo_holds`,
`armstrongDarioOrderOneOriginTwo_holds`). Theorem 1.3 therefore follows from the quantitative Green
estimate of Dario and Gu alone, hence from their Theorem 1, hence from the inputs `hSec` of their
Sections 2 and 4 with the Gaussian upper bound of Barlow, or from their Proposition 2.13 and
Theorem 3 with that bound.

* `fast_decay_of_greenQuantitative`: Theorem 1.3 from `SupercriticalBondGreenQuantitativeTwo`;
* `fast_decay_of_darioGu`: Theorem 1.3 from Theorem 1 of Dario and Gu (`DarioGuHeatKernelTwo`);
* `fast_decay_of_sections_barlow`, `fast_decay_of_flux_gradient_barlow`: Theorem 1.3 from the
  inputs of Theorem 1 of Dario and Gu (Sections 2 and 4, or Proposition 2.13 and Theorem 3) and the
  Gaussian upper bound of Barlow.

Every hypothesis of these theorems is proved: the Green estimate and Theorem 1 of Dario and Gu in
dimension two (`supercriticalBondGreenQuantitativeTwo_holds`, `darioGuHeatKernelTwo_holds`) and
Theorem 1.3 itself (`fast_decay_holds`), all in `Rigidity.Assembly.ProvedFluxWeakNorm`, and the
Gaussian upper bound of Barlow (`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`).
-/

namespace Rigidity.Assembly.WithPlanarInputs

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Green

/-- **Theorem 1.3** of the paper in dimension two from the quantitative Green estimate of Dario
and Gu (Theorem 2, (1.11)) alone. The paper takes Theorems 2.4 and 2.5 and the Green estimate as
inputs; here the corrector and regularity inputs in dimension two are proved. -/
theorem fast_decay_of_greenQuantitative (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) : FastDecayStmt p :=
  fast_decay_of_planar_estimates p hpc hp1
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds
    Rigidity.Poincare.correctorQuantitativeInputTwo_holds
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds
    Rigidity.Poincare.armstrongDarioOrderOneOriginTwo_holds hGQ

/-- **Theorem 1.3** of the paper in dimension two from Theorem 1 of Dario and Gu
(`DarioGuHeatKernelTwo`) alone; their Theorem 2 follows from it with the order-zero estimate. -/
theorem fast_decay_of_darioGu (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hP : DarioGuHeatKernelTwo) : FastDecayStmt p :=
  fast_decay_of_greenQuantitative p hpc hp1
    (supercriticalBondGreenQuantitativeTwo_of_darioGu_of_orderZero hP
      Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds)

/-- **Theorem 1.3** of the paper in dimension two from the inputs `hSec` of Sections 2 and 4 of
Dario and Gu and the Gaussian upper bound of Barlow. -/
theorem fast_decay_of_sections_barlow (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hSec : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuApproxLemmaTwo p σ ∧ DarioGuTwoScaleErrorTwo p σ ∧
        DarioGuDensityGaussianTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) : FastDecayStmt p :=
  fast_decay_of_darioGu p hpc hp1
    (Rigidity.Poincare.darioGuHeatKernelTwo_of_sections_barlow hSec hBar)

/-- **Theorem 1.3** of the paper in dimension two from Proposition 2.13 and Theorem 3 of Dario and
Gu and the Gaussian upper bound of Barlow. -/
theorem fast_decay_of_flux_gradient_barlow (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hG3 : DarioGuGradientBoundTwo) (hBar : BarlowGaussianUpperBoundTwo) : FastDecayStmt p :=
  fast_decay_of_darioGu p hpc hp1
    (Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow hflux hG3 hBar)

end Rigidity.Assembly.WithPlanarInputs
