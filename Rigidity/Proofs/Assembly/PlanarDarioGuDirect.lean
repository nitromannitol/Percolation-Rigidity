import Rigidity.Proofs.Assembly.PlanarDarioGu
import Rigidity.Proofs.Green.DarioGuGradientDirect

/-!
# Theorems 1 and 2 of Dario and Gu in dimension two from Proposition 2.13 and Theorem 4

Theorem 3 of Dario and Gu in dimension two (`DarioGuGradientBoundTwo`) is proved from Theorem 4,
the Gaussian upper bound of Barlow (`darioGuGradientBoundTwo_of_barlow`, through the elliptic
estimate for time slices of the heat kernel; Theorem 5 and Proposition 3.9 of the source are not
used). With it, Theorem 1 (`DarioGuHeatKernelTwo`), Theorem 2 (the quantitative Green estimate
`SupercriticalBondGreenQuantitativeTwo`) and Theorem 1.3 of the paper follow from Proposition 2.13
of Dario and Gu (`DarioGuFluxWeakNormTwo`) and Theorem 4 alone.

* `darioGuHeatKernelTwo_of_flux_barlow`: Theorem 1 of Dario and Gu;
* `supercriticalBondGreenQuantitativeTwo_of_flux_barlow`: Theorem 2 of Dario and Gu;
* `fast_decay_of_flux_barlow`: Theorem 1.3 of the paper.
-/

namespace Rigidity.Assembly.WithPlanarInputs

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Green

/-- **Dario–Gu, Theorem 1, in dimension two**, from Proposition 2.13 and Theorem 4. -/
theorem darioGuHeatKernelTwo_of_flux_barlow
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) : DarioGuHeatKernelTwo :=
  Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow hflux
    (darioGuGradientBoundTwo_of_barlow hBar) hBar

/-- **Dario–Gu, Theorem 2, in dimension two** (the quantitative Green estimate, with the random
additive constant of the plane), from Proposition 2.13 and Theorem 4. -/
theorem supercriticalBondGreenQuantitativeTwo_of_flux_barlow
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) :
    Rigidity.External.SupercriticalBondGreenQuantitativeTwo :=
  supercriticalBondGreenQuantitativeTwo_of_darioGu_of_orderZero
    (darioGuHeatKernelTwo_of_flux_barlow hflux hBar)
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds

/-- **Theorem 1.3** of the paper in dimension two from Proposition 2.13 of Dario and Gu and the
Gaussian upper bound of Barlow. -/
theorem fast_decay_of_flux_barlow (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hBar : BarlowGaussianUpperBoundTwo) : FastDecayStmt p :=
  fast_decay_of_flux_gradient_barlow p hpc hp1 hflux (darioGuGradientBoundTwo_of_barlow hBar) hBar

end Rigidity.Assembly.WithPlanarInputs
