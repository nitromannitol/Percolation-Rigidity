import Rigidity.Proofs.Assembly.PlanarDarioGuDirect
import Rigidity.Proofs.Green.DarioGuGradientHolds
import Rigidity.Proofs.Assembly.ProvedBarlow

/-!
# Theorems 1 and 2 of Dario and Gu in dimension two from Proposition 2.13 alone

The Gaussian upper bound of Barlow (`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`) and
Theorem 3 of Dario and Gu (`Rigidity.Green.darioGuGradientBoundTwo_holds`) being proved, Theorem 1
(`DarioGuHeatKernelTwo`) and Theorem 2 (`SupercriticalBondGreenQuantitativeTwo`) of Dario and Gu,
and Theorem 1.3 of the paper, follow from Proposition 2.13 of Dario and Gu
(`DarioGuFluxWeakNormTwo`) alone.
-/

namespace Rigidity.Assembly.WithProvedBarlow

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Green

/-- **Dario–Gu, Theorem 1, in dimension two**, from Proposition 2.13. -/
theorem darioGuHeatKernelTwo_of_flux
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ) : DarioGuHeatKernelTwo :=
  Rigidity.Assembly.WithPlanarInputs.darioGuHeatKernelTwo_of_flux_barlow hflux
    Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

/-- **Dario–Gu, Theorem 2, in dimension two** (the quantitative Green estimate, with the random
additive constant of the plane), from Proposition 2.13. -/
theorem supercriticalBondGreenQuantitativeTwo_of_flux
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ) :
    Rigidity.External.SupercriticalBondGreenQuantitativeTwo :=
  Rigidity.Assembly.WithPlanarInputs.supercriticalBondGreenQuantitativeTwo_of_flux_barlow hflux
    Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds

/-- **Theorem 1.3** of the paper in dimension two from Proposition 2.13 of Dario and Gu alone. -/
theorem fast_decay_of_flux (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ) : FastDecayStmt p :=
  fast_decay_of_flux_gradient p hpc hp1 hflux darioGuGradientBoundTwo_holds

end Rigidity.Assembly.WithProvedBarlow
