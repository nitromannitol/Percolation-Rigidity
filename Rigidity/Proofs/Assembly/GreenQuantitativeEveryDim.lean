import Rigidity.Proofs.Assembly.ProvedGradient
import Rigidity.Proofs.Green.GreenQuantitativeThree

/-!
# Theorem 2 of Dario and Gu in every dimension from its remaining inputs

The quantitative Green estimate of Dario and Gu in every dimension `d ≥ 2`
(`LatticeProb.External.SupercriticalBondGreenQuantitative`, Theorem 2) follows from
Proposition 2.13 of Dario and Gu in dimension two (`DarioGuFluxWeakNormTwo`), Theorem 1 of Dario
and Gu in every dimension `d ≥ 3` (`DarioGuHeatKernelD d`) and the small-time bound of the heat
kernel for `d ≥ 3` (`HeatSmallTimeD d`, from the Carne–Varopoulos bound).
-/

namespace Rigidity.Assembly.WithProvedBarlow

open LatticeProb.Percolation Rigidity.Green

/-- **Dario–Gu, Theorem 2, in every dimension**, from Proposition 2.13 in dimension two and
Theorem 1 and the small-time bound in every dimension `d ≥ 3`. -/
theorem supercriticalBondGreenQuantitative_of_flux_heatKernel
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hP : ∀ (d : ℕ) [NeZero d], 3 ≤ d → DarioGuHeatKernelD d)
    (hS : ∀ (d : ℕ) [NeZero d], 3 ≤ d → HeatSmallTimeD d) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_two_of_three
    (supercriticalBondGreenQuantitativeTwo_of_flux hflux)
    (supercriticalBondGreenQuantitativeThree_of_heatKernel hP hS)

end Rigidity.Assembly.WithProvedBarlow
