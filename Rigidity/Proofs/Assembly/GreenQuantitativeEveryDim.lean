import Rigidity.Proofs.Assembly.ProvedGradient
import Rigidity.Proofs.Assembly.ProvedFluxWeakNorm
import Rigidity.Proofs.Green.BondCarneVaropoulos
import Rigidity.Proofs.Green.GreenQuantitativeThree
import Rigidity.Proofs.Green.HeatKernelHoldsD

/-!
# Theorem 2 of Dario and Gu in every dimension from its remaining inputs

The quantitative Green estimate of Dario and Gu in every dimension `d ≥ 2`
(`LatticeProb.External.SupercriticalBondGreenQuantitative`, Theorem 2) follows from
Proposition 2.13 of Dario and Gu in dimension two (`DarioGuFluxWeakNormTwo`), Theorem 1 of Dario
and Gu in every dimension `d ≥ 3` (`DarioGuHeatKernelD d`) and the small-time bound of the heat
kernel for `d ≥ 3` (`OpenHeatSmallTimeD d`, from the Carne–Varopoulos bound).

The small-time bound is proved (`openHeatSmallTimeD_holds`): the heat kernel `openHeatD` is
`bondHeat` and the norm of the displacement `edzD x y` is `WeakPoincare.latticeDist x y`, both by
definition, so `OpenHeatSmallTimeD d` is `HeatSmallTimeD d` (`heatSmallTimeD_holds`).
Proposition 2.13 is proved too (`darioGuFluxWeakNormTwo_holds`), so the input in every dimension
follows from Theorem 1 of Dario and Gu in every dimension `d ≥ 3` alone
(`ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_heatKernel`). Theorem 1 in dimension
`d` follows from the whole-cluster estimate (4.40) with Proposition 2.12 (`DarioGuGaussianFlowD d`,
`darioGuHeatKernelD_of_gaussianFlow`), so the input in every dimension follows from that estimate
in every dimension `d ≥ 3` alone
(`ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_gaussianFlow`).
-/

namespace Rigidity.Green

/-- The small-time bound `p(t, x, y) ≤ C e^{-|x - y|/C}` for `0 < t ≤ |x - y|` on the infinite
components of `ℤ^d`, with `C = 8d`. -/
theorem openHeatSmallTimeD_holds {d : ℕ} [NeZero d] : OpenHeatSmallTimeD d :=
  heatSmallTimeD_holds

end Rigidity.Green

namespace Rigidity.Assembly.WithProvedBarlow

open LatticeProb.Percolation Rigidity.Green

/-- **Dario–Gu, Theorem 2, in every dimension**, from Proposition 2.13 in dimension two and
Theorem 1 and the small-time bound in every dimension `d ≥ 3`. -/
theorem supercriticalBondGreenQuantitative_of_flux_heatKernel
    (hflux : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∃ σ : ℝ, 0 < σ ∧ DarioGuFluxWeakNormTwo p σ)
    (hP : ∀ (d : ℕ) [NeZero d], 3 ≤ d → DarioGuHeatKernelD d)
    (hS : ∀ (d : ℕ) [NeZero d], 3 ≤ d → OpenHeatSmallTimeD d) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_two_of_three
    (supercriticalBondGreenQuantitativeTwo_of_flux hflux)
    (supercriticalBondGreenQuantitativeThree_of_heatKernel hP hS)

end Rigidity.Assembly.WithProvedBarlow

namespace Rigidity.Assembly.ProvedFluxWeakNorm

open Rigidity.Green

/-- **Dario–Gu, Theorem 2, in every dimension**, from Theorem 1 of Dario and Gu in every dimension
`d ≥ 3` alone: Proposition 2.13 in dimension two and the small-time bound are proved. -/
theorem supercriticalBondGreenQuantitative_of_heatKernel
    (hP : ∀ (d : ℕ) [NeZero d], 3 ≤ d → DarioGuHeatKernelD d) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  Rigidity.Assembly.WithProvedBarlow.supercriticalBondGreenQuantitative_of_flux_heatKernel
    darioGuFluxWeakNormTwo_holds hP fun _ _ _ => openHeatSmallTimeD_holds

/-- **Dario–Gu, Theorem 2, in every dimension**, from the whole-cluster estimate of Dario and Gu,
(4.40) with Proposition 2.12, in every dimension `d ≥ 3` alone: Theorem 1 follows from it
(`darioGuHeatKernelD_of_gaussianFlow`). -/
theorem supercriticalBondGreenQuantitative_of_gaussianFlow
    (hflow : ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval,
      LatticeProb.Percolation.criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
        ∃ σ : ℝ, 0 < σ ∧ DarioGuGaussianFlowD d p σ) :
    LatticeProb.External.SupercriticalBondGreenQuantitative :=
  supercriticalBondGreenQuantitative_of_heatKernel fun d _ hd =>
    darioGuHeatKernelD_of_gaussianFlow (by omega) (hflow d hd)

end Rigidity.Assembly.ProvedFluxWeakNorm
