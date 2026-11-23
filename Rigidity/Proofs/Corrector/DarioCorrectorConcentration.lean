import Rigidity.Proofs.Corrector.ConcentrationTwoHolds
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds

/-!
# Theorem 1 of Dario in dimension two with the concentration inequality proved

With `concentrationTwo_holds` (Dario, Proposition 2.17), Theorem 1 of Dario in dimension two
(`DarioOptimalCorrectorTwo`) follows from the multiscale Poincaré inequality
(`MultiscalePoincareTwo`, Proposition 2.19), the quantitative sublinearity of the corrector
(`CorrectorOscSublinearTwo`; Armstrong and Dario, (1.22), recalled as Dario, (2.1)) and Lemma 3.3
(`DarioLemmaThreeThree`) alone.
-/

namespace Rigidity.Corrector

/-- **Dario, Theorem 1, in dimension two**, from the multiscale Poincaré inequality, the
quantitative sublinearity of the corrector and Lemma 3.3; the concentration inequality, the
qualitative corrector input and the order-zero regularity are proved. -/
theorem darioOptimalCorrectorTwo_of_poincare_osc {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hMSP : MultiscalePoincareTwo A₀) (h122 : CorrectorOscSublinearTwo)
    (h33 : DarioLemmaThreeThree) : DarioOptimalCorrectorTwo :=
  Rigidity.Proofs.Regularity.darioOptimalCorrectorTwo_of_oscillation hA₀ hMSP
    concentrationTwo_holds h122 h33

end Rigidity.Corrector
