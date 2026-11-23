import Rigidity.Proofs.Poincare.MultiscalePoincareHolds
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds

/-!
# Theorem 1 of Dario in dimension two with the multiscale Poincaré inequality proved

With `multiscalePoincareTwo_holds` (Dario, Proposition 2.19, (2.26)), Theorem 1 of Dario in
dimension two (`DarioOptimalCorrectorTwo`) follows from the concentration inequality
(Proposition 2.17), the quantitative sublinearity (1.22) and Lemma 3.3 alone
(`darioOptimalCorrectorTwo_of_concentration`).
-/

namespace Rigidity.Poincare

/-- **Dario, Theorem 1, in dimension two**, from the concentration inequality, the quantitative
sublinearity (1.22) and Lemma 3.3; the multiscale Poincaré inequality, the qualitative corrector
input and the order-zero regularity are proved. -/
theorem darioOptimalCorrectorTwo_of_concentration (hconc : Rigidity.Corrector.ConcentrationTwo)
    (h122 : Rigidity.Corrector.CorrectorOscSublinearTwo)
    (h33 : Rigidity.Corrector.DarioLemmaThreeThree) :
    Rigidity.Corrector.DarioOptimalCorrectorTwo := by
  obtain ⟨A₀, hA₀, hMSP⟩ := multiscalePoincareTwo_holds
  exact Rigidity.Proofs.Regularity.darioOptimalCorrectorTwo_of_oscillation hA₀ hMSP hconc h122 h33

end Rigidity.Poincare
