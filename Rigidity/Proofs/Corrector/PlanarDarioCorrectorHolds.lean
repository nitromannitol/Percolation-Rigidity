import Rigidity.Proofs.Corrector.DarioPropThreeOne
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationHolds

/-!
# Theorem 1 of Dario and the quantitative corrector input in dimension two

`darioOptimalCorrectorTwo_of_lemmas` takes the qualitative corrector input (R2), the order-zero
regularity input (R3), the multiscale Poincaré inequality `MultiscalePoincareTwo A₀`, the
concentration inequality of Proposition 2.17 (`ConcentrationTwo`) and Lemmas 3.2 and 3.3 of
Dario (`DarioLemmaThreeTwo`, `DarioLemmaThreeThree`). The order-zero regularity input is proved in
dimension two with no hypothesis (`armstrongDarioOrderZeroTwo_holds`), so Theorem 1 of Dario
(`DarioOptimalCorrectorTwo`) and the quantitative corrector input of Dario and Gu
(`CorrectorQuantitativeInputTwo`, Proposition 2.12) follow from exactly the qualitative corrector
input, the multiscale Poincaré inequality with some positive constant, the concentration
inequality and Lemmas 3.2 and 3.3.
-/

namespace Rigidity.Corrector

open Rigidity.External

/-- **Dario, Theorem 1, in dimension two**, from the qualitative corrector input, the multiscale
Poincaré inequality (Proposition 2.19) with some positive constant, the concentration inequality
(Proposition 2.17) and Lemmas 3.2 and 3.3. -/
theorem darioOptimalCorrectorTwo_of_inputs (hR2 : SupercriticalBondCorrectorInputTwo)
    (hMSP : ∃ A₀ : ℝ, 0 < A₀ ∧ MultiscalePoincareTwo A₀) (hconc : ConcentrationTwo)
    (h32 : DarioLemmaThreeTwo) (h33 : DarioLemmaThreeThree) : DarioOptimalCorrectorTwo := by
  obtain ⟨A₀, hA₀, hM⟩ := hMSP
  exact darioOptimalCorrectorTwo_of_lemmas hR2
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hA₀ hM hconc h32 h33

/-- **Dario and Gu, Proposition 2.12, in dimension two**, from the qualitative corrector input,
the multiscale Poincaré inequality with some positive constant, the concentration inequality and
Lemmas 3.2 and 3.3 of Dario. -/
theorem correctorQuantitativeInputTwo_of_inputs (hR2 : SupercriticalBondCorrectorInputTwo)
    (hMSP : ∃ A₀ : ℝ, 0 < A₀ ∧ MultiscalePoincareTwo A₀) (hconc : ConcentrationTwo)
    (h32 : DarioLemmaThreeTwo) (h33 : DarioLemmaThreeThree) :
    CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_dario
    (darioOptimalCorrectorTwo_of_inputs hR2 hMSP hconc h32 h33) hR2

end Rigidity.Corrector
