import Rigidity.Proofs.Regularity.PlanarCorrectorOscHolds
import Rigidity.Proofs.Corrector.PlanarDarioCorrectorHolds

/-!
# Lemma 3.2 of Dario in dimension two with no hypothesis

The quantitative sublinearity (1.22) of Armstrong and Dario in dimension two
(`CorrectorOscSublinearTwo`) is proved (`correctorOscSublinearTwo_holds`, from
`Rigidity.Proofs.Regularity.planarCorrectorOscSublinearTwo_holds`), and so are the order-zero
regularity and the qualitative corrector input. Hence:

* `darioLemmaThreeTwo_holds`: Lemma 3.2 of Dario in dimension two (`DarioLemmaThreeTwo`), by
  `darioLemmaThreeTwo_of_osc`;
* `darioOptimalCorrectorTwo_of_lemmaThreeThree`: Theorem 1 of Dario in dimension two from the
  multiscale Poincaré inequality, the concentration inequality and Lemma 3.3;
* `correctorQuantitativeInputTwo_of_lemmaThreeThree`: Proposition 2.12 of Dario and Gu in dimension
  two from the same three inputs.
-/

namespace Rigidity.Corrector

open Rigidity.External

/-- **Armstrong–Dario, (1.22), in dimension two** (Dario, (2.1)), with no hypothesis. -/
theorem correctorOscSublinearTwo_holds : CorrectorOscSublinearTwo :=
  Rigidity.Proofs.Regularity.planarCorrectorOscSublinearTwo_holds

/-- **Dario, Lemma 3.2, in dimension two**, with no hypothesis:
`|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r` for `r ≥ 1`. -/
theorem darioLemmaThreeTwo_holds : DarioLemmaThreeTwo :=
  darioLemmaThreeTwo_of_osc Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds
    correctorOscSublinearTwo_holds

/-- **Dario, Theorem 1, in dimension two**, from the multiscale Poincaré inequality with some
positive constant, the concentration inequality and Lemma 3.3. -/
theorem darioOptimalCorrectorTwo_of_lemmaThreeThree
    (hMSP : ∃ A₀ : ℝ, 0 < A₀ ∧ MultiscalePoincareTwo A₀) (hconc : ConcentrationTwo)
    (h33 : DarioLemmaThreeThree) : DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_inputs
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds hMSP hconc
    darioLemmaThreeTwo_holds h33

/-- **Dario and Gu, Proposition 2.12, in dimension two**, from the multiscale Poincaré inequality
with some positive constant, the concentration inequality and Lemma 3.3 of Dario. -/
theorem correctorQuantitativeInputTwo_of_lemmaThreeThree
    (hMSP : ∃ A₀ : ℝ, 0 < A₀ ∧ MultiscalePoincareTwo A₀) (hconc : ConcentrationTwo)
    (h33 : DarioLemmaThreeThree) : CorrectorQuantitativeInputTwo :=
  correctorQuantitativeInputTwo_of_inputs
    Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds hMSP hconc
    darioLemmaThreeTwo_holds h33

end Rigidity.Corrector
