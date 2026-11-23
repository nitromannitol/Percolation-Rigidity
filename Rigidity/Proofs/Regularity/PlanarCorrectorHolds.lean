import Rigidity.Proofs.Regularity.PlanarOrderOneDimension
import Rigidity.Proofs.Regularity.PlanarOrderOneOriginInputs
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationHolds
import Rigidity.Proofs.Green.PlanarGreenColumnCorrector
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoProof

/-!
# The planar corrector input, the Green column and Theorem 2 (iii) at `k = 1` in dimension two

The qualitative corrector input `SupercriticalBondCorrectorInputTwo` (R2) follows from the minimal
scales, the order-zero regularity and (7.18) at `k = 2`
(`supercriticalBondCorrectorInputTwo_of_mesoscopic`). In dimension two the three are proved for
`p > p_c(2)` (`planarMinimalScalesTwo_holds`, `armstrongDarioOrderZeroTwo_holds`, and (7.18) from
the estimates on squares, `planarSquareEstimatesTwo_holds`), so:

* `supercriticalBondCorrectorInputTwo_holds`: R2 in dimension two, with no hypothesis;
* `supercriticalBondGreenColumnExistenceTwo_holds`: R6 in dimension two, with no hypothesis;
* `armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector`: Theorem 2 (iii) at `k = 1` at the
  origin in dimension two (R4) from Theorem 1 of Dario (`DarioOptimalCorrectorTwo`) alone;
* `darioOptimalCorrectorTwo_of_oscillation`: Theorem 1 of Dario in dimension two from the
  multiscale Poincaré inequality, the concentration inequality, (1.22) and Lemma 3.3, with R2 and
  R3 discharged.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb.Percolation Rigidity.External

/-- The statement of (7.18) at `k = 2` in the plane used for the dimension of `𝒜_1` is that of
`ArmstrongDarioMesoscopicDegreeTwoPlanar`. -/
theorem mesoscopicDegreeTwoPlanarInput_iff :
    MesoscopicDegreeTwoPlanarInput ↔ ArmstrongDarioMesoscopicDegreeTwoPlanar :=
  Iff.rfl

/-- **Armstrong–Dario, Lemma 7.3, (7.18) at `k = 2`, in the plane**, with no hypothesis beyond
`p > p_c(2)`, from the estimates on squares. -/
theorem mesoscopicDegreeTwoPlanarInput_holds : MesoscopicDegreeTwoPlanarInput :=
  armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates fun _ hpc hp1 =>
    planarSquareEstimatesTwo_holds hpc hp1

/-- **R2 in dimension two**: the planar qualitative corrector input, with no hypothesis beyond
`p > p_c(2)`. -/
theorem supercriticalBondCorrectorInputTwo_holds : SupercriticalBondCorrectorInputTwo :=
  supercriticalBondCorrectorInputTwo_of_mesoscopic mesoscopicDegreeTwoPlanarInput_holds
    (fun _ hpc _ => planarMinimalScalesTwo_holds hpc) armstrongDarioOrderZeroTwo_holds

/-- **The existence of the planar corrected planes**, with no hypothesis. -/
theorem planarCorrectedPlaneExistenceTwo_holds : PlanarCorrectedPlaneExistenceTwo :=
  planarCorrectedPlaneExistenceTwo_of_minimalScales
    (fun _ hpc _ => planarMinimalScalesTwo_holds hpc) armstrongDarioOrderZeroTwo_holds

/-- **`dim 𝒜_1 ≤ 3` in the plane**, with no hypothesis. -/
theorem planarOrderOneDimensionTwo_holds : PlanarOrderOneDimensionTwo :=
  planarOrderOneDimensionTwo_of_minimalScales mesoscopicDegreeTwoPlanarInput_holds
    (fun _ hpc _ => planarMinimalScalesTwo_holds hpc) armstrongDarioOrderZeroTwo_holds

/-- **R6 in dimension two**: the existence and uniqueness of the planar Green columns, with no
hypothesis beyond `p > p_c(2)`. -/
theorem supercriticalBondGreenColumnExistenceTwo_holds :
    SupercriticalBondGreenColumnExistenceTwo :=
  Rigidity.Green.supercriticalBondGreenColumnExistenceTwo_of_correctorInput
    supercriticalBondCorrectorInputTwo_holds

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in dimension two** (R4), from
Theorem 1 of Dario alone: the corrected planes and the bound on the dimension of `𝒜_1` are
proved. -/
theorem armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo) : ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_dario hD planarCorrectedPlaneExistenceTwo_holds
    planarOrderOneDimensionTwo_holds

/-- **Dario, Theorem 1, in dimension two**, from the multiscale Poincaré inequality, the
concentration inequality, the quantitative sublinearity (1.22) and Lemma 3.3, with the qualitative
corrector input and the order-zero regularity proved. -/
theorem darioOptimalCorrectorTwo_of_oscillation {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hMSP : Rigidity.Corrector.MultiscalePoincareTwo A₀) (hconc : Rigidity.Corrector.ConcentrationTwo)
    (h122 : Rigidity.Corrector.CorrectorOscSublinearTwo)
    (h33 : Rigidity.Corrector.DarioLemmaThreeThree) :
    Rigidity.Corrector.DarioOptimalCorrectorTwo :=
  Rigidity.Corrector.darioOptimalCorrectorTwo_of_osc supercriticalBondCorrectorInputTwo_holds
    armstrongDarioOrderZeroTwo_holds hA₀ hMSP hconc h122 h33

end Rigidity.Proofs.Regularity
