import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationInputs
import Rigidity.Proofs.Regularity.PlanarOrderOneOriginInputs
import Rigidity.Proofs.Dirichlet.PlanarTheoremOneHolds
import Rigidity.Proofs.Cluster.PlanarMinimalScales

/-!
# Lemma 7.1 and the order-zero regularity in dimension two, with no hypothesis

The inputs of `planarHarmonicApproximationTwo_of_inputs` are the minimal scales of the planar
partition (`PlanarMinimalScalesTwo p`, the statement `Rigidity.Proofs.Cluster.PlanarMinimalScales p`
of Proposition 2.4) and Theorem 1 in dimension two with the discrete homogenized solution
(`PlanarHomogenizationErrorTwo p p'`, the statement
`Rigidity.Dirichlet.PlanarHomogenizationError p p'`). Both are proved for `p > p_c(2)`
(`planarMinimalScales_holds`, `planarHomogenizationError_holds`), so the following hold with no
hypothesis beyond `p > p_c(2)`:

* `planarSquareEstimatesTwo_holds`: the estimates on the squares of the proof of Lemma 7.1;
* `planarHarmonicApproximationTwo_holds`: Lemma 7.1 in dimension two
  (`PlanarHarmonicApproximationTwo`);
* `armstrongDarioOrderZeroTwo_holds`: Theorem 2 (iii) for `k = 0` in dimension two
  (`ArmstrongDarioOrderZeroTwo`).

`armstrongDarioOrderOneOriginTwo_of_dario` is Theorem 2 (iii) for `k = 1` at the origin in
dimension two from Theorem 1 of Dario (`DarioOptimalCorrectorTwo`), the existence of the corrected
planes (`PlanarCorrectedPlaneExistenceTwo`) and `dim 𝒜_1 ≤ 3` (`PlanarOrderOneDimensionTwo`).
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb.Percolation Rigidity.External

/-- The minimal scales of the planar partition, in the form used for Lemma 7.1, for `p > p_c(2)`. -/
theorem planarMinimalScalesTwo_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarMinimalScalesTwo p :=
  Rigidity.Proofs.Cluster.planarMinimalScales_holds hpc

/-- Theorem 1 in dimension two, in the form used for Lemma 7.1, for `p > p_c(2)` and `p' > 2`. -/
theorem planarHomogenizationErrorTwo_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {p' : ℝ} (hp' : 2 < p') :
    PlanarHomogenizationErrorTwo p p' :=
  Rigidity.Dirichlet.planarHomogenizationError_holds hpc hp'

/-- **The estimates on squares of the proof of Lemma 7.1**, for `p_c(2) < p < 1`, with no further
hypothesis. -/
theorem planarSquareEstimatesTwo_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : PlanarSquareEstimatesTwo p :=
  planarSquareEstimatesTwo_of_parts
    (planarHarmonicDistTwo_of_homogenizationError hpc hp1 (planarMinimalScalesTwo_holds hpc)
      fun _ hp' => planarHomogenizationErrorTwo_holds hpc hp')
    (planarCoarseComparisonTwo_of_minimalScales hpc hp1 (planarMinimalScalesTwo_holds hpc))
    (planarCoarseBoundTwo_of_minimalScales hpc hp1 (planarMinimalScalesTwo_holds hpc))

/-- **Armstrong–Dario, Lemma 7.1, in dimension two**, with no hypothesis. -/
theorem planarHarmonicApproximationTwo_holds : PlanarHarmonicApproximationTwo :=
  planarHarmonicApproximationTwo_of_inputs (fun _ hpc _ => planarMinimalScalesTwo_holds hpc)
    fun _ hpc _ _ hp' => planarHomogenizationErrorTwo_holds hpc hp'

/-- **Armstrong–Dario, Theorem 2 (iii) for `k = 0`, in dimension two**, with no hypothesis. -/
theorem armstrongDarioOrderZeroTwo_holds : ArmstrongDarioOrderZeroTwo :=
  armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation planarHarmonicApproximationTwo_holds

/-- **Armstrong–Dario, Theorem 2 (iii) for `k = 1`, at the origin, in dimension two**, from
Theorem 1 of Dario, the existence of the corrected planes and the bound `dim 𝒜_1 ≤ 3`. -/
theorem armstrongDarioOrderOneOriginTwo_of_dario (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo)
    (hex : PlanarCorrectedPlaneExistenceTwo) (hdim : PlanarOrderOneDimensionTwo) :
    ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_squareEstimates
    (fun _ hpc hp1 => planarSquareEstimatesTwo_holds hpc hp1) hD hex hdim

end Rigidity.Proofs.Regularity
