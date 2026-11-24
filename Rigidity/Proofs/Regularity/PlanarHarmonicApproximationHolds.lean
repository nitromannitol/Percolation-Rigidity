import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationInputs
import Rigidity.Proofs.Regularity.PlanarOrderOneOriginInputs
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarTheoremOneHolds
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMinimalScales
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationHolds
import Rigidity.Proofs.S3.Reflection

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

/-- **Armstrong–Dario, Theorem 2 (iii) for `k = 1`, at the origin, in dimension two**, from
Theorem 1 of Dario, the existence of the corrected planes and the bound `dim 𝒜_1 ≤ 3`. -/
theorem armstrongDarioOrderOneOriginTwo_of_dario (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo)
    (hex : PlanarCorrectedPlaneExistenceTwo) (hdim : PlanarOrderOneDimensionTwo) :
    ArmstrongDarioOrderOneOriginTwo :=
  armstrongDarioOrderOneOriginTwo_of_squareEstimates
    (fun _ hpc hp1 => planarSquareEstimatesTwo_holds hpc hp1) hD hex hdim

end Rigidity.Proofs.Regularity
