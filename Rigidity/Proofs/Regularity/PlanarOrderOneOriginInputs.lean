import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicDegreeTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationTwo
import Rigidity.Proofs.Regularity.PlanarCorrectorReduction
import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMinimalScales
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderOneOriginInputs

/-!
# Theorem 2 (iii) at `k = 1` in the plane from the estimates on squares

The inputs of `armstrongDarioOrderOneOriginTwo_of_inputs` are discharged as follows.

* `PlanarCoarseHarmonicApproximationTwo` is `PlanarHarmonicApproximationTwo`
  (`planarCoarseHarmonicApproximationTwo_iff`): the coarsenings `coarseAtAnchor C u` and
  `planarCoarse C u` are the same function.
* `PlanarPartCubeMoments p` holds for `p > p_c(2)` (`planarPartCubeMoments_holds`): it is part of
  the minimal scales `Rigidity.Proofs.Cluster.PlanarMinimalScales p` of Proposition 2.4
  (`Rigidity.Proofs.Cluster.planarMinimalScales_holds`).
* `PlanarPartitionSizeScale p`, the hypothesis on the partition cubes of
  `planarHarmonicApproximationTwo_of_squareEstimates`, follows from the same minimal scales with
  `t = 1` and `α = 1/2`, above `max(M, 81)` (`planarPartitionSizeScale_of_partCubeMoments`,
  `planarPartitionSizeScale_holds`).
* The planar corrector inputs are `supercriticalBondCorrectorInputTwo_of_orderOne` (Theorem 2 (i),
  (ii) at `k = 1` and the order-zero regularity) and `correctorQuantitativeInputTwo_of_dario`
  (Theorem 1 of Dario, `DarioOptimalCorrectorTwo`).

`armstrongDarioOrderOneOriginTwo_of_squareEstimates`: Theorem 2 (iii) at `k = 1` in the plane from
the estimates on squares of the proof of Lemma 7.1 (`PlanarSquareEstimatesTwo`), Dario's Theorem 1
in dimension two, the existence of the corrected planes and `dim 𝒜_1 ≤ 3`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.S2

/-- **Armstrong–Dario, Theorem 2 (iii) at `k = 1`, at the origin, in the plane**, from the
estimates on squares of the proof of Lemma 7.1, Theorem 1 of Dario in dimension two, the existence
of the corrected planes and the bound `dim 𝒜_1 ≤ 3`. -/
theorem armstrongDarioOrderOneOriginTwo_of_squareEstimates
    (hS : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarSquareEstimatesTwo p)
    (hD : Rigidity.Corrector.DarioOptimalCorrectorTwo)
    (hex : PlanarCorrectedPlaneExistenceTwo) (hdim : PlanarOrderOneDimensionTwo) :
    ArmstrongDarioOrderOneOriginTwo := by
  have hHA := planarHarmonicApproximationTwo_of_squareEstimates_holds hS
  have hR2 := supercriticalBondCorrectorInputTwo_of_orderOne
    (armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation hHA) hex hdim
  exact armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar
    (armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates hS)
    (Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario hD hR2) hR2

end Rigidity.Proofs.Regularity
