import Rigidity.Proofs.Regularity.PlanarAffineApproximationNu
import Rigidity.Proofs.Percolation.PlanarFlatnessAE
import Rigidity.Proofs.Cluster.PlanarConvergenceRate
import Rigidity.Proofs.Cluster.PlanarRHRestrictQuad

/-!
# The approximation of affine functions on the planar cluster from the minimal scales

Lemma 5.8, (5.33), of Armstrong and Dario (arXiv:1609.09431v2) in expectation
(`exists_planarNuFlatness_majorant_ae`, from Lemma 5.5, `planarRestrictQuadCoarsenNu_holds`) and
Lemma 5.10 (`exists_planarTau_le_geometric`) discharge the first two inputs of
`planarAffineApproximationAeTwo_of_nuFlatness`. What remains are the minimal scales of
Proposition 2.4 and, for the corrected planes, the order-zero regularity.
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Cluster

theorem planarNuFlatnessMajorantTwo_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) : PlanarNuFlatnessMajorantTwo p :=
  exists_planarNuFlatness_majorant_ae hpc (planarRestrictQuadCoarsenNu_holds hpc)

theorem planarTauGeometricTwo_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) : PlanarTauGeometricTwo p :=
  exists_planarTau_le_geometric hpc

/-- **The approximation of affine functions with an almost surely finite scale** from the minimal
scales of Proposition 2.4. -/
theorem planarAffineApproximationAeTwo_of_minimalScales
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p) :
    PlanarAffineApproximationAeTwo :=
  planarAffineApproximationAeTwo_of_nuFlatness (fun _ hpc _ => planarNuFlatnessMajorantTwo_holds hpc)
    (fun _ hpc _ => planarTauGeometricTwo_holds hpc) hM5

/-- **Every slope has a corrected plane on the planar cluster** from the minimal scales of
Proposition 2.4 and the order-zero regularity. -/
theorem planarCorrectedPlaneExistenceTwo_of_minimalScales
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hR3 : ArmstrongDarioOrderZeroTwo) : PlanarCorrectedPlaneExistenceTwo :=
  planarCorrectedPlaneExistenceTwo_of_nuFlatness (fun _ hpc _ => planarNuFlatnessMajorantTwo_holds hpc)
    (fun _ hpc _ => planarTauGeometricTwo_holds hpc) hM5 hR3

end Rigidity.Proofs.Regularity
