import Rigidity.Proofs.Cluster.PartitionSobolev
import Rigidity.Proofs.Cluster.PlanarLatticeSobolev

/-!
# The Sobolev inequality on the cluster in the plane

Armstrong and Dario, Proposition 3.4 with `d = 2` and `s = 2` (so `s_* = 1`), in the case
`∑_{C_*(U)} w = 0`, from the planar lattice Sobolev inequality on squares: there is a constant
`K` such that for every configuration of the partition event, every triadic cube `U` resolved by
the partition into good cubes and every `w` of mean zero on `C_*(U)`,
`∑_{x ∈ C_*(U)} w(x)² ≤ K (∑_{z ∈ C_*(U)} (3^{ρ(z)})² |∇w 1_{a≠0}|(z))²`,
with `ρ` the reach scale (Armstrong and Dario have the weight `size(□_𝒫(z))^{sd} = size^4`).
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

/-- **Armstrong and Dario, Proposition 3.4, in the plane with `s = 2`** (case
`∑_{C_*(U)} w = 0`). -/
theorem exists_partition_sum_sq_le_two :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration 2) (hP : PartitionEvent ω) (U : TriadicCube 2)
      (hU : PartitionResolved ω U) (w : Vertex 2 → ℝ),
      ∑ x ∈ crossingClusterVertices ω U, w x = 0 →
        ∑ x ∈ crossingClusterVertices ω U, w x ^ 2 ≤
          K * (∑ z ∈ crossingClusterVertices ω U,
            ((3 : ℝ) ^ (partitionCoarseData (by norm_num) hP U hU).reachScale z) ^ 2 *
              gradNormIn (openGraph ω) (crossingClusterVertices ω U) w z) ^ 2 := by
  obtain ⟨K, hK, h⟩ := exists_partition_sum_rpow_le_of_latticeSobolevOn (d := 2) (by norm_num)
    (s := 2) (t := 1) (S := 4) (by norm_num) le_rfl (by norm_num) (by norm_num)
  refine ⟨K, hK, fun ω hP U hU w hw => ?_⟩
  have hsize : 0 < U.toIntegerCube.size := by
    show 0 < 3 ^ U.scale
    positivity
  have h' := h ω hP U hU (U.toIntegerCube.latticeSobolevOn_two hsize) w hw
  simp only [one_mul, div_one, Real.rpow_one, Real.rpow_two, Nat.cast_ofNat, sq_abs] at h'
  exact h'

end Rigidity.Percolation
