import Rigidity.Proofs.Cluster.ReverseHolderCube
import Rigidity.Proofs.Cluster.ReverseHolderSobolev

/-!
# The reverse Hölder inequality on the crossing cluster of a resolved cube

Armstrong–Dario, Lemma 3.6, deterministic part, for the partition into good cubes: let
`□_{m+1}` be the triadic cube of scale `m + 1` centered at the origin, resolved by the partition, and
`U = 𝒞_*(□_{m+1})` its crossing cluster. The crossing cluster contains every vertex of `□_{m+1}`
joined to it by an open edge (`mem_crossingCluster_of_adj`), `□_{m+1}` is the triple of
`□_m = cube m 0` (`triadicCube_vertices_eq_enl`), and the Sobolev hypothesis is Proposition 3.4
(`clusterSobolevTwo_of_latticeSobolevOn`). Hence, given the lattice Sobolev–Poincaré inequality on
`□_{m+1}` with exponents `2`, `2_*` and the moment bound
`∑_{z ∈ U} (3^{ρ(z)})^{2ds} ≤ C_G |□_{m+1}|` of the reach scales `ρ`, every function harmonic on `U`
satisfies the reverse Hölder inequality between the points of `U` in `□_m` and `U`
(`reverse_holder_partition`). The points of `U` in `□_m` contain `𝒞_*(□_m)`, the domain of the left
side in the source.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical

variable {d : ℕ}

/-- The crossing cluster contains every vertex of the cube joined to it by an open edge. -/
theorem mem_crossingCluster_of_adj {ω : Configuration d} {Q : TriadicCube d} {z y : Vertex d}
    (hz : z ∈ Q.crossingCluster ω) (hadj : (openGraph ω).Adj z y) (hy : y ∈ Q.vertices) :
    y ∈ Q.crossingCluster ω := by
  obtain ⟨root, hroot, hreach⟩ := hz
  have hzQ : z ∈ Q.vertices := Q.crossingCluster_subset ω ⟨root, hroot, hreach⟩
  exact ⟨root, hroot, hreach.trans (SimpleGraph.Adj.reachable ⟨hadj, hzQ, hy⟩)⟩

theorem idx_zero_vertex (k : ℕ) : idx k (0 : Vertex d) = 0 := by
  funext i
  have h1 := two_mul_halfSide_add_one k
  have h2 := halfSide_nonneg k
  have hs : (0 : ℤ) < 3 ^ k := by positivity
  simp only [idx, Pi.zero_apply, zero_add]
  exact ediv_eq_of_le_of_lt hs (by simp [h2]) (by linarith)

theorem center_zero_vertex (k : ℕ) : center k (0 : Vertex d) = 0 := by
  funext i
  simp [center, idx_zero_vertex]

/-- The triadic cube of scale `m + 1` centered at the origin is the triple of `cube m 0`. -/
theorem triadicCube_vertices_eq_enl (m : ℕ) (y : Vertex d) :
    y ∈ (⟨m + 1, 0⟩ : TriadicCube d).vertices ↔ y ∈ enl 1 m (0 : Vertex d) := by
  rw [enl, mem_box, center_zero_vertex]
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
    sub_zero]
  have h1 := two_mul_halfSide_add_one (m + 1)
  refine forall_congr' fun i => ?_
  rw [abs_mul, abs_two]
  constructor <;> intro h <;> omega

/-- **Reverse Hölder inequality on the crossing cluster of a resolved cube** (Armstrong–Dario,
Lemma 3.6, deterministic part, for the partition into good cubes). -/
theorem reverse_holder_partition (hd : 2 ≤ d) {S : ℝ} (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ω : Configuration d) (hP : PartitionEvent ω) (m : ℕ)
      (hU : PartitionResolved ω ⟨m + 1, 0⟩),
      LatticeSobolevOn (⟨m + 1, 0⟩ : TriadicCube d).toIntegerCube.vertices 2 (lowerSobolevTwo d) S →
      ∀ {CG s t : ℝ}, 0 ≤ CG → s.HolderConjugate t →
      ∑ z ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
          ((3 : ℝ) ^ (partitionCoarseData (by omega) hP ⟨m + 1, 0⟩ hU).reachScale z) ^
            (2 * (d : ℝ) * s) ≤ CG * (3 : ℝ) ^ ((m + 1) * d) →
      ∀ u : Vertex d → ℝ, (∀ x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
          (∀ y, (openGraph ω).Adj x y → y ∈ crossingClusterVertices ω ⟨m + 1, 0⟩) →
            openLaplacian ω u x = 0) →
      (1 / (3 : ℝ) ^ (m * d)) * ∑ x ∈ (crossingClusterVertices ω ⟨m + 1, 0⟩).filter
          (· ∈ cube m (0 : Vertex d)),
          clusterGradSq ω (crossingClusterVertices ω ⟨m + 1, 0⟩) u x ≤
        8 * d * K * CG ^ (2 / (s * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          ((1 / (3 : ℝ) ^ ((m + 1) * d)) * ∑ x ∈ crossingClusterVertices ω ⟨m + 1, 0⟩,
            clusterGradSq ω (crossingClusterVertices ω ⟨m + 1, 0⟩) u x ^
              (t * lowerSobolevTwo d / 2)) ^ (2 / (t * lowerSobolevTwo d)) := by
  obtain ⟨K, hK0, hK⟩ := clusterSobolevTwo_of_latticeSobolevOn (d := d) hd hS
  refine ⟨K, hK0, ?_⟩
  intro ω hP m hU hLS CG s t hCG hst hgood u hu
  set Q : TriadicCube d := ⟨m + 1, 0⟩ with hQ
  set U := crossingClusterVertices ω Q with hUdef
  have hclosed : ∀ z ∈ U, ∀ y, (openGraph ω).Adj z y → y ∈ enl 1 m (0 : Vertex d) → y ∈ U := by
    intro z hz y hadj hy
    have hyQ : y ∈ Q.vertices := (triadicCube_vertices_eq_enl m y).mpr hy
    rw [hUdef, mem_crossingClusterVertices] at hz ⊢
    exact mem_crossingCluster_of_adj hz hadj hyQ
  exact reverse_holder_triadic ω (by omega) m 0 U (U.filter (· ∈ cube m (0 : Vertex d)))
    (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) hclosed _
    (fun z => by positivity) hK0 hCG hst (hK ω hP Q hU hLS) hgood u hu

end Rigidity.Proofs.Cluster
