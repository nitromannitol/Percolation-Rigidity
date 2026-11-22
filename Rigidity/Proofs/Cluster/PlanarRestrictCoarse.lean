import Rigidity.Proofs.Cluster.PlanarEdgePairing

/-!
# The pairing of a coarsened gradient with a bounded field, through the Meyers estimate

The deterministic part of Steps 2 and 3 of the proof of Lemma 5.5 of Armstrong and Dario, in
dimension two, for one subcube. Let `V` be a triadic cube with cluster `𝒞(V)`, `B ⊆ V` a resolved
integer square (in the proof, `V` with the boundary layer `K_z` removed), `w` a function and
`E = |∇w 1_{𝐚≠0}|²` on `𝒞(V)`. For a field `g` with `|g| ≤ G` on the lattice edges and Meyers cells
covering `𝒞(B)` inside `V`,
`⟨∇[w]_𝒫, g⟩_V² ≤ 8 G² |B| C² (∑_{𝒞(B)} W^{3q})^{1/q} C_M^{1/p} N ∑_V E
  + 16 G² |V \ B| ∑_V |∇[w]_𝒫|²`:
the first term is Step 3 (`planarBox_coarse_energy_le_of_meyers`), the second the boundary layer of
Step 2 (`edgePairing_sq_le_of_subset`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical

variable {ω : Configuration 2}

/-- **The pairing of a coarsened gradient with a bounded field on a subcube** (Armstrong and
Dario, proof of Lemma 5.5, Steps 2 and 3, deterministic part, in dimension two). -/
theorem edgePairing_coarse_sq_le_of_meyers (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    {B : IntegerCube 2} (hBr : PlanarBoxResolved ω B)
    (hBV : B.vertices ⊆ V.toIntegerCube.vertices) (w : Vertex 2 → ℝ)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex 2 → ℝ)
    (hWt : ∀ z ∈ boxClusterVertices ω B,
      (3 : ℝ) ^ (planarBoxCoarseData hP B hBr).pairReachScale z ≤ Wt z)
    {p q CM : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (I : Finset (ℕ × Vertex 2)) {N : ℕ}
    (hcov : ∀ z ∈ boxClusterVertices ω B, ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => clusterEnergy ω (clusterVertices ω V) w x ^ p) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) w) ^ p) :
    edgePairing V.toIntegerCube.vertices g (fun x => w (planarCoarseAnchor ω x)) ^ 2 ≤
      8 * G ^ 2 * B.vertices.card *
        ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
          (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
          ((∑ z ∈ boxClusterVertices ω B, (Wt z ^ 3) ^ q) ^ (1 / q) *
            (CM ^ (1 / p) * ((N : ℝ) *
              ∑ x ∈ V.toIntegerCube.vertices, clusterEnergy ω (clusterVertices ω V) w x)))) +
      16 * G ^ 2 * (V.toIntegerCube.vertices \ B.vertices).card *
        ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph 2)
          V.toIntegerCube.vertices (fun x => w (planarCoarseAnchor ω x)) x ^ 2 := by
  have hBV' : boxClusterVertices ω B ⊆ clusterVertices ω V :=
    boxClusterVertices_subset_clusterVertices fun x hx =>
      (V.mem_toIntegerCube_vertices x).1 (hBV (Finset.mem_coe.1 hx))
  have hsplit := edgePairing_sq_le_of_subset hBV hg (fun x => w (planarCoarseAnchor ω x))
  have hmey := planarBox_coarse_energy_le_of_meyers hP hBr hBV' w Wt hWt hpq hCM I hcov hV hN hM
  refine hsplit.trans (add_le_add_left ?_ _)
  exact mul_le_mul_of_nonneg_left hmey (by positivity)

end Rigidity.Proofs.Cluster
