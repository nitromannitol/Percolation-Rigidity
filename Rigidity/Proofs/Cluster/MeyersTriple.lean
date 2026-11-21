import Rigidity.Proofs.Cluster.MeyersCluster
import Rigidity.External.WellConnected

/-!
# The Meyers estimate with the clusters of the triples

In `meyers_cluster` every cube `□'` of the hypothesis carries a set `U' ⊆ U₀ ∩ 3□'` closed under open
edges inside `3□'` and containing `U₀ ∩ □'`. When `U₀` itself contains every vertex of `3□` joined to it
by an open edge (as the crossing cluster `𝒞_*(□_{m+1})` does), such a set is `tripleCluster ω U₀ k y`:
the vertices of `U₀ ∩ 3□'` joined inside `U₀ ∩ 3□'` to a vertex of `U₀ ∩ □'` (for a well-connected
`3□'`, the cluster `𝒞_max(3□')` of Armstrong and Dario). In `meyers_tripleCluster` the remaining
hypotheses on the cubes are the Sobolev inequality and the moment bound on these sets.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.External
open scoped BigOperators Classical

variable {d : ℕ}

/-- The vertices of `U₀ ∩ 3□'`, `□' = cube k y`, joined inside `U₀ ∩ 3□'` by open edges to a vertex
of `U₀ ∩ □'`. -/
noncomputable def tripleCluster (ω : Configuration d) (U₀ : Finset (Vertex d)) (k : ℕ)
    (y : Vertex d) : Finset (Vertex d) :=
  ((enl 1 k y).filter (· ∈ U₀)).filter fun w => ∃ x ∈ U₀, x ∈ cube k y ∧
    (openIn ω ↑((enl 1 k y).filter (· ∈ U₀))).Reachable x w

theorem tripleCluster_subset_enl (ω : Configuration d) (U₀ : Finset (Vertex d)) (k : ℕ)
    (y : Vertex d) : tripleCluster ω U₀ k y ⊆ enl 1 k y := fun _ hw =>
  (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1

theorem tripleCluster_subset (ω : Configuration d) (U₀ : Finset (Vertex d)) (k : ℕ)
    (y : Vertex d) : tripleCluster ω U₀ k y ⊆ U₀ := fun _ hw =>
  (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2

theorem mem_tripleCluster_of_mem_cube (ω : Configuration d) {U₀ : Finset (Vertex d)} {k : ℕ}
    {y x : Vertex d} (hx : x ∈ U₀) (hxc : x ∈ cube k y) : x ∈ tripleCluster ω U₀ k y :=
  Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨cube_subset_enl 1 k y hxc, hx⟩, x, hx, hxc,
    SimpleGraph.Reachable.refl x⟩

/-- If `U₀` contains every vertex of `Ω ⊇ 3□'` joined to it by an open edge, `tripleCluster` is
closed under open edges inside `3□'`. -/
theorem tripleCluster_closed (ω : Configuration d) {U₀ Ω : Finset (Vertex d)} {k : ℕ}
    {y : Vertex d} (hU₀ : ∀ z ∈ U₀, ∀ w, (openGraph ω).Adj z w → w ∈ Ω → w ∈ U₀)
    (hΩ : enl 1 k y ⊆ Ω) {z w : Vertex d} (hz : z ∈ tripleCluster ω U₀ k y)
    (hadj : (openGraph ω).Adj z w) (hw : w ∈ enl 1 k y) : w ∈ tripleCluster ω U₀ k y := by
  rw [tripleCluster, Finset.mem_filter] at hz ⊢
  obtain ⟨hzB, x, hx, hxc, hreach⟩ := hz
  have hwU : w ∈ U₀ := hU₀ z (Finset.mem_filter.mp hzB).2 w hadj (hΩ hw)
  have hwB : w ∈ (enl 1 k y).filter (· ∈ U₀) := Finset.mem_filter.mpr ⟨hw, hwU⟩
  refine ⟨hwB, x, hx, hxc, hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
  exact ⟨hadj, Finset.mem_coe.mpr hzB, Finset.mem_coe.mpr hwB⟩

/-- **The Meyers estimate with the clusters of the triples** (Armstrong–Dario, Proposition 3.8,
deterministic part). As `meyers_cluster`, with `U₀` containing every vertex of `3□` joined to it by an
open edge and the Sobolev inequality and the moment bound required on `tripleCluster ω U₀ k y`. -/
theorem meyers_tripleCluster (hd : 1 ≤ d) {CS CG K : ℝ} (hCS : 0 ≤ CS) (hCG : 0 ≤ CG)
    (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (n : ℕ) (x₀ : Vertex d) (U₀ : Finset (Vertex d))
        (u : Vertex d → ℝ) (s : Vertex d → ℕ) (size : Vertex d → ℝ),
        (∀ x ∈ U₀, (∀ y, (openGraph ω).Adj x y → y ∈ U₀) → openLaplacian ω u x = 0) →
        (∀ z ∈ U₀, ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 n x₀ → w ∈ U₀) →
        (∀ x, 0 ≤ size x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          ClusterSobolevTwo ω (tripleCluster ω U₀ k y) size CS ∧
            ∑ x ∈ tripleCluster ω U₀ k y, size x ^ (2 * (d : ℝ) * (d + 2)) ≤
              CG * (3 : ℝ) ^ ((k + 1) * d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2) := by
  obtain ⟨ε, hε, t, ht, C, hC, hM⟩ := meyers_cluster (d := d) hd hCS hCG hK
  refine ⟨ε, hε, t, ht, C, hC, ?_⟩
  intro ω n x₀ U₀ u s size hu hU₀ hsize hcell hnb hΩ hcubes hmom
  refine hM ω n x₀ U₀ u s size hu hsize hcell hnb hΩ (fun k y hk hsub => ?_) hmom
  obtain ⟨hSob, hgood⟩ := hcubes k y hk hsub
  exact ⟨tripleCluster ω U₀ k y, tripleCluster_subset_enl ω U₀ k y, tripleCluster_subset ω U₀ k y,
    fun z hz w hadj hw => tripleCluster_closed ω hU₀ hsub hz hadj hw,
    fun x hx hxc => mem_tripleCluster_of_mem_cube ω hx hxc, hSob, hgood⟩

end Rigidity.Proofs.Cluster
