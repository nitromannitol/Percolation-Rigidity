import Rigidity.Proofs.Cluster.PlanarRestrictQuad

/-!
# The planar Meyers estimate for the harmonic functions of a resolved cube

The quantities `μ` and `ν` of Armstrong and Dario are optimized over the space `A_*(V)` of functions
on the cluster `𝒞(V)` harmonic at the vertices whose lattice neighbours lie in `V`
(`clusterHarmonic`). At such a vertex all open neighbours lie in `𝒞(V)`, so the open Laplacian of
the extension by zero is the Laplacian on the cluster (`openLaplacian_clusterExtend`). Hence the
planar Meyers estimate `planar_meyers` applies to the functions of `A_*(V)` on every cube `□` whose
triple `3□` has its lattice neighbours in `V` (`planar_meyers_clusterHarmonic`); this is the form in
which it is used in the proof of Lemma 5.5 (for `u(·, □_m, q)|_V - u(·, V, q)`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The open Laplacian of the extension of a function on the cluster, at a vertex whose open
neighbours lie in the cluster, is its Laplacian on the cluster. -/
theorem openLaplacian_clusterExtend {V : TriadicCube 2} (w : ClusterFun ω V)
    (x : ↥(clusterVertices ω V))
    (hall : ∀ y, (openGraph ω).Adj x.1 y → y ∈ clusterVertices ω V) :
    openLaplacian ω (clusterExtend ω V w) x.1 = clusterLaplacianAt ω V x w := by
  rw [clusterLaplacianAt_apply, openLaplacian]
  have h1 : (openGraph ω).neighborFinset x.1 =
      (clusterVertices ω V).filter ((openGraph ω).Adj x.1) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨hall y h, h⟩, fun h => h.2⟩
  rw [h1, Finset.sum_filter, ← Finset.sum_coe_sort (clusterVertices ω V)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [clusterExtend_apply_of_mem w y.2, clusterExtend_apply_of_mem w x.2]

/-- The extension of a function of `A_*(V)` is harmonic for the open edges at every vertex of the
cluster whose lattice neighbours lie in `V`. -/
theorem openLaplacian_clusterExtend_eq_zero (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) {w : ClusterFun ω V} (hw : w ∈ clusterHarmonic ω V) {x : Vertex 2}
    (hx : x ∈ clusterVertices ω V) (hint : V.IsInterior x) :
    openLaplacian ω (clusterExtend ω V w) x = 0 := by
  have hall : ∀ y, (openGraph ω).Adj x y → y ∈ clusterVertices ω V := fun y hadj =>
    mem_clusterVertices_of_adj_mem hP hV hx hadj (hint y fun i => by
      have h := Rigidity.Proofs.S3.abs_coord_sub_le_one_of_adj (openGraph_le ω hadj) i
      rwa [abs_sub_comm] at h)
  rw [openLaplacian_clusterExtend w ⟨x, hx⟩ hall]
  exact (mem_clusterHarmonic.1 hw) ⟨x, hx⟩ hint

/-- **The planar Meyers estimate for the functions of `A_*(V)`** (Armstrong–Dario,
Proposition 3.8, deterministic part, in dimension two). As `planar_meyers`, for a resolved
triadic cube `V`, a function `w ∈ A_*(V)` and a cube `□ = cube n x₀` whose triple has its lattice
neighbours in `V`; `E = |∇w 1_{𝐚≠0}|²` on `𝒞(V)`. -/
theorem planar_meyers_clusterHarmonic {CG K : ℝ} (hCG : 0 ≤ CG) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration 2) (_ : PlanarPartitionEvent ω) (V : TriadicCube 2)
        (_ : PlanarResolved ω V) (w : ClusterFun ω V) (_ : w ∈ clusterHarmonic ω V) (n : ℕ)
        (x₀ : Vertex 2) (s : Vertex 2 → ℕ),
        (∀ x ∈ enl 1 n x₀, V.IsInterior x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
            ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x =>
            clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀)
            (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ (1 + ε / 2) := by
  obtain ⟨ε, hε, t, ht, C, hC, hM⟩ := planar_meyers hCG hK
  refine ⟨ε, hε, t, ht, C, hC, ?_⟩
  intro ω hP V hV w hw n x₀ s hint hcell hnb hΩ hcubes hmom
  have hsub : (↑(enl 1 n x₀) : Set (Vertex 2)) ⊆ V.vertices := fun x hx =>
    hint x (Finset.mem_coe.1 hx) x fun i => by simp
  exact hM ω hP V n x₀ (clusterExtend ω V w) s hsub
    (fun x hx hxe _ => openLaplacian_clusterExtend_eq_zero hP hV hw hx (hint x hxe))
    hcell hnb hΩ hcubes hmom

end Rigidity.Proofs.Cluster
