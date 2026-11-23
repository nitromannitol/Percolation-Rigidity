import Rigidity.Proofs.Regularity.PlanarClusterInclusions
import Rigidity.Proofs.Percolation.PlanarOmegaCaccioppoli
import Rigidity.Proofs.S3.Divergence

/-!
# Harmonic functions on the infinite cluster restricted to the clusters of squares

The estimates of the proof of Armstrong–Dario, Lemma 7.1 (arXiv:1609.09431v2), are applied to a
function `u` harmonic on `𝒞_∞ ∩ B_R` through its restriction to the cluster `C_*(V)` of a
resolved triadic cube `V` contained in the ball. The planar Caccioppoli and Meyers estimates of the
repository are stated for the space `A_*(V) = clusterHarmonic ω V` of functions on `C_*(V)`
harmonic at the vertices whose lattice neighbours lie in `V`. When `C_*(V) ⊆ 𝒞_∞` and `u` is
harmonic at these vertices, the restriction `clusterRestrictTo C u V` lies in `A_*(V)`
(`clusterRestrictTo_mem_clusterHarmonic`): at such a vertex every open neighbour lies in `C_*(V)`,
so that the Laplacian on `C_*(V)` is the Laplacian on `𝒞_∞`. With it, the planar Caccioppoli
inequality from `□_{n+1}` to `□_n` holds for `u` (`clusterForm_clusterRestrictTo_le`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

variable {ω : Configuration 2}

/-- The restriction of a function on an open component to the cluster `C_*(V)` of a triadic cube
(the function extended by `0` off the component). -/
noncomputable def clusterRestrictTo (C : OpenComponent ω) (u : C → ℝ) (V : TriadicCube 2) :
    ClusterFun ω V :=
  fun x => Rigidity.Section3.extend C u x.1

/-- **The restriction of a harmonic function to the cluster of a resolved cube is in `A_*(V)`.** -/
theorem clusterRestrictTo_mem_clusterHarmonic (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (C : OpenComponent ω) {u : C → ℝ}
    (hsub : ∀ x ∈ clusterVertices ω V, x ∈ C.supp)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ clusterVertices ω V → V.IsInterior x →
      componentLaplacian C u ⟨x, hx⟩ = 0) :
    clusterRestrictTo C u V ∈ clusterHarmonic ω V := by
  rw [mem_clusterHarmonic]
  intro x hint
  have hxC := hsub x.1 x.2
  have h0 := hharm x.1 hxC x.2 hint
  rw [Rigidity.Proofs.S3.componentLaplacian_eq_sum_lattice C u x.1 hxC, ← Finset.sum_filter] at h0
  rw [clusterLaplacianAt_apply]
  have e1 : ∑ y : ↥(clusterVertices ω V), (if (openGraph ω).Adj x.1 y.1 then
      clusterRestrictTo C u V y - clusterRestrictTo C u V x else 0) =
      ∑ y ∈ clusterVertices ω V, (if (openGraph ω).Adj x.1 y then
        Rigidity.Section3.extend C u y - Rigidity.Section3.extend C u x.1 else 0) := by
    rw [← Finset.sum_coe_sort (clusterVertices ω V)]
    rfl
  rw [e1, ← Finset.sum_filter]
  have hset : (clusterVertices ω V).filter (fun y => (openGraph ω).Adj x.1 y) =
      ((lattice 2).neighborFinset x.1).filter (fun y => (openGraph ω).Adj x.1 y) := by
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨-, hy⟩
      exact ⟨openGraph_le ω hy, hy⟩
    · rintro ⟨-, hy⟩
      exact ⟨mem_clusterVertices_of_adj hP hV x.2 hint hy, hy⟩
  rw [hset]
  exact h0

theorem clusterExtend_clusterRestrictTo (C : OpenComponent ω) (u : C → ℝ) {V : TriadicCube 2}
    {x : Vertex 2} (hx : x ∈ clusterVertices ω V) :
    clusterExtend ω V (clusterRestrictTo C u V) x = Rigidity.Section3.extend C u x := by
  rw [clusterExtend_apply_of_mem _ hx]
  rfl

/-- **The Caccioppoli inequality from `□_{n+1}` to `□_n` for a function harmonic on the infinite
cluster** (Armstrong and Dario, Lemma 3.5, in dimension two): the Dirichlet form of `u` on
`C_*(□_n)` is at most `16 (3^n - 1)⁻² ∑_{C_*(□_{n+1})} (u - c)²`. -/
theorem clusterForm_clusterRestrictTo_le (hP : PlanarPartitionEvent ω) {n : ℕ} (hn : 1 ≤ n)
    (hU : PlanarResolved ω ⟨n + 1, 0⟩) (C : OpenComponent ω) {u : C → ℝ}
    (hsub : ∀ x ∈ clusterVertices ω ⟨n + 1, 0⟩, x ∈ C.supp)
    (hharm : ∀ (x : Vertex 2) (hx : x ∈ C.supp), x ∈ clusterVertices ω ⟨n + 1, 0⟩ →
      (⟨n + 1, 0⟩ : TriadicCube 2).IsInterior x → componentLaplacian C u ⟨x, hx⟩ = 0)
    (c : ℝ) :
    clusterForm ω ⟨n, 0⟩ (clusterRestrictExt ⟨n, 0⟩ (clusterRestrictTo C u ⟨n + 1, 0⟩))
        (clusterRestrictExt ⟨n, 0⟩ (clusterRestrictTo C u ⟨n + 1, 0⟩)) ≤
      16 / ((3 : ℝ) ^ n - 1) ^ 2 * ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
        (Rigidity.Section3.extend C u x - c) ^ 2 := by
  have h := clusterForm_restrict_le_caccioppoli hP hn hU
    (clusterRestrictTo_mem_clusterHarmonic hP hU C hsub hharm) c
  have e : ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩,
      (clusterExtend ω ⟨n + 1, 0⟩ (clusterRestrictTo C u ⟨n + 1, 0⟩) x - c) ^ 2 =
      ∑ x ∈ clusterVertices ω ⟨n + 1, 0⟩, (Rigidity.Section3.extend C u x - c) ^ 2 :=
    Finset.sum_congr rfl fun x hx => by rw [clusterExtend_clusterRestrictTo C u hx]
  rw [e] at h
  exact h

end Rigidity.Proofs.Regularity
