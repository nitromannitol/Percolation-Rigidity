import Rigidity.Steps.S3.CompareDifferentPlanes

/-!
# Lemma 3.3: the infinite cluster after closing a non-disconnecting finite set of bonds

Step `step:3.3-flip-cluster` of Lemma 3.3 (paper L895 of the corrected draft). Let `C_∞` be the
unique infinite cluster of `ω` and `B` a finite set of bonds such that any two vertices of `C_∞`
are still connected by an open path after the bonds of `B` are closed. Closing bonds only removes
open edges, so every cluster of the new configuration lies inside a cluster of `ω`. The cluster of
the new configuration containing a vertex of `C_∞` therefore has exactly the vertices of `C_∞`,
and any infinite cluster of the new configuration lies inside an infinite cluster of `ω`, hence
inside `C_∞`, hence coincides with it.
-/

namespace Rigidity.Proofs.S3

open LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

namespace FlipCluster

/-- Closing bonds can only remove open edges. -/
theorem openGraph_closeBonds_le (B : Finset (Bond d)) (ω : Configuration d) :
    openGraph (closeBonds B ω) ≤ openGraph ω := by
  rintro x y ⟨h, ho⟩
  refine ⟨h, ?_⟩
  unfold closeBonds at ho
  split_ifs at ho
  exact ho

/-- A cluster of a configuration with fewer open bonds lies inside the cluster of `ω` of any of
its vertices. -/
theorem supp_subset_of_closeBonds (B : Finset (Bond d)) (ω : Configuration d)
    (D : OpenComponent (closeBonds B ω)) {v : Vertex d} (hv : v ∈ D.supp) :
    D.supp ⊆ ((openGraph ω).connectedComponentMk v).supp := by
  intro u hu
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hu hv ⊢
  exact SimpleGraph.ConnectedComponent.sound
    (SimpleGraph.Reachable.mono (openGraph_closeBonds_le B ω)
      (SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)))

end FlipCluster

/-- Step `step:3.3-flip-cluster` (paper L895): closing the bonds of a finite set `B` whose removal
does not disconnect the unique infinite cluster leaves a unique infinite cluster, with the same
vertices. -/
theorem flipClusterStep : FlipClusterStep d := by
  intro ω h B hreach
  have hCinf : (uniqueInfiniteComponent h).supp.Infinite := uniqueInfiniteComponent_infinite h
  obtain ⟨x₀, hx₀⟩ := hCinf.nonempty
  let C' : OpenComponent (closeBonds B ω) := (openGraph (closeBonds B ω)).connectedComponentMk x₀
  have hsupp : C'.supp = (uniqueInfiniteComponent h).supp := by
    ext y
    constructor
    · intro hy
      have hsub := FlipCluster.supp_subset_of_closeBonds B ω C'
        (SimpleGraph.ConnectedComponent.connectedComponentMk_mem (v := x₀)) hy
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hsub hx₀ ⊢
      exact hsub.trans hx₀
    · intro hy
      exact SimpleGraph.ConnectedComponent.sound (hreach y hy x₀ hx₀)
  have hC'inf : C'.supp.Infinite := hsupp ▸ hCinf
  have huniq : HasUniqueInfiniteOpenComponent (closeBonds B ω) := by
    refine ⟨C', hC'inf, fun D hD => ?_⟩
    obtain ⟨v, hv⟩ := hD.nonempty
    have hinf := Set.Infinite.mono (FlipCluster.supp_subset_of_closeBonds B ω D hv) hD
    have hvC : v ∈ C'.supp := by
      rw [hsupp, SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (eq_uniqueInfiniteComponent_iff h _).mpr hinf
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv hvC
    exact hv.symm.trans hvC
  refine ⟨huniq, ?_⟩
  rw [((eq_uniqueInfiniteComponent_iff huniq C').mpr hC'inf).symm, hsupp]

end Rigidity.Proofs.S3
