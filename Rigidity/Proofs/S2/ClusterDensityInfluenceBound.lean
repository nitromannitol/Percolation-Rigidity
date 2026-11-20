import Rigidity.Proofs.S2.ClusterDensityInfluence

/-!
# Bounds for a single-bond density influence

The change of the infinite-cluster count is controlled by the finite components at the
endpoints of the resampled bond, before and after resampling.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The vertices of a component when it is finite, and the empty set otherwise. -/
noncomputable def finiteComponentVertices (ω : Configuration d) (x : Vertex d) : Finset (Vertex d) := by
  classical
  exact if h : ((openGraph ω).connectedComponentMk x).supp.Finite then h.toFinset else ∅

/-- A vertex reachable from a finite component lies in its finite vertex set. -/
theorem mem_finiteComponentVertices_of_reachable {ω : Configuration d} {x y : Vertex d}
    (hxy : (openGraph ω).Reachable x y)
    (hf : ((openGraph ω).connectedComponentMk y).supp.Finite) :
    x ∈ finiteComponentVertices ω y := by
  classical
  simp only [finiteComponentVertices, dif_pos hf, Set.Finite.mem_toFinset]
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
    (SimpleGraph.ConnectedComponent.sound hxy)

/-- The finite-component vertex count agrees with the cardinality of its support. -/
theorem card_finiteComponentVertices (ω : Configuration d) (x : Vertex d) :
    (finiteComponentVertices ω x).card = ((openGraph ω).connectedComponentMk x).supp.ncard := by
  classical
  by_cases hf : ((openGraph ω).connectedComponentMk x).supp.Finite
  · simp [finiteComponentVertices, hf, Set.ncard_eq_toFinset_card]
  · simp [finiteComponentVertices, hf, (Set.not_finite.mp hf).ncard]

/-- A single resampling changes the density count by at most the sum of the finite component
sizes at the bond endpoints, in the original and resampled configurations. -/
theorem abs_infiniteClusterCount_resampleBond_le (m : ℕ) (k : Vertex d)
    (ω η : Configuration d) (e : Bond d) :
    |(infiniteClusterCount (triadicCube d m k) ω : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ)| ≤
      ∑ y ∈ e.val.toFinset,
        (((finiteComponentVertices ω y).card : ℝ) +
          ((finiteComponentVertices (resampleBond ω η e) y).card : ℝ)) := by
  classical
  rw [abs_infiniteClusterCount_resampleBond]
  let S := (infiniteClusterTrace m k ω \ infiniteClusterTrace m k (resampleBond ω η e)) ∪
    (infiniteClusterTrace m k (resampleBond ω η e) \ infiniteClusterTrace m k ω)
  let T := e.val.toFinset.biUnion fun y =>
    finiteComponentVertices ω y ∪ finiteComponentVertices (resampleBond ω η e) y
  have hsub : S ⊆ T := by
    intro x hx
    rcases changed_trace_vertex_reaches_finite_component m k ω η e hx with h | h
    · obtain ⟨y, hy, hxy, hfin⟩ := h
      exact Finset.mem_biUnion.mpr ⟨y, Sym2.mem_toFinset.mpr hy,
        Finset.mem_union_left _ (mem_finiteComponentVertices_of_reachable hxy hfin)⟩
    · obtain ⟨y, hy, hxy, hfin⟩ := h
      exact Finset.mem_biUnion.mpr ⟨y, Sym2.mem_toFinset.mpr hy,
        Finset.mem_union_right _ (mem_finiteComponentVertices_of_reachable hxy hfin)⟩
  have hcard : S.card ≤ ∑ y ∈ e.val.toFinset,
      ((finiteComponentVertices ω y).card +
        (finiteComponentVertices (resampleBond ω η e) y).card) := by
    calc
      _ ≤ T.card := Finset.card_le_card hsub
      _ ≤ ∑ y ∈ e.val.toFinset,
          (finiteComponentVertices ω y ∪ finiteComponentVertices (resampleBond ω η e) y).card :=
        Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun y _ => Finset.card_union_le _ _
  exact_mod_cast hcard

end Rigidity.Proofs.S2
