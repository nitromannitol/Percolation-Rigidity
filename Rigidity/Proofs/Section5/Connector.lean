import Rigidity.Steps.Section5.InfiniteDisjointPaths

/-!
# Proposition 5.12: connectors and last exits

This file proves `ConnectorStep` (Proposition 5.12, corrected draft L2101-2111 with correction
[C22]: the connectors join all the initial points). No literature input is used.

Let `S` be a connected set of `𝒞_∞` containing `n` disjoint infinite paths `γₖ`.

* `exists_finite_connected_superset`: the initial points `γₖ(0)` lie in a finite connected set
  `T ⊆ S`, the union of paths of `S` joining them (`SimpleGraph.extend_finset_to_connected`);
* `γₖ` is injective and `T` is finite, so `γₖ` has a last visit `mₖ` to `T`, and the ray
  `ρₖ(m) = γₖ(mₖ + m)` starts in `T` and never returns to it. The rays are disjoint since
  `ρₖ` is a tail of `γₖ`.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

variable {ω : Configuration 2}

/-- A connected set of `𝒞_∞` induces a preconnected subgraph. -/
theorem preconnected_induce_of_isConnectedSet {C : OpenComponent ω} {S : Set C}
    (hS : IsConnectedSet C S) : ((componentGraph C).induce S).Preconnected := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨_, _, h⟩ := hS x hx y hy
  exact h

/-- A finite subset of a connected set `S` of `𝒞_∞` lies in a finite connected subset of `S`. -/
theorem exists_finite_connected_superset {C : OpenComponent ω} {S : Set C}
    (hS : IsConnectedSet C S) (F : Finset C) (hF : (F : Set C) ⊆ S) :
    ∃ T : Set C, T.Finite ∧ (F : Set C) ⊆ T ∧ T ⊆ S ∧ IsConnectedSet C T := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨∅, Set.finite_empty, by simp, Set.empty_subset _, fun _ h => h.elim⟩
  obtain ⟨t', ht, hconn⟩ := SimpleGraph.extend_finset_to_connected
    (preconnected_induce_of_isConnectedSet hS) (t := F.subtype (· ∈ S))
    ⟨⟨x, hF hx⟩, Finset.mem_subtype.2 hx⟩
  refine ⟨Subtype.val '' (t' : Set S), t'.finite_toSet.image _, fun y hy => ?_, ?_, ?_⟩
  · exact ⟨⟨y, hF hy⟩, ht (Finset.mem_subtype.2 hy), rfl⟩
  · rintro _ ⟨v, _, rfl⟩
    exact v.2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨w⟩ := hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    let φ : ((componentGraph C).induce S).induce (t' : Set S) →g
        (componentGraph C).induce (Subtype.val '' (t' : Set S)) :=
      { toFun := fun v => ⟨v.1.1, v.1, v.2, rfl⟩, map_rel' := fun h => h }
    exact ⟨_, _, ⟨w.map φ⟩⟩

/-- `ConnectorStep` (L2101-2111, [C22]): a connected `S` containing `n` disjoint infinite
paths contains a finite connected `T` and `n` disjoint infinite paths which start in `T` and never
return to it. -/
theorem connectorStep : ConnectorStep := by
  classical
  intro ω C S hS n ⟨γ, hγ, hdisj⟩
  obtain ⟨T, hTfin, hFT, hTS, hTconn⟩ := exists_finite_connected_superset hS
    (Finset.univ.image fun k => γ k 0) (by
      intro x hx
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      exact (hγ k).2.2 0)
  have hstart : ∀ k, γ k 0 ∈ T := fun k => hFT (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩)
  -- the last visit of `γₖ` to `T`
  have hlast : ∀ k, ∃ M, γ k M ∈ T ∧ ∀ m, γ k m ∈ T → m ≤ M := by
    intro k
    have hbdd : BddAbove {m | γ k m ∈ T} := (hTfin.preimage (hγ k).1.injOn).bddAbove
    exact ⟨sSup {m | γ k m ∈ T}, Nat.sSup_mem ⟨0, hstart k⟩ hbdd, fun m hm => le_csSup hbdd hm⟩
  choose M hMmem hMmax using hlast
  refine ⟨T, hTfin, hTS, hTconn, fun k m => γ k (M k + m), fun k => ⟨?_, fun m => ?_, fun m => ?_⟩,
    hMmem, fun k m hm => ?_, fun k l hkl => ?_⟩
  · exact (hγ k).1.comp (add_right_injective _)
  · exact (hγ k).2.1 (M k + m)
  · exact (hγ k).2.2 _
  · have := hMmax k _ hm
    omega
  · refine Disjoint.mono ?_ ?_ (hdisj k l hkl) <;> exact Set.range_subset_iff.2 fun m => ⟨_, rfl⟩

end Rigidity.Proofs.Section5
