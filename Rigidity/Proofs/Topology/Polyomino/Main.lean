import Rigidity.Proofs.Topology.Polyomino.Jordan

/-! # One boundary polygon

For a finite set `S` of cells such that the interior `Ω` of their union is connected, its
complement in `S²` is connected, and every boundary point is simple, the frontier of `Ω` is the
trace of one closed lattice polygon without repeated corner (`frontier_eq_polyTrace`): the
polygon through a boundary side of a cell of `S` with largest first coordinate contains every
boundary side, since a boundary side in another component of the boundary graph would give a
second polygon, and `Ω` would lie inside both (`subset_inside`, `outside_subset`).
-/

open Set Filter Topology Function Bornology LatticeProb

namespace Rigidity.Proofs.Topology.Polyomino

open Rigidity.Proofs.Section5.JordanLoop Rigidity.Section2

variable {S : Set (ℤ × ℤ)}

/-- The edges of a walk are the pairs of consecutive vertices. -/
theorem exists_edge_eq {V : Type*} {G : SimpleGraph V} {u w : V} {p : G.Walk u w} {a b : V}
    (h : s(a, b) ∈ p.edges) : ∃ i < p.length, s(a, b) = s(p.getVert i, p.getVert (i + 1)) := by
  rw [SimpleGraph.Walk.edges, List.mem_map] at h
  obtain ⟨d, hd, hde⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hd
  refine ⟨i, by rwa [SimpleGraph.Walk.length_darts] at hi, ?_⟩
  rw [← hde, SimpleGraph.Walk.darts_getElem_eq_getVert, SimpleGraph.Dart.edge_mk]

/-- The component of a corner with a neighbour in the boundary graph is a cycle: a closed
polygon of boundary sides without repeated corner, containing every boundary side at a corner of
the component. -/
theorem exists_polygon (hS : S.Finite) (hNC : NoChecker S) (v : Corner S) :
    ∃ (M : ℕ) (c : ℕ → ℤ × ℤ), 3 ≤ M ∧ c M = c 0 ∧
      (∀ i < M, BAdj S (c i) (c (i + 1))) ∧
      (∀ i j, i ≤ M → j ≤ M → c i = c j → i = j ∨ (i = 0 ∧ j = M) ∨ (i = M ∧ j = 0)) ∧
      (∀ a b : Corner S, (bGraph S).Reachable v a → BAdj S a.1 b.1 →
        ∃ i < M, s(a.1, b.1) = s(c i, c (i + 1))) ∧
      (∀ i, ∃ a : Corner S, a.1 = c i ∧ (bGraph S).Reachable v a) := by
  classical
  have : Finite (Corner S) := (corner_finite hS).to_subtype
  have : Fintype (Corner S) := Fintype.ofFinite _
  obtain ⟨w, hw⟩ := v.2
  have hn : ((bGraph S).neighborSet v).Nonempty :=
    ⟨⟨w, v.1, hw.symm⟩, (SimpleGraph.mem_neighborSet _ _ _).2 hw⟩
  have hcyc := bGraph_isCycles hNC
  obtain ⟨p, hp, hverts⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := (bGraph S).connectedComponentMk v)
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem hn
  have hreach : ∀ a, a ∈ p.support → (bGraph S).Reachable v a := by
    intro a ha
    have : a ∈ ((bGraph S).connectedComponentMk v).supp := by
      rw [← hverts]
      exact (SimpleGraph.Walk.mem_verts_toSubgraph p).2 ha
    exact (SimpleGraph.ConnectedComponent.exact
      ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 this)).symm
  refine ⟨p.length, fun i => (p.getVert i).1, hp.three_le_length, by simp,
    fun i hi => p.adj_getVert_succ hi, ?_, ?_,
    fun i => ⟨p.getVert i, rfl, hreach _ (p.getVert_mem_support i)⟩⟩
  · intro i j hi hj h
    have h' : p.getVert i = p.getVert j := Subtype.ext h
    by_cases hi0 : i = 0
    · subst hi0
      rw [SimpleGraph.Walk.getVert_zero] at h'
      have := (hp.getVert_endpoint_iff hj).1 h'.symm
      omega
    by_cases hj0 : j = 0
    · subst hj0
      rw [SimpleGraph.Walk.getVert_zero] at h'
      have := (hp.getVert_endpoint_iff hi).1 h'
      omega
    left
    exact hp.getVert_injOn ⟨by omega, hi⟩ ⟨by omega, hj⟩ h'
  · intro a b ha hab
    have hav : a ∈ p.toSubgraph.verts := by
      rw [hverts]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        (SimpleGraph.ConnectedComponent.sound ha.symm)
    have hadj : p.toSubgraph.Adj a b := (hp.adj_toSubgraph_iff_of_isCycles hcyc hav b).2 hab
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] at hadj
    obtain ⟨i, hi, he⟩ := exists_edge_eq hadj
    refine ⟨i, hi, ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]

theorem segment_eq_of_sym2 {a b x y : ℤ × ℤ} (h : s(a, b) = s(x, y)) :
    segment ℝ (mpt a) (mpt b) = segment ℝ (mpt x) (mpt y) := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _

/-- The data of the boundary polygon through a corner. -/
theorem exists_loop_data (hS : S.Finite) (hNC : NoChecker S) {σ : E2 → S2}
    (hσ : IsOpenEmbedding σ) (hσr : range σ = {northPole}ᶜ)
    (hconn : IsPreconnected (interior (cellUnion S)))
    (hcompl : IsPreconnected (σ '' interior (cellUnion S))ᶜ) (v : Corner S) :
    ∃ (M : ℕ) (c : ℕ → ℤ × ℤ), 3 ≤ M ∧ c M = c 0 ∧
      (∀ i < M, (lattice 2).Adj (toV (c i)) (toV (c (i + 1)))) ∧
      (∀ i j, i ≤ M → j ≤ M → c i = c j → i = j ∨ (i = 0 ∧ j = M) ∨ (i = M ∧ j = 0)) ∧
      (∀ a b : Corner S, (bGraph S).Reachable v a → BAdj S a.1 b.1 →
        ∃ i < M, s(a.1, b.1) = s(c i, c (i + 1))) ∧
      (∀ i, ∃ a : Corner S, a.1 = c i ∧ (bGraph S).Reachable v a) ∧
      polyTrace c M ⊆ bdry S ∧ Nonempty (polyTrace c M ≃ₜ Circle) ∧
      ∃ I O : Set E2, IsOpen I ∧ IsOpen O ∧ IsConnected O ∧ IsBounded I ∧ ¬ IsBounded O ∧
        Disjoint I O ∧ (polyTrace c M)ᶜ = I ∪ O ∧ frontier I = polyTrace c M ∧
        frontier O = polyTrace c M ∧ interior (cellUnion S) ⊆ I := by
  obtain ⟨M, c, hM, hcM, hb, hinj, hedge, hvert⟩ := exists_polygon hS hNC v
  have hadj : ∀ i < M, (lattice 2).Adj (toV (c i)) (toV (c (i + 1))) :=
    fun i hi => (hb i hi).lattice_adj
  have hJ : polyTrace c M ⊆ bdry S := iUnion₂_subset fun i hi => (hb i hi).segment_subset
  obtain ⟨he, I, O, hIo, hOo, hOc, hIb, hIne, hOb, hIO, hcov, hfI, hfO, hIc⟩ :=
    jordan_of_polygon hM hcM hadj hinj
  exact ⟨M, c, hM, hcM, hadj, hinj, hedge, hvert, hJ, he, I, O, hIo, hOo, hOc, hIb, hOb, hIO,
    hcov, hfI, hfO, subset_inside hS hNC hσ hσr hconn hcompl hJ hIo hOo hIb hIne hIO hcov hIc⟩

/-- **The frontier is one Jordan polygon.** For a finite set of cells such that the interior of
their union is connected, its complement in `S²` is connected, and every boundary point is simple,
the frontier of the interior is homeomorphic to the circle and is the trace of a closed lattice
polygon without repeated corner. -/
theorem frontier_eq_polyTrace (hS : S.Finite) {σ : E2 → S2} (hσ : IsOpenEmbedding σ)
    (hσr : range σ = {northPole}ᶜ) (hconn : IsConnected (interior (cellUnion S)))
    (hcompl : IsConnected (σ '' interior (cellUnion S))ᶜ)
    (hsimple : ∀ x ∈ frontier (interior (cellUnion S)),
      IsSimpleBoundaryPoint (interior (cellUnion S)) x) :
    Nonempty (frontier (interior (cellUnion S)) ≃ₜ Circle) ∧
    ∃ (M : ℕ) (c : ℕ → ℤ × ℤ), 3 ≤ M ∧ c M = c 0 ∧
      (∀ i < M, (lattice 2).Adj (toV (c i)) (toV (c (i + 1)))) ∧
      (∀ i j, i < M → j < M → c i = c j → i = j) ∧
      frontier (interior (cellUnion S)) = polyTrace c M := by
  have hNC := noChecker_of_simple hS hsimple
  obtain ⟨y, hy⟩ := hconn.nonempty
  obtain ⟨c₁, hc₁, -⟩ := mem_iUnion₂.1 (interior_subset hy)
  obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image S (fun c => c.1) hS ⟨c₁, hc₁⟩
  have hE : c₀ + Dir.E.v ∉ S := fun h => by
    have := hmax _ h
    simp [Dir.v] at this
  let v₀ : Corner S := ⟨sideStart c₀ .E, sideEnd c₀ .E, c₀, hc₀, .E, hE, rfl⟩
  obtain ⟨M, c, hM, hcM, hadj, hinj, hedge, hvert, hJ, he, I, O, hIo, hOo, hOc, hIb, hOb, hIO,
    hcov, hfI, hfO, hΩI⟩ :=
    exists_loop_data hS hNC hσ hσr hconn.isPreconnected hcompl.isPreconnected v₀
  have hcl : bdry S ⊆ closure (interior (cellUnion S)) := by
    rw [← frontier_interior_cellUnion hS]
    exact frontier_subset_closure
  have hsub : bdry S ⊆ polyTrace c M := by
    intro p hp
    obtain ⟨a, b, hab, hpab⟩ := exists_badj_of_mem_bdry hp
    let a' : Corner S := ⟨a, b, hab⟩
    by_cases hr : (bGraph S).Reachable v₀ a'
    · obtain ⟨i, hi, hs⟩ := hedge a' ⟨b, a, hab.symm⟩ hr hab
      rw [segment_eq_of_sym2 hs] at hpab
      exact mem_iUnion₂.2 ⟨i, hi, hpab⟩
    exfalso
    obtain ⟨M', c', hM', hcM', hadj', hinj', hedge', hvert', hJ', he', I', O', hIo', hOo', hOc',
      hIb', hOb', hIO', hcov', hfI', hfO', hΩI'⟩ :=
      exists_loop_data hS hNC hσ hσr hconn.isPreconnected hcompl.isPreconnected a'
    have hdisj : Disjoint (polyTrace c M) (polyTrace c' M') := by
      refine disjoint_polyTrace hadj hadj' fun i j hij => hr ?_
      obtain ⟨x, hx, hxr⟩ := hvert i
      obtain ⟨x', hx', hxr'⟩ := hvert' j
      have : x = x' := Subtype.ext (hx.trans (hij.trans hx'.symm))
      exact hxr.trans (this ▸ hxr'.symm)
    have h1 := outside_subset (hJ'.trans hcl) hdisj hΩI hfI hIO hOc.isPreconnected hOb hIo'
      hOo' hIO' hcov' hIb'
    have h2 := outside_subset (hJ.trans hcl) hdisj.symm hΩI' hfI' hIO' hOc'.isPreconnected hOb'
      hIo hOo hIO hcov hIb
    have hOO : O = O' := Subset.antisymm h1 h2
    have hJJ : polyTrace c M = polyTrace c' M' := by rw [← hfO, ← hfO', hOO]
    obtain ⟨q, hq⟩ : (polyTrace c M).Nonempty :=
      ⟨mpt (c 0), mem_iUnion₂.2 ⟨0, by omega, left_mem_segment ℝ _ _⟩⟩
    exact Set.disjoint_left.1 hdisj hq (hJJ ▸ hq)
  have hfr : frontier (interior (cellUnion S)) = polyTrace c M := by
    rw [frontier_interior_cellUnion hS]
    exact Subset.antisymm hsub hJ
  refine ⟨⟨(Homeomorph.setCongr hfr).trans he.some⟩, M, c, hM, hcM, hadj, fun i j hi hj h => ?_,
    hfr⟩
  rcases hinj i j hi.le hj.le h with h | h | h <;> omega

end Rigidity.Proofs.Topology.Polyomino
