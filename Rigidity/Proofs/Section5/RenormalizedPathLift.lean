import Rigidity.Proofs.Section5.KestenLocalLink

/-!
# Lifting renormalized site walks

A walk of open renormalized sites carries an open lattice walk inside its enlarged blocks.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5.Kesten

/-- The union of the enlarged blocks visited by a renormalized site list. -/
def renormPathRegion (R : ℕ) (l : List PlanarCarrier) : Set (Vertex 2) :=
  ⋃ z ∈ l, cubeAt (renormCentre R z) (11 * R / 10)

/-- A channel start lies in its cube. -/
theorem AnyChannel.mem_cube {ω : Configuration 2} {X : Finset (Vertex 2)}
    {c y : Vertex 2} {r j : ℕ} (h : AnyChannel ω X c r j y) : y ∈ cubeAt c r := by
  rcases h with h | h
  · obtain ⟨_, W, hW, _, _⟩ := h
    exact (hW y W.start_mem_support).1.1
  · obtain ⟨_, W, hW, _, _⟩ := h
    exact (hW y W.start_mem_support).1.1

/-- An open renormalized site has a channel in its enlarged block. -/
theorem exists_channel_of_renorm_open {ω : Configuration 2} {R : ℕ} {z : PlanarCarrier}
    (hR : 3210 ≤ R) (hz : renormField R ω z = true) :
    ∃ j < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10), ∃ y,
      AnyChannel ω ∅ (renormCentre R z) (11 * R / 10) j y := by
  set r := 11 * R / 10
  have hp := params (Cf := 0) (R := R) (by omega)
  have hr : r = R + R / 10 := hp.1
  have hw : 1 ≤ chanWidth r := hp.2.1
  have hm : 2 * chanWidth r ≤ R / 10 := hp.2.2.1
  have hN : 0 < (2 * r + 1) / chanWidth r := Nat.div_pos (by omega) (by omega)
  let J := Finset.range ((2 * r + 1) / chanWidth r)
  have hJ : ∀ j ∈ J, j < (2 * r + 1) / chanWidth r := fun j hj => Finset.mem_range.1 hj
  have hcard : (∅ : Finset (Vertex 2)).card < J.card := by simpa [J] using hN
  have hgood : IsVeryGood ω (renormCentre R z) r := by
    simpa only [renormField, decide_eq_true_eq] using hz
  obtain ⟨j, hj, y, hy⟩ := exists_unhit_channel hgood.2.1 ∅ J hJ hw hcard
  exact ⟨j, hJ j hj, y, Or.inl hy⟩

/-- Any given channel at the start of an open renormalized walk connects inside the visited
blocks to a channel at its endpoint. -/
theorem renorm_walk_lifts_channel {ω : Configuration 2} {R : ℕ} (hR : 3210 ≤ R)
    {u v : PlanarCarrier} (w : (siteOpenGraph (renormField R ω)).Walk u v) :
    ∀ j < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10), ∀ y,
      AnyChannel ω ∅ (renormCentre R u) (11 * R / 10) j y →
      ∃ j' < (2 * (11 * R / 10) + 1) / chanWidth (11 * R / 10), ∃ y',
        AnyChannel ω ∅ (renormCentre R v) (11 * R / 10) j' y' ∧
        ReachIn ω (renormPathRegion R w.support) y y' := by
  induction w with
  | nil =>
    intro j hj y hy
    refine ⟨j, hj, y, hy, SimpleGraph.Walk.nil, ?_⟩
    intro x hx
    have hxy : x = y := by simpa using hx
    subst x
    simp only [renormPathRegion, SimpleGraph.Walk.support_nil, List.mem_singleton,
      Set.iUnion_iUnion_eq_left]
    exact hy.mem_cube
  | @cons u u' v hadj w ih =>
    intro j hj y hy
    obtain ⟨j₁, hj₁, y₁, hy₁, j₂, hj₂, y₂, hy₂, hlink⟩ :=
      renorm_neighbours_linked_in_union hR hadj
    have hgood : IsVeryGood ω (renormCentre R u) (11 * R / 10) := by
      simpa only [renormField, decide_eq_true_eq] using hadj.2.1
    have hfirst := channels_reachable_in_cube hR hgood hj hj₁ hy hy₁
    obtain ⟨j', hj', y', hy', hlast⟩ := ih j₂ hj₂ y₂ hy₂
    have hu : cubeAt (renormCentre R u) (11 * R / 10) ⊆
        renormPathRegion R (SimpleGraph.Walk.cons hadj w).support := by
      intro x hx
      simp only [renormPathRegion, Set.mem_iUnion, SimpleGraph.Walk.support_cons]
      exact ⟨u, List.mem_cons_self, hx⟩
    have hu' : cubeAt (renormCentre R u') (11 * R / 10) ⊆
        renormPathRegion R (SimpleGraph.Walk.cons hadj w).support := by
      intro x hx
      simp only [renormPathRegion, Set.mem_iUnion, SimpleGraph.Walk.support_cons]
      exact ⟨u', List.mem_cons_of_mem _ w.start_mem_support, hx⟩
    have hw : renormPathRegion R w.support ⊆
        renormPathRegion R (SimpleGraph.Walk.cons hadj w).support := by
      intro x hx
      simp only [renormPathRegion, Set.mem_iUnion, SimpleGraph.Walk.support_cons] at hx ⊢
      obtain ⟨z, hz, hxz⟩ := hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hxz⟩
    exact ⟨j', hj', y', hy', (hfirst.mono hu).trans
      ((hlink.mono (Set.union_subset hu hu')).trans (hlast.mono hw))⟩

/-- An open renormalized walk lifts to an open lattice walk through its enlarged blocks. -/
theorem renorm_walk_lifts {ω : Configuration 2} {R : ℕ} (hR : 3210 ≤ R)
    {u v : PlanarCarrier} (w : (siteOpenGraph (renormField R ω)).Walk u v)
    (hu : renormField R ω u = true) :
    ∃ x ∈ cubeAt (renormCentre R u) (11 * R / 10),
      ∃ y ∈ cubeAt (renormCentre R v) (11 * R / 10),
        ReachIn ω (renormPathRegion R w.support) x y := by
  obtain ⟨j, hj, x, hx⟩ := exists_channel_of_renorm_open hR hu
  obtain ⟨j', hj', y, hy, hxy⟩ := renorm_walk_lifts_channel hR w j hj x hx
  exact ⟨x, hx.mem_cube, y, hy.mem_cube, hxy⟩

end Rigidity.Proofs.Section5.Kesten
