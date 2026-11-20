import Rigidity.Proofs.Section5.RenormalizedPathLift
import Rigidity.Proofs.Section5.SiteRectangleCrossings

/-!
# Lifting disjoint renormalized crossings

Open site crossings yield open lattice paths supported in their enlarged blocks.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5 Percolation.Literature

namespace Rigidity.Proofs.Section5.Kesten

/-- The two-coordinate lattice representation maps open-site edges to planar site edges. -/
def planarOpenSiteHom (η : PlanarCarrier → Bool) : planarOpenSiteGraph η →g siteOpenGraph η where
  toFun x := (x 0, x 1)
  map_rel' {x y} h := by
    refine ⟨?_, h.2⟩
    change |x 0 - y 0| + |x 1 - y 1| = 1
    have hs := stepKind_of_adj h.1
    rcases hs with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩ <;>
      rcases abs_cases (x 0 - y 0) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases (x 1 - y 1) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

/-- A horizontal site crossing in a positive-width rectangle lifts to a self-avoiding open
lattice path whose length is bounded by its number of sites times the block volume. -/
theorem horizontal_crossing_lifts {ω : Configuration 2} {R m n : ℕ} (hR : 3210 ≤ R)
    (hm : 0 < m) {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (renormField R ω)) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) l) :
    ∃ x ∈ cubeAt (renormCentre R (l.head hl.ne_nil 0, l.head hl.ne_nil 1)) (11 * R / 10),
      ∃ y ∈ cubeAt (renormCentre R (l.getLast hl.ne_nil 0, l.getLast hl.ne_nil 1)) (11 * R / 10),
        ∃ P : (openGraph ω).Walk x y, P.IsPath ∧
          (∀ z ∈ P.support, z ∈ renormPathRegion R (l.map fun z => (z 0, z 1))) ∧
          P.length < l.length * (2 * (11 * R / 10) + 1) ^ 2 := by
  have hchain : l.IsChain (planarOpenSiteGraph (renormField R ω)).Adj :=
    hl.1.imp fun _ _ he => (Menger.mem_edgesIn.1 he).1
  have hopen : renormField R ω (l.head hl.ne_nil 0, l.head hl.ne_nil 1) = true := by
    cases l with
    | nil => exact (hl.ne_nil rfl).elim
    | cons a t =>
      cases t with
      | nil =>
        obtain ⟨x, hx, hxL⟩ := hl.2.1
        obtain ⟨y, hy, hyR⟩ := hl.2.2
        simp only [List.head?_cons, List.getLast?_singleton, Option.mem_def,
          Option.some.injEq] at hx hy
        subst x y
        have h0 := (Finset.mem_filter.1 hxL).2
        have h1 := (Finset.mem_filter.1 hyR).2
        omega
      | cons b t =>
        exact (List.isChain_cons_cons.1 hchain).1.2.1
  let P := SimpleGraph.Walk.ofSupport l hl.ne_nil hchain
  let Q := P.map (planarOpenSiteHom (renormField R ω))
  obtain ⟨x, hx, y, hy, W, hWpath, hWsupport, hWlen⟩ := renorm_walk_lifts_short_path hR Q hopen
  refine ⟨x, hx, y, hy, W, hWpath, ?_, ?_⟩
  · have hQsupport : Q.support = l.map (fun z => (z 0, z 1)) := by
      change (P.map (planarOpenSiteHom (renormField R ω))).support = _
      rw [SimpleGraph.Walk.support_map]
      change List.map _ (SimpleGraph.Walk.ofSupport l hl.ne_nil hchain).support = _
      rw [SimpleGraph.Walk.support_ofSupport]
      rfl
    rw [← hQsupport]
    exact hWsupport
  · simpa only [Q, SimpleGraph.Walk.length_map, P, SimpleGraph.Walk.length_ofSupport,
      Nat.sub_add_cancel (List.length_pos_iff_ne_nil.2 hl.ne_nil)] using hWlen

/-- At most nine regions of pairwise disjoint lattice-represented site paths can contain the
same lattice vertex. -/
theorem card_disjoint_crossing_regions_meeting_le_nine {R : ℕ} {x : Vertex 2}
    (L : Finset (List (LatticeModels.Site 2)))
    (hdisj : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → ∀ z ∈ l, z ∉ l')
    (hx : ∀ l ∈ L, x ∈ renormPathRegion R (l.map fun z => (z 0, z 1))) : L.card ≤ 9 := by
  classical
  let f : LatticeModels.Site 2 → PlanarCarrier := fun z => (z 0, z 1)
  have hf : Function.Injective f := by
    intro a b hab
    exact LatticeModels.Site.eq_iff_two.2 ⟨congrArg Prod.fst hab, congrArg Prod.snd hab⟩
  have hmap : Function.Injective (List.map f) := List.map_injective_iff.2 hf
  have hd : ∀ l ∈ L.image (List.map f), ∀ l' ∈ L.image (List.map f),
      l ≠ l' → ∀ z ∈ l, z ∉ l' := by
    intro l hl l' hl' hne z hz hz'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hl'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hz
    obtain ⟨v, hv, huv⟩ := List.mem_map.1 hz'
    have huv' : v = u := hf huv
    subst v
    exact hdisj a ha b hb (fun h => hne (congrArg (List.map f) h)) u hu hv
  have hb := card_disjoint_path_regions_meeting_le_nine (L.image (List.map f)) hd (by
    intro l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hl
    exact hx a ha)
  rwa [Finset.card_image_of_injective _ hmap] at hb

end Rigidity.Proofs.Section5.Kesten
