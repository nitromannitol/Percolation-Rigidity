import Rigidity.Proofs.Section5.RenormalizedCrossingLift
import Rigidity.Proofs.Section5.PlanarFieldTranslation

/-!
# Isometries of open planar site graphs

Translations and coordinate swaps identify the site graphs of transformed fields with
subgraphs of the original field.
-/

open LatticeProb.Percolation Rigidity.Steps.Section5 Rigidity.Section5 Percolation.Literature

namespace Rigidity.Proofs.Section5.Kesten

/-- Translating the coordinates of a translated field gives a site graph homomorphism. -/
def translateOpenSiteHom (a : PlanarCarrier) (η : PlanarCarrier → Bool) :
    siteOpenGraph (translatePlanarField a η) →g siteOpenGraph η where
  toFun z := a + z
  map_rel' {z w} h := by
    refine ⟨?_, h.2⟩
    simpa only [Prod.fst_add, Prod.snd_add, add_sub_add_left_eq_sub] using h.1

/-- Exchanging the coordinates of a swapped field gives a site graph homomorphism. -/
def swapOpenSiteHom (η : PlanarCarrier → Bool) :
    siteOpenGraph (swapPlanarField η) →g siteOpenGraph η where
  toFun := Prod.swap
  map_rel' {z w} h := by
    refine ⟨?_, h.2⟩
    simpa only [Prod.fst_swap, Prod.snd_swap, add_comm] using h.1

/-- A positive-width site crossing lifts through any open-site homomorphism into the
renormalized field. -/
theorem horizontal_crossing_lifts_of_site_hom {ω : Configuration 2} {R m n : ℕ}
    (hR : 3210 ≤ R) (hm : 0 < m) (η : PlanarCarrier → Bool)
    (φ : siteOpenGraph η →g siteOpenGraph (renormField R ω))
    (hφ : ∀ z, η z = true → renormField R ω (φ z) = true)
    {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph η) (Finset.finite_toSet (rectangle m n)))
      (↑(leftSide m n)) (↑(rightSide m n)) l) :
    ∃ x ∈ cubeAt (renormCentre R (φ (l.head hl.ne_nil 0, l.head hl.ne_nil 1))) (11 * R / 10),
      ∃ y ∈ cubeAt (renormCentre R (φ (l.getLast hl.ne_nil 0, l.getLast hl.ne_nil 1)))
        (11 * R / 10), ∃ P : (openGraph ω).Walk x y, P.IsPath ∧
          (∀ z ∈ P.support, z ∈ renormPathRegion R (l.map fun z => φ (z 0, z 1))) ∧
          P.length < l.length * (2 * (11 * R / 10) + 1) ^ 2 := by
  have hchain : l.IsChain (planarOpenSiteGraph η).Adj :=
    hl.1.imp fun _ _ he => (Menger.mem_edgesIn.1 he).1
  have hopen : η (l.head hl.ne_nil 0, l.head hl.ne_nil 1) = true := by
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
      | cons b t => exact (List.isChain_cons_cons.1 hchain).1.2.1
  let P := SimpleGraph.Walk.ofSupport l hl.ne_nil hchain
  let Q := (P.map (planarOpenSiteHom η)).map φ
  obtain ⟨x, hx, y, hy, W, hWpath, hWsupport, hWlen⟩ :=
    renorm_walk_lifts_short_path hR Q (hφ _ hopen)
  refine ⟨x, hx, y, hy, W, hWpath, ?_, ?_⟩
  · have hQsupport : Q.support = l.map (fun z => φ (z 0, z 1)) := by
      change ((P.map (planarOpenSiteHom η)).map φ).support = _
      rw [SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_map]
      change List.map _ (List.map _ (SimpleGraph.Walk.ofSupport l hl.ne_nil hchain).support) = _
      rw [SimpleGraph.Walk.support_ofSupport, List.map_map]
      rfl
    rw [← hQsupport]
    exact hWsupport
  · simpa only [Q, SimpleGraph.Walk.length_map, P, SimpleGraph.Walk.length_ofSupport,
      Nat.sub_add_cancel (List.length_pos_iff_ne_nil.2 hl.ne_nil)] using hWlen

/-- A translated horizontal crossing lifts to an open lattice path through the translated
blocks. -/
theorem translated_crossing_lifts {ω : Configuration 2} {R m n : ℕ}
    (hR : 3210 ≤ R) (hm : 0 < m) (a : PlanarCarrier) {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk
      (Menger.edgesIn (planarOpenSiteGraph (translatePlanarField a (renormField R ω)))
        (Finset.finite_toSet (rectangle m n))) (↑(leftSide m n)) (↑(rightSide m n)) l) :
    ∃ x ∈ cubeAt (renormCentre R (a + (l.head hl.ne_nil 0, l.head hl.ne_nil 1))) (11 * R / 10),
      ∃ y ∈ cubeAt (renormCentre R (a + (l.getLast hl.ne_nil 0, l.getLast hl.ne_nil 1)))
        (11 * R / 10), ∃ P : (openGraph ω).Walk x y, P.IsPath ∧
          (∀ z ∈ P.support, z ∈ renormPathRegion R (l.map fun z => a + (z 0, z 1))) ∧
          P.length < l.length * (2 * (11 * R / 10) + 1) ^ 2 := by
  exact horizontal_crossing_lifts_of_site_hom hR hm _ (translateOpenSiteHom a _)
    (fun _ h => h) hl

/-- After exchanging axes, a translated crossing lifts to an open lattice path through the
corresponding blocks. -/
theorem swapped_translated_crossing_lifts {ω : Configuration 2} {R m n : ℕ}
    (hR : 3210 ≤ R) (hm : 0 < m) (a : PlanarCarrier) {l : List (LatticeModels.Site 2)}
    (hl : Menger.IsLinkWalk
      (Menger.edgesIn
        (planarOpenSiteGraph (translatePlanarField a (swapPlanarField (renormField R ω))))
        (Finset.finite_toSet (rectangle m n))) (↑(leftSide m n)) (↑(rightSide m n)) l) :
    ∃ x ∈ cubeAt (renormCentre R (Prod.swap (a + (l.head hl.ne_nil 0, l.head hl.ne_nil 1))))
        (11 * R / 10),
      ∃ y ∈ cubeAt (renormCentre R (Prod.swap (a + (l.getLast hl.ne_nil 0, l.getLast hl.ne_nil 1))))
        (11 * R / 10), ∃ P : (openGraph ω).Walk x y, P.IsPath ∧
          (∀ z ∈ P.support, z ∈ renormPathRegion R
            (l.map fun z => Prod.swap (a + (z 0, z 1)))) ∧
          P.length < l.length * (2 * (11 * R / 10) + 1) ^ 2 := by
  exact horizontal_crossing_lifts_of_site_hom hR hm _
    ((swapOpenSiteHom _).comp (translateOpenSiteHom a _)) (fun _ h => h) hl

/-- An injective relabeling of pairwise disjoint site paths preserves the ninefold bound on
visited-block regions. -/
theorem card_injective_path_regions_meeting_le_nine {V : Type*} {R : ℕ} {x : Vertex 2}
    (f : V → PlanarCarrier) (hf : Function.Injective f) (L : Finset (List V))
    (hdisj : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → ∀ z ∈ l, z ∉ l')
    (hx : ∀ l ∈ L, x ∈ renormPathRegion R (l.map f)) : L.card ≤ 9 := by
  classical
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

/-- Translated disjoint crossings have at most nine visited-block regions at any vertex. -/
theorem card_translated_crossing_regions_meeting_le_nine {R : ℕ} {x : Vertex 2}
    (a : PlanarCarrier) (L : Finset (List (LatticeModels.Site 2)))
    (hdisj : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → ∀ z ∈ l, z ∉ l')
    (hx : ∀ l ∈ L, x ∈ renormPathRegion R (l.map fun z => a + (z 0, z 1))) : L.card ≤ 9 := by
  apply card_injective_path_regions_meeting_le_nine (fun z => a + (z 0, z 1)) ?_ L hdisj hx
  intro z w h
  have h' : (z 0, z 1) = (w 0, w 1) := add_left_cancel h
  exact LatticeModels.Site.eq_iff_two.2 ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

/-- The same bound holds when the translated crossings are coordinate-swapped. -/
theorem card_swapped_crossing_regions_meeting_le_nine {R : ℕ} {x : Vertex 2}
    (a : PlanarCarrier) (L : Finset (List (LatticeModels.Site 2)))
    (hdisj : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → ∀ z ∈ l, z ∉ l')
    (hx : ∀ l ∈ L, x ∈ renormPathRegion R (l.map fun z => Prod.swap (a + (z 0, z 1)))) :
    L.card ≤ 9 := by
  have hinj : Function.Injective (fun z : LatticeModels.Site 2 => Prod.swap (a + (z 0, z 1))) := by
    intro z w h
    have h' : (z 0, z 1) = (w 0, w 1) := add_left_cancel (Prod.swap_injective h)
    exact LatticeModels.Site.eq_iff_two.2 ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  exact card_injective_path_regions_meeting_le_nine (R := R) (x := x) _ hinj L hdisj hx

end Rigidity.Proofs.Section5.Kesten
