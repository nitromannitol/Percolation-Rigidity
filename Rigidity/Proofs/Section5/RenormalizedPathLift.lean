import Rigidity.Proofs.Section5.KestenLocalLink
import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Lifting renormalized site walks

A walk of open renormalized sites carries an open lattice walk inside its enlarged blocks.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5.Kesten

/-- The union of the enlarged blocks visited by a renormalized site list. -/
def renormPathRegion (R : ℕ) (l : List PlanarCarrier) : Set (Vertex 2) :=
  ⋃ z ∈ l, cubeAt (renormCentre R z) (11 * R / 10)

/-- Enlarged blocks that meet at one vertex have centers at star distance at most one. -/
theorem renorm_sites_close_of_mem_blocks {R : ℕ} {z w : PlanarCarrier} {x : Vertex 2}
    (hz : x ∈ cubeAt (renormCentre R z) (11 * R / 10))
    (hw : x ∈ cubeAt (renormCentre R w) (11 * R / 10)) :
    |z.1 - w.1| ≤ 1 ∧ |z.2 - w.2| ≤ 1 := by
  have hr : ((11 * R / 10 : ℕ) : ℤ) ≤ 2 * (R : ℤ) := by
    exact_mod_cast (show 11 * R / 10 ≤ 2 * R by omega)
  have hR : (0 : ℤ) ≤ R := by positivity
  have hcoord {a b t : ℤ} (ha : |t - (2 * (R : ℤ) + 1) * a| ≤ (11 * R / 10 : ℕ))
      (hb : |t - (2 * (R : ℤ) + 1) * b| ≤ (11 * R / 10 : ℕ)) : |a - b| ≤ 1 := by
    have ha' := abs_le.1 ha
    have hb' := abs_le.1 hb
    apply abs_le.2
    constructor
    · by_contra h
      have hmul := mul_nonneg (show (0 : ℤ) ≤ 2 * R + 1 by omega)
        (show (0 : ℤ) ≤ b - a - 2 by omega)
      nlinarith
    · by_contra h
      have hmul := mul_nonneg (show (0 : ℤ) ≤ 2 * R + 1 by omega)
        (show (0 : ℤ) ≤ a - b - 2 by omega)
      nlinarith
  constructor
  · apply hcoord (t := x 0)
    · simpa only [cubeAt, renormCentre, Matrix.cons_val_zero] using hz 0
    · simpa only [cubeAt, renormCentre, Matrix.cons_val_zero] using hw 0
  · apply hcoord (t := x 1)
    · simpa only [cubeAt, renormCentre, Matrix.cons_val_one, Matrix.cons_val_zero] using hz 1
    · simpa only [cubeAt, renormCentre, Matrix.cons_val_one, Matrix.cons_val_zero] using hw 1

/-- At most nine enlarged blocks contain any fixed lattice vertex. -/
theorem card_renorm_blocks_containing_le_nine {R : ℕ} {x : Vertex 2}
    (V : Finset PlanarCarrier)
    (hV : ∀ z ∈ V, x ∈ cubeAt (renormCentre R z) (11 * R / 10)) : V.card ≤ 9 := by
  classical
  by_cases hne : V.Nonempty
  · obtain ⟨z, hz⟩ := hne
    let B := (Finset.Icc (z.1 - 1) (z.1 + 1)).product (Finset.Icc (z.2 - 1) (z.2 + 1))
    have hsub : V ⊆ B := by
      intro w hw
      have h := renorm_sites_close_of_mem_blocks (hV w hw) (hV z hz)
      have h₁ := abs_le.1 h.1
      have h₂ := abs_le.1 h.2
      apply Finset.mem_product.2
      constructor <;> apply Finset.mem_Icc.2 <;> omega
    calc
      V.card ≤ B.card := Finset.card_le_card hsub
      _ = 9 := by
        dsimp only [B]
        rw [Finset.product_eq_sprod, Finset.card_product, Int.card_Icc, Int.card_Icc]
        have h₁ : z.1 + 1 + 1 - (z.1 - 1) = 3 := by omega
        have h₂ : z.2 + 1 + 1 - (z.2 - 1) = 3 := by omega
        rw [h₁, h₂]
        decide
  · have hVempty : V = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    simp [hVempty]

/-- At most nine pairwise site-disjoint path regions contain a given lattice vertex. -/
theorem card_disjoint_path_regions_meeting_le_nine {R : ℕ} {x : Vertex 2}
    (L : Finset (List PlanarCarrier))
    (hdisj : ∀ l ∈ L, ∀ l' ∈ L, l ≠ l' → ∀ z ∈ l, z ∉ l')
    (hx : ∀ l ∈ L, x ∈ renormPathRegion R l) : L.card ≤ 9 := by
  classical
  have hex : ∀ l ∈ L, ∃ z, z ∈ l ∧ x ∈ cubeAt (renormCentre R z) (11 * R / 10) := by
    intro l hl
    obtain ⟨z, hz, hxz⟩ : ∃ z, ∃ _ : z ∈ l,
        x ∈ cubeAt (renormCentre R z) (11 * R / 10) := by
      simpa only [renormPathRegion, Set.mem_iUnion] using hx l hl
    exact ⟨z, hz, hxz⟩
  let f : List PlanarCarrier → PlanarCarrier := fun l =>
    if hl : l ∈ L then Classical.choose (hex l hl) else 0
  have hf (l : List PlanarCarrier) (hl : l ∈ L) :
      f l ∈ l ∧ x ∈ cubeAt (renormCentre R (f l)) (11 * R / 10) := by
    dsimp only [f]
    rw [dif_pos hl]
    exact Classical.choose_spec (hex l hl)
  have hinj : Set.InjOn f (↑L : Set (List PlanarCarrier)) := by
    intro l hl l' hl' heq
    by_contra hne
    apply hdisj l hl l' hl' hne (f l) (hf l hl).1
    rw [heq]
    exact (hf l' hl').1
  have hb : (L.image f).card ≤ 9 := card_renorm_blocks_containing_le_nine _ (by
    intro z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hz
    exact (hf l hl).2)
  rwa [Finset.card_image_of_injOn hinj] at hb

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

/-- The lifted lattice path can be chosen self-avoiding, with length at most the number of
visited sites times the volume of one enlarged block. -/
theorem renorm_walk_lifts_short_path {ω : Configuration 2} {R : ℕ} (hR : 3210 ≤ R)
    {u v : PlanarCarrier} (w : (siteOpenGraph (renormField R ω)).Walk u v)
    (hu : renormField R ω u = true) :
    ∃ x ∈ cubeAt (renormCentre R u) (11 * R / 10),
      ∃ y ∈ cubeAt (renormCentre R v) (11 * R / 10),
        ∃ P : (openGraph ω).Walk x y, P.IsPath ∧
          (∀ z ∈ P.support, z ∈ renormPathRegion R w.support) ∧
          P.length < (w.length + 1) * (2 * (11 * R / 10) + 1) ^ 2 := by
  classical
  obtain ⟨x, hx, y, hy, P, hP⟩ := renorm_walk_lifts hR w hu
  let V := w.support.toFinset.biUnion fun z =>
    Rigidity.Proofs.S3.cubeFinset (renormCentre R z) (11 * R / 10)
  have hsub : P.bypass.support.toFinset ⊆ V := by
    intro z hz
    have hz' : z ∈ P.support := P.support_bypass_subset_support (List.mem_toFinset.1 hz)
    have hzR := hP z hz'
    simp only [renormPathRegion, Set.mem_iUnion] at hzR
    obtain ⟨a, ha, hza⟩ := hzR
    apply Finset.mem_biUnion.2
    refine ⟨a, List.mem_toFinset.2 ha, ?_⟩
    apply Rigidity.Proofs.S3.mem_cubeFinset.2
    exact hza
  have hcard : V.card ≤ w.support.length * (2 * (11 * R / 10) + 1) ^ 2 := by
    calc
      V.card ≤ w.support.toFinset.card * (2 * (11 * R / 10) + 1) ^ 2 :=
        Finset.card_biUnion_le_card_mul _ _ _ fun z _ => by
          rw [Rigidity.Proofs.S3.card_cubeFinset]
      _ ≤ w.support.length * (2 * (11 * R / 10) + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (List.toFinset_card_le _)
  have hlen := (Finset.card_le_card hsub).trans hcard
  rw [List.toFinset_card_of_nodup P.bypass_isPath.support_nodup,
    SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_support] at hlen
  refine ⟨x, hx, y, hy, P.bypass, P.bypass_isPath, ?_, by omega⟩
  intro z hz
  exact hP z (P.support_bypass_subset_support hz)

end Rigidity.Proofs.Section5.Kesten
