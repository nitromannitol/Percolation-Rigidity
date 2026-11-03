import Rigidity.Proofs.Section5.GoodEventBasics
import Rigidity.Steps.S3.NotLipschitzInner

/-!
# Lemma 5.25: the direction-free third good event (L2370, [C32])

`ThirdGoodEventStep` of `Rigidity/Steps/Section5/GoodEventLowerBound.lean`: for every `C_χ ≥ 1`,
the third good event `G_3(0, C_χ)` (some edge `(0, y)` of `𝒞_∞` across which every corrected plane
`ℓ_{e₁}` increases by at least `C_χ`, [C32]) contains a measurable event of positive probability.

* `neighborRise_of_notLipschitz`: from Proposition 3.2, for every `L ≥ 1`, with positive (outer)
  probability the origin lies in `𝒞_∞` and has a neighbour `y` in `𝒞_∞` with
  `ℓ_{e₁}(y) - ℓ_{e₁}(0) > L`. A large `|ℓ(0) - ℓ(e_i)|` gives either this event at the origin or,
  read from `e_i`, the same event at `e_i`, which a translation moves to the origin (the
  "symmetry arguments" of L2370).
* `exists_measurable_subset_eventG3`: the uniqueness of the corrected plane up to additive
  constants (`SupercriticalBondCorrectorInput`) turns "some corrected plane" into "every corrected
  plane", and the measurable rooted plane field of Lattice-Probability makes the event measurable.
* `thirdGoodEventStep`: the step.

The printed event on the edge `(0, e₁)` needs the signed variant of Proposition 3.2
(`Rigidity/Steps/S3/HorizontalIncrement.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- The vertex `x` lies in the infinite cluster and has a neighbour `y` in the cluster across which
a corrected plane `ℓ_{e₁}` increases by more than `L`: `ℓ_{e₁}(y) - ℓ_{e₁}(x) > L`. -/
def neighborRiseEvent (x : Vertex 2) (L : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ y : uniqueInfiniteComponent h, (componentGraph _).Adj ⟨x, hx⟩ y ∧
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) u ∧
        L < u y - u ⟨x, hx⟩}

/-- The event `neighborRiseEvent` moves with the environment. -/
theorem neighborRiseEvent_translation (z : Vertex 2) {x : Vertex 2} {L : ℝ}
    {ω : Configuration 2} (hω : ω ∈ neighborRiseEvent x L) :
    configurationTranslation z ω ∈ neighborRiseEvent (x + z) L := by
  obtain ⟨h, hx, y, hadj, u, hu, hlt⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  have hxz : x + z ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp :=
    (add_mem_openComponentTranslation_supp z _ x).mpr hx
  have e0 : (⟨x + z, hxz⟩ : openComponentTranslation z ω (uniqueInfiniteComponent h)) =
      openComponentTranslationIso z _ ⟨x, hx⟩ := rfl
  refine ⟨hxz, openComponentTranslationIso z _ y,
    by rw [e0]; exact (openComponentTranslationIso z _).map_adj_iff.mpr hadj,
    fun v => u ((openComponentTranslationIso z _).symm v),
    (isCorrectedPlane_translation_iff z _ _ u).mpr hu, ?_⟩
  rw [e0]
  simpa only [RelIso.symm_apply_apply] using hlt

/-- A null event has null preimages under the lattice translations (outer measure). -/
theorem latticeBondLaw_preimage_translation_null {p : unitInterval} {A : Set (Configuration 2)}
    (hA : latticeBondLaw 2 p A = 0) (z : Vertex 2) :
    latticeBondLaw 2 p (configurationTranslation z ⁻¹' A) = 0 := by
  have hτ := measurePreserving_configurationTranslation p z
  refine measure_mono_null
    (Set.preimage_mono (subset_toMeasurable (latticeBondLaw 2 p) A)) ?_
  rw [hτ.measure_preimage (measurableSet_toMeasurable _ A).nullMeasurableSet,
    measure_toMeasurable]
  exact hA

/-- **Direction-free variant of Proposition 3.2.** For every `L ≥ 1`, with positive (outer)
probability the origin lies in the infinite cluster and has a neighbour in the cluster across which
a corrected plane `ℓ_{e₁}` increases by more than `L`. -/
theorem neighborRise_of_notLipschitz {p : unitInterval}
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) (L : ℝ) (hL : 1 ≤ L) :
    latticeBondLaw 2 p (neighborRiseEvent 0 L) ≠ 0 := by
  intro h0
  set A := neighborRiseEvent 0 L
  refine (h32.originGradient_ne_zero (by linarith : (1 : ℝ) ≤ 2 * L))
    (measure_mono_null ?_ (measure_union_null h0
    (measure_iUnion_null fun i : Fin 2 =>
      latticeBondLaw_preimage_translation_null h0 (-LatticeProb.unit i))))
  rintro ω ⟨h, ho, u, hu, hlt⟩
  unfold Rigidity.Section3.originGradientNorm at hlt
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := (Finset.univ : Finset (Fin 2)))
    (f := fun _ => L) (lt_of_eq_of_lt (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num) hlt)
  split_ifs at hi with hadj
  · have hy := (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    have hA : (componentGraph (uniqueInfiniteComponent h)).Adj ⟨0, ho⟩
        ⟨LatticeProb.unit i, hy⟩ := ((uniqueInfiniteComponent h).toSimpleGraph_adj ho hy).2 hadj
    rcases lt_abs.mp hi with hi | hi
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
      have hmem : ω ∈ neighborRiseEvent (LatticeProb.unit i) L :=
        ⟨h, hy, ⟨0, ho⟩, hA.symm, u, hu, by linarith⟩
      have := neighborRiseEvent_translation (-LatticeProb.unit i) hmem
      rwa [add_neg_cancel] at this
    · exact Or.inl ⟨h, ho, ⟨LatticeProb.unit i, hy⟩, hA, u, hu, by linarith⟩
  · linarith

/-- **The third good event has positive probability** ([C32]), from Proposition 3.2: for
`p_c(2) < p < 1` and every `C_χ ≥ 1`, the direction-free event `G_3(0, C_χ)` contains a measurable
event of positive probability. The uniqueness of the corrected plane up to additive
constants turns "some corrected plane" into "every corrected plane", and the measurable rooted plane
field makes the event measurable . -/
theorem exists_measurable_subset_eventG3
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) (Cχ : ℝ) (hCχ : 1 ≤ Cχ) :
    ∃ A ⊆ eventG3 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  set μ := latticeBondLaw 2 p
  set q : Fin 2 → ℝ := Pi.single 0 1
  have hbad := ae_iff.mp (hU 2 le_rfl p hpc hp1)
  set N := toMeasurable μ {ω | ¬ ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)} with hN
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad
  set G := Nᶜ ∩ uniqueInfiniteComponentEvent 2
  have hGm : MeasurableSet G :=
    (measurableSet_toMeasurable _ _).compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)
  have hvalid : G ⊆ correctorValidEvent 2 := by
    intro ω hω
    by_contra hn
    exact hω.1 (subset_toMeasurable _ _ fun hP => hn ⟨hω.2, by simpa using hP⟩)
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  set T : Set ↥(G ∩ infiniteComponentEvent 0) :=
    ⋃ v : Vertex 2, {z | (openGraph z.val).Adj 0 v ∧ Cχ ≤ F (z, q) v}
  have hT : MeasurableSet T := by
    refine MeasurableSet.iUnion fun v => ?_
    refine (measurable_subtype_coe (measurableSet_openGraph_adj 0 v)).inter ?_
    exact measurableSet_le measurable_const
      ((measurable_pi_apply v).comp (hFm.comp (measurable_id.prodMk measurable_const)))
  refine ⟨Subtype.val '' T, ?_, hB.subtype_image hT, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨v, hadj, hval⟩ := Set.mem_iUnion.mp hz
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    have hv : v ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    refine ⟨h, ho, ⟨v, hv⟩, ((uniqueInfiniteComponent h).toSimpleGraph_adj ho hv).2 hadj,
      fun ℓ hℓ => ?_⟩
    rw [Steps.S3.rootedPlane_eq_sub hF z h ho hℓ hv] at hval
    exact hval
  · have hS := neighborRise_of_notLipschitz h32 Cχ hCχ
    refine pos_iff_ne_zero.mpr fun hA => hS (measure_mono_null ?_ (measure_union_null hA hN0))
    rintro ω ⟨h, ho, y, hadj, u, hu, hlt⟩
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ⟨⟨ω, ⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩,
        Set.mem_iUnion.mpr ⟨y.val,
          ((uniqueInfiniteComponent h).toSimpleGraph_adj ho y.2).1 hadj, ?_⟩, rfl⟩
      rw [Steps.S3.rootedPlane_eq_sub hF _ h ho hu y.2]
      exact hlt.le

/-- **Step `ThirdGoodEventStep`** of Lemma 5.25 ([C32]), from Proposition 3.2. -/
theorem thirdGoodEventStep : ThirdGoodEventStep :=
  fun hU _ hpc hp1 h32 Cχ hCχ => exists_measurable_subset_eventG3 hU hpc hp1 h32 Cχ hCχ

end Rigidity.Proofs.Section5
