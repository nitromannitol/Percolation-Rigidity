import Rigidity.Steps.S3.ReductionToSlopeE1
import LatticeProb.Prob.Percolation.MeasurableCorrectorGradients
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth
import LatticeProb.Prob.Percolation.LatticeClusterLipschitz

/-!
# Lemma 3.1: measurability and translation covariance of the Lipschitz slopes

Shared facts for the steps `step:3.1-zero-one` and `step:3.1-deterministic-slope` of Lemma 3.1
(paper L817-838 of the corrected draft).

* On a measurable set `G` of configurations where the corrector clauses hold, the corrected plane
  `ℓ_q` has the gradient `∑ⱼ qⱼ g(ω, (x, y))ⱼ` along every open edge `(x, y)` of the cluster, for a
  measurable coefficient field `g`. Since a Lipschitz bound for the graph distance is a bound on
  the edges, the set of `L`-Lipschitz slopes is the intersection of the slabs
  `|∑ⱼ qⱼ g(ω, e)ⱼ| ≤ L`: it is closed, and the configurations for which it meets a compact (or
  an open) set of slopes form a measurable subset of `G`.
* The set of `L`-Lipschitz slopes and the event `E_L` are invariant under the translations of the
  lattice, which transport the unique infinite cluster, its corrected planes, its harmonic
  functions and its graph distance.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

section Lipschitz

variable {ω : Configuration d}

/-- A Lipschitz bound for the graph distance of a component is a bound on its open edges. -/
theorem isLipschitzWith_iff_edge (C : OpenComponent ω) (L : ℝ) (u : C → ℝ) :
    IsLipschitzWith C L u ↔ ∀ x y : C, (componentGraph C).Adj x y → |u x - u y| ≤ L :=
  component_dist_bound_iff_edge_bound C u L

/-- The Lipschitz constant of a function on the unique infinite cluster is nonnegative. -/
theorem nonneg_of_isLipschitzWith (h : HasUniqueInfiniteOpenComponent ω) {L : ℝ}
    {u : uniqueInfiniteComponent h → ℝ} (hu : IsLipschitzWith (uniqueInfiniteComponent h) L u) :
    0 ≤ L := by
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent h).nonempty_supp
  obtain ⟨x, hx, hxo⟩ := (uniqueInfiniteComponent_infinite h).nontrivial.exists_ne o
  have hdist : (componentGraph (uniqueInfiniteComponent h)).dist ⟨x, hx⟩ ⟨o, ho⟩ ≠ 0 := by
    rw [Ne, component_dist_eq_zero_iff]
    exact fun hc => hxo (congrArg Subtype.val hc)
  have hpos : (0 : ℝ) < ((componentGraph (uniqueInfiniteComponent h)).dist ⟨x, hx⟩ ⟨o, ho⟩ : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdist)
  have hle := hu ⟨x, hx⟩ ⟨o, ho⟩
  by_contra hL
  have : L * ((componentGraph (uniqueInfiniteComponent h)).dist ⟨x, hx⟩ ⟨o, ho⟩ : ℝ) < 0 :=
    mul_neg_of_neg_of_pos (not_le.mp hL) hpos
  linarith [abs_nonneg (u ⟨x, hx⟩ - u ⟨o, ho⟩)]

/-- Lipschitz bounds are transported by graph isomorphisms of components. -/
theorem isLipschitzWith_iso {ω' : Configuration d} {C : OpenComponent ω} {D : OpenComponent ω'}
    (e : componentGraph C ≃g componentGraph D) (L : ℝ) (u : C → ℝ) :
    IsLipschitzWith D L (fun y => u (e.symm y)) ↔ IsLipschitzWith C L u := by
  rw [isLipschitzWith_iff_edge, isLipschitzWith_iff_edge]
  constructor
  · intro h x y hxy
    simpa only [RelIso.symm_apply_apply] using h (e x) (e y) (e.map_adj_iff.mpr hxy)
  · intro h x y hxy
    exact h _ _ (e.symm.map_adj_iff.mpr hxy)

end Lipschitz

section Gradients

variable (G : Set (Configuration d)) (hvalid : G ⊆ correctorValidEvent d)
  (g : G → (Vertex d × Vertex d) → Fin d → ℝ)

/-- On the corrector-valid set, a slope is `L`-Lipschitz exactly when the gradients
`∑ⱼ qⱼ g(ω, e)ⱼ` of its corrected plane along the ordered pairs `e` are bounded by `L`
(the gradient vanishes off the open edges of the cluster, and `L ≥ 0` for a Lipschitz slope). -/
theorem lipschitzSlopeSet_eq_of_gradients
    (hzero : ∀ (ω : G) e, ¬ (ω.val ∈ infiniteComponentEvent e.1 ∧
      (openGraph ω.val).Adj e.1 e.2) → ∀ j, g ω e j = 0)
    (hgradient : ∀ (ω : G) (q : Fin d → ℝ)
      (u : uniqueInfiniteComponent (hvalid ω.property).1 → ℝ),
      IsCorrectedPlane (uniqueInfiniteComponent (hvalid ω.property).1) q u →
      ∀ x y : uniqueInfiniteComponent (hvalid ω.property).1,
        (openGraph ω.val).Adj x.val y.val →
        ∑ j, q j * g ω (x.val, y.val) j = u y - u x)
    (ω : G) (L : ℝ) :
    lipschitzSlopeSet ω.val L = {q | ∀ e, |∑ j, q j * g ω e j| ≤ L} := by
  have hv := hvalid ω.property
  ext q
  constructor
  · rintro ⟨h, hq⟩ e
    obtain ⟨o, ho⟩ := (uniqueInfiniteComponent h).nonempty_supp
    obtain ⟨u, hu, _⟩ := (hv.2 h).1 q ⟨o, ho⟩
    have hLip := hq u hu.1
    by_cases he : ω.val ∈ infiniteComponentEvent e.1 ∧ (openGraph ω.val).Adj e.1 e.2
    · have hx := (mem_uniqueInfiniteComponent_iff h e.1).mpr he.1
      have hy := (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hx he.2
      have hgr := hgradient ω q u hu.1 ⟨e.1, hx⟩ ⟨e.2, hy⟩ he.2
      rw [show e = (e.1, e.2) from rfl, hgr, abs_sub_comm]
      exact (isLipschitzWith_iff_edge _ L u).mp hLip ⟨e.1, hx⟩ ⟨e.2, hy⟩ he.2
    · simp only [hzero ω e he, mul_zero, Finset.sum_const_zero, abs_zero]
      exact nonneg_of_isLipschitzWith h hLip
  · intro hq
    refine ⟨hv.1, fun u hu => ?_⟩
    rw [isLipschitzWith_iff_edge]
    intro x y hxy
    rw [abs_sub_comm, ← hgradient ω q u hu x y hxy]
    exact hq (x.val, y.val)

/-- The slopes whose gradients along every ordered pair are bounded by `L`, for a fixed
coefficient field `c`; the set of `L`-Lipschitz slopes on the corrector-valid set. -/
def slabSlopeSet (c : (Vertex d × Vertex d) → Fin d → ℝ) (L : ℝ) : Set (Fin d → ℝ) :=
  {q | ∀ e, |∑ j, q j * c e j| ≤ L}

/-- The gradient bound along a fixed pair is jointly continuous in the slope and the
coefficients. -/
theorem continuous_slabGradient (e : Vertex d × Vertex d) :
    Continuous (fun p : (Fin d → ℝ) × ((Vertex d × Vertex d) → Fin d → ℝ) =>
      |∑ j, p.1 j * p.2 e j|) := by
  fun_prop

/-- The slab set is an intersection of closed slabs. -/
theorem isClosed_slabSlopeSet (c : (Vertex d × Vertex d) → Fin d → ℝ) (L : ℝ) :
    IsClosed (slabSlopeSet c L) := by
  rw [slabSlopeSet, Set.setOf_forall]
  exact isClosed_iInter fun e => isClosed_le
    ((continuous_slabGradient e).comp (Continuous.prodMk continuous_id continuous_const))
    continuous_const

/-- The coefficient fields whose slab set meets a compact set of slopes form a closed set. -/
theorem isClosed_slabSlopeSet_hit {K : Set (Fin d → ℝ)} (hK : IsCompact K) (L : ℝ) :
    IsClosed {c : (Vertex d × Vertex d) → Fin d → ℝ | (slabSlopeSet c L ∩ K).Nonempty} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hclosed : IsClosed {p : K × ((Vertex d × Vertex d) → Fin d → ℝ) |
      ∀ e, |∑ j, (p.1 : Fin d → ℝ) j * p.2 e j| ≤ L} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun e => isClosed_le ((continuous_slabGradient e).comp
      (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd))
      continuous_const
  convert isClosedMap_snd_of_compactSpace _ hclosed using 1
  ext c
  constructor
  · rintro ⟨q, hq, hqK⟩
    exact ⟨(⟨q, hqK⟩, c), hq, rfl⟩
  · rintro ⟨⟨q, c'⟩, hq, rfl⟩
    exact ⟨q, hq, q.property⟩

end Gradients

/-- The configurations of a measurable corrector-valid set whose set of `L`-Lipschitz slopes meets
a compact set `K` form a measurable set. -/
theorem measurableSet_lipschitzSlopeSet_hit_compact (G : Set (Configuration d))
    (hG : MeasurableSet G) (hvalid : G ⊆ correctorValidEvent d) (L : ℝ)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    MeasurableSet {ω | ω ∈ G ∧ (lipschitzSlopeSet ω L ∩ K).Nonempty} := by
  obtain ⟨g, hg, hzero, hgradient, -⟩ :=
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid
  have hΦ : Measurable (fun ω : G => g ω) :=
    measurable_pi_lambda _ fun e => measurable_pi_lambda _ fun j => hg e j
  have heq : {ω | ω ∈ G ∧ (lipschitzSlopeSet ω L ∩ K).Nonempty} =
      Subtype.val '' ((fun ω : G => g ω) ⁻¹'
        {c | (slabSlopeSet c L ∩ K).Nonempty}) := by
    ext ω
    constructor
    · rintro ⟨hω, hhit⟩
      refine ⟨⟨ω, hω⟩, ?_, rfl⟩
      change (slabSlopeSet (g ⟨ω, hω⟩) L ∩ K).Nonempty
      rwa [slabSlopeSet, ← lipschitzSlopeSet_eq_of_gradients G hvalid g hzero hgradient]
    · rintro ⟨ω', hhit, rfl⟩
      refine ⟨ω'.property, ?_⟩
      change (slabSlopeSet (g ω') L ∩ K).Nonempty at hhit
      rwa [slabSlopeSet, ← lipschitzSlopeSet_eq_of_gradients G hvalid g hzero hgradient] at hhit
  rw [heq]
  exact (MeasurableEmbedding.subtype_coe hG).measurableSet_image.mpr
    (hΦ (isClosed_slabSlopeSet_hit hK L).measurableSet)

/-- An open set of slopes is the union of the compact sets `F n ∩ closedBall 0 m`, where the
closed sets `F n` exhaust it. -/
theorem exists_compact_exhaustion {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∃ K : ℕ → ℕ → Set (Fin d → ℝ), (∀ n m, IsCompact (K n m)) ∧
      ∀ q, q ∈ U ↔ ∃ n m, q ∈ K n m := by
  obtain ⟨F, hF, hFU, hUnion, -⟩ := hU.exists_iUnion_isClosed
  refine ⟨fun n m => F n ∩ Metric.closedBall 0 m,
    fun n m => (isCompact_closedBall 0 m).inter_left (hF n), fun q => ⟨fun hq => ?_, ?_⟩⟩
  · rw [← hUnion, Set.mem_iUnion] at hq
    obtain ⟨n, hn⟩ := hq
    obtain ⟨m, hm⟩ := exists_nat_ge ‖q‖
    exact ⟨n, m, hn, by rwa [Metric.mem_closedBall, dist_zero_right]⟩
  · rintro ⟨n, m, hn, -⟩
    exact hFU n hn

/-- The configurations of a measurable corrector-valid set whose set of `L`-Lipschitz slopes meets
an open set `U` form a measurable set. -/
theorem measurableSet_lipschitzSlopeSet_hit_open (G : Set (Configuration d))
    (hG : MeasurableSet G) (hvalid : G ⊆ correctorValidEvent d) (L : ℝ)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    MeasurableSet {ω | ω ∈ G ∧ (lipschitzSlopeSet ω L ∩ U).Nonempty} := by
  obtain ⟨K, hK, hKU⟩ := exists_compact_exhaustion hU
  have heq : {ω | ω ∈ G ∧ (lipschitzSlopeSet ω L ∩ U).Nonempty} =
      ⋃ n, ⋃ m, {ω | ω ∈ G ∧ (lipschitzSlopeSet ω L ∩ K n m).Nonempty} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hω, q, hq, hqU⟩
      obtain ⟨n, m, hnm⟩ := (hKU q).mp hqU
      exact ⟨n, m, hω, q, hq, hnm⟩
    · rintro ⟨n, m, hω, q, hq, hnm⟩
      exact ⟨hω, q, hq, (hKU q).mpr ⟨n, m, hnm⟩⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_lipschitzSlopeSet_hit_compact G hG hvalid L (hK n m)

/-- On a measurable corrector-valid set, the set of `L`-Lipschitz slopes is closed. -/
theorem isClosed_lipschitzSlopeSet_of_mem (G : Set (Configuration d))
    (hG : MeasurableSet G) (hvalid : G ⊆ correctorValidEvent d) (L : ℝ)
    {ω : Configuration d} (hω : ω ∈ G) : IsClosed (lipschitzSlopeSet ω L) := by
  obtain ⟨g, -, hzero, hgradient, -⟩ :=
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid
  have := lipschitzSlopeSet_eq_of_gradients G hvalid g hzero hgradient ⟨ω, hω⟩ L
  rw [this]
  exact isClosed_slabSlopeSet (g ⟨ω, hω⟩) L

/-- If a measurable corrector-valid set has full measure, the configurations whose set of
`L`-Lipschitz slopes meets an open set form a null-measurable event. -/
theorem nullMeasurableSet_lipschitzSlopeSet_hit_open {μ : Measure (Configuration d)}
    (G : Set (Configuration d)) (hG : MeasurableSet G) (hvalid : G ⊆ correctorValidEvent d)
    (hGae : ∀ᵐ ω ∂μ, ω ∈ G) (L : ℝ) {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    NullMeasurableSet {ω | (lipschitzSlopeSet ω L ∩ U).Nonempty} μ := by
  refine (measurableSet_lipschitzSlopeSet_hit_open G hG hvalid L hU).nullMeasurableSet.congr ?_
  filter_upwards [hGae] with ω hω
  exact propext ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

section Translation

variable {ω : Configuration d}

/-- Translation transports the statement "every corrected plane of slope `q` is `L`-Lipschitz"
from a component to its translate. -/
theorem forall_correctedPlane_isLipschitzWith_translation_iff (z : Vertex d)
    (C : OpenComponent ω) (q : Fin d → ℝ) (L : ℝ) :
    (∀ v : openComponentTranslation z ω C → ℝ,
      IsCorrectedPlane (openComponentTranslation z ω C) q v →
        IsLipschitzWith (openComponentTranslation z ω C) L v) ↔
    (∀ u : C → ℝ, IsCorrectedPlane C q u → IsLipschitzWith C L u) := by
  let e := openComponentTranslationIso z C
  constructor
  · intro h u hu
    exact (isLipschitzWith_iso e L u).mp
      (h _ ((isCorrectedPlane_translation_iff z C q u).mpr hu))
  · intro h v hv
    let u : C → ℝ := fun x => v (e x)
    have he : (fun y => u (e.symm y)) = v := funext fun y => congrArg v (e.apply_symm_apply y)
    have hu : IsCorrectedPlane C q u := by
      apply (isCorrectedPlane_translation_iff z C q u).mp
      change IsCorrectedPlane _ q (fun y => u (e.symm y))
      rw [he]
      exact hv
    rw [← he]
    exact (isLipschitzWith_iso e L u).mpr (h u hu)

/-- The set of `L`-Lipschitz slopes is invariant under the translations of the lattice. -/
theorem lipschitzSlopeSet_translation (z : Vertex d) (ω : Configuration d) (L : ℝ) :
    lipschitzSlopeSet (configurationTranslation z ω) L = lipschitzSlopeSet ω L := by
  ext q
  constructor
  · rintro ⟨ht, hq⟩
    have h := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mp ht
    refine ⟨h, ?_⟩
    have hC := openComponentTranslation_uniqueInfiniteComponent z h
    apply (forall_correctedPlane_isLipschitzWith_translation_iff z _ q L).mp
    rw [hC]
    exact hq
  · rintro ⟨h, hq⟩
    have ht := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
    refine ⟨ht, ?_⟩
    have hC := openComponentTranslation_uniqueInfiniteComponent z h
    have := (forall_correctedPlane_isLipschitzWith_translation_iff z _ q L).mpr hq
    rw [hC] at this
    exact this

/-- Translation transports nonconstant `L`-Lipschitz harmonic functions from a component to its
translate. -/
theorem exists_lipschitz_harmonic_translation_iff (z : Vertex d) (C : OpenComponent ω) (L : ℝ) :
    (∃ v : openComponentTranslation z ω C → ℝ,
      (∀ y, componentLaplacian (openComponentTranslation z ω C) v y = 0) ∧
      IsLipschitzWith (openComponentTranslation z ω C) L v ∧ ∃ x y, v x ≠ v y) ↔
    (∃ u : C → ℝ, (∀ x, componentLaplacian C u x = 0) ∧ IsLipschitzWith C L u ∧
      ∃ x y, u x ≠ u y) := by
  let e := openComponentTranslationIso z C
  constructor
  · rintro ⟨v, hharm, hlip, x, y, hxy⟩
    let u : C → ℝ := fun x => v (e x)
    have he : (fun y => u (e.symm y)) = v := funext fun y => congrArg v (e.apply_symm_apply y)
    refine ⟨u, fun x => ?_, (isLipschitzWith_iso e L u).mp (he ▸ hlip), e.symm x, e.symm y, ?_⟩
    · rw [← componentLaplacian_translation z C u x, he]
      exact hharm _
    · change v (e (e.symm x)) ≠ v (e (e.symm y))
      rwa [e.apply_symm_apply, e.apply_symm_apply]
  · rintro ⟨u, hharm, hlip, x, y, hxy⟩
    refine ⟨fun y => u (e.symm y), fun y => ?_, (isLipschitzWith_iso e L u).mpr hlip,
      e x, e y, ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective y
      rw [componentLaplacian_translation]
      exact hharm x
    · change u (e.symm (e x)) ≠ u (e.symm (e y))
      rwa [e.symm_apply_apply, e.symm_apply_apply]

/-- The event `E_L` is invariant under the translations of the lattice. -/
theorem preimage_lipschitzHarmonicEvent (z : Vertex d) (L : ℝ) :
    configurationTranslation z ⁻¹' lipschitzHarmonicEvent d L = lipschitzHarmonicEvent d L := by
  ext ω
  change (∃ ht : HasUniqueInfiniteOpenComponent (configurationTranslation z ω), _) ↔ _
  constructor
  · rintro ⟨ht, hv⟩
    have h := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mp ht
    refine ⟨h, ?_⟩
    have hC := openComponentTranslation_uniqueInfiniteComponent z h
    apply (exists_lipschitz_harmonic_translation_iff z _ L).mp
    rw [hC]
    exact hv
  · rintro ⟨h, hu⟩
    have ht := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
    refine ⟨ht, ?_⟩
    have hC := openComponentTranslation_uniqueInfiniteComponent z h
    have := (exists_lipschitz_harmonic_translation_iff z _ L).mpr hu
    rw [hC] at this
    exact this

end Translation

end Rigidity.Proofs.S3
