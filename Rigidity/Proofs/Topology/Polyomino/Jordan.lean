import Rigidity.Proofs.Topology.Polyomino.Graph
import Rigidity.Proofs.Topology.Polyomino.Simple
import Rigidity.Proofs.Topology.PlanarJordan.Summary

/-! # The frontier of a union of cells with simple boundary is a Jordan polygon

Let `S` be a finite set of cells such that the interior `Ω` of their union is connected, its
complement in `S²` is connected, and every boundary point is simple. There is no checkerboard
corner (`noChecker_of_simple`), so every component of the boundary graph with an edge is a cycle,
whose corners form a closed lattice polygon without repeated corner (`exists_polygon`); its trace
is a Jordan curve (`jordan_of_polygon`, by the planar Jordan curve theorem
`MatedCRTHarmonic.Planar.Jordan.jordan_curve_components`).

* `Ω` lies inside every such polygon (`subset_inside`): otherwise the cells outside `S` whose
  centre lies inside would form a nonempty compact set, open and closed in the complement of `Ω`
  (at a point shared by two cells outside `S`, the centres of the two cells are joined in the
  complement of the boundary, `ctr_mem_of_cells`), which separates the complement in `S²`.
* There is only one such polygon (`false_of_two_loops`): the outside of each polygon would lie in
  the outside of the other, so the two outsides, hence the two polygons, would coincide.

Hence `∂Ω` is the trace of one polygon (`frontier_eq_polyTrace`), and is homeomorphic to the
circle.
-/

open Set Filter Topology Function Bornology LatticeProb

namespace Rigidity.Proofs.Topology.Polyomino

open Rigidity.Proofs.Section5.JordanLoop Rigidity.Section2 MatedCRTHarmonic.Planar.Jordan

/-! ### Closed paths of the plane and the circle -/

section CircleMap

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- A closed path descends to the quotient identifying the endpoints of the unit interval. -/
def pathQuot {q : E2} (β : Path q q) : Quot (AddCircle.EndpointIdent (1 : ℝ) 0) → E2 :=
  Quot.lift (fun t : Icc (0 : ℝ) (0 + 1) => β ⟨t.1, by simpa using t.2⟩) (by
    rintro _ _ ⟨⟩
    simp [β.source, β.target])

theorem continuous_pathQuot {q : E2} (β : Path q q) : Continuous (pathQuot β) := by
  apply continuous_quot_lift
  apply β.continuous.comp
  exact continuous_subtype_val.subtype_mk _

/-- The circle map of a closed path of the plane. -/
noncomputable def pathCircle {q : E2} (β : Path q q) : Circle → E2 :=
  pathQuot β ∘ (AddCircle.homeoIccQuot (1 : ℝ) 0) ∘
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm

theorem continuous_pathCircle {q : E2} (β : Path q q) : Continuous (pathCircle β) :=
  (continuous_pathQuot β).comp
    ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp
      (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.continuous)

theorem range_pathQuot {q : E2} (β : Path q q) : range (pathQuot β) = range β := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    induction z using Quot.ind with
    | _ t => exact ⟨⟨t.1, by simpa using t.2⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨Quot.mk _ ⟨t.1, ?_⟩, ?_⟩
    · simp only [zero_add]
      exact t.2
    · rfl

theorem range_pathCircle {q : E2} (β : Path q q) : range (pathCircle β) = range β := by
  calc
    range (pathCircle β) = range (pathQuot β) := by
      apply Set.Subset.antisymm
      · rintro x ⟨c, rfl⟩
        exact ⟨(AddCircle.homeoIccQuot (1 : ℝ) 0)
          ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm c), rfl⟩
      · rintro x ⟨z, rfl⟩
        refine ⟨AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
          ((AddCircle.homeoIccQuot (1 : ℝ) 0).symm z), ?_⟩
        simp only [pathCircle, Function.comp_apply, Homeomorph.symm_apply_apply,
          Homeomorph.apply_symm_apply]
    _ = range β := range_pathQuot β

theorem injective_pathCircle {q : E2} (β : Path q q) (hβ : InjOn β (Ico 0 1)) :
    Injective (pathCircle β) := by
  let h := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  let e := AddCircle.equivIco (1 : ℝ) 0
  let u : Circle → unitInterval := fun c =>
    ⟨(e (h.symm c)).1, ⟨(e (h.symm c)).2.1, by
      have hp := (e (h.symm c)).2.2
      simp only [zero_add] at hp
      exact hp.le⟩⟩
  have hu (c : Circle) : u c ∈ Ico 0 1 := by
    change (0 : ℝ) ≤ (u c : ℝ) ∧ (u c : ℝ) < 1
    have hp := (e (h.symm c)).2
    simp only [zero_add] at hp
    exact hp
  have hr (c : Circle) : pathCircle β c = β (u c) := rfl
  intro c d hcd
  have heq : u c = u d := hβ (hu c) (hu d) (by simpa only [hr] using hcd)
  apply h.symm.injective
  apply e.injective
  have hv := congrArg (fun x : unitInterval => (x : ℝ)) heq
  exact Subtype.ext hv

end CircleMap

/-! ### Closed polygons -/

/-- The closed polyline through `g 0, …, g M = g 0` as a closed path. -/
noncomputable def polyPath (g : ℕ → E2) (M : ℕ) (hM : g M = g 0) : Path (g 0) (g 0) where
  toFun t := polyline g (M * t)
  continuous_toFun := (continuous_polyline g).comp (continuous_const.mul continuous_subtype_val)
  source' := by simp [polyline_zero]
  target' := by simp [polyline_natCast, hM]

theorem range_polyPath (g : ℕ → E2) (M : ℕ) (hM : g M = g 0) (hM0 : 0 < M) :
    range (polyPath g M hM) = polyline g '' Icc 0 M := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨M * t, ⟨mul_nonneg (Nat.cast_nonneg _) t.2.1,
      by nlinarith [t.2.1, t.2.2, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
    refine ⟨⟨s / M, div_nonneg hs.1 hM'.le, (div_le_one hM').2 hs.2⟩, ?_⟩
    show polyline g (M * (s / M)) = polyline g s
    congr 1
    field_simp

theorem polyPath_injOn {g : ℕ → E2} {M : ℕ} (hM : g M = g 0) (hM0 : 0 < M)
    (hg : SegmentCondition g M) : InjOn (polyPath g M hM) (Ico 0 1) := by
  intro t ht t' ht' h
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
  change polyline g (M * t) = polyline g (M * t') at h
  have h1 : (t : ℝ) < 1 := ht.2
  have h2 : (t' : ℝ) < 1 := ht'.2
  have := polyline_injOn_Ico hg ⟨mul_nonneg hM'.le t.2.1, by nlinarith⟩
    ⟨mul_nonneg hM'.le t'.2.1, by nlinarith⟩ h
  exact Subtype.ext (mul_left_cancel₀ hM'.ne' this)

theorem image_polyline_eq (g : ℕ → E2) {M : ℕ} (hM : 0 < M) :
    polyline g '' Icc 0 M = ⋃ i < M, segment ℝ (g i) (g (i + 1)) := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨i, hi, h1, h2⟩ := exists_index hM hs
    exact mem_iUnion₂.2 ⟨i, hi, polyline_mem_segment g i ⟨h1, h2⟩⟩
  · refine iUnion₂_subset fun i hi => ?_
    rw [← image_polyline_Icc]
    refine image_mono fun s hs => ⟨le_trans (Nat.cast_nonneg i) hs.1, ?_⟩
    have : ((i : ℝ) + 1) ≤ M := by exact_mod_cast hi
    linarith [hs.2]

/-- The trace of the closed lattice polygon through the corners `c 0, …, c M`. -/
def polyTrace (c : ℕ → ℤ × ℤ) (M : ℕ) : Set E2 :=
  ⋃ i < M, segment ℝ (mpt (c i)) (mpt (c (i + 1)))

/-- A closed lattice polygon without repeated corner is homeomorphic to the circle and separates
the plane into a bounded and an unbounded component, both with frontier the polygon. -/
theorem jordan_of_polygon {M : ℕ} {c : ℕ → ℤ × ℤ} (hM : 3 ≤ M) (hcM : c M = c 0)
    (hadj : ∀ i < M, (lattice 2).Adj (toV (c i)) (toV (c (i + 1))))
    (hinj : ∀ i j, i ≤ M → j ≤ M → c i = c j → i = j ∨ (i = 0 ∧ j = M) ∨ (i = M ∧ j = 0)) :
    Nonempty (polyTrace c M ≃ₜ Circle) ∧
    ∃ I O : Set E2, IsOpen I ∧ IsOpen O ∧ IsConnected O ∧ IsBounded I ∧ I.Nonempty ∧
      ¬ IsBounded O ∧ Disjoint I O ∧ (polyTrace c M)ᶜ = I ∪ O ∧ frontier I = polyTrace c M ∧
      frontier O = polyTrace c M ∧ ∀ y ∈ I, connectedComponentIn (polyTrace c M)ᶜ y = I := by
  have hM0 : 0 < M := by omega
  have hg0 := segmentCondition_of_chain (c := fun i => toV (c i)) hadj
    (fun i j hi hj h => hinj i j hi hj (toV_injective h)) (Or.inl hM)
  have hg : SegmentCondition (fun i => mpt (c i)) M := by
    have := hg0.map toCorner toCorner_injective
    simpa only [toCorner_lp] using this
  have hgM : (fun i => mpt (c i)) M = (fun i => mpt (c i)) 0 := by simp only [hcM]
  have hβr : range (polyPath (fun i => mpt (c i)) M hgM) = polyTrace c M := by
    rw [range_polyPath _ _ _ hM0, image_polyline_eq _ hM0]
    rfl
  have hβi := polyPath_injOn hgM hM0 hg
  have hfc := continuous_pathCircle (polyPath (fun i => mpt (c i)) M hgM)
  have hfi := injective_pathCircle _ hβi
  have hfr : range (pathCircle (polyPath (fun i => mpt (c i)) M hgM)) = polyTrace c M :=
    (range_pathCircle _).trans hβr
  refine ⟨⟨(Homeomorph.setCongr hfr.symm).trans
    (hfc.isClosedEmbedding hfi).toIsEmbedding.toHomeomorph.symm⟩, ?_⟩
  let r : Metric.sphere (0 : Plane) 1 → Plane := fun t =>
    pathCircle (polyPath (fun i => mpt (c i)) M hgM) (Arcs.spherePlaneHomeoCircle t)
  have hr : Continuous r := hfc.comp Arcs.spherePlaneHomeoCircle.continuous
  have hri : Injective r := hfi.comp Arcs.spherePlaneHomeoCircle.injective
  have hrr : range r = polyTrace c M := by
    rw [← hfr]
    exact Arcs.spherePlaneHomeoCircle.surjective.range_comp
      (pathCircle (polyPath (fun i => mpt (c i)) M hgM))
  obtain ⟨x₁, hx₁, x₀, hx₀, hb, hu, hd, hcover, hf₁, hf₀⟩ := jordan_curve_components r hr hri
  rw [hrr] at hx₁ hx₀ hb hu hd hcover hf₁ hf₀
  have hJo : IsOpen (polyTrace c M)ᶜ := by
    rw [← hrr]
    exact (isCompact_range hr).isClosed.isOpen_compl
  exact ⟨_, _, hJo.connectedComponentIn, hJo.connectedComponentIn,
    isConnected_connectedComponentIn_iff.2 hx₀, hb, ⟨x₁, mem_connectedComponentIn hx₁⟩, hu, hd,
    hcover, hf₁, hf₀, fun y hy => (connectedComponentIn_eq hy).symm⟩

/-- Two closed lattice polygons without common corner have disjoint traces. -/
theorem disjoint_polyTrace {M M' : ℕ} {c c' : ℕ → ℤ × ℤ}
    (hadj : ∀ i < M, (lattice 2).Adj (toV (c i)) (toV (c (i + 1))))
    (hadj' : ∀ j < M', (lattice 2).Adj (toV (c' j)) (toV (c' (j + 1))))
    (hne : ∀ i j, c i ≠ c' j) : Disjoint (polyTrace c M) (polyTrace c' M') := by
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx'
  rw [← toCorner_lp, ← toCorner_lp, ← image_segment] at hxi hxj
  obtain ⟨y, hy, rfl⟩ := hxi
  obtain ⟨y', hy', hyy⟩ := hxj
  rw [toCorner_injective hyy] at hy'
  rcases Rigidity.Proofs.Section5.eq_or_eq_of_mem_segment_inter (hadj i hi) (hadj' j hj) hy hy'
    with h | h | h | h <;> exact hne _ _ (toV_injective h)

variable {S : Set (ℤ × ℤ)}

theorem openCell_subset_compl {J : Set E2} (hJ : J ⊆ bdry S) (c : ℤ × ℤ) : OpenCell c ⊆ Jᶜ := by
  intro q hq hqJ
  obtain ⟨c', -, n', -, h1, h2⟩ := hJ hqJ
  exact add_v_ne c' n' ((eq_of_mem_openCell hq h2).trans (eq_of_mem_openCell hq h1).symm)

theorem isCompact_cell (c : ℤ × ℤ) : IsCompact (Cell c) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_cell c)
    ((Metric.isBounded_closedBall (x := ctr c) (r := 1)).subset fun p hp => ?_)
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  obtain ⟨h0, h1⟩ := hp
  rw [abs_le] at h0 h1
  calc Real.sqrt _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by
        simp only [ctr, pt_zero, pt_one, Real.dist_eq, sq_abs]
        nlinarith)
    _ = 1 := Real.sqrt_one

theorem finite_ctr_mem {I : Set E2} (hI : IsBounded I) : {c : ℤ × ℤ | ctr c ∈ I}.Finite := by
  obtain ⟨R, hR⟩ := hI.subset_closedBall 0
  refine ((Set.finite_Icc (-⌈2 * R⌉) ⌈2 * R⌉).prod
    (Set.finite_Icc (-⌈2 * R⌉) ⌈2 * R⌉)).subset ?_
  rintro ⟨c1, c2⟩ hc
  have hb : dist (ctr (c1, c2)) 0 ≤ R := hR hc
  have h0 := (PiLp.dist_apply_le (ctr (c1, c2)) 0 0).trans hb
  have h1 := (PiLp.dist_apply_le (ctr (c1, c2)) 0 1).trans hb
  simp only [ctr, pt_zero, pt_one, Real.dist_eq, PiLp.zero_apply, sub_zero] at h0 h1
  rw [abs_le] at h0 h1
  have k := Int.le_ceil (2 * R)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact_mod_cast (show ((-⌈2 * R⌉ : ℤ) : ℝ) ≤ c1 by push_cast; linarith)
  · exact_mod_cast (show (c1 : ℝ) ≤ ((⌈2 * R⌉ : ℤ) : ℝ) by linarith)
  · exact_mod_cast (show ((-⌈2 * R⌉ : ℤ) : ℝ) ≤ c2 by push_cast; linarith)
  · exact_mod_cast (show (c2 : ℝ) ≤ ((⌈2 * R⌉ : ℤ) : ℝ) by linarith)

/-- A nonempty compact set `K` disjoint from `Ω`, open in the complement of `Ω`, separates the
complement of `σ(Ω)` in `S²`. -/
theorem not_isPreconnected_compl {σ : E2 → S2} (hσ : IsOpenEmbedding σ)
    (hσr : range σ = {northPole}ᶜ) {Ω K W : Set E2} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKΩ : Disjoint K Ω) (hW : IsOpen W) (hKW : K ⊆ W) (hWK : W \ Ω ⊆ K) :
    ¬ IsPreconnected (σ '' Ω)ᶜ := by
  intro hpre
  have hN : ∀ q : E2, σ q ≠ northPole := fun q hq => by
    have : σ q ∈ range σ := mem_range_self q
    rw [hσr, hq] at this
    exact this rfl
  have hu : IsOpen (σ '' W) := hσ.isOpenMap W hW
  have hv : IsOpen (σ '' K)ᶜ := ((hK.image hσ.continuous).isClosed).isOpen_compl
  have hcov : (σ '' Ω)ᶜ ⊆ σ '' W ∪ (σ '' K)ᶜ := by
    intro y _
    by_cases hyK : y ∈ σ '' K
    · obtain ⟨k, hk, rfl⟩ := hyK
      exact Or.inl ⟨k, hKW hk, rfl⟩
    · exact Or.inr hyK
  have hdis : (σ '' Ω)ᶜ ∩ (σ '' W ∩ (σ '' K)ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro y ⟨hyΩ, ⟨q, hqW, rfl⟩, hqK⟩
    exact hqK ⟨q, hWK ⟨hqW, fun hqΩ => hyΩ ⟨q, hqΩ, rfl⟩⟩, rfl⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hpre _ _ hu hv hcov hdis with h | h
  · obtain ⟨q, -, hq⟩ := h (show northPole ∈ (σ '' Ω)ᶜ from fun ⟨q, _, hq⟩ => hN q hq)
    exact hN q hq
  · obtain ⟨k, hk⟩ := hKne
    have hk' : σ k ∈ (σ '' Ω)ᶜ := by
      rintro ⟨q, hq, hqk⟩
      exact Set.disjoint_left.1 hKΩ hk (hσ.injective hqk ▸ hq)
    exact h hk' ⟨k, hk, rfl⟩

/-- The interior of the union lies inside every polygon of boundary sides. -/
theorem subset_inside (hS : S.Finite) (hNC : NoChecker S) {σ : E2 → S2}
    (hσ : IsOpenEmbedding σ) (hσr : range σ = {northPole}ᶜ)
    (hconn : IsPreconnected (interior (cellUnion S)))
    (hcompl : IsPreconnected (σ '' interior (cellUnion S))ᶜ) {J I O : Set E2} (hJ : J ⊆ bdry S)
    (hIo : IsOpen I) (hOo : IsOpen O) (hIb : IsBounded I) (hIne : I.Nonempty)
    (hIO : Disjoint I O) (hcover : Jᶜ = I ∪ O)
    (hIc : ∀ y ∈ I, connectedComponentIn Jᶜ y = I) : interior (cellUnion S) ⊆ I := by
  have hΩJ : interior (cellUnion S) ⊆ Jᶜ := fun q hq hqJ => by
    have h1 := hJ hqJ
    rw [← frontier_interior_cellUnion hS] at h1
    have h2 : q ∈ interior (cellUnion S) ∩ frontier (interior (cellUnion S)) := ⟨hq, h1⟩
    rw [isOpen_interior.inter_frontier_eq] at h2
    exact h2
  rcases hconn.subset_or_subset hIo hOo hIO (hcover ▸ hΩJ) with h | hO
  · exact h
  exfalso
  have hTfin : {c : ℤ × ℤ | c ∉ S ∧ ctr c ∈ I}.Finite :=
    (finite_ctr_mem hIb).subset fun c hc => hc.2
  have hKc : IsCompact (⋃ c ∈ {c : ℤ × ℤ | c ∉ S ∧ ctr c ∈ I}, Cell c) :=
    hTfin.isCompact_biUnion fun c _ => isCompact_cell c
  obtain ⟨y, hy⟩ := hIne
  obtain ⟨c₀, hc₀⟩ := exists_mem_cell y
  have hc₀I : ctr c₀ ∈ I := by
    obtain ⟨z, hzI, hzc⟩ := mem_closure_iff.1 (mem_closure_openCell hc₀) I hIo hy
    have hsub : OpenCell c₀ ⊆ connectedComponentIn Jᶜ z :=
      (isPreconnected_openCell c₀).subset_connectedComponentIn hzc (openCell_subset_compl hJ c₀)
    rw [hIc z hzI] at hsub
    exact hsub (ctr_mem_openCell c₀)
  have hc₀S : c₀ ∉ S := fun h =>
    Set.disjoint_left.1 hIO hc₀I (hO (openCell_subset_interior h (ctr_mem_openCell c₀)))
  have hKne : (⋃ c ∈ {c : ℤ × ℤ | c ∉ S ∧ ctr c ∈ I}, Cell c).Nonempty :=
    ⟨ctr c₀, mem_iUnion₂.2 ⟨c₀, ⟨hc₀S, hc₀I⟩, openCell_subset_cell c₀ (ctr_mem_openCell c₀)⟩⟩
  have hKΩ : Disjoint (⋃ c ∈ {c : ℤ × ℤ | c ∉ S ∧ ctr c ∈ I}, Cell c)
      (interior (cellUnion S)) := Set.disjoint_left.2 fun q hq hqΩ => by
    obtain ⟨c, hc, hqc⟩ := mem_iUnion₂.1 hq
    exact notMem_interior hc.1 hqc hqΩ
  choose δ hδ hball using exists_ball_cell_mem
  refine not_isPreconnected_compl hσ hσr hKc hKne hKΩ
    (isOpen_biUnion fun p _ => Metric.isOpen_ball (x := p) (ε := δ p))
    (fun p hp => mem_iUnion₂.2 ⟨p, hp, Metric.mem_ball_self (hδ p)⟩) ?_ hcompl
  rintro q ⟨hqW, hqΩ⟩
  obtain ⟨p, hpK, hqp⟩ := mem_iUnion₂.1 hqW
  obtain ⟨c, hcT, hpc⟩ := mem_iUnion₂.1 hpK
  have hnot : ¬ ∀ d, q ∈ Cell d → d ∈ S := fun h => hqΩ (mem_interior_cellUnion.2 h)
  push Not at hnot
  obtain ⟨d, hqd, hdS⟩ := hnot
  have hpd := hball p q hqp d hqd
  have hdI : ctr d ∈ I := by
    have := ctr_mem_of_cells hNC hJ (iff_of_false hcT.1 hdS) hpc hpd
    rwa [hIc _ hcT.2] at this
  exact mem_iUnion₂.2 ⟨d, ⟨hdS, hdI⟩, hqd⟩

/-- If `Ω` lies inside the Jordan curve `Ja` and `Jb` lies in the closure of `Ω`, then the outside
of `Ja` lies in the outside of `Jb`. -/
theorem outside_subset {Ω Ja Jb Ia Ib Oa Ob : Set E2} (hJb : Jb ⊆ closure Ω)
    (hJ : Disjoint Ja Jb) (hΩ : Ω ⊆ Ia) (hfa : frontier Ia = Ja) (hda : Disjoint Ia Oa)
    (hOa : IsPreconnected Oa) (hOab : ¬ IsBounded Oa) (hIb : IsOpen Ib) (hOb : IsOpen Ob)
    (hdb : Disjoint Ib Ob) (hcb : Jbᶜ = Ib ∪ Ob) (hIbb : IsBounded Ib) : Oa ⊆ Ob := by
  have h1 : Jb ⊆ Ia := fun x hx => by
    have : x ∈ closure Ia := closure_mono hΩ (hJb hx)
    rw [closure_eq_self_union_frontier, hfa] at this
    rcases this with h | h
    · exact h
    · exact absurd hx (Set.disjoint_left.1 hJ h)
  have h2 : Oa ⊆ Jbᶜ := fun x hx hxb => Set.disjoint_left.1 hda (h1 hxb) hx
  rcases hOa.subset_or_subset hIb hOb hdb (hcb ▸ h2) with h | h
  · exact absurd (hIbb.subset h) hOab
  · exact h

end Rigidity.Proofs.Topology.Polyomino
