import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Proofs.Percolation.PlanarWindows
import Rigidity.Proofs.Percolation.PlanarMuMeasurable
import Rigidity.Percolation.TriadicStableAncestors
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw
import LatticeProb.Prob.Percolation.OpenComponentTranslation

/-!
# Anchors of the translated planar partitions

Dario's §5 uses, besides the partition `𝒫` of good cubes, its translates `𝒫_y = y + 𝒫(τ_{-y})`:
the partition computed from the configuration seen from `y`, moved back by `y`. For the planar
partition of main (`planarPartCube`, anchors `planarCoarseAnchor`) this file proves:

* on the partition event, the anchors of the partition cubes of all vertices lie in one infinite
  open component (`reachable_planarCoarseAnchor`, `infinite_planarCoarseAnchor`), as for the
  partition of Armstrong and Dario (Corollary 2.10 there);
* the anchor, set to the vertex itself off the partition event (`guardAnchor`), is a measurable
  function of the configuration (`measurable_guardAnchor`);
* the anchor `shiftedAnchor y ω z = y + guardAnchor (τ_{-y} ω) (z - y)` of `𝒫_y` is measurable,
  moves with translations of the configuration (`shiftedAnchor_translation`) and lies in the
  infinite cluster when the partition event holds for `τ_{-y} ω`.

Here `τ_y = configurationTranslation y`, so that `τ_{-y} ω` is the configuration seen from `y`.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Section5
open scoped Classical

variable {ω : Configuration 2}

/-- A triadic cube containing two given triadic cubes, of scale at least that of the first. -/
theorem exists_triadicCube_superset (Q Q' : TriadicCube 2) {x y : Vertex 2}
    (hx : x ∈ Q.vertices) (hy : y ∈ Q'.vertices) :
    ∃ U : TriadicCube 2, Q.scale ≤ U.scale ∧ Q.vertices ⊆ U.vertices ∧
      Q'.vertices ⊆ U.vertices := by
  set M : ℕ := Q.scale + Q'.scale + (x 0).natAbs + (x 1).natAbs + (y 0).natAbs + (y 1).natAbs + 1
    with hMdef
  have hM : (2 * M : ℤ) < (3 : ℤ) ^ M := by
    have h := one_add_mul_le_pow (by norm_num : (-2 : ℤ) ≤ 2) M
    norm_num at h
    linarith
  set U : TriadicCube 2 := ⟨M, 0⟩
  have hmem : ∀ v : Vertex 2, (v 0).natAbs + (v 1).natAbs < M → v ∈ U.vertices := by
    intro v hv i
    change |2 * (v i - (3 : ℤ) ^ M * (0 : Fin 2 → ℤ) i)| < (3 : ℤ) ^ M
    rw [Pi.zero_apply, mul_zero, sub_zero, abs_mul, abs_two]
    have hvi : |v i| < (M : ℤ) := by
      fin_cases i
      · rw [Int.abs_eq_natAbs]; simp only [Fin.zero_eta, Fin.isValue]; omega
      · rw [Int.abs_eq_natAbs]; simp only [Fin.mk_one, Fin.isValue]; omega
    linarith
  have hxU : x ∈ U.vertices := hmem x (by omega)
  have hyU : y ∈ U.vertices := hmem y (by omega)
  have hQU : Q.scale ≤ U.scale := by change Q.scale ≤ M; omega
  have hQ'U : Q'.scale ≤ U.scale := by change Q'.scale ≤ M; omega
  refine ⟨U, hQU, ?_, ?_⟩
  · rw [TriadicCube.eq_ancestor_of_mem hx hxU hQU]
    exact Q.vertices_subset_ancestor _
  · rw [TriadicCube.eq_ancestor_of_mem hy hyU hQ'U]
    exact Q'.vertices_subset_ancestor _

/-- Lattice neighbours differ by at most one in every coordinate. -/
theorem near_of_nearestNeighbor_adj {a b : Vertex 2} (h : (nearestNeighborGraph 2).Adj a b) :
    ∀ i, |a i - b i| ≤ 1 := by
  have h' : ∃ j : Fin 2, b = a + LatticeProb.unit j ∨ a = b + LatticeProb.unit j := h
  obtain ⟨j, hj | hj⟩ := h' <;> intro i <;> subst hj <;>
    simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply] <;> split_ifs <;> simp

/-- The anchors of the partition cubes of two lattice neighbours are joined by an open path. -/
theorem reachable_planarCoarseAnchor_of_near (hP : PlanarPartitionEvent ω) {x y : Vertex 2}
    (hnear : ∀ i, |x i - y i| ≤ 1) :
    (openGraph ω).Reachable (planarCoarseAnchor ω x) (planarCoarseAnchor ω y) := by
  obtain ⟨hsc1, hsc2⟩ := planarPartCube_scales_close hP hnear
  rcases le_total (planarPartCube ω x).scale (planarPartCube ω y).scale with h | h
  · obtain ⟨U, hU, hQ, hQ'⟩ := exists_triadicCube_superset (planarPartCube ω x)
      (planarPartCube ω y) (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1
    obtain ⟨W, -⟩ := TriadicCube.reachIn_planarAnchor_pairWindow (planarPartCube_meshed hP x).1
      (planarPartCube_meshed hP y).1 (planarPartCube_large hP x) hU hQ hQ' h hsc2
      (planarPartCube_spec hP x).1 (planarPartCube_spec hP y).1 hnear
    exact ⟨W⟩
  · have hnear' : ∀ i, |y i - x i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hnear i
    obtain ⟨U, hU, hQ, hQ'⟩ := exists_triadicCube_superset (planarPartCube ω y)
      (planarPartCube ω x) (planarPartCube_spec hP y).1 (planarPartCube_spec hP x).1
    obtain ⟨W, -⟩ := TriadicCube.reachIn_planarAnchor_pairWindow (planarPartCube_meshed hP y).1
      (planarPartCube_meshed hP x).1 (planarPartCube_large hP y) hU hQ hQ' h hsc1
      (planarPartCube_spec hP y).1 (planarPartCube_spec hP x).1 hnear'
    exact ⟨W.reverse⟩

/-- **All anchors lie in one open component** (Armstrong and Dario, Corollary 2.10, for the
planar partition). -/
theorem reachable_planarCoarseAnchor (hP : PlanarPartitionEvent ω) (x y : Vertex 2) :
    (openGraph ω).Reachable (planarCoarseAnchor ω x) (planarCoarseAnchor ω y) := by
  obtain ⟨W⟩ := (LatticeProb.Graph.Zd.latticeConnected 2).preconnected x y
  induction W with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab _ ih =>
      exact (reachable_planarCoarseAnchor_of_near hP (near_of_nearestNeighbor_adj hab)).trans ih

/-- The anchor of a partition cube lies in the cube. -/
theorem planarCoarseAnchor_mem (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    planarCoarseAnchor ω x ∈ (planarPartCube ω x).vertices :=
  (TriadicCube.planarAnchor_spec (planarPartCube_meshed hP x).1 (planarPartCube_large hP x)).1

/-- The open component of the anchors is infinite. -/
theorem infinite_planarCoarseAnchor (hP : PlanarPartitionEvent ω) (x : Vertex 2) :
    ω ∈ infiniteComponentEvent (planarCoarseAnchor ω x) := by
  change ((openGraph ω).connectedComponentMk (planarCoarseAnchor ω x)).supp.Infinite
  intro hfin
  apply Set.infinite_univ (α := Vertex 2)
  have hcover : (Set.univ : Set (Vertex 2)) ⊆
      ⋃ a ∈ ((openGraph ω).connectedComponentMk (planarCoarseAnchor ω x)).supp,
        (planarPartCube ω a).vertices := by
    intro y _
    simp only [Set.mem_iUnion]
    refine ⟨planarCoarseAnchor ω y, ?_, ?_⟩
    · rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
      exact (reachable_planarCoarseAnchor hP x y).symm
    · rw [planarPartCube_eq_of_mem hP (planarCoarseAnchor_mem hP y)]
      exact (planarPartCube_spec hP y).1
  exact (hfin.biUnion fun a _ => (planarPartCube ω a).toIntegerCube.vertices.finite_toSet.subset
    fun x hx => Finset.mem_coe.2 (((planarPartCube ω a).mem_toIntegerCube_vertices x).2 hx)).subset
    hcover

/-- The anchor of the partition cube, set to the vertex itself off the partition event. -/
noncomputable def guardAnchor (ω : Configuration 2) (z : Vertex 2) : Vertex 2 :=
  if PlanarPartitionEvent ω then planarCoarseAnchor ω z else z

theorem guardAnchor_of_event (hP : PlanarPartitionEvent ω) (z : Vertex 2) :
    guardAnchor ω z = planarCoarseAnchor ω z := if_pos hP

/-- **The anchor is measurable**: on the partition event it is determined by the partition cube
and the finite set of displacements with the anchor property. -/
theorem measurable_guardAnchor (z : Vertex 2) : Measurable fun ω => guardAnchor ω z := by
  let filt : Configuration 2 → TriadicCube 2 → Finset (Vertex 2) := fun ω Q =>
    Q.displacements.filter fun e => Q.IsPlanarAnchor ω (Q.center + e)
  let φ : Configuration 2 → Option (TriadicCube 2 × Finset (Vertex 2)) := fun ω =>
    if PlanarPartitionEvent ω then some (planarPartCube ω z, filt ω (planarPartCube ω z))
    else none
  have hφ : ∀ t, MeasurableSet (φ ⁻¹' {t}) := by
    rintro (_ | ⟨Q, F⟩)
    · have : φ ⁻¹' {none} = {ω | PlanarPartitionEvent ω}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq, φ]
        split_ifs with h <;> simp [h]
      rw [this]
      exact measurableSet_planarPartitionEvent.compl
    · have : φ ⁻¹' {some (Q, F)} = {ω | PlanarPartitionEvent ω} ∩
          {ω | z ∈ Q.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω)} ∩ {ω | filt ω Q = F} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq, φ]
        constructor
        · intro h
          split_ifs at h with hP
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          refine ⟨⟨hP, ?_⟩, ?_⟩
          · rw [← h1]; exact planarPartCube_spec hP z
          · rw [← h1]; exact h2
        · rintro ⟨⟨hP, hz, hQ⟩, hF⟩
          rw [if_pos hP, planarPartCube_eq hP hz hQ, hF]
      rw [this]
      refine (measurableSet_planarPartitionEvent.inter (measurableSet_setOf.2
        (measurable_const.and (measurable_isMaximalStopping_planarGoodCubes Q)))).inter ?_
      exact measurableSet_filter_eq _ _ fun e => measurable_isPlanarAnchor Q (Q.center + e)
  refine measurable_of_fiber_const φ hφ fun ω ω' h => ?_
  by_cases hP : PlanarPartitionEvent ω
  · have hP' : PlanarPartitionEvent ω' := by
      by_contra hP'
      simp only [φ, if_pos hP, if_neg hP'] at h
      exact Option.some_ne_none _ h
    simp only [φ, if_pos hP, if_pos hP', Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [guardAnchor_of_event hP, guardAnchor_of_event hP']
    unfold planarCoarseAnchor
    rw [h1]
    refine planarAnchor_eq_of_filter_eq ?_ ?_ ?_
    · rw [← h1]; exact ⟨(planarPartCube_meshed hP z).1, planarPartCube_large hP z⟩
    · exact ⟨(planarPartCube_meshed hP' z).1, planarPartCube_large hP' z⟩
    · have := h2
      rw [h1] at this
      exact this
  · have hP' : ¬ PlanarPartitionEvent ω' := by
      intro hP'
      simp only [φ, if_neg hP, if_pos hP'] at h
      exact Option.some_ne_none _ h.symm
    unfold guardAnchor
    rw [if_neg hP, if_neg hP']

/-- The anchor of the translated partition `𝒫_y`. -/
noncomputable def shiftedAnchor (y : Vertex 2) (ω : Configuration 2) (z : Vertex 2) : Vertex 2 :=
  y + guardAnchor (configurationTranslation (-y) ω) (z - y)

theorem measurable_configurationTranslation (y : Vertex 2) :
    Measurable (configurationTranslation y : Configuration 2 → Configuration 2) :=
  (configurationTranslationMeasurableEquiv y).measurable

theorem measurable_shiftedAnchor (y z : Vertex 2) : Measurable fun ω => shiftedAnchor y ω z :=
  (measurable_of_countable fun v : Vertex 2 => y + v).comp
    ((measurable_guardAnchor (z - y)).comp (measurable_configurationTranslation (-y)))

theorem shiftedAnchor_zero (ω : Configuration 2) (z : Vertex 2) :
    shiftedAnchor 0 ω z = guardAnchor ω z := by
  simp [shiftedAnchor, configurationTranslation_zero]

/-- **The translated partitions move with the configuration**: `𝒫_{y + y'}(τ_{y'} ω) = y' + 𝒫_y(ω)`
at the level of anchors. -/
theorem shiftedAnchor_translation (y y' : Vertex 2) (ω : Configuration 2) (v : Vertex 2) :
    shiftedAnchor (y + y') (configurationTranslation y' ω) (v + y') = shiftedAnchor y ω v + y' := by
  unfold shiftedAnchor
  rw [configurationTranslation_add, show -(y + y') + y' = -y by abel,
    show v + y' - (y + y') = v - y by abel]
  abel

/-- Translating a configuration moves infinite components. -/
theorem mem_infiniteComponentEvent_translation (z : Vertex 2) {ω : Configuration 2} {a : Vertex 2}
    (ha : ω ∈ infiniteComponentEvent a) :
    configurationTranslation z ω ∈ infiniteComponentEvent (a + z) := by
  have h := (openComponentTranslation_infinite_iff z ((openGraph ω).connectedComponentMk a)).2 ha
  rw [openComponentTranslation_mk] at h
  exact h

/-- On the partition event of `τ_{-y} ω`, the anchors of `𝒫_y` lie in an infinite component. -/
theorem infinite_shiftedAnchor {y : Vertex 2} (hP : PlanarPartitionEvent (configurationTranslation (-y) ω))
    (z : Vertex 2) : ω ∈ infiniteComponentEvent (shiftedAnchor y ω z) := by
  have h := mem_infiniteComponentEvent_translation y (infinite_planarCoarseAnchor hP (z - y))
  rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero] at h
  unfold shiftedAnchor
  rw [guardAnchor_of_event hP, add_comm]
  exact h

/-- The partition event holds almost surely for every translate of the configuration. -/
theorem ae_planarPartitionEvent_translation {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (y : Vertex 2) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, PlanarPartitionEvent (configurationTranslation y ω) :=
  (measurePreserving_configurationTranslation p y).quasiMeasurePreserving.ae
    (ae_planarPartitionEvent hpc)

end Rigidity.Corrector
