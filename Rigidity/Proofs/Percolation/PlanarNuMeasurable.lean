import Rigidity.Proofs.Percolation.PlanarClusterTransport
import Rigidity.Percolation.TriadicStoppingMeasurable
import Rigidity.Percolation.TriadicGoodCubes

/-!
# Measurability of the planar partition and of `ν`

The partition event, resolution of a fixed triadic cube and the quantity
`ω ↦ 1{the partition event holds and V is resolved} · ν(V, p)` are measurable.

On the partition event, membership of a vertex `x` of a resolved cube `V` in the cluster `C_*(V)`
has an anchor-free form: some partition cube containing `x` carries a long open path inside it
which is joined to `x` inside `V`. This uses that the anchor of a meshed cube is joined to every
long open path of the cube. Since `ν(V, p)` depends only on the cluster and on the open edges
between its vertices, the quantity above is a function of countably many measurable events.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A function which is constant on the fibres of a map to a countable type with measurable fibres
is measurable. -/
theorem measurable_of_fiber_const {Ω β T : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [Countable T] (φ : Ω → T) (hφ : ∀ t, MeasurableSet (φ ⁻¹' {t})) {g : Ω → β}
    (hg : ∀ ω ω', φ ω = φ ω' → g ω = g ω') : Measurable g := by
  intro s _
  have heq : g ⁻¹' s = ⋃ t ∈ φ '' (g ⁻¹' s), φ ⁻¹' {t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · intro h
      exact ⟨φ ω, ⟨ω, h, rfl⟩, rfl⟩
    · rintro ⟨t, ⟨ω', h', rfl⟩, h⟩
      rw [hg ω ω' h]
      exact h'
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable _) fun t _ => hφ t

/-- The event that a finite filter of a fixed finite set equals a given finite set is measurable
when the filtering predicate is measurable at each point. -/
theorem measurableSet_filter_eq {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (S C : Finset α) {q : Ω → α → Prop} (hq : ∀ x, Measurable fun ω => q ω x) :
    MeasurableSet {ω | S.filter (q ω) = C} := by
  have heq : {ω | S.filter (q ω) = C} = {ω | ∀ x, (x ∈ S ∧ q ω x) ↔ x ∈ C} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.ext_iff, Finset.mem_filter]
  rw [heq]
  exact measurableSet_setOf.2 (Measurable.forall fun x =>
    (measurable_const.and (hq x)).iff measurable_const)

/-- Membership of a triadic cube in the planar partition is a measurable event. -/
theorem measurable_isMaximalStopping_planarGoodCubes (Q : TriadicCube 2) :
    Measurable fun ω : Configuration 2 => Q.IsMaximalStopping (planarGoodCubes ω) :=
  measurableSet_setOf.1 (TriadicCube.measurableSet_isMaximalStopping (fun ω => planarGoodCubes ω)
    (fun T => TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
      measurableSet_mem_planarMeshedFamily T) Q)

/-- The planar partition event is measurable. -/
theorem measurableSet_planarPartitionEvent :
    MeasurableSet {ω : Configuration 2 | PlanarPartitionEvent ω} := by
  have hM := measurable_isMaximalStopping_planarGoodCubes
  unfold PlanarPartitionEvent ExistsUnique
  exact measurableSet_setOf.2 (Measurable.forall fun x => Measurable.exists fun Q =>
    (measurable_const.and (hM Q)).and (Measurable.forall fun R =>
      (measurable_const.and (hM R)).imp measurable_const))

/-- On the partition event, resolution of a cube in terms of the partition cubes containing its
vertices. -/
theorem planarResolved_iff (hP : PlanarPartitionEvent ω) (V : TriadicCube 2) :
    PlanarResolved ω V ↔ ∀ z ∈ V.vertices, ∀ Q : TriadicCube 2, z ∈ Q.vertices →
      Q.IsMaximalStopping (planarGoodCubes ω) → Q.scale ≤ V.scale := by
  constructor
  · intro hV z hz Q hzQ hQ
    rw [← planarPartCube_eq hP hzQ hQ]
    exact hV z hz
  · intro h z hz
    exact h z hz _ (planarPartCube_spec hP z).1 (planarPartCube_spec hP z).2

/-- The event that the partition event holds and a fixed cube is resolved is measurable. -/
theorem measurableSet_planarPartitionEvent_resolved (V : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | PlanarPartitionEvent ω ∧ PlanarResolved ω V} := by
  have heq : {ω : Configuration 2 | PlanarPartitionEvent ω ∧ PlanarResolved ω V} =
      {ω | PlanarPartitionEvent ω} ∩ {ω | ∀ z ∈ V.vertices, ∀ Q : TriadicCube 2, z ∈ Q.vertices →
        Q.IsMaximalStopping (planarGoodCubes ω) → Q.scale ≤ V.scale} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    exact ⟨fun h => ⟨h.1, (planarResolved_iff h.1 V).1 h.2⟩,
      fun h => ⟨h.1, (planarResolved_iff h.1 V).2 h.2⟩⟩
  rw [heq]
  exact measurableSet_planarPartitionEvent.inter (measurableSet_setOf.2 (Measurable.forall fun z =>
    measurable_const.imp (Measurable.forall fun Q => measurable_const.imp
      ((measurable_isMaximalStopping_planarGoodCubes Q).imp measurable_const))))

/-- The anchor-free link of a vertex to the cluster of a cube: some partition cube containing the
vertex carries a long open path inside it which is joined to the vertex inside the cube. -/
def PlanarClusterLink (ω : Configuration 2) (V : TriadicCube 2) (x : Vertex 2) : Prop :=
  ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω) ∧
    ∃ a b : Vertex 2, ∃ k : Fin 2, ReachIn ω Q.vertices a b ∧
      a k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ b k ∧ ReachIn ω V.vertices x a

theorem measurable_planarClusterLink (V : TriadicCube 2) (x : Vertex 2) :
    Measurable fun ω : Configuration 2 => PlanarClusterLink ω V x := by
  unfold PlanarClusterLink
  exact Measurable.exists fun Q => measurable_const.and
    ((measurable_isMaximalStopping_planarGoodCubes Q).and (Measurable.exists fun a =>
      Measurable.exists fun b => Measurable.exists fun k =>
        (measurableSet_setOf.1 (measurableSet_reachIn _ a b)).and
          (measurable_const.and (measurableSet_setOf.1 (measurableSet_reachIn _ x a)))))

/-- **Anchor-free cluster membership.** On the partition event, a vertex belongs to the cluster
of a resolved cube if and only if it lies in the cube and is linked to it. -/
theorem mem_planarCubeCluster_iff_link (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) (x : Vertex 2) :
    x ∈ planarCubeCluster ω V ↔ x ∈ V.vertices ∧ PlanarClusterLink ω V x := by
  constructor
  · rintro ⟨hx, hreach⟩
    set Q := planarPartCube ω x
    have hQV := planarPartCube_subset_of_resolved hP hV hx
    obtain ⟨a, b, k, hab, hlong⟩ := Q.exists_long_reachIn (planarPartCube_meshed hP x).1
      (planarPartCube_large hP x)
    have hA := (Q.planarAnchor_spec (planarPartCube_meshed hP x).1
      (planarPartCube_large hP x)).2.1 a b k hab hlong
    exact ⟨hx, Q, (planarPartCube_spec hP x).1, (planarPartCube_spec hP x).2, a, b, k, hab, hlong,
      hreach.trans (hA.mono hQV)⟩
  · rintro ⟨hx, Q, hxQ, hQ, a, b, k, hab, hlong, hxa⟩
    have hQx := planarPartCube_eq hP hxQ hQ
    have hQV := planarPartCube_subset_of_resolved hP hV hx
    rw [hQx] at hQV
    have hA := (Q.planarAnchor_spec (hQx ▸ (planarPartCube_meshed hP x).1)
      (hQx ▸ planarPartCube_large hP x)).2.1 a b k hab hlong
    refine ⟨hx, ?_⟩
    rw [hQx]
    exact hxa.trans (hA.mono hQV).symm

/-- **Measurability of `ν`.** The quantity `1{partition event, V resolved} · ν(V, p)` is
measurable. -/
theorem measurable_planarNu_indicator (V : TriadicCube 2) (p : Fin 2 → ℝ) :
    Measurable fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (planarNu ω V p)
      else 0 := by
  set S := V.toIntegerCube.vertices
  let φ : Configuration 2 → Option (Finset (Vertex 2) × Finset (Vertex 2 × Vertex 2)) :=
    fun ω => if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      some (S.filter (PlanarClusterLink ω V), (S ×ˢ S).filter fun e => (openGraph ω).Adj e.1 e.2)
    else none
  have hE := measurableSet_planarPartitionEvent_resolved V
  refine measurable_of_fiber_const φ (fun t => ?_) (fun ω ω' h => ?_)
  · rcases t with _ | ⟨C, E⟩
    · have heq : φ ⁻¹' {none} =
          {ω | PlanarPartitionEvent ω ∧ PlanarResolved ω V}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h <;> simp [h]
      rw [heq]
      exact hE.compl
    · have heq : φ ⁻¹' {some (C, E)} =
          {ω | PlanarPartitionEvent ω ∧ PlanarResolved ω V} ∩
            ({ω | S.filter (PlanarClusterLink ω V) = C} ∩
              {ω | (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2) = E}) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h
        · simp only [Option.some.injEq, Prod.mk.injEq, h, true_and]
        · simp only [h, false_and]
      rw [heq]
      exact hE.inter ((measurableSet_filter_eq S C (measurable_planarClusterLink V)).inter
        (measurableSet_filter_eq (S ×ˢ S) E fun e =>
          measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)))
  · by_cases hω : PlanarPartitionEvent ω ∧ PlanarResolved ω V
    · have hω' : PlanarPartitionEvent ω' ∧ PlanarResolved ω' V := by
        by_contra hn
        simp only [φ, if_pos hω, if_neg hn, reduceCtorEq] at h
      simp only [φ, if_pos hω, if_pos hω', Option.some.injEq, Prod.mk.injEq] at h
      rw [if_pos hω, if_pos hω']
      congr 1
      refine (planarNu_eq_of_cluster_eq (fun x => ?_) (fun x hx y hy => ?_) p).symm
      · rw [mem_clusterVertices, mem_clusterVertices, mem_planarCubeCluster_iff_link hω'.1 hω'.2,
          mem_planarCubeCluster_iff_link hω.1 hω.2, ← V.mem_toIntegerCube_vertices]
        have h1 := Finset.ext_iff.1 h.1 x
        simp only [Finset.mem_filter] at h1
        exact h1.symm
      · have hx' := (mem_planarCubeCluster_iff_link hω.1 hω.2 x).1 (mem_clusterVertices.1 hx)
        have hy' := (mem_planarCubeCluster_iff_link hω.1 hω.2 y).1 (mem_clusterVertices.1 hy)
        have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx'.1
        have hyS : y ∈ S := (V.mem_toIntegerCube_vertices y).2 hy'.1
        have h2 := Finset.ext_iff.1 h.2 (x, y)
        simp only [Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
        exact h2.symm
    · have hω' : ¬ (PlanarPartitionEvent ω' ∧ PlanarResolved ω' V) := by
        intro hn
        simp only [φ, if_neg hω, if_pos hn, reduceCtorEq] at h
      rw [if_neg hω, if_neg hω']

end Rigidity.Percolation
