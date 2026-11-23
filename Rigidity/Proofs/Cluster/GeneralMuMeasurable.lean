import Rigidity.Proofs.Cluster.GeneralMuLocality
import Rigidity.Proofs.Partition.Measurability
import Rigidity.Proofs.Percolation.PlanarNuMeasurable

/-!
# Measurability of `μ` on resolved cubes in every dimension

On the partition event, a triadic cube `V` is resolved when the partition cubes of its vertices
have scale at most that of `V`; this is a measurable event, since the partition cube of a fixed
vertex is a measurable function on the partition event. The quantity `μ(V, q)` depends only on the
open edges inside `V` and the anchors of the partition cubes of the vertices of `V`
(`cubeMu_eq_of_adj_iff_of_anchor_eq`), which take countably many values with measurable fibres.
Hence `1{P, V res} (-μ(V, q))` is measurable.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The event that the partition exists and resolves `V` is measurable. -/
theorem measurableSet_partitionEvent_resolved (V : TriadicCube d) :
    MeasurableSet {ω : Configuration d | PartitionEvent ω ∧ PartitionResolved ω V} := by
  have heq : {ω : Configuration d | PartitionEvent ω ∧ PartitionResolved ω V} =
      {ω | PartitionEvent ω} ∩ ⋂ z : ↥V.toIntegerCube.vertices,
        ⋃ Q ∈ {Q : TriadicCube d | Q.scale ≤ V.scale},
          {ω | PartitionEvent ω ∧ partitionCube ω z.1 = Q} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion,
      exists_prop]
    constructor
    · rintro ⟨hP, hres⟩
      refine ⟨hP, fun z => ⟨partitionCube ω z.1, hres z.1 ?_, hP, rfl⟩⟩
      exact (V.mem_toIntegerCube_vertices z.1).1 z.2
    · rintro ⟨hP, h⟩
      refine ⟨hP, fun z hz => ?_⟩
      obtain ⟨Q, hQ, -, hzQ⟩ := h ⟨z, (V.mem_toIntegerCube_vertices z).2 hz⟩
      rw [hzQ]
      exact hQ
  rw [heq]
  exact measurableSet_partitionEvent.inter (MeasurableSet.iInter fun z =>
    MeasurableSet.biUnion (Set.to_countable _) fun Q _ => measurableSet_partitionCube_eq z.1 Q)

/-- **Measurability of `μ`.** The quantity `1{partition event, V resolved} · (-μ(V, q))` is
measurable. -/
theorem measurable_cubeMu_indicator (V : TriadicCube d) (q : Fin d → ℝ) :
    Measurable fun ω : Configuration d =>
      if PartitionEvent ω ∧ PartitionResolved ω V then ENNReal.ofReal (-cubeMu ω V q)
      else 0 := by
  set S := V.toIntegerCube.vertices
  let φ : Configuration d → Option (Finset (Vertex d × Vertex d) × (↥S → Vertex d)) :=
    fun ω => if PartitionEvent ω ∧ PartitionResolved ω V then
      some ((S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2),
        fun x => partitionAnchor ω x.1)
    else none
  have hE := measurableSet_partitionEvent_resolved V
  refine measurable_of_constant_on_fibres φ (fun t => ?_) (fun ω ω' h => ?_)
  · rcases t with _ | ⟨E, a⟩
    · have heq : φ ⁻¹' {none} = {ω | PartitionEvent ω ∧ PartitionResolved ω V}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h <;> simp [h]
      rw [heq]
      exact hE.compl
    · have heq : φ ⁻¹' {some (E, a)} =
          {ω | PartitionEvent ω ∧ PartitionResolved ω V} ∩
            ({ω | (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2) = E} ∩
              ⋂ x : ↥S, {ω | PartitionEvent ω ∧ partitionAnchor ω x.1 = a x}) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_iInter, φ]
        split_ifs with h
        · simp only [Option.some.injEq, Prod.mk.injEq, h, true_and, funext_iff]
        · simp only [h, false_and]
      rw [heq]
      refine hE.inter ((measurableSet_filter_eq (S ×ˢ S) E fun e =>
        measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)).inter ?_)
      exact MeasurableSet.iInter fun x => measurableSet_partitionAnchor_eq x.1 (a x)
  · by_cases hω : PartitionEvent ω ∧ PartitionResolved ω V
    · have hω' : PartitionEvent ω' ∧ PartitionResolved ω' V := by
        by_contra hn
        simp only [φ, if_pos hω, if_neg hn, reduceCtorEq] at h
      simp only [φ, if_pos hω, if_pos hω', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hAdj, hAnc⟩ := h
      rw [if_pos hω, if_pos hω']
      congr 2
      refine (cubeMu_eq_of_adj_iff_of_anchor_eq (fun x hx y hy => ?_) (fun x hx => ?_) q).symm
      · have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx
        have hyS : y ∈ S := (V.mem_toIntegerCube_vertices y).2 hy
        have h2 := Finset.ext_iff.1 hAdj (x, y)
        simp only [Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
        exact h2
      · exact (congrFun hAnc ⟨x, (V.mem_toIntegerCube_vertices x).2 hx⟩).symm
    · have hω' : ¬ (PartitionEvent ω' ∧ PartitionResolved ω' V) := by
        intro hn
        simp only [φ, if_neg hω, if_pos hn, reduceCtorEq] at h
      rw [if_neg hω, if_neg hω']

end Rigidity.Percolation
