import Rigidity.Proofs.Percolation.PlanarMuTransport
import Rigidity.Proofs.Percolation.PlanarNuMeasurable

/-!
# Measurability of `μ` in the plane

The quantity `μ(V, q)` depends only on the cluster `C_*(V)`, on the open edges between its
vertices and on the coarse anchors of the vertices of `V`. On the partition event, the coarse
anchor of a vertex is determined by its partition cube and by the finite set of displacements from
the centre of that cube which have the anchor property. These are countably many measurable data,
so `1{partition event, V resolved} · (-μ(V, q))` is measurable.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- `μ` depends only on the cluster, the open edges between its vertices and the coarse
anchors. -/
theorem planarMu_eq_of_cluster_anchor_eq {U : TriadicCube 2}
    (hC : ∀ x, x ∈ clusterVertices ω' U ↔ x ∈ clusterVertices ω U)
    (hadj : ∀ x ∈ clusterVertices ω U, ∀ y ∈ clusterVertices ω U,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (hanc : ∀ x ∈ U.vertices, planarCoarseAnchor ω' x = planarCoarseAnchor ω x)
    (q : Fin 2 → ℝ) : planarMu ω' U q = planarMu ω U q := by
  let e : ↥(clusterVertices ω U) ≃ ↥(clusterVertices ω' U) :=
    Equiv.subtypeEquivRight fun x => (hC x).symm
  have hext : ∀ (u : ClusterFun ω U) (y : Vertex 2),
      clusterExtend ω' U (u ∘ e.symm) y = clusterExtend ω U u y := by
    intro u y
    by_cases hy : y ∈ clusterVertices ω U
    · have hy' := (hC y).2 hy
      rw [clusterExtend_apply_of_mem _ hy', clusterExtend_apply_of_mem _ hy]
      rfl
    · have hy' : y ∉ clusterVertices ω' U := fun h => hy ((hC y).1 h)
      change (if h : y ∈ clusterVertices ω' U then (u ∘ e.symm) ⟨y, h⟩ else 0) =
        if h : y ∈ clusterVertices ω U then u ⟨y, h⟩ else 0
      rw [dif_neg hy', dif_neg hy]
  refine planarMu_eq_of_equiv e (fun x y => by
      simp only [e, Equiv.subtypeEquivRight_apply_coe]
      exact hadj x.1 x.2 y.1 y.2)
    (fun x => by simp only [e, Equiv.subtypeEquivRight_apply_coe]) rfl q fun u => ?_
  rw [coarsePairing_apply, coarsePairing_apply]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [hanc _ ((U.mem_toIntegerCube_vertices _).1 hi),
      hanc _ ((U.mem_toIntegerCube_vertices _).1 hx), hext, hext]
  · rfl

/-- The displacements from the centre of the vertices of a triadic cube. -/
noncomputable def TriadicCube.displacements (Q : TriadicCube 2) : Finset (Vertex 2) :=
  Q.toIntegerCube.vertices.image (· - Q.center)

/-- The anchor property of a fixed vertex is a measurable event. -/
theorem measurable_isPlanarAnchor (Q : TriadicCube 2) (a : Vertex 2) :
    Measurable fun ω : Configuration 2 => Q.IsPlanarAnchor ω a := by
  unfold TriadicCube.IsPlanarAnchor
  refine measurable_const.and ((Measurable.forall fun c => Measurable.forall fun d =>
    Measurable.forall fun k => (measurableSet_setOf.1 (measurableSet_reachIn _ c d)).imp
      (measurable_const.imp (measurableSet_setOf.1 (measurableSet_reachIn _ a c)))).and
    (Measurable.forall fun c => Measurable.forall fun d =>
    Measurable.forall fun k => (measurableSet_setOf.1 (measurableSet_reachIn _ c d)).imp
      (measurable_const.imp (measurableSet_setOf.1 (measurableSet_reachIn _ a c)))))

/-- The anchor of a meshed cube is determined by the displacements with the anchor property. -/
theorem planarAnchor_eq_of_filter_eq {Q : TriadicCube 2}
    (hQ : Q.planarMeshed ω ∧ 1000 ≤ 3 ^ Q.scale) (hQ' : Q.planarMeshed ω' ∧ 1000 ≤ 3 ^ Q.scale)
    (h : Q.displacements.filter (fun e => Q.IsPlanarAnchor ω (Q.center + e)) =
      Q.displacements.filter (fun e => Q.IsPlanarAnchor ω' (Q.center + e))) :
    Q.planarAnchor ω = Q.planarAnchor ω' := by
  have hpred : (fun e => Q.IsPlanarAnchor ω (Q.center + e)) =
      fun e => Q.IsPlanarAnchor ω' (Q.center + e) := by
    funext e
    apply propext
    by_cases he : e ∈ Q.displacements
    · have := Finset.ext_iff.1 h e
      simp only [Finset.mem_filter, he, true_and] at this
      exact this
    · have hnot : ∀ ω'' : Configuration 2, ¬ Q.IsPlanarAnchor ω'' (Q.center + e) := by
        intro ω'' ha
        exact he (Finset.mem_image.2 ⟨Q.center + e, (Q.mem_toIntegerCube_vertices _).2 ha.1,
          add_sub_cancel_left _ _⟩)
      exact ⟨fun h1 => absurd h1 (hnot ω), fun h1 => absurd h1 (hnot ω')⟩
  unfold TriadicCube.planarAnchor
  rw [if_pos hQ, if_pos hQ', hpred]

/-- **Measurability of `μ`.** The quantity `1{partition event, V resolved} · (-μ(V, q))` is
measurable. -/
theorem measurable_planarMu_indicator (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (-planarMu ω V q)
      else 0 := by
  set S := V.toIntegerCube.vertices
  let anc : Configuration 2 → ↥S → TriadicCube 2 × Finset (Vertex 2) := fun ω x =>
    (planarPartCube ω x.1, (planarPartCube ω x.1).displacements.filter fun e =>
      (planarPartCube ω x.1).IsPlanarAnchor ω ((planarPartCube ω x.1).center + e))
  let φ : Configuration 2 →
      Option (Finset (Vertex 2) × Finset (Vertex 2 × Vertex 2) ×
        (↥S → TriadicCube 2 × Finset (Vertex 2))) :=
    fun ω => if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      some (S.filter (PlanarClusterLink ω V),
        (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2), anc ω)
    else none
  have hE := measurableSet_planarPartitionEvent_resolved V
  have key : ∀ ω, PlanarPartitionEvent ω → ∀ (t : ↥S → TriadicCube 2 × Finset (Vertex 2))
      (x : ↥S), (anc ω x = t x ↔ (x.1 ∈ (t x).1.vertices ∧
        (t x).1.IsMaximalStopping (planarGoodCubes ω)) ∧
        (t x).1.displacements.filter (fun e => (t x).1.IsPlanarAnchor ω ((t x).1.center + e)) =
          (t x).2) := by
    intro ω hP t x
    constructor
    · intro hx
      have h1 : planarPartCube ω x.1 = (t x).1 := congrArg Prod.fst hx
      have h2 := congrArg Prod.snd hx
      rw [← h1]
      exact ⟨planarPartCube_spec hP x.1, h2⟩
    · rintro ⟨⟨hxQ, hQ⟩, hT⟩
      have h1 := planarPartCube_eq hP hxQ hQ
      refine Prod.ext h1 ?_
      change (planarPartCube ω x.1).displacements.filter (fun e =>
        (planarPartCube ω x.1).IsPlanarAnchor ω ((planarPartCube ω x.1).center + e)) = (t x).2
      rw [h1]
      exact hT
  refine measurable_of_fiber_const φ (fun t => ?_) (fun ω ω' h => ?_)
  · rcases t with _ | ⟨C, E, t⟩
    · have heq : φ ⁻¹' {none} =
          {ω | PlanarPartitionEvent ω ∧ PlanarResolved ω V}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h <;> simp [h]
      rw [heq]
      exact hE.compl
    · have heq : φ ⁻¹' {some (C, E, t)} =
          {ω | PlanarPartitionEvent ω ∧ PlanarResolved ω V} ∩
            ({ω | S.filter (PlanarClusterLink ω V) = C} ∩
              ({ω | (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2) = E} ∩
                {ω | ∀ x : ↥S, (x.1 ∈ (t x).1.vertices ∧
                  (t x).1.IsMaximalStopping (planarGoodCubes ω)) ∧
                  (t x).1.displacements.filter
                    (fun e => (t x).1.IsPlanarAnchor ω ((t x).1.center + e)) = (t x).2})) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h
        · simp only [Option.some.injEq, Prod.mk.injEq, h, true_and, funext_iff, key ω h.1 t]
        · simp only [h, false_and]
      rw [heq]
      refine hE.inter ((measurableSet_filter_eq S C (measurable_planarClusterLink V)).inter
        ((measurableSet_filter_eq (S ×ˢ S) E fun e =>
          measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)).inter ?_))
      exact measurableSet_setOf.2 (Measurable.forall fun x =>
        (measurable_const.and (measurable_isMaximalStopping_planarGoodCubes _)).and
          (measurableSet_setOf.1 (measurableSet_filter_eq _ _ fun e =>
            measurable_isPlanarAnchor _ _)))
  · by_cases hω : PlanarPartitionEvent ω ∧ PlanarResolved ω V
    · have hω' : PlanarPartitionEvent ω' ∧ PlanarResolved ω' V := by
        by_contra hn
        simp only [φ, if_pos hω, if_neg hn, reduceCtorEq] at h
      simp only [φ, if_pos hω, if_pos hω', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hCl, hAdj, hAnc⟩ := h
      rw [if_pos hω, if_pos hω']
      congr 2
      refine (planarMu_eq_of_cluster_anchor_eq (fun x => ?_) (fun x hx y hy => ?_)
        (fun x hx => ?_) q).symm
      · rw [mem_clusterVertices, mem_clusterVertices, mem_planarCubeCluster_iff_link hω'.1 hω'.2,
          mem_planarCubeCluster_iff_link hω.1 hω.2, ← V.mem_toIntegerCube_vertices]
        have h1 := Finset.ext_iff.1 hCl x
        simp only [Finset.mem_filter] at h1
        exact h1.symm
      · have hx' := (mem_planarCubeCluster_iff_link hω.1 hω.2 x).1 (mem_clusterVertices.1 hx)
        have hy' := (mem_planarCubeCluster_iff_link hω.1 hω.2 y).1 (mem_clusterVertices.1 hy)
        have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx'.1
        have hyS : y ∈ S := (V.mem_toIntegerCube_vertices y).2 hy'.1
        have h2 := Finset.ext_iff.1 hAdj (x, y)
        simp only [Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
        exact h2.symm
      · have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx
        have hx' := congrFun hAnc ⟨x, hxS⟩
        have hQ : planarPartCube ω x = planarPartCube ω' x := congrArg Prod.fst hx'
        have hT := congrArg Prod.snd hx'
        unfold planarCoarseAnchor
        rw [← hQ]
        refine (planarAnchor_eq_of_filter_eq ⟨(planarPartCube_meshed hω.1 x).1,
          planarPartCube_large hω.1 x⟩ ?_ ?_).symm
        · rw [hQ]
          exact ⟨(planarPartCube_meshed hω'.1 x).1, planarPartCube_large hω'.1 x⟩
        · change (planarPartCube ω x).displacements.filter (fun e =>
            (planarPartCube ω x).IsPlanarAnchor ω ((planarPartCube ω x).center + e)) =
            (planarPartCube ω' x).displacements.filter (fun e =>
              (planarPartCube ω' x).IsPlanarAnchor ω' ((planarPartCube ω' x).center + e)) at hT
          rw [← hQ] at hT
          exact hT
    · have hω' : ¬ (PlanarPartitionEvent ω' ∧ PlanarResolved ω' V) := by
        intro hn
        simp only [φ, if_neg hω, if_pos hn, reduceCtorEq] at h
      rw [if_neg hω, if_neg hω']

end Rigidity.Percolation
