import Rigidity.Steps.Section5.DisjointPathsToInfinity

/-!
# Proposition 5.21: the infinite cluster event is measurable

This file proves the step `InfiniteClusterMeasurableStep` (`step:5.21-cluster-measurable`) of
Proposition 5.21 (`Rigidity/Steps/Section5/DisjointPathsToInfinity.lean`): for each site `z` of
`ℤ²`, the event that `z` lies in an infinite open cluster of a site configuration is
measurable. The open cluster of `z` is infinite exactly when it contains sites of every
`ℓ¹`-norm (`siteCluster_infinite_iff`), and `z` is joined to `w` by an open path exactly when it
is joined by an open path with `n` steps for some `n` (`reachable_iff_exists_clusterReachIn`). The
latter is a countable union of finite intersections of the cylinder events
`{η | η v = true}`, so the event is a countable intersection of countable unions of cylinders.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- `z` is joined to `w` by an open nearest-neighbour path of `η` with `n` steps. -/
def ClusterReachIn (η : PlanarCarrier → Bool) : ℕ → PlanarCarrier → PlanarCarrier → Prop
  | 0, z, w => z = w
  | n + 1, z, w => ∃ v, ClusterReachIn η n z v ∧ (siteOpenGraph η).Adj v w

theorem reachable_iff_exists_clusterReachIn (η : PlanarCarrier → Bool) (z w : PlanarCarrier) :
    (siteOpenGraph η).Reachable z w ↔ ∃ n, ClusterReachIn η n z w := by
  constructor
  · intro h
    have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp h
    clear h
    induction h' with
    | refl => exact ⟨0, rfl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, b, hn, hbc⟩
  · rintro ⟨n, hn⟩
    induction n generalizing w with
    | zero =>
      obtain rfl : z = w := hn
      exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      obtain ⟨v, hv, hvw⟩ := hn
      exact (ih v hv).trans hvw.reachable

/-- The open cluster of `z` is infinite exactly when it contains sites of every `ℓ¹`-norm. -/
theorem siteCluster_infinite_iff (η : PlanarCarrier → Bool) (z : PlanarCarrier) :
    {w | (siteOpenGraph η).Reachable z w}.Infinite ↔
      ∀ N : ℕ, ∃ w, (siteOpenGraph η).Reachable z w ∧ (N : ℤ) < |w.1| + |w.2| := by
  constructor
  · intro h N
    by_contra hcon
    push Not at hcon
    apply h
    refine Set.Finite.subset
      (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N : Finset PlanarCarrier).finite_toSet
      fun w hw => ?_
    have hw' := hcon w hw
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
    refine ⟨abs_le.mp ?_, abs_le.mp ?_⟩ <;> linarith [abs_nonneg w.1, abs_nonneg w.2]
  · intro h hfin
    obtain ⟨B, hB⟩ := (hfin.image fun w : PlanarCarrier => |w.1| + |w.2|).bddAbove
    obtain ⟨w, hw, hlt⟩ := h B.toNat
    have h1 := hB (Set.mem_image_of_mem _ hw)
    have h2 : B ≤ (B.toNat : ℤ) := Int.self_le_toNat B
    linarith

theorem measurableSet_siteOpen (s : PlanarCarrier) :
    MeasurableSet {η : PlanarCarrier → Bool | η s = true} := by
  have h := (measurable_pi_apply s : Measurable fun f : PlanarCarrier → Bool => f s)
    (measurableSet_singleton (true : Bool))
  simpa [Set.preimage, Set.mem_singleton_iff] using h

theorem measurableSet_siteOpenGraph_adj (v w : PlanarCarrier) :
    MeasurableSet {η : PlanarCarrier → Bool | (siteOpenGraph η).Adj v w} := by
  have h : {η : PlanarCarrier → Bool | (siteOpenGraph η).Adj v w} =
      {_η | |v.1 - w.1| + |v.2 - w.2| = 1} ∩ ({η | η v = true} ∩ {η | η w = true}) := by
    ext η
    exact Iff.rfl
  rw [h]
  exact (MeasurableSet.const _).inter ((measurableSet_siteOpen v).inter (measurableSet_siteOpen w))

theorem measurableSet_clusterReachIn (n : ℕ) (z w : PlanarCarrier) :
    MeasurableSet {η : PlanarCarrier → Bool | ClusterReachIn η n z w} := by
  induction n generalizing w with
  | zero => exact MeasurableSet.const _
  | succ n ih =>
    have h : {η : PlanarCarrier → Bool | ClusterReachIn η (n + 1) z w} =
        ⋃ v, ({η | ClusterReachIn η n z v} ∩ {η | (siteOpenGraph η).Adj v w}) := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      exact Iff.rfl
    rw [h]
    exact MeasurableSet.iUnion fun v => (ih v).inter (measurableSet_siteOpenGraph_adj v w)

/-- Step `step:5.21-cluster-measurable`: the event that a site lies in an infinite open cluster
is measurable. -/
theorem infiniteClusterMeasurableStep : InfiniteClusterMeasurableStep := by
  intro z
  have h : {η : PlanarCarrier → Bool | InInfiniteSiteCluster η z} =
      {η | η z = true} ∩ ⋂ N : ℕ, ⋃ w : PlanarCarrier,
        ((⋃ n : ℕ, {η | ClusterReachIn η n z w}) ∩ {_η | (N : ℤ) < |w.1| + |w.2|}) := by
    ext η
    simp only [InInfiniteSiteCluster, Set.mem_setOf_eq]
    rw [siteCluster_infinite_iff]
    simp only [reachable_iff_exists_clusterReachIn, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_iUnion]
  rw [h]
  exact (measurableSet_siteOpen z).inter (MeasurableSet.iInter fun N =>
    MeasurableSet.iUnion fun w =>
      (MeasurableSet.iUnion fun n => measurableSet_clusterReachIn n z w).inter
        (MeasurableSet.const _))

end Rigidity.Proofs.Section5
