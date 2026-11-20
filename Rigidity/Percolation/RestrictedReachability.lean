import Rigidity.External.WellConnected
import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent

/-!
# Connectivity inside a vertex region

Open connectivity inside a fixed region is a measurable event. The proof
uses the countable family of finite open walks in the region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A finite open walk of a prescribed length, using edges inside a region. -/
def restrictedOpenWalk {d : ℕ} (ω : Configuration d) (B : Set (Vertex d)) :
    ℕ → Vertex d → Vertex d → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, (openIn ω B).Adj x z ∧ restrictedOpenWalk ω B n z y

/-- Reachability inside a region is equivalent to the existence of a finite walk. -/
theorem reachable_openIn_iff_exists_restrictedOpenWalk {d : ℕ}
    (ω : Configuration d) (B : Set (Vertex d)) (x y : Vertex d) :
    (openIn ω B).Reachable x y ↔ ∃ n, restrictedOpenWalk ω B n x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨0, rfl⟩
    | @cons u v w h p ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, v, h, hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero =>
      change x = y at hn
      subst y
      exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      obtain ⟨z, h, hz⟩ := hn
      exact h.reachable.trans (ih z hz)

/-- Adjacency inside a fixed region is a measurable event. -/
theorem measurableSet_openIn_adj {d : ℕ} (B : Set (Vertex d)) (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (openIn ω B).Adj x y} := by
  change MeasurableSet ({ω : Configuration d | (openGraph ω).Adj x y} ∩
    {ω | x ∈ B ∧ y ∈ B})
  exact (measurableSet_openGraph_adj x y).inter (MeasurableSet.const _)

/-- A fixed-length open walk inside a fixed region is a measurable event. -/
theorem measurableSet_restrictedOpenWalk {d : ℕ} (B : Set (Vertex d))
    (n : ℕ) (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | restrictedOpenWalk ω B n x y} := by
  induction n generalizing x with
  | zero => exact MeasurableSet.const _
  | succ n ih =>
    simp only [restrictedOpenWalk, Set.setOf_exists, Set.setOf_and]
    exact MeasurableSet.iUnion (fun z => (measurableSet_openIn_adj B x z).inter (ih z))

/-- Open connectivity inside a fixed region is measurable. -/
theorem measurableSet_openIn_reachable {d : ℕ} (B : Set (Vertex d)) (x y : Vertex d) :
    MeasurableSet {ω : Configuration d | (openIn ω B).Reachable x y} := by
  simp only [reachable_openIn_iff_exists_restrictedOpenWalk, Set.setOf_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_restrictedOpenWalk B n x y)

/-- Each pair of specified faces is joined inside the region. -/
def CrossableRegion {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) : Prop :=
  ∀ i, ∃ x ∈ B, ∃ y ∈ B, x ∈ lower i ∧ y ∈ upper i ∧ (openIn ω B).Reachable x y

/-- One open component inside the region meets every specified face. -/
def HasCrossingComponent {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) : Prop :=
  ∃ x ∈ B, ∀ i, (∃ y ∈ B, y ∈ lower i ∧ (openIn ω B).Reachable x y) ∧
    (∃ y ∈ B, y ∈ upper i ∧ (openIn ω B).Reachable x y)

/-- Every prescribed path in the region connects there to the component of a root
in the ambient region. The predicate `large` selects the paths to be tested. -/
def ConnectsSelectedPaths {d : ℕ} (ω : Configuration d) (B C : Set (Vertex d))
    (root : Vertex d) (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) : Prop :=
  ∀ n (γ : Fin (n + 1) → Vertex d), large n γ → γ 0 ∈ B →
    (∀ i : Fin n, (openIn ω B).Adj (γ i.castSucc) (γ i.succ)) →
      ∃ z ∈ B, (openIn ω B).Reachable (γ 0) z ∧ (openIn ω C).Reachable root z

/-- The event that every selected finite path connects to a fixed component is measurable. -/
theorem measurableSet_connectsSelectedPaths {d : ℕ} (B C : Set (Vertex d))
    (root : Vertex d) (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d | ConnectsSelectedPaths ω B C root large} := by
  apply measurableSet_setOf.2
  exact Measurable.forall fun n => Measurable.forall fun γ => measurable_const.imp
    (measurable_const.imp ((Measurable.forall fun (i : Fin n) =>
      measurableSet_setOf.1 (measurableSet_openIn_adj B (γ i.castSucc) (γ i.succ))).imp
        (Measurable.exists fun z => measurable_const.and
          ((measurableSet_setOf.1 (measurableSet_openIn_reachable B (γ 0) z)).and
            (measurableSet_setOf.1 (measurableSet_openIn_reachable C root z))))))

/-- A component meeting every face joins each pair of opposite faces. -/
theorem HasCrossingComponent.crossableRegion {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    (h : HasCrossingComponent ω B lower upper) : CrossableRegion ω B lower upper := by
  obtain ⟨x, _, hx⟩ := h
  intro i
  obtain ⟨⟨y, hyB, hyl, hy⟩, ⟨z, hzB, hzu, hz⟩⟩ := hx i
  exact ⟨y, hyB, z, hzB, hyl, hzu, hy.symm.trans hz⟩

/-- The crossability event is measurable. -/
theorem measurableSet_crossableRegion {d : ℕ} (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) :
    MeasurableSet {ω : Configuration d | CrossableRegion ω B lower upper} := by
  apply measurableSet_setOf.2
  exact Measurable.forall fun i => Measurable.exists fun x => measurable_const.and
    (Measurable.exists fun y => measurable_const.and (measurable_const.and
      (measurable_const.and (measurableSet_setOf.1 (measurableSet_openIn_reachable B x y)))))

/-- The event that one component meets all faces is measurable. -/
theorem measurableSet_hasCrossingComponent {d : ℕ} (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) :
    MeasurableSet {ω : Configuration d | HasCrossingComponent ω B lower upper} := by
  apply measurableSet_setOf.2
  exact Measurable.exists fun x => measurable_const.and (Measurable.forall fun i =>
    (Measurable.exists fun y => measurable_const.and (measurable_const.and
      (measurableSet_setOf.1 (measurableSet_openIn_reachable B x y)))).and
    (Measurable.exists fun y => measurable_const.and (measurable_const.and
      (measurableSet_setOf.1 (measurableSet_openIn_reachable B x y)))))

end Rigidity.Percolation
