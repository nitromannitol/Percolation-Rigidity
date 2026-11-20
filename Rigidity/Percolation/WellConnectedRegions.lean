import Rigidity.Percolation.RestrictedReachability
import Rigidity.Percolation.TriadicGoodCubes

/-!
# Well-connected regions

A family of finite lattice regions with marked faces can represent an
uncountable collection of geometric cubes. Its connectivity event is
measurable because there are only countably many finite lattice signatures.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A finite region together with its lower and upper faces in each direction. -/
abbrev RegionSignature (d : ℕ) :=
  Finset (Vertex d) × (Fin d → Finset (Vertex d)) × (Fin d → Finset (Vertex d))

/-- A root whose component in a region intersects all of its marked faces. -/
def IsCrossingRoot {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) (root : Vertex d) : Prop :=
  root ∈ B ∧ ∀ i,
    (∃ y ∈ B, y ∈ lower i ∧ (openIn ω B).Reachable root y) ∧
    (∃ y ∈ B, y ∈ upper i ∧ (openIn ω B).Reachable root y)

/-- Whether a fixed root is a crossing root is measurable. -/
theorem measurableSet_isCrossingRoot {d : ℕ} (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) (root : Vertex d) :
    MeasurableSet {ω : Configuration d | IsCrossingRoot ω B lower upper root} := by
  apply measurableSet_setOf.2
  exact measurable_const.and (Measurable.forall fun i =>
    (Measurable.exists fun y => measurable_const.and (measurable_const.and
      (measurableSet_setOf.1 (measurableSet_openIn_reachable B root y)))).and
    (Measurable.exists fun y => measurable_const.and (measurable_const.and
      (measurableSet_setOf.1 (measurableSet_openIn_reachable B root y)))))

/-- The ambient region has a crossing component to which all selected paths
in each test region connect, and each test region is crossable. -/
def WellConnectedRegions {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) (tests : Set (RegionSignature d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) : Prop :=
  ∃ root, IsCrossingRoot ω B lower upper root ∧ ∀ T ∈ tests,
    CrossableRegion ω (↑T.1 : Set (Vertex d)) (fun i => (↑(T.2.1 i) : Set (Vertex d))) (fun i => (↑(T.2.2 i) : Set (Vertex d))) ∧
      ConnectsSelectedPaths ω (↑T.1 : Set (Vertex d)) B root large

/-- Well-connectedness is measurable for every fixed family of finite region
signatures, even when the underlying geometric family is uncountable. -/
theorem measurableSet_wellConnectedRegions {d : ℕ} (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) (tests : Set (RegionSignature d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d | WellConnectedRegions ω B lower upper tests large} := by
  apply measurableSet_setOf.2
  exact Measurable.exists fun root =>
    (measurableSet_setOf.1 (measurableSet_isCrossingRoot B lower upper root)).and
      (Measurable.forall fun T => measurable_const.imp
        ((measurableSet_setOf.1 (measurableSet_crossableRegion
          (↑T.1 : Set (Vertex d)) (fun i => (↑(T.2.1 i) : Set (Vertex d))) (fun i => (↑(T.2.2 i) : Set (Vertex d))))).and
          (measurableSet_setOf.1 (measurableSet_connectsSelectedPaths
            (↑T.1 : Set (Vertex d)) B root large))))

/-- A well-connected region has a crossing component. -/
theorem WellConnectedRegions.hasCrossingComponent {d : ℕ} {ω : Configuration d}
    {B : Set (Vertex d)} {lower upper : Fin d → Set (Vertex d)}
    {tests : Set (RegionSignature d)}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (h : WellConnectedRegions ω B lower upper tests large) :
    HasCrossingComponent ω B lower upper := by
  obtain ⟨root, hroot, _⟩ := h
  exact ⟨root, hroot⟩

end Rigidity.Percolation
