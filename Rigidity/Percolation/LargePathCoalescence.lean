import Rigidity.Percolation.TriadicWellConnectedEvent

/-!
# Coalescence of large paths

Local coalescence of large open paths and one path anchored to an ambient
crossing component imply the path-connection part of well-connectedness.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- A selected open path in a region, indexed by its number of edges. -/
def IsSelectedOpenPath {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (n : ℕ) (γ : Fin (n + 1) → Vertex d) : Prop :=
  large n γ ∧ γ 0 ∈ B ∧
    ∀ i : Fin n, (openIn ω B).Adj (γ i.castSucc) (γ i.succ)

/-- Any two selected open paths in a region belong to the same component. -/
def LargePathsCoalesce {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) : Prop :=
  ∀ n γ, IsSelectedOpenPath ω B large n γ → ∀ m η,
    IsSelectedOpenPath ω B large m η → (openIn ω B).Reachable (γ 0) (η 0)

/-- A selected open path starts in the component of the ambient root. -/
def HasAnchoredLargePath {d : ℕ} (ω : Configuration d) (B C : Set (Vertex d))
    (root : Vertex d) (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) : Prop :=
  ∃ n γ, IsSelectedOpenPath ω B large n γ ∧ (openIn ω C).Reachable root (γ 0)

/-- Selected-path membership is measurable for fixed path data. -/
theorem measurableSet_isSelectedOpenPath {d : ℕ} (B : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop)
    (n : ℕ) (γ : Fin (n + 1) → Vertex d) :
    MeasurableSet {ω : Configuration d | IsSelectedOpenPath ω B large n γ} := by
  apply measurableSet_setOf.2
  exact measurable_const.and (measurable_const.and (Measurable.forall fun i =>
    measurableSet_setOf.1 (measurableSet_openIn_adj B (γ i.castSucc) (γ i.succ))))

/-- Large-path coalescence is a measurable event. -/
theorem measurableSet_largePathsCoalesce {d : ℕ} (B : Set (Vertex d))
    (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d | LargePathsCoalesce ω B large} := by
  apply measurableSet_setOf.2
  exact Measurable.forall fun n => Measurable.forall fun γ =>
    (measurableSet_setOf.1 (measurableSet_isSelectedOpenPath B large n γ)).imp
      (Measurable.forall fun m => Measurable.forall fun η =>
        (measurableSet_setOf.1 (measurableSet_isSelectedOpenPath B large m η)).imp
          (measurableSet_setOf.1 (measurableSet_openIn_reachable B (γ 0) (η 0))))

/-- Existence of an anchored large path is a measurable event. -/
theorem measurableSet_hasAnchoredLargePath {d : ℕ} (B C : Set (Vertex d))
    (root : Vertex d) (large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop) :
    MeasurableSet {ω : Configuration d | HasAnchoredLargePath ω B C root large} := by
  apply measurableSet_setOf.2
  exact Measurable.exists fun n => Measurable.exists fun γ =>
    (measurableSet_setOf.1 (measurableSet_isSelectedOpenPath B large n γ)).and
      (measurableSet_setOf.1 (measurableSet_openIn_reachable C root (γ 0)))

/-- Coalescence and an anchored path connect every selected path to the ambient
component. -/
theorem connectsSelectedPaths_of_coalescence {d : ℕ} {ω : Configuration d}
    {B C : Set (Vertex d)} {root : Vertex d}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (hcoalesce : LargePathsCoalesce ω B large)
    (hanchor : HasAnchoredLargePath ω B C root large) :
    ConnectsSelectedPaths ω B C root large := by
  obtain ⟨m, η, hη, hroot⟩ := hanchor
  intro n γ hlarge hstart hadj
  exact ⟨η 0, hη.2.1, hcoalesce n γ ⟨hlarge, hstart, hadj⟩ m η hη, hroot⟩

/-- Local crossability, large-path coalescence, and anchored paths give the
well-connectedness event. -/
theorem TriadicCube.wellConnectedIn_of_coalescence {d : ℕ} {Q : TriadicCube d}
    {interior : Set (Vertex d)} {ω : Configuration d} {root : Vertex d}
    (hroot : IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root)
    (htests : ∀ R ∈ Q.testCubes interior,
      CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
        (fun i => ↑(R.upperFace i)) ∧
      LargePathsCoalesce ω (↑R.vertices) Q.largePath ∧
      HasAnchoredLargePath ω (↑R.vertices) Q.vertices root Q.largePath) :
    Q.wellConnectedIn interior ω := by
  apply (Q.wellConnectedIn_iff interior ω).2
  refine ⟨root, hroot, ?_⟩
  intro R hR
  obtain ⟨hcross, hcoal, hanchor⟩ := htests R hR
  exact ⟨hcross, connectsSelectedPaths_of_coalescence hcoal hanchor⟩

end Rigidity.Percolation
