import Rigidity.Percolation.TriadicWellConnectedUnion

/-!
# Coalescence of crossing roots

When all crossing roots lie in one ambient component, a path anchored to one
crossing root is anchored to every crossing root.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

/-- Any two crossing roots lie in the same component of the region. -/
def CrossingRootsCoalesce {d : ℕ} (ω : Configuration d) (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) : Prop :=
  ∀ x y, IsCrossingRoot ω B lower upper x → IsCrossingRoot ω B lower upper y →
    (openIn ω B).Reachable x y

/-- Coalescence of crossing roots is measurable. -/
theorem measurableSet_crossingRootsCoalesce {d : ℕ} (B : Set (Vertex d))
    (lower upper : Fin d → Set (Vertex d)) :
    MeasurableSet {ω : Configuration d | CrossingRootsCoalesce ω B lower upper} := by
  apply measurableSet_setOf.2
  exact Measurable.forall fun x => Measurable.forall fun y =>
    (measurableSet_setOf.1 (measurableSet_isCrossingRoot B lower upper x)).imp
      ((measurableSet_setOf.1 (measurableSet_isCrossingRoot B lower upper y)).imp
        (measurableSet_setOf.1 (measurableSet_openIn_reachable B x y)))

/-- An anchored path remains anchored when its root is replaced by a vertex
in the same ambient component. -/
theorem HasAnchoredLargePath.of_reachable {d : ℕ} {ω : Configuration d}
    {B C : Set (Vertex d)} {root root' : Vertex d}
    {large : (n : ℕ) → (Fin (n + 1) → Vertex d) → Prop}
    (h : HasAnchoredLargePath ω B C root large)
    (hreach : (openIn ω C).Reachable root' root) :
    HasAnchoredLargePath ω B C root' large := by
  obtain ⟨n, γ, hγ, hroot⟩ := h
  exact ⟨n, γ, hγ, hreach.trans hroot⟩

/-- If a selected path exists, a crossing root has an anchored path in the test cube. -/
def TriadicCube.hasCrossingAnchor {d : ℕ} (Q : TriadicCube d) (R : IntegerCube d)
    (ω : Configuration d) : Prop :=
  HasSelectedOpenPath ω (↑R.vertices) Q.largePath →
    ∃ root, IsCrossingRoot ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) root ∧
      HasAnchoredLargePath ω (↑R.vertices) Q.vertices root Q.largePath

/-- Existence of a crossing anchor is measurable. -/
theorem TriadicCube.measurableSet_hasCrossingAnchor {d : ℕ}
    (Q : TriadicCube d) (R : IntegerCube d) :
    MeasurableSet {ω | Q.hasCrossingAnchor R ω} := by
  apply measurableSet_setOf.2
  exact (measurableSet_setOf.1 (measurableSet_hasSelectedOpenPath
    (↑R.vertices) Q.largePath)).imp (Measurable.exists fun root =>
      (measurableSet_setOf.1 (measurableSet_isCrossingRoot Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) root)).and
      (measurableSet_setOf.1 (measurableSet_hasAnchoredLargePath
        (↑R.vertices) Q.vertices root Q.largePath)))

/-- Under crossing-root coalescence, a single crossing anchor suffices for
all crossing roots in the definition of a good local test. -/
theorem TriadicCube.not_badCoalescenceTest_of_anchor {d : ℕ}
    {Q : TriadicCube d} {R : IntegerCube d} {ω : Configuration d}
    (hcross : CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
      (fun i => ↑(R.upperFace i)))
    (hcoal : LargePathsCoalesce ω (↑R.vertices) Q.largePath)
    (hroots : CrossingRootsCoalesce ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)))
    (hanchor : Q.hasCrossingAnchor R ω) : ω ∉ Q.badCoalescenceTest R := by
  rintro (h | h | ⟨root', hroot', hn⟩)
  · exact h hcross
  · exact h hcoal
  · apply hn
    intro hselected
    obtain ⟨root, hroot, hpath⟩ := hanchor hselected
    exact hpath.of_reachable (hroots root' root hroot' hroot)

/-- A bad test is bounded by failures of crossability, local coalescence,
crossing-root coalescence, and the existence of a crossing anchor. -/
theorem TriadicCube.measure_badCoalescenceTest_le {d : ℕ}
    (μ : Measure (Configuration d)) (Q : TriadicCube d) (R : IntegerCube d) :
    μ (Q.badCoalescenceTest R) ≤
      μ {ω | ¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
          (fun i => ↑(R.upperFace i))} +
      μ {ω | ¬ LargePathsCoalesce ω (↑R.vertices) Q.largePath} +
      μ {ω | ¬ CrossingRootsCoalesce ω Q.vertices
          (fun i => ↑(Q.toIntegerCube.lowerFace i))
          (fun i => ↑(Q.toIntegerCube.upperFace i))} +
      μ {ω | ¬ Q.hasCrossingAnchor R ω} := by
  classical
  let A : Set (Configuration d) := {ω | ¬ CrossableRegion ω (↑R.vertices)
    (fun i => ↑(R.lowerFace i)) (fun i => ↑(R.upperFace i))}
  let B : Set (Configuration d) := {ω | ¬ LargePathsCoalesce ω (↑R.vertices) Q.largePath}
  let C : Set (Configuration d) := {ω | ¬ CrossingRootsCoalesce ω Q.vertices
    (fun i => ↑(Q.toIntegerCube.lowerFace i)) (fun i => ↑(Q.toIntegerCube.upperFace i))}
  let D : Set (Configuration d) := {ω | ¬ Q.hasCrossingAnchor R ω}
  have hsub : Q.badCoalescenceTest R ⊆ ((A ∪ B) ∪ C) ∪ D := by
    intro ω hω
    by_contra h
    have ha : ω ∉ A := fun ha => h (Or.inl (Or.inl (Or.inl ha)))
    have hb : ω ∉ B := fun hb => h (Or.inl (Or.inl (Or.inr hb)))
    have hc : ω ∉ C := fun hc => h (Or.inl (Or.inr hc))
    have hd : ω ∉ D := fun hd => h (Or.inr hd)
    exact Q.not_badCoalescenceTest_of_anchor (not_not.mp ha) (not_not.mp hb)
      (not_not.mp hc) (not_not.mp hd) hω
  calc
    μ (Q.badCoalescenceTest R) ≤ μ (((A ∪ B) ∪ C) ∪ D) := measure_mono hsub
    _ ≤ μ ((A ∪ B) ∪ C) + μ D := measure_union_le _ _
    _ ≤ (μ (A ∪ B) + μ C) + μ D := add_le_add (measure_union_le _ _) (le_refl _)
    _ ≤ (μ A + μ B) + μ C + μ D :=
      add_le_add (add_le_add (measure_union_le _ _) (le_refl _)) (le_refl _)

end Rigidity.Percolation
