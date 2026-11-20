import Rigidity.Percolation.LargePathCoalescence
import Rigidity.Percolation.TriadicTestCubeCount

/-!
# A union bound for well-connectedness

Failure of well-connectedness is controlled by the absence of an ambient
crossing component and the failures of local test-cube conditions.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- A test fails when it is not crossable, its large paths do not coalesce, or
some ambient crossing root has no anchored large path despite the existence
of a selected path in the test. -/
def TriadicCube.badCoalescenceTest {d : ℕ} (Q : TriadicCube d) (R : IntegerCube d) :
    Set (Configuration d) :=
  {ω | ¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
      (fun i => ↑(R.upperFace i)) ∨
    ¬ LargePathsCoalesce ω (↑R.vertices) Q.largePath ∨
    ∃ root, IsCrossingRoot ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) root ∧
      ¬ (HasSelectedOpenPath ω (↑R.vertices) Q.largePath →
        HasAnchoredLargePath ω (↑R.vertices) Q.vertices root Q.largePath)}

/-- A bad local test is a measurable event. -/
theorem TriadicCube.measurableSet_badCoalescenceTest {d : ℕ}
    (Q : TriadicCube d) (R : IntegerCube d) : MeasurableSet (Q.badCoalescenceTest R) := by
  apply measurableSet_setOf.2
  exact (measurableSet_setOf.1 (measurableSet_crossableRegion (↑R.vertices)
    (fun i => ↑(R.lowerFace i)) (fun i => ↑(R.upperFace i)))).not.or
    ((measurableSet_setOf.1 (measurableSet_largePathsCoalesce
      (↑R.vertices) Q.largePath)).not.or (Measurable.exists fun root =>
        (measurableSet_setOf.1 (measurableSet_isCrossingRoot Q.vertices
          (fun i => ↑(Q.toIntegerCube.lowerFace i))
          (fun i => ↑(Q.toIntegerCube.upperFace i)) root)).and
        ((measurableSet_setOf.1 (measurableSet_hasSelectedOpenPath
          (↑R.vertices) Q.largePath)).imp
          (measurableSet_setOf.1 (measurableSet_hasAnchoredLargePath
            (↑R.vertices) Q.vertices root Q.largePath))).not))

/-- A uniform bound on bad local tests yields a finite union bound for failure
of well-connectedness, with an explicit polynomial number of tests. -/
theorem TriadicCube.measure_not_wellConnectedIn_le {d : ℕ}
    (Q : TriadicCube d) (interior : Set (Vertex d)) (hinterior : interior ⊆ Q.vertices)
    (μ : Measure (Configuration d)) (q : ℝ≥0∞)
    (hq : ∀ R ∈ Q.testCubes interior, μ (Q.badCoalescenceTest R) ≤ q) :
    μ {ω | ¬ Q.wellConnectedIn interior ω} ≤
      μ {ω | ¬ HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i))} +
      ((3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d : ℕ) * q := by
  classical
  let tests := (Q.finite_testCubes_and_ncard_le interior hinterior).1.toFinset
  let absent : Set (Configuration d) := {ω | ¬ HasCrossingComponent ω Q.vertices
    (fun i => ↑(Q.toIntegerCube.lowerFace i))
    (fun i => ↑(Q.toIntegerCube.upperFace i))}
  have htests : ∀ R, R ∈ tests ↔ R ∈ Q.testCubes interior := by
    intro R
    exact Set.Finite.mem_toFinset _
  have hsubset : {ω | ¬ Q.wellConnectedIn interior ω} ⊆
      absent ∪ ⋃ R ∈ tests, Q.badCoalescenceTest R := by
    intro ω hω
    by_cases hc : HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i))
    · obtain ⟨root, hroot⟩ := hc
      by_contra hnot
      have hgood : ∀ R ∈ Q.testCubes interior, ω ∉ Q.badCoalescenceTest R := by
        intro R hR hb
        apply hnot
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨R, (htests R).2 hR, hb⟩)
      apply hω
      apply Q.wellConnectedIn_of_coalescence hroot
      intro R hR
      have hh := hgood R hR
      change ¬ (¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
        (fun i => ↑(R.upperFace i)) ∨ ¬ LargePathsCoalesce ω (↑R.vertices) Q.largePath ∨
        ∃ r, IsCrossingRoot ω Q.vertices
          (fun i => ↑(Q.toIntegerCube.lowerFace i))
          (fun i => ↑(Q.toIntegerCube.upperFace i)) r ∧
          ¬ (HasSelectedOpenPath ω (↑R.vertices) Q.largePath →
            HasAnchoredLargePath ω (↑R.vertices) Q.vertices r Q.largePath)) at hh
      push Not at hh
      exact ⟨hh.1, hh.2.1, hh.2.2 root hroot⟩
    · exact Or.inl hc
  have hcard : tests.card ≤ (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d := by
    change (Q.finite_testCubes_and_ncard_le interior hinterior).1.toFinset.card ≤ _
    rw [← Set.ncard_eq_toFinset_card (Q.testCubes interior)
      (Q.finite_testCubes_and_ncard_le interior hinterior).1]
    exact (Q.finite_testCubes_and_ncard_le interior hinterior).2
  calc
    μ {ω | ¬ Q.wellConnectedIn interior ω} ≤
        μ (absent ∪ ⋃ R ∈ tests, Q.badCoalescenceTest R) := measure_mono hsubset
    _ ≤ μ absent + μ (⋃ R ∈ tests, Q.badCoalescenceTest R) := measure_union_le _ _
    _ ≤ μ absent + ∑ R ∈ tests, μ (Q.badCoalescenceTest R) :=
      add_le_add (le_refl _) (measure_biUnion_finset_le tests _)
    _ ≤ μ absent + (tests.card : ℝ≥0∞) * q := by
      apply add_le_add (le_refl _)
      calc
        _ ≤ ∑ _R ∈ tests, q := Finset.sum_le_sum fun R hR => hq R ((htests R).1 hR)
        _ = (tests.card : ℝ≥0∞) * q := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      have hcast : (tests.card : ℝ≥0∞) ≤
          (((3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcard
      exact mul_le_mul_left hcast q

end Rigidity.Percolation
