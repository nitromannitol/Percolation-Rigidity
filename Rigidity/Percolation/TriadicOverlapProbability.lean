import Rigidity.Percolation.TriadicOverlapWellConnected
import Rigidity.Percolation.TriadicTestCubeCount
import Rigidity.Percolation.IntegerCubeCoalescence

/-!
# Probability bound from overlap crossings

Crossing and coalescence estimates on test cubes and their overlaps imply a
finite union bound for well-connectedness of the rounded interior.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External MeasureTheory
open scoped ENNReal

/-- Uniform test and overlap estimates control the failure probability of
well-connectedness. The overlap side must be positive so its corner belongs to
the ambient cube. -/
theorem TriadicCube.measure_not_wellConnectedIn_threeQuarter_le {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) (hside : 2 ≤ Q.side)
    (hk : 0 < 3 ^ Q.scale / 20) (μ : Measure (Configuration d))
    (a b c : ℝ≥0∞)
    (hQ : μ {ω | ¬ HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) ∨
      ¬ LargePathsCoalesce ω Q.vertices
        (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))} ≤ a)
    (htest : ∀ R ∈ Q.testCubes Q.threeQuarterCube.vertices,
      μ {ω | ¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
          (fun i => ↑(R.upperFace i)) ∨
        ¬ LargePathsCoalesce ω (↑R.vertices)
          (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))} ≤ b)
    (hoverlap : ∀ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 →
      (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
      μ {ω | ¬ HasCrossingComponent ω (↑T.vertices)
        (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i))} ≤ c) :
    μ {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
      a + ((3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d : ℕ) * b +
        (Q.toIntegerCube.vertices.card : ℝ≥0∞) * c := by
  classical
  let interior : Set (Vertex d) := Q.threeQuarterCube.vertices
  have hinterior : interior ⊆ Q.vertices :=
    Q.threeQuarterCube_subset_envelope.trans Q.threeQuarterEnvelope_subset
  let tests := (Q.finite_testCubes_and_ncard_le interior hinterior).1.toFinset
  let corners := Q.toIntegerCube.vertices.filter fun x =>
    (↑(IntegerCube.atCorner x (3 ^ Q.scale / 20)).vertices : Set (Vertex d)) ⊆ Q.vertices
  let A : Set (Configuration d) := {ω | ¬ HasCrossingComponent ω Q.vertices
      (fun i => ↑(Q.toIntegerCube.lowerFace i))
      (fun i => ↑(Q.toIntegerCube.upperFace i)) ∨
    ¬ LargePathsCoalesce ω Q.vertices
      (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))}
  let B : IntegerCube d → Set (Configuration d) := fun R =>
    {ω | ¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
        (fun i => ↑(R.upperFace i)) ∨
      ¬ LargePathsCoalesce ω (↑R.vertices)
        (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))}
  let C : Vertex d → Set (Configuration d) := fun x =>
    {ω | ¬ HasCrossingComponent ω (↑(IntegerCube.atCorner x (3 ^ Q.scale / 20)).vertices)
      (fun i => ↑((IntegerCube.atCorner x (3 ^ Q.scale / 20)).lowerFace i))
      (fun i => ↑((IntegerCube.atCorner x (3 ^ Q.scale / 20)).upperFace i))}
  have htests : ∀ R, R ∈ tests ↔ R ∈ Q.testCubes interior := by
    intro R
    exact Set.Finite.mem_toFinset _
  have hsubset : {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ⊆
      (A ∪ ⋃ R ∈ tests, B R) ∪ ⋃ x ∈ corners, C x := by
    intro ω hω
    by_contra hbad
    have hA : ω ∉ A := fun h => hbad (Or.inl (Or.inl h))
    have hB : ∀ R ∈ Q.testCubes interior, ω ∉ B R := by
      intro R hR h
      exact hbad (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨R, (htests R).2 hR, h⟩)))
    have hC : ∀ T : IntegerCube d, T.size = 3 ^ Q.scale / 20 →
        (↑T.vertices : Set (Vertex d)) ⊆ Q.vertices →
        HasCrossingComponent ω (↑T.vertices)
          (fun i => ↑(T.lowerFace i)) (fun i => ↑(T.upperFace i)) := by
      intro T hsize hT
      have ht : IntegerCube.atCorner T.corner (3 ^ Q.scale / 20) = T := by
        cases T
        simp_all only [IntegerCube.atCorner]
      have hcorner : T.corner ∈ Q.toIntegerCube.vertices := by
        apply (Q.mem_toIntegerCube_vertices T.corner).mpr
        apply hT
        change T.corner ∈ T.vertices
        rw [IntegerCube.mem_vertices]
        intro i
        constructor
        · exact le_rfl
        · have hp : (0 : ℤ) < T.size := by rw [hsize]; exact_mod_cast hk
          exact lt_add_of_pos_right _ hp
      have hc : T.corner ∈ corners := by
        apply Finset.mem_filter.mpr
        refine ⟨hcorner, ?_⟩
        rw [ht]
        exact hT
      have hn : ω ∉ C T.corner := fun h => hbad (Or.inr (Set.mem_iUnion₂.mpr ⟨T.corner, hc, h⟩))
      change ¬ ¬ HasCrossingComponent ω
        (↑(IntegerCube.atCorner T.corner (3 ^ Q.scale / 20)).vertices)
        (fun i => ↑((IntegerCube.atCorner T.corner (3 ^ Q.scale / 20)).lowerFace i))
        (fun i => ↑((IntegerCube.atCorner T.corner (3 ^ Q.scale / 20)).upperFace i)) at hn
      rw [ht] at hn
      exact Classical.not_not.mp hn
    change ¬ (¬ HasCrossingComponent ω Q.vertices
        (fun i => ↑(Q.toIntegerCube.lowerFace i))
        (fun i => ↑(Q.toIntegerCube.upperFace i)) ∨
      ¬ LargePathsCoalesce ω Q.vertices
        (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))) at hA
    push Not at hA
    obtain ⟨root, hroot⟩ := hA.1
    apply hω
    apply Q.wellConnectedIn_threeQuarter_of_overlap_crossings hd hside hroot hA.2
    · intro R hR
      have hh := hB R hR
      change ¬ (¬ CrossableRegion ω (↑R.vertices) (fun i => ↑(R.lowerFace i))
          (fun i => ↑(R.upperFace i)) ∨
        ¬ LargePathsCoalesce ω (↑R.vertices)
          (pathDiameterAtLeast (((3 ^ Q.scale / 20 : ℕ) : ℤ) - 1))) at hh
      push Not at hh
      exact hh
    · exact hC
  have hcard : tests.card ≤ (3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d := by
    rw [← Set.ncard_eq_toFinset_card (Q.testCubes interior)
      (Q.finite_testCubes_and_ncard_le interior hinterior).1]
    exact (Q.finite_testCubes_and_ncard_le interior hinterior).2
  calc
    μ {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
        μ ((A ∪ ⋃ R ∈ tests, B R) ∪ ⋃ x ∈ corners, C x) := measure_mono hsubset
    _ ≤ μ A + μ (⋃ R ∈ tests, B R) + μ (⋃ x ∈ corners, C x) := by
      exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ a + (tests.card : ℝ≥0∞) * b + (corners.card : ℝ≥0∞) * c := by
      apply add_le_add
      · apply add_le_add hQ
        calc
          _ ≤ ∑ R ∈ tests, μ (B R) := measure_biUnion_finset_le tests B
          _ ≤ ∑ _R ∈ tests, b := Finset.sum_le_sum fun R hR => htest R ((htests R).1 hR)
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
      · calc
          _ ≤ ∑ x ∈ corners, μ (C x) := measure_biUnion_finset_le corners C
          _ ≤ ∑ _x ∈ corners, c := Finset.sum_le_sum fun x hx =>
            hoverlap (IntegerCube.atCorner x (3 ^ Q.scale / 20)) rfl (Finset.mem_filter.mp hx).2
          _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have ht : (tests.card : ℝ≥0∞) ≤
          (((3 ^ Q.scale + 1) * (6 * 3 ^ Q.scale + 1) ^ d : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcard
      have hc : (corners.card : ℝ≥0∞) ≤ Q.toIntegerCube.vertices.card := by
        exact_mod_cast Finset.card_filter_le _ _
      exact add_le_add (add_le_add le_rfl (mul_le_mul_left ht b)) (mul_le_mul_left hc c)

end Rigidity.Percolation
