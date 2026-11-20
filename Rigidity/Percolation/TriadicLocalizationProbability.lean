import Rigidity.Percolation.TriadicLocalizationCount
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Probability of a change in a stopping partition

A union bound over nearby bad cubes bounds the probability of a discrepancy
between partitions built from two nested collections of good cubes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- If the complement of a region is sufficiently far from a cube, a change
in a stopping partition within that cube is witnessed by a larger bad cube. -/
theorem TriadicCube.exists_large_bad_near_of_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} {U : Set (Vertex d)} (hGH : G ⊆ H)
    (hlocal : ∀ T : TriadicCube d, T.vertices ⊆ U → T ∈ H → T ∈ G)
    (A : TriadicCube d) (n : ℕ)
    (hdist : ∀ x ∈ A.vertices, ∀ y ∉ U, ∃ i, 12 * (3 : ℤ) ^ n ≤ |x i - y i|)
    {x : Vertex d} (hx : x ∈ A.vertices) {Q R : TriadicCube d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d, n < T.scale ∧ T ∉ G ∧
      ∃ x ∈ A.vertices, ∃ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side := by
  obtain ⟨T, y, hTG, _, hyT, hyU, hnear⟩ :=
    exists_bad_near_compl_of_stopping_ne hGH hlocal hxQ hxR hQ hR hne
  have hlarge : n < T.scale := by
    by_contra h
    have hle : T.side ≤ (3 : ℤ) ^ n :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    obtain ⟨i, hi⟩ := hdist x hx y hyU
    have hclose := hnear i
    omega
  exact ⟨T, hlarge, hTG, x, hx, y, hyT, hnear⟩

/-- A scale-dependent bad-cube estimate controls the probability that the
maximal stopping partitions differ anywhere in a cube. -/
theorem TriadicCube.measure_stopping_discrepancy_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G H : Ω → Set (TriadicCube d))
    (U : Set (Vertex d)) (A : TriadicCube d) (n : ℕ)
    (hGH : ∀ ω, G ω ⊆ H ω)
    (hlocal : ∀ ω T, T.vertices ⊆ U → T ∈ H ω → T ∈ G ω)
    (hdist : ∀ x ∈ A.vertices, ∀ y ∉ U, ∃ i, 12 * (3 : ℤ) ^ n ≤ |x i - y i|)
    (p : ℕ → ℝ≥0∞) (hprob : ∀ T : TriadicCube d, μ {ω | T ∉ G ω} ≤ p T.scale) :
    μ {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        p (n + 1 + k) := by
  classical
  let cubes : ℕ → Finset (TriadicCube d) := fun k =>
    (A.finite_near_at_scale (n + 1 + k)).1.toFinset
  let bad : TriadicCube d → Set Ω := fun T => {ω | T ∉ G ω}
  have hsubset : {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ⊆ ⋃ k, ⋃ T ∈ cubes k, bad T := by
    intro ω hω
    obtain ⟨x, hx, Q, R, hxQ, hxR, hQ, hR, hne⟩ := hω
    obtain ⟨T, hlarge, hbad, hnear⟩ :=
      exists_large_bad_near_of_stopping_ne (hGH ω) (hlocal ω) A n hdist hx hxQ hxR hQ hR hne
    refine Set.mem_iUnion.mpr ⟨T.scale - (n + 1), Set.mem_iUnion.mpr ⟨T, ?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨?_, hbad⟩
    simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨by omega, hnear⟩
  calc
    μ {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤ μ (⋃ k, ⋃ T ∈ cubes k, bad T) :=
          measure_mono hsubset
    _ ≤ ∑' k, μ (⋃ T ∈ cubes k, bad T) := measure_iUnion_le _
    _ ≤ ∑' k, (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        p (n + 1 + k) := by
      apply ENNReal.tsum_le_tsum
      intro k
      calc
        μ (⋃ T ∈ cubes k, bad T) ≤ ∑ T ∈ cubes k, μ (bad T) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ _T ∈ cubes k, p (n + 1 + k) := by
          apply Finset.sum_le_sum
          intro T hT
          have hscale : T.scale = n + 1 + k := by
            simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hT
            exact hT.1
          simpa only [bad, hscale] using hprob T
        _ = (cubes k).card * p (n + 1 + k) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
            p (n + 1 + k) := by
          gcongr
          have hc := (A.finite_near_at_scale (n + 1 + k)).2
          rw [Set.ncard_eq_toFinset_card _ (A.finite_near_at_scale (n + 1 + k)).1] at hc
          exact_mod_cast hc

end Rigidity.Percolation
