import Rigidity.Percolation.TriadicLocalizationCentered
import Rigidity.Percolation.TriadicLocalizationSharp

/-!
# Localization for good-cube events with centered support

A discrepancy in stopping partitions is controlled by the probability of a
bad cube whose centered enlargement reaches outside the localization region.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- If the complement of a region is sufficiently far from a set inside a cube, a change
in a stopping partition within the set is witnessed by a larger bad cube. -/
theorem TriadicCube.exists_large_bad_near_of_centered_stopping_ne {d : ℕ}
    {G H : Set (TriadicCube d)} {U : Set (Vertex d)} (hGH : G ⊆ H)
    (hlocal : ∀ T : TriadicCube d, T.centeredTriple ⊆ U → T ∈ H → T ∈ G)
    (A : TriadicCube d) (V : Set (Vertex d)) (hVA : V ⊆ A.vertices) (n : ℕ)
    (hdist : ∀ x ∈ V, ∀ y ∉ U, ∃ i, 14 * (3 : ℤ) ^ n ≤ |x i - y i|)
    {x : Vertex d} (hx : x ∈ V) {Q R : TriadicCube d}
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hQ : Q.IsMaximalStopping G) (hR : R.IsMaximalStopping H) (hne : Q ≠ R) :
    ∃ T : TriadicCube d, n < T.scale ∧ T ∉ G ∧
      ∃ x ∈ A.vertices, ∃ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side := by
  obtain ⟨T, hTG, _, hnear, y, hyT, hyU, hclose⟩ :=
    exists_bad_near_centeredTriple_compl_of_stopping_ne hGH hlocal hxQ hxR hQ hR hne
  have hlarge : n < T.scale := by
    by_contra h
    have hle : T.side ≤ (3 : ℤ) ^ n :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    obtain ⟨i, hi⟩ := hdist x hx y hyU
    have hclose := hclose i
    omega
  exact ⟨T, hlarge, hTG, x, hVA hx, T.center, T.center_mem, hnear T.center T.center_mem⟩

/-- A scale-dependent bad-cube estimate controls the probability that the
maximal stopping partitions differ anywhere in a set inside a cube. -/
theorem TriadicCube.measure_centered_stopping_discrepancy_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G H : Ω → Set (TriadicCube d))
    (U : Set (Vertex d)) (A : TriadicCube d) (V : Set (Vertex d)) (hVA : V ⊆ A.vertices) (n : ℕ)
    (hGH : ∀ ω, G ω ⊆ H ω)
    (hlocal : ∀ ω T, T.centeredTriple ⊆ U → T ∈ H ω → T ∈ G ω)
    (hdist : ∀ x ∈ V, ∀ y ∉ U, ∃ i, 14 * (3 : ℤ) ^ n ≤ |x i - y i|)
    (p : ℕ → ℝ≥0∞) (hprob : ∀ T : TriadicCube d, μ {ω | T ∉ G ω} ≤ p T.scale) :
    μ {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        p (n + 1 + k) := by
  classical
  let cubes : ℕ → Finset (TriadicCube d) := fun k =>
    (A.finite_near_at_scale (n + 1 + k)).1.toFinset
  let bad : TriadicCube d → Set Ω := fun T => {ω | T ∉ G ω}
  have hsubset : {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ⊆ ⋃ k, ⋃ T ∈ cubes k, bad T := by
    intro ω hω
    obtain ⟨x, hx, Q, R, hxQ, hxR, hQ, hR, hne⟩ := hω
    obtain ⟨T, hlarge, hbad, hnear⟩ :=
      exists_large_bad_near_of_centered_stopping_ne (hGH ω) (hlocal ω) A V hVA n hdist hx hxQ hxR hQ hR hne
    refine Set.mem_iUnion.mpr ⟨T.scale - (n + 1), Set.mem_iUnion.mpr ⟨T, ?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨?_, hbad⟩
    simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨by omega, hnear⟩
  calc
    μ {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
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


/-- A stretched-exponential bad-cube bound yields a stretched-exponential
estimate for changes in the stopping partition inside a subset of a cube. -/
theorem TriadicCube.measure_centered_stopping_discrepancy_le_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G H : Ω → Set (TriadicCube d))
    (U : Set (Vertex d)) (A : TriadicCube d) (V : Set (Vertex d)) (hVA : V ⊆ A.vertices) (n : ℕ)
    (hGH : ∀ ω, G ω ⊆ H ω)
    (hlocal : ∀ ω T, T.centeredTriple ⊆ U → T ∈ H ω → T ∈ G ω)
    (hdist : ∀ x ∈ V, ∀ y ∉ U, ∃ i, 14 * (3 : ℤ) ^ n ≤ |x i - y i|)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
        ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k := by
  calc
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * ENNReal.ofReal (Real.exp (-c * b ^ (n + 1 + k)))) :=
      measure_centered_stopping_discrepancy_le μ G H U A V hVA n hGH hlocal hdist
        (fun j => C * ENNReal.ofReal (Real.exp (-c * b ^ j))) hprob
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * (ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
          ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have hcount : (2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d ≤
          (2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d := by
        apply pow_le_pow_left'
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_left
        exact pow_le_pow_right₀ (by omega) (by omega)
      have hexp := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc (n + 1) k)
      simp only [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_pow (Real.exp_nonneg _) k] at hexp
      have hcount' : (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) ≤
          (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcount
      exact mul_le_mul' hcount' (mul_le_mul' le_rfl hexp)
    _ = _ := by
      simp_rw [← mul_assoc, ENNReal.tsum_mul_left]


/-- Under a probability measure, the localization bound has a linear scale
ratio at the cost of weakening the stretched-exponential rate by `d`. -/
theorem TriadicCube.measure_centered_stopping_discrepancy_le_stretched_linear {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G H : Ω → Set (TriadicCube d)) (U : Set (Vertex d)) (A : TriadicCube d) (V : Set (Vertex d)) (hVA : V ⊆ A.vertices) (n : ℕ)
    (hGH : ∀ ω, G ω ⊆ H ω)
    (hlocal : ∀ ω T, T.centeredTriple ⊆ U → T ∈ H ω → T ∈ G ω)
    (hdist : ∀ x ∈ V, ∀ y ∉ U, ∃ i, 14 * (3 : ℤ) ^ n ≤ |x i - y i|)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ V, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) *
        ((2 * 3 ^ (A.scale - (n + 1)) + 29 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp ((-c * b ^ (n + 1)) / d)) := by
  let K : ℝ≥0∞ := max 1 (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k)
  let B : ℝ≥0∞ := ((2 * 3 ^ (A.scale - (n + 1)) + 29 : ℕ) : ℝ≥0∞)
  let z : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((-c * b ^ (n + 1)) / d))
  have hK : 1 ≤ K := le_max_left _ _
  have hKpow : K ≤ K ^ d := by
    simpa only [pow_one] using (pow_le_pow_right' hK hd)
  have hD : C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k ≤ K ^ d :=
    (le_max_right _ _).trans hKpow
  have hz : z ^ d = ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) := by
    dsimp only [z]
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _) d, ← Real.exp_nat_mul]
    congr 2
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  apply le_of_le_one_of_le_pow hd
  · calc
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · calc
      _ ≤ (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
          ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k :=
        measure_centered_stopping_discrepancy_le_stretched μ G H U A V hVA n hGH hlocal hdist C b c hb hc hprob
      _ = B ^ d * (C * ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k) * z ^ d := by
        rw [hz]
        simp only [B, Nat.cast_pow]
        ac_rfl
      _ ≤ B ^ d * K ^ d * z ^ d := by gcongr
      _ = (K * B * z) ^ d := by rw [mul_pow, mul_pow]; ac_rfl


end Rigidity.Percolation
