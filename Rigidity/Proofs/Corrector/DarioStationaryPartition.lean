import Rigidity.Proofs.Partition.GeneralPartition
import Rigidity.Proofs.Percolation.PlanarPartition
import Rigidity.Percolation.TriadicLocalizationProbability
import Rigidity.Percolation.TriadicLocalizationStretched

/-!
# Dario's stationary partitions and the estimate (3.3)

For the proof of Lemma 3.2, Dario applies the partition construction of Proposition 2.1 to the
collection `𝒢_stat^k = 𝒢 ∪ ⋃_{n ≥ k} 𝒯_n` of the good cubes and all the triadic cubes of scale at
least `k`, which gives a partition `𝒫_stat^k` stationary under `3^k ℤ^d`, and states
(3.3): `P[∃ x ∈ □_k, □_𝒫(x) ≠ □_{𝒫_stat^k}(x)] ≤ C exp(-C⁻¹ 3^k)`, "with a proof similar to the
one of Armstrong and Dario, Proposition 2.1 (iv)".

Here, for the planar good cubes of main (`planarGoodCubes`):

* `statGoodCubes k ω = planarGoodCubes ω ∪ {T | k ≤ T.scale}`;
* `measure_not_mem_planarGoodCubes_le`: a good cube fails with probability at most
  `B exp(-c 3^n)` at scale `n`;
* `ae_statPartition`, `stat_stoppingSize_exp_moment`: almost surely the maximal stopping cubes of
  `statGoodCubes k` partition `ℤ²`, with sizes of uniform exponential moments (main's
  `partition_estimates_general`, Armstrong and Dario, Proposition 2.1);
* `measure_stopping_discrepancy_le_of_new`: if `G ⊆ H` and every cube of `H \ G` has scale
  above `n`, the probability that the maximal stopping cubes of `G` and `H` differ somewhere in a
  cube `A` is at most the sum over the scales above `n` of the number of cubes of that scale near
  `A` times the probability that one of them is not in `G` (main's
  `exists_new_good_near_of_stopping_ne`: a change of the stopping cube at `x` gives a cube of
  `H \ G` within twelve of its sides from `x`);
* `measure_planarPartition_ne_stat_le`: **(3.3)**, for every cube `A` of scale `k ≥ 1`, with the
  printed form `C exp(-C⁻¹ 3^k)`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

/-- **Discrepancy of stopping partitions from new cubes of large scale**: if `G ⊆ H` and the cubes
of `H \ G` have scales above `n`, the maximal stopping cubes of `G` and `H` differ somewhere in `A`
only if a cube of scale above `n` near `A` is not in `G`. -/
theorem TriadicCube.measure_stopping_discrepancy_le_of_new {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G H : Ω → Set (TriadicCube d)) (A : TriadicCube d)
    (n : ℕ) (hGH : ∀ ω, G ω ⊆ H ω) (hnew : ∀ ω T, T ∈ H ω → T ∉ G ω → n < T.scale)
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
    obtain ⟨T, hTG, hTH, hnear⟩ :=
      exists_new_good_near_of_stopping_ne (hGH ω) hxQ hxR hQ hR hne
    have hlarge := hnew ω T hTH hTG
    refine Set.mem_iUnion.mpr ⟨T.scale - (n + 1), Set.mem_iUnion.mpr ⟨T, ?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨?_, hTG⟩
    simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨by omega, x, hx, _, T.center_mem, hnear _ T.center_mem⟩
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

/-- The stretched-exponential form of `measure_stopping_discrepancy_le_of_new`. -/
theorem TriadicCube.measure_stopping_discrepancy_le_of_new_stretched {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (G H : Ω → Set (TriadicCube d)) (A : TriadicCube d)
    (n : ℕ) (hGH : ∀ ω, G ω ⊆ H ω) (hnew : ∀ ω T, T ∈ H ω → T ∉ G ω → n < T.scale)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube d,
      x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
        R.IsMaximalStopping (H ω) ∧ Q ≠ R} ≤
      (((2 * 3 ^ (A.scale - (n + 1)) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
        ENNReal.ofReal (Real.exp (-c * b ^ (n + 1))) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k := by
  calc
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + 1 + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * ENNReal.ofReal (Real.exp (-c * b ^ (n + 1 + k)))) :=
      measure_stopping_discrepancy_le_of_new μ G H A n hGH hnew
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

/-- **The planar good cubes fail with exponentially small probability**: there are `B < ∞` and
`c > 0` with `P[T ∉ 𝒢] ≤ B exp(-c 3^n)` for every triadic cube `T` of scale `n`. -/
theorem measure_not_mem_planarGoodCubes_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ T : TriadicCube 2,
      latticeBondLaw 2 p {ω | T ∉ planarGoodCubes ω} ≤
        B * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ T.scale)) := by
  obtain ⟨C, c, hC, hc, hlarge⟩ := measure_not_planarMeshed_le hpc
  have hall := TriadicCube.measure_le_exp_of_large_scale (latticeBondLaw 2 p)
    (fun Q => {ω | Q ∉ planarMeshedFamily ω}) 7 C c hC hc hlarge
  set B : ℝ := C + Real.exp (c * (3 : ℝ) ^ 7) with hBdef
  have hB : 0 ≤ B := by positivity
  have hW : ∀ Q : TriadicCube 2, latticeBondLaw 2 p {ω | Q ∉ planarMeshedFamily ω} ≤
      ENNReal.ofReal B * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ Q.scale)) := fun Q => by
    rw [← ENNReal.ofReal_mul hB]
    exact hall Q
  refine ⟨max (ENNReal.ofReal (Real.exp (c / 3))) ((1 + 3 ^ 2) * ENNReal.ofReal B), ?_, c / 3,
    by positivity, TriadicCube.measure_not_mem_goodOfWellConnected_le (latticeBondLaw 2 p)
      planarMeshedFamily (ENNReal.ofReal B) c hc hW⟩
  exact ne_of_lt (max_lt_iff.mpr ⟨ENNReal.ofReal_lt_top,
    lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)⟩)

/-- Dario's collection `𝒢_stat^k = 𝒢 ∪ ⋃_{n ≥ k} 𝒯_n` of the good cubes and all the triadic cubes
of scale at least `k`. -/
def statGoodCubes (k : ℕ) (ω : Configuration 2) : Set (TriadicCube 2) :=
  planarGoodCubes ω ∪ {T | k ≤ T.scale}

theorem planarGoodCubes_subset_stat (k : ℕ) (ω : Configuration 2) :
    planarGoodCubes ω ⊆ statGoodCubes k ω :=
  Set.subset_union_left

theorem measurableSet_mem_statGoodCubes (k : ℕ) (T : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | T ∈ statGoodCubes k ω} := by
  have h : {ω : Configuration 2 | T ∈ statGoodCubes k ω} =
      {ω | T ∈ planarGoodCubes ω} ∪ {_ω | k ≤ T.scale} := rfl
  rw [h]
  exact (TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
    measurableSet_mem_planarMeshedFamily T).union (MeasurableSet.const _)

/-- **The stationary partition and its sizes** (Armstrong and Dario, Proposition 2.1, for
`𝒢_stat^k`): almost surely every vertex lies in a unique maximal stopping cube of
`statGoodCubes k`, and the sizes have uniform exponential moments. -/
theorem stat_partition_estimates {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (k : ℕ) :
    (∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (statGoodCubes k ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex 2,
      Integrable (fun ω => Real.exp ((TriadicCube.stoppingSize (statGoodCubes k ω) x / θ) ^
        (1 : ℝ))) (latticeBondLaw 2 p) ∧
      (∫ ω, Real.exp ((TriadicCube.stoppingSize (statGoodCubes k ω) x / θ) ^ (1 : ℝ))
        ∂latticeBondLaw 2 p) ≤ 2) := by
  obtain ⟨B, hB, c, hc, hfail⟩ := measure_not_mem_planarGoodCubes_le hpc
  have hq : ∀ T : TriadicCube 2, latticeBondLaw 2 p {ω | T ∉ statGoodCubes k ω} ≤
      ENNReal.ofReal (B.toReal * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ (1 : ℝ))) := by
    intro T
    rw [Real.rpow_one, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hB]
    refine (measure_mono fun ω hω => ?_).trans (hfail T)
    exact fun h => hω (planarGoodCubes_subset_stat k ω h)
  obtain ⟨h1, h2, -⟩ := partition_estimates_general (d := 2) (by norm_num)
    (latticeBondLaw 2 p) (statGoodCubes k) (measurableSet_mem_statGoodCubes k)
    ENNReal.toReal_nonneg hc one_pos hq
  exact ⟨h1, h2⟩

/-- **Dario, (3.3)**: there are `K, c > 0` such that for every `k ≥ 1` and every triadic cube `A`
of scale `k`, the maximal stopping cubes of the good cubes and of `𝒢_stat^k` agree at every
vertex of `A` outside an event of probability at most `K exp(-c 3^k)`. -/
theorem measure_planarPartition_ne_stat_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ A : TriadicCube 2, A.scale = k →
      latticeBondLaw 2 p {ω | ∃ x ∈ A.vertices, ∃ Q R : TriadicCube 2,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (planarGoodCubes ω) ∧
          R.IsMaximalStopping (statGoodCubes k ω) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * Real.exp (-c * (3 : ℝ) ^ k)) := by
  obtain ⟨B, hB, c, hc, hfail⟩ := measure_not_mem_planarGoodCubes_le hpc
  obtain ⟨S, hS⟩ : ∃ S : ℝ≥0∞, S = ∑' j : ℕ, ENNReal.ofReal (Real.exp (-c * (3 - 1))) ^ j :=
    ⟨_, rfl⟩
  have hr1 : ENNReal.ofReal (Real.exp (-c * (3 - 1))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (Real.exp_lt_exp.2 (by linarith)).trans_eq Real.exp_zero
  have hSfin : S ≠ ∞ := by
    rw [hS, ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr1).ne'
  refine ⟨(((2 * 3 ^ 0 + 29) ^ 2 : ℕ) : ℝ) * B.toReal * S.toReal + 1, c, by positivity, hc,
    fun k hk A hA => ?_⟩
  have hnew : ∀ ω T, T ∈ statGoodCubes k ω → T ∉ planarGoodCubes ω → k - 1 < T.scale := by
    intro ω T hT hTG
    rcases hT with hT | hT
    · exact absurd hT hTG
    · change k ≤ T.scale at hT
      omega
  have h := TriadicCube.measure_stopping_discrepancy_le_of_new_stretched (latticeBondLaw 2 p)
    planarGoodCubes (statGoodCubes k) A (k - 1) (planarGoodCubes_subset_stat k) hnew B 3 c
    (by norm_num) hc hfail
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1, hA, Nat.sub_self, ← hS] at h
  refine h.trans ?_
  have he : 0 < Real.exp (-c * (3 : ℝ) ^ k) := Real.exp_pos _
  have key : (((2 * 3 ^ 0 + 29) ^ 2 : ℕ) : ℝ≥0∞) * B * ENNReal.ofReal (Real.exp (-c * 3 ^ k)) *
      S = ENNReal.ofReal ((((2 * 3 ^ 0 + 29) ^ 2 : ℕ) : ℝ) * B.toReal * S.toReal *
        Real.exp (-c * (3 : ℝ) ^ k)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hB, ENNReal.ofReal_toReal hSfin,
      ENNReal.ofReal_natCast]
    ring
  rw [key]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [add_mul, one_mul]
  linarith

end Rigidity.Percolation
