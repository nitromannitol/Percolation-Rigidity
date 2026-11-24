import Rigidity.Proofs.Cluster.GeneralRestrictBadProb
import Rigidity.Proofs.Cluster.GeneralRHProb
import Rigidity.Proofs.Partition.MinimalScaleCubes

/-!
# The tails of the events of the bad event of Lemma 5.5, in every dimension

For supercritical bond percolation on `ℤᵈ`, `d ≥ 2`, the three kinds of events of the bad event
`cubeRestrictBad` of the proof of Lemma 5.5 have probabilities decaying faster than every power of
`3^{-k}`, `k` their scale:

* a partition cube of scale at least `k` at a vertex: stretched-exponential tail of the sizes of
  the partition cubes (`exists_measure_partitionCube_scale_ge_le_pow`, from
  `exists_measure_partitionCube_scale_ge_le`);
* a large average of `size(□_𝒫)^τ` on a cell of scale `k`: Proposition 2.4 on every triadic cube
  (`exists_measure_sum_size_cube_gt_le_pow`, from `exists_measure_sum_partitionCube_gt_le`);
* a failure of the partition `𝓡` of the reverse Hölder cubes on a cell: the tail of
  Definition 3.7 (`RHPartition`, `rhPartition_holds`).

With `measure_cubeRestrictBad_le`, the bad event has probability at most `C 3^{-βn}` for every `β`,
uniformly over the cubes of scale at most `M n` (`exists_measure_cubeRestrictBad_le`). The
polynomial decay of the exponential tails is `exp(-a x) ≤ L! a^{-L} x^{-L}`
(`exp_neg_mul_le_factorial_div`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
  Rigidity.Proofs.Cluster.GeneralDim
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- `exp(-a x) ≤ L! a^{-L} x^{-L}` for `a, x > 0`. -/
theorem exp_neg_mul_le_factorial_div {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (L : ℕ) :
    Real.exp (-a * x) ≤ L.factorial / a ^ L * (x⁻¹) ^ L := by
  have h := Real.pow_div_factorial_le_exp (a * x) (le_of_lt (mul_pos ha hx)) L
  have hpos : 0 < (a * x) ^ L / L.factorial := by positivity
  rw [neg_mul, Real.exp_neg]
  calc (Real.exp (a * x))⁻¹ ≤ ((a * x) ^ L / L.factorial)⁻¹ := inv_anti₀ hpos h
    _ = L.factorial / a ^ L * (x⁻¹) ^ L := by
        rw [inv_div, mul_pow, inv_pow]
        field_simp

/-- **Polynomial tails of the scales of the partition cubes.** -/
theorem exists_measure_partitionCube_scale_ge_le_pow [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (L : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (x : Vertex d) (k : ℕ),
      latticeBondLaw d p {ω | PartitionEvent ω ∧ k ≤ (partitionCube ω x).scale} ≤
        C * (3⁻¹ : ℝ≥0∞) ^ (L * k) := by
  obtain ⟨a, ha, h⟩ := exists_measure_partitionCube_scale_ge_le hd hpc
  set K : ℝ := 2 * (L.factorial / a ^ L) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_ne_top, fun x k => ?_⟩
  have hsub : {ω | PartitionEvent ω ∧ k ≤ (partitionCube ω x).scale} ⊆
      {ω | PartitionEvent ω ∧ k ≤ (partitionCube ω x).scale + 2} :=
    fun ω hω => ⟨hω.1, by have := hω.2; omega⟩
  refine (measure_mono hsub).trans ((h k x).trans ?_)
  have he := exp_neg_mul_le_factorial_div ha (by positivity : (0 : ℝ) < 3 ^ k) L
  calc ENNReal.ofReal (2 * Real.exp (-a * (3 : ℝ) ^ k))
      ≤ ENNReal.ofReal (K * ((3 : ℝ) ^ k)⁻¹ ^ L) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hK, mul_assoc]
        exact mul_le_mul_of_nonneg_left he (by norm_num)
    _ = ENNReal.ofReal K * (3⁻¹ : ℝ≥0∞) ^ (k * L) := ofReal_mul_inv_three_pow K hK0 k L
    _ = ENNReal.ofReal K * (3⁻¹ : ℝ≥0∞) ^ (L * k) := by rw [mul_comm k L]

/-- The cube of scale `k` of a vertex is the vertex set of a triadic cube. -/
theorem cube_eq_toIntegerCube_vertices (k : ℕ) (y : Vertex d) :
    cube k y = (⟨k, idx k y⟩ : TriadicCube d).toIntegerCube.vertices := by
  ext x
  rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]

/-- **Polynomial tails of the averages of the powers of the sizes on the cubes of scale `k`**
(Proposition 2.4 of Armstrong and Dario on every triadic cube). -/
theorem exists_measure_sum_size_cube_gt_le_pow [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (τ : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ℕ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (k : ℕ) (y : Vertex d),
      latticeBondLaw d p {ω | A * (cube k y).card <
          ∑ x ∈ cube k y, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ≤
        C * (3⁻¹ : ℝ≥0∞) ^ (L * k) := by
  obtain ⟨C0, C', hC', c', hc', h⟩ := exists_measure_sum_partitionCube_gt_le hd hpc τ
  refine ⟨max C0 0, le_max_right _ _, fun L => ?_⟩
  set e : ℕ := 2 * (d + τ + 1) with he
  have he0 : (0 : ℝ) < e := by positivity
  set K : ℝ := (e * L).factorial / c' ^ (e * L) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C' * ENNReal.ofReal K, by finiteness, fun k y => ?_⟩
  set R : TriadicCube d := ⟨k, idx k y⟩ with hR
  have hcube := cube_eq_toIntegerCube_vertices k y
  have hsub : {ω | max C0 0 * (cube k y).card <
      ∑ x ∈ cube k y, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ⊆
      {ω | C0 * 3 ^ (d * R.scale) <
        ∑ x ∈ R.toIntegerCube.vertices, (3 : ℝ) ^ (τ * (partitionCube ω x).scale)} := by
    intro ω hω
    change max C0 0 * (cube k y).card <
      ∑ x ∈ cube k y, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ at hω
    change C0 * 3 ^ (d * k) <
      ∑ x ∈ R.toIntegerCube.vertices, (3 : ℝ) ^ (τ * (partitionCube ω x).scale)
    rw [← hcube]
    have hcard : ((cube k y).card : ℝ) = 3 ^ (d * k) := by
      rw [card_cube, ← pow_mul, mul_comm]
    rw [hcard] at hω
    have hsum : ∑ x ∈ cube k y, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ =
        ∑ x ∈ cube k y, (3 : ℝ) ^ (τ * (partitionCube ω x).scale) :=
      Finset.sum_congr rfl fun x _ => by rw [← pow_mul, mul_comm]
    rw [hsum] at hω
    have h3 : C0 * (3 : ℝ) ^ (d * k) ≤ max C0 0 * 3 ^ (d * k) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  refine (measure_mono hsub).trans ((h R).trans ?_)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  set z : ℝ := ((3 : ℝ) ^ k) ^ (1 / (e : ℝ)) with hz
  have hz0 : 0 < z := by positivity
  have hexp := exp_neg_mul_le_factorial_div hc' hz0 (e * L)
  have hzpow : (z⁻¹) ^ (e * L) = ((3 : ℝ) ^ k)⁻¹ ^ L := by
    rw [inv_pow, inv_pow, hz, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    rw [show (1 / (e : ℝ)) * ((e * L : ℕ) : ℝ) = (L : ℝ) by
      push_cast
      field_simp, Real.rpow_natCast]
  have hfin : ENNReal.ofReal (Real.exp (-c' * z)) ≤
      ENNReal.ofReal (K * ((3 : ℝ) ^ k)⁻¹ ^ L) := by
    rw [← hzpow]
    exact ENNReal.ofReal_le_ofReal hexp
  calc ENNReal.ofReal (Real.exp (-c' * z)) ≤ ENNReal.ofReal (K * ((3 : ℝ) ^ k)⁻¹ ^ L) := hfin
    _ = ENNReal.ofReal K * (3⁻¹ : ℝ≥0∞) ^ (k * L) := ofReal_mul_inv_three_pow K hK0 k L
    _ = ENNReal.ofReal K * (3⁻¹ : ℝ≥0∞) ^ (L * k) := by rw [mul_comm k L]

/-- **The probability of the bad event of the proof of Lemma 5.5** (every dimension `d ≥ 2`,
`p > p_c(d)`): with the partition `𝓡` of Definition 3.7, for every `τ` there is `A_τ` and for every
`t > 0` a constant `K` such that, for all `M` and `β`, the bad event has probability at most
`C 3^{-βn}` for every cube `U` and `2d ≤ n < scale U ≤ M n`. -/
theorem exists_measure_cubeRestrictBad_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ A₀ : ℝ, ∃ s : Configuration d → Vertex d → ℕ,
      (∀ᵐ ω ∂(latticeBondLaw d p),
        (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
        (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
        ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) ∧
      ∀ τ : ℕ, ∃ Aτ : ℝ, 0 ≤ Aτ ∧ ∀ t : ℝ, 0 < t → ∃ K : ℝ, 0 ≤ K ∧ ∀ M β : ℕ,
        ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube d) (n : ℕ), 2 * d ≤ n → n < U.scale →
          U.scale ≤ M * n →
            latticeBondLaw d p (cubeRestrictBad s t K τ Aτ U n) ≤ C * (3⁻¹ : ℝ≥0∞) ^ (β * n) := by
  have hd0 : 0 < d := by omega
  obtain ⟨A₀, s, hae, htail⟩ := rhPartition_holds hd hpc
  refine ⟨A₀, s, hae, fun τ => ?_⟩
  obtain ⟨Aτ, hAτ, hb⟩ := exists_measure_sum_size_cube_gt_le_pow hd hpc τ
  refine ⟨Aτ, hAτ, fun t ht => ?_⟩
  obtain ⟨K, hK, hB⟩ := htail t ht
  refine ⟨K, hK, fun M β => ?_⟩
  set L := 2 * d * (d * M + β) with hL
  obtain ⟨Ca, hCa, ha⟩ := exists_measure_partitionCube_scale_ge_le_pow hd hpc L
  obtain ⟨Cb, hCb, hb'⟩ := hb L
  obtain ⟨Cc0, hCc0, hc⟩ := hB L
  have hc' : ∀ (k : ℕ) (y : Vertex d), latticeBondLaw d p {ω | (∃ z ∈ enl 1 k y, k < s ω z) ∨
      K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ s ω x) ^ t} ≤
      ENNReal.ofReal Cc0 * (3⁻¹ : ℝ≥0∞) ^ (L * k) := fun k y => by
    refine (hc k y).trans (le_of_eq ?_)
    rw [ofReal_mul_inv_three_pow Cc0 hCc0 k L, mul_comm k L]
  exact measure_cubeRestrictBad_le hd0 (latticeBondLaw d p) s hCa hCb ENNReal.ofReal_ne_top
    ha hb' hc'

end Rigidity.Percolation
