import Rigidity.Proofs.Cluster.PlanarRestrictErrorMajorant
import Rigidity.Proofs.Cluster.PlanarGehringInputs
import Rigidity.Proofs.Cluster.PlanarPartitionScaleTail

/-!
# The bad event of the proof of Lemma 5.5

For a triadic cube `U` of scale `m` and `n` with `9 m ≤ 10 n`, let `j = ⌊n/2⌋` and
`k = ⌊(n - j)/3⌋`. The bad event `restrictBad` of the proof of Lemma 5.5 of Armstrong and Dario
(in the repaired form) is the union of
* some vertex of `U` has a planar partition cube of scale larger than `j` (the event `Γ`);
* for some vertex `z` of `U`, `∑_{x ∈ cube k z} planarReach(x)² > A₂ |cube k z|` (off this event
  the reach is at most `√A₂ 3^k` on `U`);
* for some cell `□'` of scale `j - 1` of the inner square of a subcube of scale `n`, either
  `∑_{□'} planarReach^τ > A_τ |□'|` or the Gehring partition `s` has a cell of scale larger than
  `j - 1` on `3□'` or `∑_{□'} (3^s)^t > K |□'|`.
If the probabilities of the individual events decay like `|S| 3^{-21(j+1)}`, `3^{-60 k}` and
`3^{-14 (j-1)}`, the bad event has probability at most `C 3^{-4n}`
(`measure_restrictBad_le`): the number of events is at most `|U| ≤ 3^{3n}` and the exponents
exceed `7n` up to constants. The reach is almost surely finite everywhere
(`ae_planarReach_ne_top`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- The bad event of the proof of Lemma 5.5 for the cube `U` and the scale `n`. -/
def restrictBad (s : Configuration 2 → Vertex 2 → ℕ) (t K : ℝ) (τ : ℕ) (Aτ A₂ : ℝ)
    (U : TriadicCube 2) (n : ℕ) : Set (Configuration 2) :=
  {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
      n / 2 < (planarPartCube ω x).scale} ∪
    (⋃ z ∈ U.toIntegerCube.vertices, {ω | ENNReal.ofReal (A₂ * (cube ((n - n / 2) / 3) z).card) <
      ∑ x ∈ cube ((n - n / 2) / 3) z, planarReach ω x ^ 2}) ∪
    (⋃ V ∈ subcubesAt U n, ⋃ c ∈ midCells V (n / 2),
      ({ω | ENNReal.ofReal (Aτ * (cube c.1 c.2).card) < ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}))

/-- The reach of the planar partition is almost surely finite at every vertex. -/
theorem ae_planarReach_ne_top {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ z, planarReach ω z ≠ ∞ := by
  obtain ⟨C, hC, hle⟩ := exists_lintegral_tsum_ninefold_le hpc (0 + 1)
  rw [ae_all_iff]
  intro z
  have hfin : ∫⁻ ω, reachSum ω (0 + 1) z ∂(latticeBondLaw 2 p) ≠ ∞ :=
    ne_top_of_le_ne_top hC (hle z)
  filter_upwards [ae_lt_top (measurable_reachSum (0 + 1) z) hfin] with ω hω
  have h := planarReach_pow_le ω z 0
  have h1 : planarReach ω z ≤ planarReach ω z ^ (0 + 1) := by rw [zero_add, pow_one]
  exact ne_top_of_le_ne_top hω.ne (h1.trans h)

/-- The number of cells of the inner square is at most the size of the cube. -/
theorem card_midCells_le {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale) :
    (midCells V j).card ≤ V.toIntegerCube.vertices.card :=
  Finset.card_image_le.trans (Finset.card_le_card (innerSquare_subset hj))

/-- `3^a 3^{-b} ≤ 3^d 3^{-c}` when `a + c ≤ b + d`. -/
theorem three_pow_mul_inv_pow_le {a b c d : ℕ} (h : a + c ≤ b + d) :
    (3 : ℝ≥0∞) ^ a * (3⁻¹) ^ b ≤ 3 ^ d * (3⁻¹) ^ c := by
  have h3 : (3 : ℝ≥0∞) * 3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hle : (3⁻¹ : ℝ≥0∞) ^ (b + d) ≤ (3⁻¹) ^ (a + c) :=
    pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 (by norm_num)) h
  have e1 : (3⁻¹ : ℝ≥0∞) ^ b = 3 ^ d * (3⁻¹) ^ (b + d) := by
    rw [pow_add, ← mul_assoc, mul_comm ((3 : ℝ≥0∞) ^ d), mul_assoc, ← mul_pow, h3, one_pow,
      mul_one]
  have e2 : (3 : ℝ≥0∞) ^ a * (3⁻¹) ^ (a + c) = (3⁻¹) ^ c := by
    rw [pow_add, ← mul_assoc, ← mul_pow, h3, one_pow, one_mul]
  calc (3 : ℝ≥0∞) ^ a * (3⁻¹) ^ b = 3 ^ d * (3 ^ a * (3⁻¹) ^ (b + d)) := by rw [e1]; ring
    _ ≤ 3 ^ d * (3 ^ a * (3⁻¹) ^ (a + c)) := by gcongr
    _ = 3 ^ d * (3⁻¹) ^ c := by rw [e2]

theorem ofReal_mul_inv_three_pow (C : ℝ) (hC : 0 ≤ C) (k B : ℕ) :
    ENNReal.ofReal (C * ((3 : ℝ) ^ k)⁻¹ ^ B) = ENNReal.ofReal C * (3⁻¹ : ℝ≥0∞) ^ (k * B) := by
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ← ENNReal.inv_pow, ← pow_mul, ENNReal.inv_pow]

/-- The size of a triadic cube of scale `m` is `3^{2m}`. -/
theorem card_toIntegerCube_vertices_eq_three_pow (U : TriadicCube 2) :
    (U.toIntegerCube.vertices.card : ℝ≥0∞) = 3 ^ (2 * U.scale) := by
  have h := card_toIntegerCube_vertices_eq U
  have h' : U.toIntegerCube.vertices.card = 3 ^ (2 * U.scale) := by
    have : ((U.toIntegerCube.vertices.card : ℕ) : ℝ) = ((3 ^ (2 * U.scale) : ℕ) : ℝ) := by
      rw [h]
      push_cast
      rw [pow_mul]
      norm_num
    exact_mod_cast this
  rw [h']
  norm_cast

/-- **The probability of the bad event of the proof of Lemma 5.5.** -/
theorem measure_restrictBad_le (μ : Measure (Configuration 2)) (s : Configuration 2 → Vertex 2 → ℕ)
    {t K : ℝ} {τ : ℕ} {Aτ A₂ : ℝ} {Cs : ℝ≥0∞} (hCs : Cs ≠ ∞)
    (hscale : ∀ (S : Finset (Vertex 2)) (j : ℕ),
      μ {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ S, j < (planarPartCube ω x).scale} ≤
        Cs * S.card * (3⁻¹ : ℝ≥0∞) ^ ((j + 1) * (20 + 1)))
    {C₂ Cτ Cg : ℝ} (hC₂ : 0 ≤ C₂) (hCτ : 0 ≤ Cτ) (hCg : 0 ≤ Cg)
    (h2 : ∀ (k : ℕ) (y : Vertex 2), μ {ω | ENNReal.ofReal (A₂ * (cube k y).card) <
        ∑ x ∈ cube k y, planarReach ω x ^ 2} ≤ ENNReal.ofReal (C₂ * ((3 : ℝ) ^ k)⁻¹ ^ 60))
    (hτ : ∀ (k : ℕ) (y : Vertex 2), μ {ω | ENNReal.ofReal (Aτ * (cube k y).card) <
        ∑ x ∈ cube k y, planarReach ω x ^ τ} ≤ ENNReal.ofReal (Cτ * ((3 : ℝ) ^ k)⁻¹ ^ 14))
    (hg : ∀ (k : ℕ) (y : Vertex 2), μ {ω | (∃ z ∈ enl 1 k y, k < s ω z) ∨
        K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ s ω x) ^ t} ≤
      ENNReal.ofReal (Cg * ((3 : ℝ) ^ k)⁻¹ ^ 14)) :
    ∃ Cb : ℝ≥0∞, Cb ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), 9 * U.scale ≤ 10 * n →
      n < U.scale → μ (restrictBad s t K τ Aτ A₂ U n) ≤ Cb * (3⁻¹ : ℝ≥0∞) ^ (4 * n) := by
  refine ⟨Cs + ENNReal.ofReal C₂ * 3 ^ 60 + (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * 3 ^ 21,
    by finiteness, fun U n hmn hnm => ?_⟩
  set m := U.scale with hm
  set j := n / 2 with hj
  set k := (n - n / 2) / 3 with hk
  have hn9 : 9 ≤ n := by omega
  have hj1 : 1 ≤ j := by omega
  have hjm : j < U.scale := by omega
  set N : ℝ≥0∞ := (U.toIntegerCube.vertices.card : ℝ≥0∞) with hNdef
  have hN : N = 3 ^ (2 * m) := card_toIntegerCube_vertices_eq_three_pow U
  -- the three parts
  have hE2 : μ {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
      n / 2 < (planarPartCube ω x).scale} ≤ Cs * (3⁻¹ : ℝ≥0∞) ^ (4 * n) := by
    refine (hscale U.toIntegerCube.vertices j).trans ?_
    rw [mul_assoc, ← hNdef, hN]
    gcongr
    calc (3 : ℝ≥0∞) ^ (2 * m) * 3⁻¹ ^ ((j + 1) * (20 + 1))
        ≤ 3 ^ 0 * (3⁻¹) ^ (4 * n) := three_pow_mul_inv_pow_le (by omega)
      _ = (3⁻¹) ^ (4 * n) := by rw [pow_zero, one_mul]
  have hE5 : μ (⋃ z ∈ U.toIntegerCube.vertices,
      {ω | ENNReal.ofReal (A₂ * (cube ((n - n / 2) / 3) z).card) <
        ∑ x ∈ cube ((n - n / 2) / 3) z, planarReach ω x ^ 2}) ≤
      ENNReal.ofReal C₂ * 3 ^ 60 * (3⁻¹ : ℝ≥0∞) ^ (4 * n) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ z ∈ U.toIntegerCube.vertices, μ {ω | ENNReal.ofReal (A₂ *
          (cube ((n - n / 2) / 3) z).card) < ∑ x ∈ cube ((n - n / 2) / 3) z, planarReach ω x ^ 2}
        ≤ ∑ _z ∈ U.toIntegerCube.vertices, ENNReal.ofReal C₂ * (3⁻¹ : ℝ≥0∞) ^ (k * 60) :=
          Finset.sum_le_sum fun z _ => (h2 _ z).trans (le_of_eq (ofReal_mul_inv_three_pow C₂ hC₂ _ _))
      _ = ENNReal.ofReal C₂ * (N * (3⁻¹ : ℝ≥0∞) ^ (k * 60)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hNdef]
          ring
      _ ≤ ENNReal.ofReal C₂ * (3 ^ 60 * (3⁻¹ : ℝ≥0∞) ^ (4 * n)) := by
          rw [hN]
          exact mul_le_mul_of_nonneg_left (three_pow_mul_inv_pow_le (by omega)) zero_le
      _ = _ := by ring
  have hE67 : μ (⋃ V ∈ subcubesAt U n, ⋃ c ∈ midCells V (n / 2),
      ({ω | ENNReal.ofReal (Aτ * (cube c.1 c.2).card) < ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t})) ≤
      (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * 3 ^ 21 * (3⁻¹ : ℝ≥0∞) ^ (4 * n) := by
    have hcell : ∀ V ∈ subcubesAt U n, ∀ c ∈ midCells V (n / 2),
        μ ({ω | ENNReal.ofReal (Aτ * (cube c.1 c.2).card) <
            ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ} ∪
          {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
            K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}) ≤
        (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * (3⁻¹ : ℝ≥0∞) ^ ((j - 1) * 14) := by
      intro V _ c hc
      have hc1 : c.1 = j - 1 := fst_of_mem_midCells hc
      refine (measure_union_le _ _).trans ?_
      rw [add_mul]
      refine add_le_add ((hτ c.1 c.2).trans (le_of_eq ?_)) ((hg c.1 c.2).trans (le_of_eq ?_))
      · rw [ofReal_mul_inv_three_pow Cτ hCτ, hc1]
      · rw [ofReal_mul_inv_three_pow Cg hCg, hc1]
    have hcard : ∑ V ∈ subcubesAt U n, ((midCells V (n / 2)).card : ℝ≥0∞) ≤ N := by
      calc ∑ V ∈ subcubesAt U n, ((midCells V (n / 2)).card : ℝ≥0∞)
          ≤ ∑ V ∈ subcubesAt U n, (V.toIntegerCube.vertices.card : ℝ≥0∞) := by
            refine Finset.sum_le_sum fun V hV => ?_
            have hVs : V.scale = n := scale_of_mem_subcubesAt hV
            exact_mod_cast card_midCells_le (by omega : n / 2 < V.scale)
        _ = N := sum_card_subcubes hnm.le
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ V ∈ subcubesAt U n, μ (⋃ c ∈ midCells V (n / 2),
          ({ω | ENNReal.ofReal (Aτ * (cube c.1 c.2).card) <
              ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ} ∪
            {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
              K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}))
        ≤ ∑ V ∈ subcubesAt U n, ∑ c ∈ midCells V (n / 2),
            (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * (3⁻¹ : ℝ≥0∞) ^ ((j - 1) * 14) :=
          Finset.sum_le_sum fun V hV => (measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun c hc => hcell V hV c hc)
      _ = (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * (3⁻¹ : ℝ≥0∞) ^ ((j - 1) * 14) *
            ∑ V ∈ subcubesAt U n, ((midCells V (n / 2)).card : ℝ≥0∞) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun V _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * (3⁻¹ : ℝ≥0∞) ^ ((j - 1) * 14) * N := by
          gcongr
      _ = (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * (N * (3⁻¹ : ℝ≥0∞) ^ ((j - 1) * 14)) := by ring
      _ ≤ (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * (3 ^ 21 * (3⁻¹ : ℝ≥0∞) ^ (4 * n)) := by
          rw [hN]
          exact mul_le_mul_of_nonneg_left (three_pow_mul_inv_pow_le (by omega)) zero_le
      _ = _ := by ring
  calc μ (restrictBad s t K τ Aτ A₂ U n)
      ≤ μ {ω | PlanarPartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
            n / 2 < (planarPartCube ω x).scale} +
          μ (⋃ z ∈ U.toIntegerCube.vertices,
            {ω | ENNReal.ofReal (A₂ * (cube ((n - n / 2) / 3) z).card) <
              ∑ x ∈ cube ((n - n / 2) / 3) z, planarReach ω x ^ 2}) +
          μ (⋃ V ∈ subcubesAt U n, ⋃ c ∈ midCells V (n / 2),
            ({ω | ENNReal.ofReal (Aτ * (cube c.1 c.2).card) <
                ∑ x ∈ cube c.1 c.2, planarReach ω x ^ τ} ∪
              {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
                K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t})) := by
        unfold restrictBad
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ Cs * (3⁻¹ : ℝ≥0∞) ^ (4 * n) + ENNReal.ofReal C₂ * 3 ^ 60 * (3⁻¹ : ℝ≥0∞) ^ (4 * n) +
          (ENNReal.ofReal Cτ + ENNReal.ofReal Cg) * 3 ^ 21 * (3⁻¹ : ℝ≥0∞) ^ (4 * n) := by
        gcongr
    _ = _ := by ring

end Rigidity.Proofs.Cluster
