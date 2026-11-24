import Rigidity.Proofs.Cluster.GeneralRestrictOffBad
import Rigidity.Proofs.Cluster.PlanarRestrictBad

/-!
# The probability of the bad event of the proof of Lemma 5.5, in every dimension

For a triadic cube `U` of scale `m ≤ M n` and `2d ≤ n`, the bad event `cubeRestrictBad` is a union
of at most `|U| = 3^{dm}` events at the vertices of `U` (a partition cube of scale at least
`j = ⌊n/(2d)⌋`) and of at most `2 |U|` events at the cells of scale `j - 1` (a large average of
`size(□_𝒫)^τ`, or a failure of the partition of the reverse Hölder cubes on the cell). If each of
these events at scale `k` has probability at most `C 3^{-L k}` with `L = 2d (d M + β)`, then the
bad event has probability at most `C' 3^{-β n}` (`measure_cubeRestrictBad_le`): since
`2d (j - 1) ≥ n - 4d + 1`, `3^{dm} 3^{-L(j-1)} ≤ 3^{4d(dM + β)} 3^{-βn}`. This is the
general-dimensional form of `Rigidity.Proofs.Cluster.measure_restrictBad_le`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The number of cells of scale `j - 1` of the inner cube is at most the size of the cube. -/
theorem card_midCubeCells_le {V : TriadicCube d} {j : ℕ} (hj : j < V.scale) :
    (midCubeCells V j).card ≤ V.toIntegerCube.vertices.card :=
  Finset.card_image_le.trans (Finset.card_le_card (innerCube_subset hj))

/-- The subcubes of scale `n` of `U` have `|U|` vertices in total. -/
theorem sum_card_subcubesAt_eq (U : TriadicCube d) {n : ℕ} (hn : n ≤ U.scale) :
    ∑ V ∈ U.subcubesAt n, (V.toIntegerCube.vertices.card : ℝ≥0∞) =
      U.toIntegerCube.vertices.card := by
  have h := card_subcubesAt_mul_general U hn
  have h1 : ∑ V ∈ U.subcubesAt n, (V.toIntegerCube.vertices.card : ℝ) =
      (U.toIntegerCube.vertices.card : ℝ) := by
    rw [U.card_toIntegerCube_vertices, ← h, Finset.sum_congr rfl fun V hV => by
      rw [V.card_toIntegerCube_vertices, TriadicCube.latticeVolume,
        TriadicCube.scale_of_mem_subcubesAt hV], Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ V ∈ U.subcubesAt n, V.toIntegerCube.vertices.card =
      U.toIntegerCube.vertices.card := by exact_mod_cast h1
  rw [← h2]
  push_cast
  rfl

theorem card_toIntegerCube_vertices_eq_three_pow_mul (U : TriadicCube d) :
    (U.toIntegerCube.vertices.card : ℝ≥0∞) = 3 ^ (d * U.scale) := by
  rw [IntegerCube.card_vertices_eq]
  change (((3 ^ U.scale) ^ d : ℕ) : ℝ≥0∞) = _
  rw [← pow_mul, mul_comm]
  push_cast
  rfl

/-- The exponent bookkeeping: `d m + β n ≤ L (j - 1) + 4d (dM + β)` for `j = ⌊n/(2d)⌋ ≥ 1`,
`m ≤ M n` and `L = 2d (dM + β)`. -/
theorem exponent_le_of_div {M β m n : ℕ} (hd : 0 < d) (hn : 2 * d ≤ n) (hm : m ≤ M * n) :
    d * m + β * n ≤ 2 * d * (d * M + β) * (n / (2 * d) - 1) + 4 * d * (d * M + β) := by
  set j := n / (2 * d) with hj
  have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hmod := Nat.div_add_mod n (2 * d)
  have hlt := Nat.mod_lt n (by omega : 0 < 2 * d)
  have h2 : n < 2 * d * j + 2 * d := by rw [← hj] at hmod; omega
  have e : 2 * d * (d * M + β) * (j - 1) + 4 * d * (d * M + β) =
      (d * M + β) * (2 * d * j + 2 * d) := by
    obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hi, Nat.add_sub_cancel]
    ring
  rw [e]
  have h3 : (d * M + β) * n ≤ (d * M + β) * (2 * d * j + 2 * d) :=
    Nat.mul_le_mul_left _ h2.le
  have h4 : d * m ≤ d * M * n := by
    calc d * m ≤ d * (M * n) := Nat.mul_le_mul_left _ hm
      _ = d * M * n := by ring
  nlinarith

/-- **The probability of the bad event of the proof of Lemma 5.5**, from tails of the
individual events (every dimension `d ≥ 1`). -/
theorem measure_cubeRestrictBad_le (hd : 0 < d) (μ : Measure (Configuration d))
    (s : Configuration d → Vertex d → ℕ) {t K : ℝ} {τ : ℕ} {Aτ : ℝ} {M β : ℕ}
    {Ca Cb Cc : ℝ≥0∞} (hCa : Ca ≠ ∞) (hCb : Cb ≠ ∞) (hCc : Cc ≠ ∞)
    (ha : ∀ (x : Vertex d) (k : ℕ), μ {ω | PartitionEvent ω ∧ k ≤ (partitionCube ω x).scale} ≤
      Ca * (3⁻¹ : ℝ≥0∞) ^ (2 * d * (d * M + β) * k))
    (hb : ∀ (k : ℕ) (y : Vertex d), μ {ω | Aτ * (cube k y).card <
        ∑ x ∈ cube k y, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ≤
      Cb * (3⁻¹ : ℝ≥0∞) ^ (2 * d * (d * M + β) * k))
    (hc : ∀ (k : ℕ) (y : Vertex d), μ {ω | (∃ z ∈ enl 1 k y, k < s ω z) ∨
        K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ s ω x) ^ t} ≤
      Cc * (3⁻¹ : ℝ≥0∞) ^ (2 * d * (d * M + β) * k)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube d) (n : ℕ), 2 * d ≤ n → n < U.scale →
      U.scale ≤ M * n → μ (cubeRestrictBad s t K τ Aτ U n) ≤ C * (3⁻¹ : ℝ≥0∞) ^ (β * n) := by
  set L := 2 * d * (d * M + β) with hL
  set S := 4 * d * (d * M + β) with hS
  refine ⟨(Ca + (Cb + Cc)) * 3 ^ S, by finiteness, fun U n hn hnm hmn => ?_⟩
  set j := n / (2 * d) with hj
  have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hjn : j < n := Nat.div_lt_self (by omega) (by omega)
  set N : ℝ≥0∞ := (U.toIntegerCube.vertices.card : ℝ≥0∞) with hNdef
  have hN : N = 3 ^ (d * U.scale) := card_toIntegerCube_vertices_eq_three_pow_mul U
  have hexp : N * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1)) ≤ 3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n) := by
    rw [hN]
    exact three_pow_mul_inv_pow_le (exponent_le_of_div hd hn hmn)
  have hpow : (3⁻¹ : ℝ≥0∞) ^ (L * j) ≤ (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1)) :=
    pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 (by norm_num))
      (Nat.mul_le_mul_left _ (Nat.sub_le j 1))
  -- the vertex events
  have hE1 : μ {ω | PartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
      n / (2 * d) ≤ (partitionCube ω x).scale} ≤ Ca * (3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n)) := by
    have hsub : {ω | PartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
        n / (2 * d) ≤ (partitionCube ω x).scale} ⊆ ⋃ x ∈ U.toIntegerCube.vertices,
          {ω | PartitionEvent ω ∧ j ≤ (partitionCube ω x).scale} := by
      rintro ω ⟨hP, x, hx, hxs⟩
      exact Set.mem_iUnion₂.2 ⟨x, hx, hP, hxs⟩
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    calc ∑ x ∈ U.toIntegerCube.vertices,
          μ {ω | PartitionEvent ω ∧ j ≤ (partitionCube ω x).scale}
        ≤ ∑ _x ∈ U.toIntegerCube.vertices, Ca * (3⁻¹ : ℝ≥0∞) ^ (L * j) :=
          Finset.sum_le_sum fun x _ => ha x j
      _ = Ca * (N * (3⁻¹ : ℝ≥0∞) ^ (L * j)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hNdef]
          ring
      _ ≤ Ca * (N * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1))) := by gcongr
      _ ≤ Ca * (3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n)) := by gcongr
  -- the cell events
  have hcell : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      μ ({ω | Aτ * (cube c.1 c.2).card <
          ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}) ≤
      (Cb + Cc) * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1)) := by
    intro V _ c hcm
    have hc1 : c.1 = j - 1 := fst_of_mem_midCubeCells hcm
    refine (measure_union_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ((hb c.1 c.2).trans (le_of_eq ?_)) ((hc c.1 c.2).trans (le_of_eq ?_))
    · rw [hc1]
    · rw [hc1]
  have hcard : ∑ V ∈ U.subcubesAt n, ((midCubeCells V j).card : ℝ≥0∞) ≤ N := by
    calc ∑ V ∈ U.subcubesAt n, ((midCubeCells V j).card : ℝ≥0∞)
        ≤ ∑ V ∈ U.subcubesAt n, (V.toIntegerCube.vertices.card : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun V hV => ?_
          have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
          exact_mod_cast card_midCubeCells_le (by omega : j < V.scale)
      _ = N := sum_card_subcubesAt_eq U hnm.le
  have hE2 : μ (⋃ V ∈ U.subcubesAt n, ⋃ c ∈ midCubeCells V j,
      ({ω | Aτ * (cube c.1 c.2).card <
          ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t})) ≤
      (Cb + Cc) * (3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ V ∈ U.subcubesAt n, μ (⋃ c ∈ midCubeCells V j,
          ({ω | Aτ * (cube c.1 c.2).card <
              ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
            {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
              K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}))
        ≤ ∑ V ∈ U.subcubesAt n, ∑ c ∈ midCubeCells V j,
            (Cb + Cc) * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1)) :=
          Finset.sum_le_sum fun V hV => (measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun c hc => hcell V hV c hc)
      _ = (Cb + Cc) * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1)) *
            ∑ V ∈ U.subcubesAt n, ((midCubeCells V j).card : ℝ≥0∞) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun V _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (Cb + Cc) * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1)) * N := by gcongr
      _ = (Cb + Cc) * (N * (3⁻¹ : ℝ≥0∞) ^ (L * (j - 1))) := by ring
      _ ≤ (Cb + Cc) * (3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n)) := by gcongr
  calc μ (cubeRestrictBad s t K τ Aτ U n)
      ≤ μ {ω | PartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
            n / (2 * d) ≤ (partitionCube ω x).scale} +
          μ (⋃ V ∈ U.subcubesAt n, ⋃ c ∈ midCubeCells V j,
            ({ω | Aτ * (cube c.1 c.2).card <
                ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
              {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
                K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t})) := by
        unfold cubeRestrictBad
        exact measure_union_le _ _
    _ ≤ Ca * (3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n)) +
          (Cb + Cc) * (3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n)) := add_le_add hE1 hE2
    _ = (Ca + (Cb + Cc)) * 3 ^ S * (3⁻¹ : ℝ≥0∞) ^ (β * n) := by ring

end Rigidity.Percolation
