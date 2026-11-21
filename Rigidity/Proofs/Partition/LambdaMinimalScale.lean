import Rigidity.Proofs.Partition.LambdaScale
import Rigidity.Proofs.Partition.MinimalScale

/-!
# Probability of many bad cubes near a triadic cube

The two failure events of `sum_pow_scale_le_of_counts` are rare. A bad cube of scale at least `J`
near the cube of scale `m` centred at the origin occurs with probability at most
`C 3^{d m} exp(-c 3^J)`, by a union bound over the at most `25ᵈ 3^{d m}` nearby cubes of each
scale. Once `j` is so large that `e · 25ᵈ · 3^{(τ + 1)(j + 1)} · C exp(-c 3^j) ≤ e⁻¹`, at least
`3^{e_j}` bad cubes of scale `j` in a residue class occur with probability at most `exp(-3^{e_j})`.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The threshold scale beyond which the residue classes rarely contain many bad cubes. -/
theorem exists_large_scale_exp_le (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (k : ℕ) :
    ∃ j0 : ℕ, 3 ≤ j0 ∧ ∀ j, j0 ≤ j →
      A * (3 : ℝ) ^ (k * (j + 1)) * Real.exp (-c * (3 : ℝ) ^ j) ≤ Real.exp (-1) := by
  set B : ℝ := A * 3 ^ k * ((k.factorial : ℝ) / (c / 2) ^ k) with hBdef
  have hB : 0 ≤ B := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 / c) * (1 + B)) (by norm_num : (1 : ℝ) < 3)
  refine ⟨max n 3, le_max_right _ _, fun j hj => ?_⟩
  set y : ℝ := (3 : ℝ) ^ j with hydef
  have hy0 : 0 ≤ y := by positivity
  have hyn : (2 / c) * (1 + B) < y :=
    hn.trans_le (pow_le_pow_right₀ (by norm_num) ((le_max_left _ _).trans hj))
  have h1 : (3 : ℝ) ^ (k * (j + 1)) = 3 ^ k * y ^ k := by
    rw [hydef, ← pow_mul, ← pow_add]
    congr 1
    ring
  have h2 := pow_mul_exp_neg_le k hc hy0
  have h3 : A * (3 : ℝ) ^ (k * (j + 1)) * Real.exp (-c * y) ≤ B * Real.exp (-(c / 2) * y) := by
    rw [h1, hBdef]
    have hA3 : 0 ≤ A * 3 ^ k := by positivity
    calc A * (3 ^ k * y ^ k) * Real.exp (-c * y) = A * 3 ^ k * (y ^ k * Real.exp (-c * y)) := by
          ring
      _ ≤ A * 3 ^ k * ((k.factorial : ℝ) / (c / 2) ^ k * Real.exp (-(c / 2) * y)) :=
          mul_le_mul_of_nonneg_left h2 hA3
      _ = _ := by ring
  have h4 : -(c / 2) * y ≤ -(1 + B) := by
    have : (c / 2) * ((2 / c) * (1 + B)) = 1 + B := by field_simp
    nlinarith
  have h5 : B * Real.exp (-(c / 2) * y) ≤ B * Real.exp (-(1 + B)) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h4) hB
  have h6 : B * Real.exp (-(1 + B)) ≤ Real.exp (-1) := by
    have hexp : Real.exp (-(1 + B)) = Real.exp (-1) * Real.exp (-B) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hBe : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    have hBe' : B * Real.exp (-B) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos B)]
      exact hBe
    have he : 0 < Real.exp (-1) := Real.exp_pos _
    nlinarith
  exact h3.trans (h5.trans h6)

/-- **A large bad cube near the cube of scale `m`** occurs with probability at most
`25ᵈ 3^{d m} C exp(-c 3^J) ∑_k exp(-2c)^k`. -/
theorem measure_exists_bad_near_le (p : unitInterval) {C1 c : ℝ} (hC1 : 0 ≤ C1) (hc : 0 < c)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * (3 : ℝ) ^ T.scale))) (m J : ℕ) :
    latticeBondLaw d p {ω | ∃ T : TriadicCube d, J ≤ T.scale ∧ T ∉ TriadicCube.goodCubes ω ∧
        ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} ≤
      ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) * ENNReal.ofReal (Real.exp (-c * 3 ^ J)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (3 - 1))) ^ k := by
  classical
  let B : ℕ → Set (Configuration d) := fun n =>
    ⋃ ι ∈ nearIndices d m n, {ω | (⟨n, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω}
  have hsub : {ω | ∃ T : TriadicCube d, J ≤ T.scale ∧ T ∉ TriadicCube.goodCubes ω ∧
      ∃ x ∈ (originCube d m).vertices, ∀ i, |x i - T.center i| ≤ 11 * T.side} ⊆
      {ω | ∃ n : ℕ, J ≤ n ∧ ω ∈ B n} := by
    rintro ω ⟨T, hJ, hbad, x, hx, hnear⟩
    refine ⟨T.scale, hJ, ?_⟩
    simp only [B, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨T.index, index_mem_nearIndices hx hnear, hbad⟩
  have hB : ∀ n : ℕ, latticeBondLaw d p (B n) ≤
      ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1) *
        ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := by
    intro n
    have hcard : ((nearIndices d m n).card : ℝ) ≤ 25 ^ d * 3 ^ (d * m) := by
      rw [card_nearIndices]
      have h1 : (1 : ℝ) ≤ 3 ^ (m - n) := one_le_pow₀ (by norm_num)
      have h2 : (3 : ℝ) ^ (m - n) ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      calc (2 * (3 : ℝ) ^ (m - n) + 23) ^ d ≤ (25 * 3 ^ m) ^ d := by gcongr; linarith
        _ = 25 ^ d * 3 ^ (d * m) := by rw [mul_pow, ← pow_mul, mul_comm m d]
    calc latticeBondLaw d p (B n)
        ≤ ∑ ι ∈ nearIndices d m n,
            latticeBondLaw d p {ω | (⟨n, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _ι ∈ nearIndices d m n, ENNReal.ofReal (C1 * Real.exp (-c * (3 : ℝ) ^ n)) :=
          Finset.sum_le_sum fun ι _ => hq _
      _ = ENNReal.ofReal ((nearIndices d m n).card * (C1 * Real.exp (-c * (3 : ℝ) ^ n))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (25 ^ d * 3 ^ (d * m) * C1 * Real.exp (-c * (3 : ℝ) ^ n)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : 0 ≤ C1 * Real.exp (-c * (3 : ℝ) ^ n) := by positivity
          calc ((nearIndices d m n).card : ℝ) * (C1 * Real.exp (-c * (3 : ℝ) ^ n))
              ≤ 25 ^ d * 3 ^ (d * m) * (C1 * Real.exp (-c * (3 : ℝ) ^ n)) :=
                mul_le_mul_of_nonneg_right hcard he
            _ = _ := by ring
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]
  exact (measure_mono hsub).trans
    (measure_exists_large_index_le_stretched _ B _ 3 c (by norm_num) hc hB J)

/-- **Many bad cubes in a residue class at a large scale** occur with probability at most
`exp(-3^{e})`, `e = d (m - j) - (τ + 1)(j + 1)`. -/
theorem measure_classBadCount_ge_le (p : unitInterval) {C1 c : ℝ} (hC1 : 0 ≤ C1)
    (hq : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * (3 : ℝ) ^ T.scale))) {m j τ : ℕ} (hj3 : 3 ≤ j)
    (hj : Real.exp 1 * 25 ^ d * C1 * (3 : ℝ) ^ ((τ + 1) * (j + 1)) *
      Real.exp (-c * (3 : ℝ) ^ j) ≤ Real.exp (-1))
    (hexp : (τ + 1) * (j + 1) ≤ d * (m - j)) (r : Fin d → Fin 3) :
    latticeBondLaw d p {ω | 3 ^ (d * (m - j) - (τ + 1) * (j + 1)) ≤ classBadCount ω m j r} ≤
      ENNReal.ofReal (Real.exp (-(3 : ℝ) ^ (d * (m - j) - (τ + 1) * (j + 1)))) := by
  set e := d * (m - j) - (τ + 1) * (j + 1) with hedef
  set a : ℝ := C1 * Real.exp (-c * (3 : ℝ) ^ j) with hadef
  have ha : 0 ≤ a := by positivity
  have hk : 0 < 3 ^ e := by positivity
  have h := measure_le_classBadCount_le p ha (m := m) hj3 (fun ι => hq _) r hk
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hde : d * (m - j) = e + (τ + 1) * (j + 1) := by omega
  have hN : (2 * (3 : ℝ) ^ (m - j) + 23) ^ d ≤ 25 ^ d * (3 ^ e * 3 ^ ((τ + 1) * (j + 1))) := by
    have h1 : (1 : ℝ) ≤ 3 ^ (m - j) := one_le_pow₀ (by norm_num)
    calc (2 * (3 : ℝ) ^ (m - j) + 23) ^ d ≤ (25 * 3 ^ (m - j)) ^ d := by gcongr; linarith
      _ = 25 ^ d * 3 ^ (d * (m - j)) := by rw [mul_pow, ← pow_mul, mul_comm (m - j) d]
      _ = _ := by rw [hde, pow_add]
  have hbase : Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ) ≤
      Real.exp (-1) := by
    have hpos : (0 : ℝ) < ((3 ^ e : ℕ) : ℝ) := by exact_mod_cast hk
    rw [div_le_iff₀ hpos]
    have hcast : ((3 ^ e : ℕ) : ℝ) = 3 ^ e := by push_cast; ring
    rw [hcast]
    have hea : 0 ≤ Real.exp 1 * a := by positivity
    calc Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a
        ≤ Real.exp 1 * (25 ^ d * (3 ^ e * 3 ^ ((τ + 1) * (j + 1)))) * a := by gcongr
      _ = (Real.exp 1 * 25 ^ d * C1 * (3 : ℝ) ^ ((τ + 1) * (j + 1)) *
            Real.exp (-c * (3 : ℝ) ^ j)) * 3 ^ e := by rw [hadef]; ring
      _ ≤ Real.exp (-1) * 3 ^ e := mul_le_mul_of_nonneg_right hj (by positivity)
  have hb0 : 0 ≤ Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ) := by
    positivity
  calc (Real.exp 1 * (2 * (3 : ℝ) ^ (m - j) + 23) ^ d * a / ((3 ^ e : ℕ) : ℝ)) ^ (3 ^ e)
      ≤ Real.exp (-1) ^ (3 ^ e) := pow_le_pow_left₀ hb0 hbase _
    _ = Real.exp (-(3 : ℝ) ^ e) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

end Rigidity.Percolation
