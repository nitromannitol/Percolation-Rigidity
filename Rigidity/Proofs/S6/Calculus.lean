import Rigidity.Steps.S6.SlowMixing

/-!
# Calculus for the mixing time bounds of the sandpile chain

Steps `UpperTimeStep` (paper L2951 of the corrected draft) and `LowerBoundStep` (paper
L2964-2969, correction C25c).

* Upper time: for `1 ≤ m ≤ (2n+1)^d ≤ 3^d n^d`,
  `log(2m(1 + 1/ε)) ≤ log(2(1 + 1/ε)) + d log 3 + d log n ≤ (d+1) log n` for large `n`, so
  `K m log(2m(1 + 1/ε)) ≤ K 3^d (d+1) n^d log n`.
* Lower bound: for `m ≥ 8`, `log(1 - 4/m) ≥ 1 - (1 - 4/m)⁻¹ ≥ -8/m`
  (`Real.one_sub_inv_le_log_of_pos`), so with `c = c₀/32`, `m, N ≥ c₀ n^d` and
  `t ≤ c n^d log n`,
  `log (N (1 - 4/m)^{2t}) ≥ log c₀ + d log n - 16t/m ≥ log c₀ + (1/2) log n → ∞` (`d ≥ 1`).
-/

open Filter

namespace Rigidity.Proofs.S6

/-- Calculus for step:6.5-upper (paper L2951): `K m log(2m(1 + 1/ε)) ≤ C n^d log n` for
`m ≤ (2n+1)^d` and large `n`, with `C = K 3^d (d+1)`. -/
theorem upperTimeStep {d : ℕ} : Steps.S6.UpperTimeStep d := by
  intro K hK
  refine ⟨K * 3 ^ d * (d + 1), by positivity, fun ε hε => ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (Real.log (2 * (1 + 1 / ε)) + d * Real.log 3)
  filter_upwards [hlog, eventually_ge_atTop 1] with n hn hn1 m hm
  simp only [Function.comp_apply] at hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1'
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  have hm3 : (m : ℝ) ≤ 3 ^ d * (n : ℝ) ^ d := by
    rw [← mul_pow]
    calc (m : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast hm
      _ ≤ (3 * n) ^ d := by
        gcongr
        push_cast
        linarith
  have hε' : 0 < 2 * (1 + 1 / ε) := by positivity
  have hlogm : Real.log m ≤ d * Real.log 3 + d * Real.log n := by
    calc Real.log m ≤ Real.log (3 ^ d * (n : ℝ) ^ d) := Real.log_le_log (by positivity) hm3
      _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hL : Real.log (2 * m * (1 + 1 / ε)) ≤ (d + 1) * Real.log n := by
    rw [show 2 * (m : ℝ) * (1 + 1 / ε) = 2 * (1 + 1 / ε) * m by ring,
      Real.log_mul hε'.ne' (by positivity)]
    linarith
  have hL0 : 0 ≤ Real.log (2 * m * (1 + 1 / ε)) := by
    apply Real.log_nonneg
    have : (0 : ℝ) < 1 / ε := by positivity
    nlinarith
  calc K * m * Real.log (2 * m * (1 + 1 / ε))
      ≤ K * (3 ^ d * (n : ℝ) ^ d) * ((d + 1) * Real.log n) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm3 hK.le) hL hL0 (by positivity)
    _ = K * 3 ^ d * (d + 1) * (n : ℝ) ^ d * Real.log n := by ring

/-- Calculus for step:6.5-lower (paper L2964-2969, correction C25c): with `c = c₀/32`, if
`m, N ≥ c₀ n^d` and `t ≤ c n^d log n` then `N (1 - 4/m)^{2t} ≥ ε` for large `n` (`d ≥ 1`). -/
theorem lowerBoundStep {d : ℕ} (hd : 1 ≤ d) : Steps.S6.LowerBoundStep d := by
  intro c₀ hc₀
  refine ⟨c₀ / 32, by positivity, fun ε hε => ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (2 * (Real.log ε - Real.log c₀))
  filter_upwards [hlog, tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 / c₀),
    eventually_ge_atTop 1] with n hn hn8 hn1 m N t hm hN ht
  simp only [Function.comp_apply] at hn
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have hnd : (n : ℝ) ≤ (n : ℝ) ^ d := le_self_pow₀ hn1' (by omega)
  have hc₀n : 0 < c₀ * (n : ℝ) ^ d := by positivity
  have hm8 : (8 : ℝ) ≤ m := by
    calc (8 : ℝ) = c₀ * (8 / c₀) := by field_simp
      _ ≤ c₀ * (n : ℝ) ^ d := by gcongr; linarith
      _ ≤ m := hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hc₀n hN
  -- `y = 4/m ∈ [0, 1/2]` and `log (1 - y) ≥ -2y`
  have hy0 : (0 : ℝ) ≤ 4 / m := by positivity
  have hy2 : 4 / (m : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    linarith
  have hxpos : 0 < 1 - 4 / (m : ℝ) := by linarith
  have hlogx : -(2 * (4 / (m : ℝ))) ≤ Real.log (1 - 4 / (m : ℝ)) := by
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hxpos)
    have : (1 - 4 / (m : ℝ))⁻¹ ≤ 1 + 2 * (4 / m) := by
      rw [inv_eq_one_div, div_le_iff₀ hxpos]
      nlinarith [mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - 2 * (4 / m))]
    linarith
  -- `16 t / m ≤ (1/2) log n`
  have h16 : 16 * (t : ℝ) / m ≤ 1 / 2 * Real.log n := by
    rw [div_le_iff₀ hmpos]
    nlinarith [mul_le_mul_of_nonneg_left hm hlogn]
  have hB : -(1 / 2 * Real.log n) ≤ 2 * (t : ℝ) * Real.log (1 - 4 / (m : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hlogx (by positivity : (0 : ℝ) ≤ 2 * t)
    have e : 2 * (t : ℝ) * -(2 * (4 / m)) = -(16 * t / m) := by ring
    linarith
  have hA : Real.log c₀ + Real.log n ≤ Real.log N := by
    calc Real.log c₀ + Real.log n ≤ Real.log c₀ + Real.log ((n : ℝ) ^ d) := by
          gcongr
      _ = Real.log (c₀ * (n : ℝ) ^ d) := (Real.log_mul hc₀.ne' (by positivity)).symm
      _ ≤ Real.log N := Real.log_le_log hc₀n hN
  rw [← Real.log_le_log_iff hε (mul_pos hNpos (pow_pos hxpos _)),
    Real.log_mul hNpos.ne' (pow_pos hxpos _).ne', Real.log_pow]
  push_cast
  linarith

end Rigidity.Proofs.S6
