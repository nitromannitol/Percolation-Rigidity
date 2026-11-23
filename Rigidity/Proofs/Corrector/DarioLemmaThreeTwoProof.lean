import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoMean
import Rigidity.Proofs.Corrector.DarioPropThreeOne

/-!
# Dario's Lemma 3.2 from the quantitative sublinearity (1.22)

`darioLemmaThreeTwo_of_osc`: **Lemma 3.2** (`DarioLemmaThreeTwo`,
`|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r`) from the order-zero regularity (R3) and (1.22)
(`CorrectorOscSublinearTwo`), following Dario's proof with `3^k ≤ r^{1/2} < 3^{k+1}`:

* Step 1 (`exists_lintegral_abs_statDiscrepancy_le`): the coarsened gradients of `𝒫` and
  `𝒫_stat^k` differ by `χ(z̄_stat(y)) - χ(z̄(y)) - (χ(z̄_stat(y + e_j)) - χ(z̄(y + e_j)))`, of
  expectation at most `2 K (1 + θ₀ 9^k)^4 e^{-c 3^k/2}`;
* Step 2 (`sum_statMean_period_eq_zero`): the mean of `∇[χ]_{𝒫_stat^k}` is `3^k`-periodic with sum
  zero over a period;
* Step 3 (`abs_tsum_openHeat_mul_periodic_le_exp`): its heat-kernel average is at most
  `e^{-16 r}` times its sum over a period.

The polynomial factors are absorbed by `e^{-c √r / 6}` (`exp_bound_lemmaThreeTwo`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

theorem summable_latticeHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    Summable fun y => latticeHeat t x y :=
  (ENNReal.summable_toReal (by rw [tsum_ofReal_latticeHeat ht x]; exact ENNReal.one_ne_top)).congr
    fun y => ENNReal.toReal_ofReal (latticeHeat_nonneg ht x y)

theorem tsum_latticeHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) : ∑' y, latticeHeat t x y = 1 := by
  have h := tsum_ofReal_latticeHeat ht x
  rw [← ENNReal.ofReal_tsum_of_nonneg (latticeHeat_nonneg ht x) (summable_latticeHeat ht x)] at h
  have h0 : 0 ≤ ∑' y, latticeHeat t x y := tsum_nonneg (latticeHeat_nonneg ht x)
  rw [← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).1 h

/-- `y^n e^{-a y} ≤ n! / a^n` for `y ≥ 0` and `a > 0`. -/
theorem pow_mul_exp_neg_le {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n * Real.exp (-(a * y)) ≤ n.factorial / a ^ n := by
  have h := Real.pow_div_factorial_le_exp (a * y) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have han : 0 < a ^ n := pow_pos ha n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [le_div_iff₀ han]
  have he : Real.exp (-(a * y)) * Real.exp (a * y) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos := Real.exp_pos (-(a * y))
  calc y ^ n * Real.exp (-(a * y)) * a ^ n = (a ^ n * y ^ n) * Real.exp (-(a * y)) := by ring
    _ ≤ (Real.exp (a * y) * n.factorial) * Real.exp (-(a * y)) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = n.factorial * (Real.exp (-(a * y)) * Real.exp (a * y)) := by ring
    _ = n.factorial := by rw [he, mul_one]

/-- **The final inequality of Lemma 3.2**: for `r ≥ 1` and `9^k ≤ r < 9^{k+1}`,
`e^{-16 r} 9^k (2A + 2B) + 2B ≤ (A/64 + 4K')/r` with `B = K (1 + θ₀ 9^k)^4 e^{-c 3^k/2}`. -/
theorem exp_bound_lemmaThreeTwo {A K c θ₀ r : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hc : 0 < c)
    (hθ₀ : 0 ≤ θ₀) (hr : 1 ≤ r) {k : ℕ} (h9k : (9 : ℝ) ^ k ≤ r) (hr9 : r < 9 * 9 ^ k) :
    Real.exp (-(16 * r)) * 9 ^ k * (2 * A + 2 * (K * (1 + θ₀ * 9 ^ k) ^ 4 *
        Real.exp (-(c * 3 ^ k / 2)))) + 2 * (K * (1 + θ₀ * 9 ^ k) ^ 4 *
        Real.exp (-(c * 3 ^ k / 2))) ≤
      (A / 64 + 4 * (K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12))) / r := by
  have hr0 : 0 < r := by linarith
  set B := K * (1 + θ₀ * 9 ^ k) ^ 4 * Real.exp (-(c * 3 ^ k / 2)) with hB
  have hB0 : 0 ≤ B := by positivity
  set x := Real.sqrt r with hx
  have hx1 : 1 ≤ x := by rw [hx]; exact Real.one_le_sqrt.2 hr
  have hxr : x ^ 2 = r := Real.sq_sqrt hr0.le
  -- `3^k ≥ √r / 3`
  have h3k : x / 3 ≤ (3 : ℝ) ^ k := by
    have h9 : (9 : ℝ) ^ k = ((3 : ℝ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 : (x / 3) ^ 2 ≤ ((3 : ℝ) ^ k) ^ 2 := by
      rw [div_pow, hxr, ← h9]
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  -- the bound on `r B`
  have hrB : r * B ≤ K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) / r := by
    have hpoly : (1 + θ₀ * 9 ^ k) ^ 4 ≤ (1 + θ₀) ^ 4 * x ^ 8 := by
      have h1 : 1 + θ₀ * 9 ^ k ≤ (1 + θ₀) * x ^ 2 := by
        rw [hxr]
        nlinarith
      calc (1 + θ₀ * 9 ^ k) ^ 4 ≤ ((1 + θ₀) * x ^ 2) ^ 4 :=
            pow_le_pow_left₀ (by positivity) h1 4
        _ = (1 + θ₀) ^ 4 * x ^ 8 := by ring
    have hexp : Real.exp (-(c * 3 ^ k / 2)) ≤ Real.exp (-(c / 6 * x)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hf := pow_mul_exp_neg_le (a := c / 6) (y := x) (by positivity) (by positivity) 12
    have hr2 : r * r = x ^ 4 := by rw [← hxr]; ring
    rw [le_div_iff₀ hr0, hB]
    calc r * (K * (1 + θ₀ * 9 ^ k) ^ 4 * Real.exp (-(c * 3 ^ k / 2))) * r
        ≤ r * (K * ((1 + θ₀) ^ 4 * x ^ 8) * Real.exp (-(c / 6 * x))) * r := by gcongr
      _ = K * (1 + θ₀) ^ 4 * (x ^ 12 * Real.exp (-(c / 6 * x))) := by
          rw [← hxr]
          ring
      _ ≤ K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) := by gcongr
  -- the bound on `e^{-16 r} r`
  have hexpr : Real.exp (-(16 * r)) * r ≤ 1 / (128 * r) := by
    have h := pow_mul_exp_neg_le (a := 16) (y := r) (by norm_num) hr0.le 2
    rw [le_div_iff₀ (by positivity)]
    have : (Nat.factorial 2 : ℝ) / 16 ^ 2 = 1 / 128 := by norm_num [Nat.factorial]
    rw [this] at h
    nlinarith
  have hexp1 : Real.exp (-(16 * r)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  set K' := K * (1 + θ₀) ^ 4 * (Nat.factorial 12 / (c / 6) ^ 12) with hK'
  have hB' : B ≤ K' / r := by
    have : B ≤ r * B := le_mul_of_one_le_left hB0 hr
    linarith
  calc Real.exp (-(16 * r)) * 9 ^ k * (2 * A + 2 * B) + 2 * B
      ≤ Real.exp (-(16 * r)) * r * (2 * A) + r * (2 * B) + 2 * B := by
        have h1 : Real.exp (-(16 * r)) * 9 ^ k ≤ Real.exp (-(16 * r)) * r :=
          mul_le_mul_of_nonneg_left h9k (Real.exp_pos _).le
        have h2 : Real.exp (-(16 * r)) * r ≤ r := by nlinarith [Real.exp_pos (-(16 * r))]
        nlinarith [Real.exp_pos (-(16 * r))]
    _ ≤ 1 / (128 * r) * (2 * A) + 2 * (K' / r) + 2 * (K' / r) := by
        have t1 : Real.exp (-(16 * r)) * r * (2 * A) ≤ 1 / (128 * r) * (2 * A) :=
          mul_le_mul_of_nonneg_right hexpr (by positivity)
        have t2 : r * (2 * B) ≤ 2 * (K' / r) := by linarith [hrB]
        have t3 : 2 * B ≤ 2 * (K' / r) := by linarith [hB']
        linarith [t1, t2, t3]
    _ = (A / 64 + 4 * K') / r := by
        field_simp
        ring

end Rigidity.Corrector
