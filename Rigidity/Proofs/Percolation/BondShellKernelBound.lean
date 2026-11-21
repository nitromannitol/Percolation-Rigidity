import Rigidity.Proofs.Percolation.BondShellStretchedExponential

/-!
# Quantitative bound for the planar shell kernel

The quadratic stretched-exponential shell kernel has total mass at most a constant times the
eighth inverse power of its decay rate.
-/

namespace Rigidity.Percolation

/-- The total quadratic shell weight grows at most like the eighth inverse power of the rate. -/
theorem shell_kernel_sum_le_inverse_eighth :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)) ∧
      (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)) ≤
        D * (1 + (1 / c) ^ 8) := by
  let w : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  let J : ℝ := ∑' n, w n
  let A : ℝ := 16 * (Nat.factorial 8 : ℝ)
  let D : ℝ := (1 + A) * (1 + J)
  have hw : Summable w := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective
    simpa only [w, Function.comp_def, Nat.cast_succ] using h
  have hw0 (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hJ : 0 ≤ J := tsum_nonneg hw0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun c hc => ?_⟩
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt n)
  let K : ℝ := 1 + A / c ^ 8
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hqs : Summable q := summable_shift_square_exp_sqrt c hc
  have hpoint (n : ℕ) : q n ≤ K * w n := by
    by_cases hn : n = 0
    · subst n
      have h : 0 ≤ A / c ^ 8 := div_nonneg hA (pow_nonneg hc.le _)
      have h' : (1 : ℝ) ≤ 1 + A / c ^ 8 := by linarith
      simpa [q, K, w] using h'
    · have hn' : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn'
      have hnpos : 0 < (n : ℝ) := by linarith
      have hnplus : 0 < (n : ℝ) + 1 := by positivity
      have hsq : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
      have hinv : 1 / (n : ℝ) ^ 2 ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hnpos 2) (pow_pos hnplus 2)]
        nlinarith
      have hmain := LatticeProb.pow_mul_exp_neg_sqrt_le_factorial_div_mul_inv_sq c hc 2 n hn'
      have hfac : 0 ≤ (Nat.factorial 8 : ℝ) / c ^ 8 := by positivity
      change (n : ℝ) ^ 2 * Real.exp (-c * Real.sqrt n) ≤
        ((Nat.factorial 8 : ℝ) / c ^ 8) * (1 / (n : ℝ) ^ 2) at hmain
      dsimp only [q, K, w, A]
      calc
        _ ≤ 4 * ((n : ℝ) ^ 2 * Real.exp (-c * Real.sqrt n)) := by
          nlinarith [Real.exp_pos (-c * Real.sqrt n)]
        _ ≤ 4 * (((Nat.factorial 8 : ℝ) / c ^ 8) * (1 / (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
        _ ≤ 4 * (((Nat.factorial 8 : ℝ) / c ^ 8) * (4 / ((n : ℝ) + 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv hfac) (by norm_num)
        _ = (16 * (Nat.factorial 8 : ℝ) / c ^ 8) * (1 / ((n : ℝ) + 1) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
          (div_nonneg (by norm_num) (sq_nonneg ((n : ℝ) + 1)))
  have hsum : (∑' n, q n) ≤ K * J := by
    calc
      _ ≤ ∑' n, K * w n := hqs.tsum_le_tsum hpoint (hw.mul_left K)
      _ = _ := tsum_mul_left
  have hinv : 0 ≤ (1 / c) ^ 8 := by positivity
  have hcoeff : K ≤ (1 + A) * (1 + (1 / c) ^ 8) := by
    dsimp only [K]
    rw [one_div, inv_pow, div_eq_mul_inv]
    have hinv' : 0 ≤ (c ^ 8)⁻¹ := inv_nonneg.mpr (pow_nonneg hc.le _)
    nlinarith [mul_nonneg hA hinv']
  refine ⟨hqs, hsum.trans ?_⟩
  calc
    K * J ≤ ((1 + A) * (1 + (1 / c) ^ 8)) * (1 + J) :=
      mul_le_mul hcoeff (by linarith) hJ (by positivity)
    _ = D * (1 + (1 / c) ^ 8) := by dsimp only [D]; ring

end Rigidity.Percolation
