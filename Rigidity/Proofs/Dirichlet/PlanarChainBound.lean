import Rigidity.Proofs.Dirichlet.PlanarErrorChain

/-!
# The rate of the error chain of Section 6 in dimension two

With `K = 3^k`, `L = 3^m`, `Λ = 3^{k₀}`, `8k ≤ m + 7`, the normalized sums of the datum
`S₂ ≤ L² A₂ M²`, `S_t ≤ L² A_t M^t` and the mesoscopic error `ε ≤ E K^{-c₀}`, the errors of the
chain are bounded by `δ₁ ≤ B₁ L² M² K^{-c₀}` (`chainDeltaOne_le`),
`δ₂ ≤ B₂ Λ⁶ L² M² K^{-c₀}` (`chainDeltaTwo_le`) and `δ₃ ≤ (612 K₀ K² Λ⁶ + 2 C₃) S₂`
(`chainDeltaThree_le`), for `c₀ ≤ min(1/2, 4(1 − 2/t), 4γ)`; the right side of `planar_error_chain`
is then at most `B Λ¹² L⁴ M² K^{-c₀}` (`chain_le`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

theorem three_pow_mul_eq (a k : ℕ) : (3 : ℝ) ^ (a * k) = ((3 : ℝ) ^ k) ^ a := by
  rw [mul_comm, pow_mul]

theorem rpow_le_mul_rpow_neg_of_le_div_pow {K x c e : ℝ} {n : ℕ} (hK : 1 ≤ K) (hx : 0 ≤ x)
    (hc : 0 ≤ c) (he : 0 ≤ e) (h : x ≤ c / K ^ n) :
    x ^ e ≤ c ^ e * K ^ (-((n : ℝ) * e)) := by
  have hK0 : 0 < K := by linarith
  calc x ^ e ≤ (c / K ^ n) ^ e := Real.rpow_le_rpow hx h he
    _ = c ^ e * K ^ (-((n : ℝ) * e)) := by
      rw [Real.div_rpow hc (by positivity), Real.rpow_neg hK0.le, Real.rpow_mul hK0.le,
        Real.rpow_natCast, div_eq_mul_inv]

theorem rpow_neg_le_rpow_neg {K a b : ℝ} (hK : 1 ≤ K) (h : b ≤ a) : K ^ (-a) ≤ K ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_le hK (neg_le_neg h)

theorem one_div_le_rpow_neg {K c : ℝ} (hK : 1 ≤ K) (hc : c ≤ 1) : 1 / K ≤ K ^ (-c) := by
  rw [one_div, ← Real.rpow_neg_one K]
  exact rpow_neg_le_rpow_neg hK hc

theorem sqrt_one_div_le_rpow_neg {K c : ℝ} (hK : 1 ≤ K) (hc : c ≤ 1 / 2) :
    √(1 / K) ≤ K ^ (-c) := by
  have hK0 : 0 < K := by linarith
  rw [show (1 : ℝ) / K = K⁻¹ from one_div K, Real.sqrt_eq_rpow, Real.inv_rpow hK0.le,
    ← Real.rpow_neg hK0.le]
  exact rpow_neg_le_rpow_neg hK hc

theorem rpow_two_div_mul_rpow {M a t : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (ht : 0 < t) :
    (a * M ^ t) ^ (2 / t) = a ^ (2 / t) * M ^ 2 := by
  rw [Real.mul_rpow ha (Real.rpow_nonneg hM _), ← Real.rpow_mul hM,
    show t * (2 / t) = 2 by field_simp, Real.rpow_two]

/-- The constant of the bound of `δ₁`. -/
noncomputable def chainBoundOne (σ E t A2 At : ℝ) : ℝ :=
  2 * (E * σ ^ 2 + 5 * σ) * A2 + 2 * σ * A2 +
    σ * (12 * 3 ^ 7) ^ (1 - 2 / t) *
      ((2 : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t)) * At) ^ (2 / t)

/-- **The bound of the error `δ₁` of Lemma 6.2.** -/
theorem chainDeltaOne_le {σ ε t E A2 At c₀ M S2 St : ℝ} {m k : ℕ} (hσ : 0 < σ) (ht : 2 < t)
    (hE : 0 ≤ E) (hAt : 0 ≤ At) (hM : 0 ≤ M) (hc₀ : c₀ ≤ 1 / 2)
    (hc₀t : c₀ ≤ 4 * (1 - 2 / t)) (hkm : 8 * k ≤ m + 7)
    (hε : ε ≤ E * ((3 : ℝ) ^ k) ^ (-c₀)) (hS20 : 0 ≤ S2)
    (hS2 : S2 ≤ ((3 : ℝ) ^ m) ^ 2 * (A2 * M ^ 2)) (hSt0 : 0 ≤ St)
    (hSt : St / ((3 : ℝ) ^ m) ^ 2 ≤ At * M ^ t) :
    chainDeltaOne σ ε t m k S2 St ≤
      chainBoundOne σ E t A2 At * (((3 : ℝ) ^ m) ^ 2 * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀)) := by
  have e1 : ((((3 ^ (2 * k - k) - 1) * 3 ^ k : ℕ) : ℝ)) = ((3 : ℝ) ^ k - 1) * (3 : ℝ) ^ k := by
    rw [show 2 * k - k = k by omega, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
    push_cast
    ring
  have hKL : ((3 : ℝ) ^ k) ^ 8 ≤ 3 ^ 7 * (3 : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hL0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  unfold chainDeltaOne
  rw [e1]
  push_cast
  simp only [three_pow_mul_eq]
  set K := (3 : ℝ) ^ k with hK
  set L := (3 : ℝ) ^ m with hL
  set Kc := K ^ (-c₀) with hKc
  have hK0 : 0 < K := by linarith
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg hK0.le _
  have hinvK : 1 / K ≤ Kc := one_div_le_rpow_neg hK1 (by linarith)
  have hsqK : √(1 / K) ≤ Kc := sqrt_one_div_le_rpow_neg hK1 hc₀
  have hX' : 1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2 ≤ 2 * (1 / K) := by
    have e : ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2 = (1 - 1 / K) ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_nonneg (1 / K)]
  have hsqX : √(1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2) ≤ 2 * Kc := by
    refine (Real.sqrt_le_sqrt hX').trans ?_
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    have h2 : √(2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have := Real.sqrt_nonneg (1 / K)
    nlinarith
  have hsqK2 : √(1 / K ^ 2) = 1 / K := by
    rw [show (1 : ℝ) / K ^ 2 = (1 / K) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsqK2' : √(K ^ 2) = K := Real.sqrt_sq hK0.le
  have he : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact ht.le
  have ht0 : 0 < t := by linarith
  have ha : 2 * ((ε * σ ^ 2 + σ * (1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2) / 2 +
      σ * (√(1 / K ^ 2) + √(1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2) + √(1 / K))) * S2) ≤
      2 * ((E * σ ^ 2 + 5 * σ) * Kc * (L ^ 2 * (A2 * M ^ 2))) := by
    have hb : ε * σ ^ 2 + σ * (1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2) / 2 +
        σ * (√(1 / K ^ 2) + √(1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2) + √(1 / K)) ≤
        (E * σ ^ 2 + 5 * σ) * Kc := by
      rw [hsqK2]
      have h1 : ε * σ ^ 2 ≤ E * Kc * σ ^ 2 := mul_le_mul_of_nonneg_right hε (sq_nonneg σ)
      have h2 := mul_le_mul_of_nonneg_left (hX'.trans (by linarith : 2 * (1 / K) ≤ 2 * Kc)) hσ.le
      have h3 : σ * (1 / K + √(1 - ((K - 1) * K) ^ 2 / (K ^ 2) ^ 2) + √(1 / K)) ≤
          σ * (4 * Kc) := mul_le_mul_of_nonneg_left (by linarith) hσ.le
      linarith
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb hS2 hS20 (by positivity)) (by norm_num)
  have hb' : 2 * (σ / √(K ^ 2) * S2) ≤ 2 * (σ * Kc * (L ^ 2 * (A2 * M ^ 2))) := by
    rw [hsqK2']
    have hb : σ / K ≤ σ * Kc := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvK hσ.le
    exact mul_le_mul_of_nonneg_left (mul_le_mul hb hS2 hS20 (by positivity)) (by norm_num)
  have hc' : L ^ 2 * (σ * ((2 * 2 * (K ^ 4 + 1 + K ^ 2) / L) ^ (1 - 2 / t) *
      ((2 : ℝ) ^ (t / 2 - 1) *
        ((1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t * (K ^ 2 / K ^ 4) ^ t)) * St) / L ^ 2) ^ (2 / t))) ≤
      L ^ 2 * (σ * (((12 * 3 ^ 7) ^ (1 - 2 / t) * Kc) * (((2 : ℝ) ^ (t / 2 - 1) *
        (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t)) * At) ^ (2 / t) * M ^ 2))) := by
    have hbase : 2 * 2 * (K ^ 4 + 1 + K ^ 2) / L ≤ 12 * 3 ^ 7 / K ^ 4 := by
      have h4 : K ^ 4 + 1 + K ^ 2 ≤ 3 * K ^ 4 := by
        have := one_le_pow₀ (n := 4) hK1
        have := pow_le_pow_right₀ hK1 (show 2 ≤ 4 by norm_num)
        linarith
      rw [div_le_div_iff₀ hL0 (show (0 : ℝ) < K ^ 4 by positivity)]
      calc 2 * 2 * (K ^ 4 + 1 + K ^ 2) * K ^ 4 ≤ 2 * 2 * (3 * K ^ 4) * K ^ 4 := by gcongr
        _ = 12 * K ^ 8 := by ring
        _ ≤ 12 * (3 ^ 7 * L) := by gcongr
        _ = 12 * 3 ^ 7 * L := by ring
    have hpow1 := rpow_le_mul_rpow_neg_of_le_div_pow hK1 (by positivity) (by norm_num) he hbase
    have hpow1' : (2 * 2 * (K ^ 4 + 1 + K ^ 2) / L) ^ (1 - 2 / t) ≤
        (12 * 3 ^ 7) ^ (1 - 2 / t) * Kc :=
      hpow1.trans (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hK1 (by push_cast; linarith))
        (by positivity))
    have hq1 : (K ^ 2 / K ^ 4) ^ t ≤ 1 :=
      Real.rpow_le_one (by positivity) ((div_le_one (by positivity)).2
        (pow_le_pow_right₀ hK1 (by norm_num))) ht0.le
    have hc1 : 1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t * (K ^ 2 / K ^ 4) ^ t) ≤
        1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t) := by
      have h := mul_le_mul_of_nonneg_left hq1 (by positivity : (0 : ℝ) ≤ 2 ^ t)
      rw [mul_one] at h
      have := mul_le_mul_of_nonneg_left (show 1 + 2 ^ t + 2 ^ t * (K ^ 2 / K ^ 4) ^ t ≤
        1 + 2 ^ t + 2 ^ t by linarith) (by positivity : (0 : ℝ) ≤ 3 ^ (t - 1))
      linarith
    have hinner : (2 : ℝ) ^ (t / 2 - 1) *
        ((1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t * (K ^ 2 / K ^ 4) ^ t)) * St) / L ^ 2 ≤
        (2 : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t)) * At * M ^ t :=
      calc (2 : ℝ) ^ (t / 2 - 1) *
            ((1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t * (K ^ 2 / K ^ 4) ^ t)) * St) / L ^ 2 =
            (2 : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t * (K ^ 2 / K ^ 4) ^ t)) *
              (St / L ^ 2) := by ring
        _ ≤ (2 : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t)) * (At * M ^ t) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hc1 (by positivity)) hSt (by positivity)
            (by positivity)
        _ = (2 : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t)) * At * M ^ t := by
          ring
    have hpow2 := Real.rpow_le_rpow (by positivity) hinner (by positivity : (0 : ℝ) ≤ 2 / t)
    rw [rpow_two_div_mul_rpow
      (a := (2 : ℝ) ^ (t / 2 - 1) * (1 + 3 ^ (t - 1) * (1 + 2 ^ t + 2 ^ t)) * At) hM
      (by positivity) ht0] at hpow2
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul hpow1' hpow2
      (by positivity) (by positivity)) hσ.le) (by positivity)
  refine (add_le_add (add_le_add ha hb') hc').trans (le_of_eq ?_)
  unfold chainBoundOne
  ring

theorem nine_pow_eq (n : ℕ) : (9 : ℝ) ^ n = ((3 : ℝ) ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

theorem eightyone_pow_eq (n : ℕ) : (81 : ℝ) ^ n = ((3 : ℝ) ^ n) ^ 4 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The bound of the Poincaré constants of the chain. -/
theorem chainP_le {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (m k₀ : ℕ) :
    chainP K₀ m k₀ ≤ 153 / 2 * K₀ * ((3 : ℝ) ^ m) ^ 2 * ((3 : ℝ) ^ k₀) ^ 6 := by
  unfold chainP
  rw [nine_pow_eq k₀, eightyone_pow_eq k₀, nine_pow_eq (m + 1), pow_succ (3 : ℝ) m]
  have hΛ : 1 ≤ ((3 : ℝ) ^ k₀) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have h : 1 + 9 / 8 * ((3 : ℝ) ^ k₀) ^ 2 ≤ 17 / 8 * ((3 : ℝ) ^ k₀) ^ 2 := by linarith
  calc 4 * (1 + 9 / 8 * ((3 : ℝ) ^ k₀) ^ 2) * K₀ * ((3 : ℝ) ^ m * 3) ^ 2 * ((3 : ℝ) ^ k₀) ^ 4
      ≤ 4 * (17 / 8 * ((3 : ℝ) ^ k₀) ^ 2) * K₀ * ((3 : ℝ) ^ m * 3) ^ 2 *
        ((3 : ℝ) ^ k₀) ^ 4 := by gcongr
    _ = 153 / 2 * K₀ * ((3 : ℝ) ^ m) ^ 2 * ((3 : ℝ) ^ k₀) ^ 6 := by ring

theorem chainP_nonneg {K₀ : ℝ} (hK₀ : 0 ≤ K₀) (m k₀ : ℕ) : 0 ≤ chainP K₀ m k₀ := by
  unfold chainP
  positivity

/-- **The bound of the error `δ₃`.** -/
theorem chainDeltaThree_le {σ K₀ C₃ S2 : ℝ} {k k₀ : ℕ} (hσ : 0 < σ) (hK₀ : 0 ≤ K₀)
    (hC₃ : 0 ≤ C₃) (hS2 : 0 ≤ S2) :
    chainDeltaThree σ K₀ C₃ k k₀ S2 ≤
      (612 * K₀ * ((3 : ℝ) ^ k) ^ 2 * ((3 : ℝ) ^ k₀) ^ 6 + 2 * C₃) * S2 := by
  have hPT := chainP_le hK₀ k k₀
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  unfold chainDeltaThree
  change 2 * (chainP K₀ k k₀ * (4 * S2)) + _ ≤ _
  push_cast
  simp only [three_pow_mul_eq]
  rw [div_self hσ.ne', one_mul]
  have hq : C₃ * ((3 : ℝ) ^ k) ^ 4 / (((3 : ℝ) ^ k) ^ 4) ^ 2 ≤ C₃ := by
    rw [mul_div_assoc]
    refine mul_le_of_le_one_right hC₃ ?_
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ ((3 : ℝ) ^ k) ^ 4 := one_le_pow₀ hK1
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hPT (by positivity : (0 : ℝ) ≤ 4 * S2)
  have h2 := mul_le_mul_of_nonneg_right hq hS2
  linarith

/-- The constant of the bound of `δ₂`. -/
noncomputable def chainBoundTwo (σ E γ t K₀ CA A2 At : ℝ) : ℝ :=
  6 * (E + 12) * A2 + 18 * max σ 1 * (240 * max σ 1 / σ + 1) * A2 +
    6 * max σ 1 * (612 * K₀ + 2 * CA) * A2 +
    (2 + 3 * max σ 1 / σ) * (2 * (σ * (40 * 3 ^ 7) ^ (1 - 2 / t) *
        ((2 : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t)) +
      88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * 2) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) * (10 * 3 ^ 7) ^ γ *
        ((2 : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t))

/-- **The bound of the error `δ₂` of Lemma 6.3.** -/
theorem chainDeltaTwo_le {σ ε γ t E A2 At c₀ M S2 St K₀ CA : ℝ} {m k k₀ : ℕ} (hσ : 0 < σ)
    (ht : 2 < t) (hγ0 : 0 < γ) (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2)
    (hAt : 0 ≤ At) (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀) (hCA : 0 ≤ CA) (hc₀ : c₀ ≤ 1 / 2)
    (hc₀t : c₀ ≤ 4 * (1 - 2 / t)) (hc₀γ : c₀ ≤ 4 * γ) (hkm : 8 * k ≤ m + 7)
    (hε : ε ≤ E * ((3 : ℝ) ^ k) ^ (-c₀)) (hS20 : 0 ≤ S2)
    (hS2 : S2 ≤ ((3 : ℝ) ^ m) ^ 2 * (A2 * M ^ 2)) (hSt0 : 0 ≤ St)
    (hSt : St / ((3 : ℝ) ^ m) ^ 2 ≤ At * M ^ t) :
    chainDeltaTwo σ ε γ t K₀ CA m k k₀ S2 St ≤
      chainBoundTwo σ E γ t K₀ CA A2 At *
        (((3 : ℝ) ^ k₀) ^ 6 * (((3 : ℝ) ^ m) ^ 2 * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀))) := by
  have hKL : ((3 : ℝ) ^ k) ^ 8 ≤ 3 ^ 7 * (3 : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hL0 : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hPT := chainP_le hK₀ k k₀
  unfold chainDeltaTwo chainPT
  push_cast
  simp only [three_pow_mul_eq]
  set K := (3 : ℝ) ^ k with hK
  set L := (3 : ℝ) ^ m with hL
  set Λ := (3 : ℝ) ^ k₀ with hΛ
  set Kc := K ^ (-c₀) with hKc
  set PT := 4 * (1 + 9 / 8 * (9 : ℝ) ^ k₀) * K₀ * 9 ^ (k + 1) * 81 ^ k₀ with hPTdef
  have hK0 : 0 < K := by linarith
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg hK0.le _
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by norm_num)
  have hΛ6 : 1 ≤ Λ ^ 6 := one_le_pow₀ hΛ1
  have hΛΛ6 : Λ ≤ Λ ^ 6 := le_self_pow₀ hΛ1 (by norm_num)
  have hinvK : 1 / K ≤ Kc := one_div_le_rpow_neg hK1 (by linarith)
  have he : 0 ≤ 1 - 2 / t := by
    rw [sub_nonneg, div_le_one (by linarith)]
    exact ht.le
  have ht0 : 0 < t := by linarith
  have hWb : 0 ≤ (2 * 2 : ℝ) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2))) :=
    div_nonneg (by positivity) (by linarith)
  have hW : 0 ≤ ((2 * 2 : ℝ) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
    Real.rpow_nonneg hWb _
  have hd : 6 * K ^ 2 * ((ε + 2 * (5 * Λ + 1) / K) * (S2 / K ^ 2)) ≤
      6 * (E + 12) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by
    have a1 : E * Kc ≤ E * Λ ^ 6 * Kc := by
      have := mul_le_mul_of_nonneg_left hΛ6 (mul_nonneg hE hKc0)
      linarith
    have a2 : 2 * (5 * Λ + 1) / K ≤ 12 * Λ ^ 6 * Kc := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith) hinvK (by positivity) (by positivity)
    have hx : ε + 2 * (5 * Λ + 1) / K ≤ (E + 12) * Λ ^ 6 * Kc := by linarith
    calc 6 * K ^ 2 * ((ε + 2 * (5 * Λ + 1) / K) * (S2 / K ^ 2))
        = 6 * (ε + 2 * (5 * Λ + 1) / K) * S2 * (K ^ 2 / K ^ 2) := by ring
      _ = 6 * (ε + 2 * (5 * Λ + 1) / K) * S2 := by rw [div_self (by positivity), mul_one]
      _ ≤ 6 * ((E + 12) * Λ ^ 6 * Kc) * (L ^ 2 * (A2 * M ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hS2 hS20 (by positivity)
      _ = 6 * (E + 12) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by ring
  have he' : 3 * (max σ 1 * (2 * (3 * ((1 + 2) * 2 ^ 2 * K ^ 3 * (10 * 2 * max σ 1 /
      (σ * (K ^ 4) ^ 2)) + 1 / K) * S2))) ≤
      18 * max σ 1 * (240 * max σ 1 / σ + 1) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by
    have hK38 : K ^ 3 / (K ^ 4) ^ 2 ≤ 1 / K := by
      rw [div_le_div_iff₀ (show (0 : ℝ) < (K ^ 4) ^ 2 by positivity) hK0,
        show K ^ 3 * K = K ^ 4 by ring, one_mul]
      exact le_self_pow₀ (one_le_pow₀ hK1) (by norm_num)
    have hY : (1 + 2) * 2 ^ 2 * K ^ 3 * (10 * 2 * max σ 1 / (σ * (K ^ 4) ^ 2)) + 1 / K ≤
        (240 * max σ 1 / σ + 1) * Kc := by
      have e : (1 + 2) * 2 ^ 2 * K ^ 3 * (10 * 2 * max σ 1 / (σ * (K ^ 4) ^ 2)) =
          240 * max σ 1 / σ * (K ^ 3 / (K ^ 4) ^ 2) := by
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hK38 (by positivity : (0 : ℝ) ≤ 240 * max σ 1 / σ)
      have := mul_le_mul_of_nonneg_left hinvK (by positivity : (0 : ℝ) ≤ 240 * max σ 1 / σ + 1)
      linarith
    calc 3 * (max σ 1 * (2 * (3 * ((1 + 2) * 2 ^ 2 * K ^ 3 * (10 * 2 * max σ 1 /
          (σ * (K ^ 4) ^ 2)) + 1 / K) * S2)))
        = 18 * max σ 1 * (((1 + 2) * 2 ^ 2 * K ^ 3 * (10 * 2 * max σ 1 /
          (σ * (K ^ 4) ^ 2)) + 1 / K) * S2) := by ring
      _ ≤ 18 * max σ 1 * (((240 * max σ 1 / σ + 1) * Kc) * (L ^ 2 * (A2 * M ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hY hS2 hS20 (by positivity)) (by positivity)
      _ ≤ Λ ^ 6 * (18 * max σ 1 * (((240 * max σ 1 / σ + 1) * Kc) * (L ^ 2 * (A2 * M ^ 2)))) :=
        le_mul_of_one_le_left (by positivity) hΛ6
      _ = 18 * max σ 1 * (240 * max σ 1 / σ + 1) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by
        ring
  have hf : 6 * max σ 1 * (2 * (1 / K ^ 3) ^ 2) *
      (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2) ≤
      6 * max σ 1 * (612 * K₀ + 2 * CA) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by
    have hPT' : PT ≤ 153 / 2 * K₀ * K ^ 2 * Λ ^ 6 := hPT
    have q1 : (1 / K ^ 3) ^ 2 * K ^ 2 ≤ 1 / K := by
      rw [show (1 / K ^ 3) ^ 2 * K ^ 2 = K ^ 2 / (K ^ 3) ^ 2 by ring,
        div_le_div_iff₀ (show (0 : ℝ) < (K ^ 3) ^ 2 by positivity) hK0,
        show K ^ 2 * K = K ^ 3 by ring, one_mul]
      exact le_self_pow₀ (one_le_pow₀ hK1) (by norm_num)
    have q2 : (1 / K ^ 3) ^ 2 * (K ^ 4 / (K ^ 4) ^ 2) ≤ 1 / K := by
      rw [show (1 / K ^ 3) ^ 2 * (K ^ 4 / (K ^ 4) ^ 2) = K ^ 4 / ((K ^ 3) ^ 2 * (K ^ 4) ^ 2) by
        ring, div_le_div_iff₀ (show (0 : ℝ) < (K ^ 3) ^ 2 * (K ^ 4) ^ 2 by positivity) hK0,
        one_mul]
      calc K ^ 4 * K = K ^ 5 := by ring
        _ ≤ K ^ 14 := pow_le_pow_right₀ hK1 (by norm_num)
        _ = (K ^ 3) ^ 2 * (K ^ 4) ^ 2 := by ring
    have r1 : (1 / K ^ 3) ^ 2 * PT ≤ 153 / 2 * K₀ * Λ ^ 6 * (1 / K) :=
      calc (1 / K ^ 3) ^ 2 * PT ≤ (1 / K ^ 3) ^ 2 * (153 / 2 * K₀ * K ^ 2 * Λ ^ 6) :=
            mul_le_mul_of_nonneg_left hPT' (by positivity)
        _ = 153 / 2 * K₀ * Λ ^ 6 * ((1 / K ^ 3) ^ 2 * K ^ 2) := by ring
        _ ≤ 153 / 2 * K₀ * Λ ^ 6 * (1 / K) := mul_le_mul_of_nonneg_left q1 (by positivity)
    have r2 : (1 / K ^ 3) ^ 2 * (CA * K ^ 4 / (K ^ 4) ^ 2) ≤ CA * (1 / K) :=
      calc (1 / K ^ 3) ^ 2 * (CA * K ^ 4 / (K ^ 4) ^ 2) =
            CA * ((1 / K ^ 3) ^ 2 * (K ^ 4 / (K ^ 4) ^ 2)) := by ring
        _ ≤ CA * (1 / K) := mul_le_mul_of_nonneg_left q2 hCA
    have s1 := mul_le_mul_of_nonneg_right r1 hS20
    have s2 := mul_le_mul_of_nonneg_right r2 hS20
    have s3 : (612 * K₀ * Λ ^ 6 + 2 * CA) * (1 / K) * S2 ≤
        (612 * K₀ + 2 * CA) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by
      have h : 612 * K₀ * Λ ^ 6 + 2 * CA ≤ (612 * K₀ + 2 * CA) * Λ ^ 6 := by
        have := mul_le_mul_of_nonneg_left hΛ6 (by positivity : (0 : ℝ) ≤ 2 * CA)
        linarith only [this]
      exact mul_le_mul (mul_le_mul h hinvK (by positivity) (by positivity)) hS2 hS20
        (by positivity)
    have r : 2 * (1 / K ^ 3) ^ 2 * (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2) ≤
        (612 * K₀ + 2 * CA) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) :=
      calc 2 * (1 / K ^ 3) ^ 2 * (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2)
          = 8 * ((1 / K ^ 3) ^ 2 * PT * S2) +
            2 * ((1 / K ^ 3) ^ 2 * (CA * K ^ 4 / (K ^ 4) ^ 2) * S2) := by ring
        _ ≤ 8 * (153 / 2 * K₀ * Λ ^ 6 * (1 / K) * S2) + 2 * (CA * (1 / K) * S2) :=
          add_le_add (mul_le_mul_of_nonneg_left s1 (by norm_num))
            (mul_le_mul_of_nonneg_left s2 (by norm_num))
        _ = (612 * K₀ * Λ ^ 6 + 2 * CA) * (1 / K) * S2 := by ring
        _ ≤ (612 * K₀ + 2 * CA) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := s3
    calc 6 * max σ 1 * (2 * (1 / K ^ 3) ^ 2) * (PT * (4 * S2) + CA * K ^ 4 / (K ^ 4) ^ 2 * S2)
        = 6 * max σ 1 * (2 * (1 / K ^ 3) ^ 2 * (PT * (4 * S2) +
          CA * K ^ 4 / (K ^ 4) ^ 2 * S2)) := by ring
      _ ≤ 6 * max σ 1 * ((612 * K₀ + 2 * CA) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2))) :=
        mul_le_mul_of_nonneg_left r (by positivity)
      _ = 6 * max σ 1 * (612 * K₀ + 2 * CA) * Λ ^ 6 * Kc * (L ^ 2 * (A2 * M ^ 2)) := by ring
  have hg : L ^ 2 * ((2 + 3 * max σ 1 / σ) * (2 * (σ * ((2 * 2 *
      (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ (1 - 2 / t) *
        ((2 : ℝ) ^ (t / 2 - 1) * (St / L ^ 2)) ^ (2 / t))) +
      88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * 2) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
        ((K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ γ *
        ((2 : ℝ) ^ (t / 2 - 1) * (St / L ^ 2)) ^ (2 / t))) ≤
      Λ ^ 6 * (L ^ 2 * ((2 + 3 * max σ 1 / σ) * (2 * (σ * (((40 * 3 ^ 7) ^ (1 - 2 / t) * Kc) *
        (((2 : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t) * M ^ 2))) +
        88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
          ((2 * 2) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) *
          ((10 * 3 ^ 7) ^ γ * Kc) * (((2 : ℝ) ^ (t / 2 - 1) * At) ^ (2 / t) * M ^ 2)))) := by
    have hℓ : K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1 ≤ 10 * K ^ 4 := by
      have h1 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
      have h2 : K ≤ K ^ 4 := le_self_pow₀ hK1 (by norm_num)
      have h3 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
      linarith
    have hb1 : 2 * 2 * (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L ≤ 40 * 3 ^ 7 / K ^ 4 := by
      rw [div_le_div_iff₀ hL0 (show (0 : ℝ) < K ^ 4 by positivity)]
      calc 2 * 2 * (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) * K ^ 4 ≤
            2 * 2 * (10 * K ^ 4) * K ^ 4 := by gcongr
        _ = 40 * K ^ 8 := by ring
        _ ≤ 40 * (3 ^ 7 * L) := by gcongr
        _ = 40 * 3 ^ 7 * L := by ring
    have hb2 : (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L ≤ 10 * 3 ^ 7 / K ^ 4 := by
      rw [div_le_div_iff₀ hL0 (show (0 : ℝ) < K ^ 4 by positivity)]
      calc (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) * K ^ 4 ≤ (10 * K ^ 4) * K ^ 4 := by gcongr
        _ = 10 * K ^ 8 := by ring
        _ ≤ 10 * (3 ^ 7 * L) := by gcongr
        _ = 10 * 3 ^ 7 * L := by ring
    have hp1 : (2 * 2 * (K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ (1 - 2 / t) ≤
        (40 * 3 ^ 7) ^ (1 - 2 / t) * Kc :=
      (rpow_le_mul_rpow_neg_of_le_div_pow hK1 (by positivity) (by norm_num) he hb1).trans
        (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hK1 (by push_cast; linarith))
          (by positivity))
    have hp2 : ((K ^ 4 + 3 + 3 * K + K ^ 3 + K + 1) / L) ^ γ ≤ (10 * 3 ^ 7) ^ γ * Kc :=
      (rpow_le_mul_rpow_neg_of_le_div_pow hK1 (by positivity) (by norm_num) hγ0.le hb2).trans
        (mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hK1 (by push_cast; linarith))
          (by positivity))
    have hH0 : (2 : ℝ) ^ (t / 2 - 1) * (St / L ^ 2) ≤ (2 : ℝ) ^ (t / 2 - 1) * At * M ^ t := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hSt (by positivity)
    have hH := Real.rpow_le_rpow (by positivity) hH0 (by positivity : (0 : ℝ) ≤ 2 / t)
    rw [rpow_two_div_mul_rpow (a := (2 : ℝ) ^ (t / 2 - 1) * At) hM (by positivity) ht0] at hH
    have hA : (0 : ℝ) ≤ 88 * max σ 1 * Real.exp (γ + 4 * γ ^ 2) *
        ((2 * 2) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
      mul_nonneg (by positivity) hW
    have hmain := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul hp1 hH (by positivity) (by positivity)) hσ.le)
        (by norm_num : (0 : ℝ) ≤ 2))
      (mul_le_mul (mul_le_mul_of_nonneg_left hp2 hA) hH (by positivity) (by positivity)))
      (by positivity : (0 : ℝ) ≤ 2 + 3 * max σ 1 / σ)) (sq_nonneg L)
    exact hmain.trans (le_mul_of_one_le_left (by positivity) hΛ6)
  refine (add_le_add (add_le_add (add_le_add hd he') hf) hg).trans (le_of_eq ?_)
  unfold chainBoundTwo
  ring

theorem chainBoundOne_nonneg {σ E t A2 At : ℝ} (hσ : 0 < σ) (hE : 0 ≤ E) (hA2 : 0 ≤ A2)
    (hAt : 0 ≤ At) : 0 ≤ chainBoundOne σ E t A2 At := by
  unfold chainBoundOne
  positivity

theorem chainBoundTwo_nonneg {σ E γ t K₀ CA A2 At : ℝ} (hσ : 0 < σ)
    (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2) (hAt : 0 ≤ At) (hK₀ : 0 ≤ K₀)
    (hCA : 0 ≤ CA) : 0 ≤ chainBoundTwo σ E γ t K₀ CA A2 At := by
  have hWb : 0 ≤ (2 * 2 : ℝ) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2))) :=
    div_nonneg (by positivity) (by linarith)
  have hW : 0 ≤ ((2 * 2 : ℝ) ^ (t / (t - 2)) / (1 - γ * (t / (t - 2)))) ^ (1 - 2 / t) :=
    Real.rpow_nonneg hWb _
  unfold chainBoundTwo
  positivity

theorem sq_le_mul_rpow_neg {K L c₀ : ℝ} (hK : 1 ≤ K) (hc₀ : c₀ ≤ 14) (hKL : K ^ 8 ≤ 3 ^ 7 * L) :
    K ^ 2 ≤ 3 ^ 14 * L ^ 2 * K ^ (-c₀) := by
  have hK0 : 0 < K := by linarith
  have hKc : K ^ c₀ * K ^ (-c₀) = 1 := by
    rw [Real.rpow_neg hK0.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hK0 _).ne']
  have h14 : K ^ c₀ ≤ K ^ 14 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hK (by push_cast; linarith)
  have h16 : K ^ 2 * K ^ 14 ≤ 3 ^ 14 * L ^ 2 := by
    rw [← pow_add]
    calc K ^ (2 + 14) = (K ^ 8) ^ 2 := by ring
      _ ≤ (3 ^ 7 * L) ^ 2 := by gcongr
      _ = 3 ^ 14 * L ^ 2 := by ring
  calc K ^ 2 = K ^ 2 * K ^ c₀ * K ^ (-c₀) := by rw [mul_assoc, hKc, mul_one]
    _ ≤ 3 ^ 14 * L ^ 2 * K ^ (-c₀) :=
      mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left h14 (by positivity)).trans h16)
        (Real.rpow_nonneg hK0.le _)

/-- The constant of the bound of the error chain. -/
noncomputable def chainBound (σ E γ t A2 At K₀ C₃ CA : ℝ) : ℝ :=
  153 * K₀ * (chainBoundOne σ E t A2 At + chainBoundTwo σ E γ t K₀ CA A2 At) +
    2 * 3 ^ 14 * (612 * K₀ + 2 * C₃) * A2

/-- **The bound of the error chain**: with `K = 3^k`, `L = 3^m`, `Λ = 3^{k₀}`, the right side of
`planar_error_chain` is at most `B Λ¹² L⁴ M² K^{-c₀}`. -/
theorem chain_le {σ ε γ t E A2 At c₀ M S2 St K₀ C₃ CA : ℝ} {m k k₀ : ℕ} (hσ : 0 < σ)
    (ht : 2 < t) (hγ0 : 0 < γ) (hγt : γ * (t / (t - 2)) < 1) (hE : 0 ≤ E) (hA2 : 0 ≤ A2)
    (hAt : 0 ≤ At) (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀) (hC₃ : 0 ≤ C₃) (hCA : 0 ≤ CA)
    (hc₀ : c₀ ≤ 1 / 2) (hc₀t : c₀ ≤ 4 * (1 - 2 / t)) (hc₀γ : c₀ ≤ 4 * γ) (hkm : 8 * k ≤ m + 7)
    (hε : ε ≤ E * ((3 : ℝ) ^ k) ^ (-c₀)) (hS20 : 0 ≤ S2)
    (hS2 : S2 ≤ ((3 : ℝ) ^ m) ^ 2 * (A2 * M ^ 2)) (hSt0 : 0 ≤ St)
    (hSt : St / ((3 : ℝ) ^ m) ^ 2 ≤ At * M ^ t) :
    2 * (chainP K₀ m k₀ * ((chainDeltaOne σ ε t m k S2 St +
        chainDeltaTwo σ ε γ t K₀ CA m k k₀ S2 St) / 1)) + 2 * chainDeltaThree σ K₀ C₃ k k₀ S2 ≤
      chainBound σ E γ t A2 At K₀ C₃ CA *
        (((3 : ℝ) ^ k₀) ^ 12 * (((3 : ℝ) ^ m) ^ 4 * M ^ 2 * ((3 : ℝ) ^ k) ^ (-c₀))) := by
  have h1 := chainDeltaOne_le hσ ht hE hAt hM hc₀ hc₀t hkm hε hS20 hS2 hSt0 hSt
  have h2 := chainDeltaTwo_le (k₀ := k₀) (K₀ := K₀) (CA := CA) hσ ht hγ0 hγt hE hA2 hAt hM hK₀
    hCA hc₀ hc₀t hc₀γ hkm hε hS20 hS2 hSt0 hSt
  have h3 := chainDeltaThree_le (k := k) (k₀ := k₀) hσ hK₀ hC₃ hS20
  have hP := chainP_le hK₀ m k₀
  have hP0 := chainP_nonneg hK₀ m k₀
  have hB1 := chainBoundOne_nonneg hσ hE hA2 hAt (σ := σ) (t := t)
  have hB2 := chainBoundTwo_nonneg hσ hγt hE hA2 hAt hK₀ hCA (γ := γ)
  have hK1 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hKL : ((3 : ℝ) ^ k) ^ 8 ≤ 3 ^ 7 * (3 : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  set K := (3 : ℝ) ^ k with hK
  set L := (3 : ℝ) ^ m with hL
  set Λ := (3 : ℝ) ^ k₀ with hΛ
  set Kc := K ^ (-c₀) with hKc
  have hKc0 : 0 ≤ Kc := Real.rpow_nonneg (by linarith) _
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ (by norm_num)
  have hΛ6 : 1 ≤ Λ ^ 6 := one_le_pow₀ hΛ1
  have hΛ12 : Λ ^ 6 ≤ Λ ^ 12 := pow_le_pow_right₀ hΛ1 (by norm_num)
  have hK2 := sq_le_mul_rpow_neg hK1 (by linarith : c₀ ≤ 14) hKL
  have hK2' : 1 ≤ 3 ^ 14 * L ^ 2 * Kc := le_trans (one_le_pow₀ hK1) hK2
  have hX0 : 0 ≤ L ^ 2 * M ^ 2 * Kc := by positivity
  have hD : chainDeltaOne σ ε t m k S2 St + chainDeltaTwo σ ε γ t K₀ CA m k k₀ S2 St ≤
      (chainBoundOne σ E t A2 At + chainBoundTwo σ E γ t K₀ CA A2 At) *
        (Λ ^ 6 * (L ^ 2 * M ^ 2 * Kc)) := by
    have : chainBoundOne σ E t A2 At * (L ^ 2 * M ^ 2 * Kc) ≤
        chainBoundOne σ E t A2 At * (Λ ^ 6 * (L ^ 2 * M ^ 2 * Kc)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX0 hΛ6) hB1
    linarith
  have hPD : chainP K₀ m k₀ * ((chainDeltaOne σ ε t m k S2 St +
        chainDeltaTwo σ ε γ t K₀ CA m k k₀ S2 St) / 1) ≤
      153 / 2 * K₀ * L ^ 2 * Λ ^ 6 * ((chainBoundOne σ E t A2 At +
        chainBoundTwo σ E γ t K₀ CA A2 At) * (Λ ^ 6 * (L ^ 2 * M ^ 2 * Kc))) := by
    rw [div_one]
    exact (mul_le_mul_of_nonneg_left hD hP0).trans
      (mul_le_mul_of_nonneg_right hP (by positivity))
  have h3' : chainDeltaThree σ K₀ C₃ k k₀ S2 ≤
      3 ^ 14 * (612 * K₀ + 2 * C₃) * A2 * (Λ ^ 12 * (L ^ 4 * M ^ 2 * Kc)) := by
    have hc : 612 * K₀ * K ^ 2 * Λ ^ 6 + 2 * C₃ ≤
        (612 * K₀ + 2 * C₃) * (3 ^ 14 * L ^ 2 * Kc * Λ ^ 12) := by
      have e1 : 612 * K₀ * K ^ 2 * Λ ^ 6 ≤ 612 * K₀ * (3 ^ 14 * L ^ 2 * Kc) * Λ ^ 12 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hK2 (by positivity)) hΛ12 (by positivity)
          (by positivity)
      have e2 : 2 * C₃ ≤ 2 * C₃ * (3 ^ 14 * L ^ 2 * Kc * Λ ^ 12) :=
        le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le hK2' (one_le_pow₀ hΛ1))
      linarith
    calc chainDeltaThree σ K₀ C₃ k k₀ S2
        ≤ (612 * K₀ * K ^ 2 * Λ ^ 6 + 2 * C₃) * S2 := h3
      _ ≤ ((612 * K₀ + 2 * C₃) * (3 ^ 14 * L ^ 2 * Kc * Λ ^ 12)) * (L ^ 2 * (A2 * M ^ 2)) :=
        mul_le_mul hc hS2 hS20 (by positivity)
      _ = 3 ^ 14 * (612 * K₀ + 2 * C₃) * A2 * (Λ ^ 12 * (L ^ 4 * M ^ 2 * Kc)) := by ring
  unfold chainBound
  linarith

end Rigidity.Dirichlet
