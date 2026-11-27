import Rigidity.Proofs.Green.DarioGuCorrectorLemma

/-!
# Estimates on `Φ_C` for Lemma 4.1 of Dario–Gu

* `dgPhi_anti`: `Φ_C(t, r)` is nonincreasing in `r`.
* `dgPhi_le_mul_dgPhi`: for `r' ≤ 2r`, `Φ_C(τ, r) ≤ e^{-g(τ, r)/(2C)} Φ_{16C}(τ, r') / 16`
  (the comparison (4.12) of the source between the supremum and the infimum of `Φ_C` on
  a dyadic annulus).
* `dgPhi_le_rpow_mul_dgPhi`: for `r ≥ 2t/3`, `Φ_C(t, r) ≤ (9C/4) t^{-1/2} Φ_{2C}(t, r)`.
* `inv_mul_exp_le_dgPhi`: for `r ≤ s ≤ t ≤ 3s/2`, `s^{-1} exp(-r²/(C s)) ≤ (3/(2C')) Φ_{C'}(t, r)`.
* `sum_openHeat_mul_dgPhi_le`: Theorem 4 near `y`, Proposition 2.15 far from `y` and the
  semigroup property (3.2) of `Φ_C` give `Σ_z p(s, x, z) Φ_{C₁}(τ, z - y) ≤ K Φ_{C'}(τ + s, x - y)`
  (the computation (4.15) of the source).
* `sum_pow_mul_exp_neg_le`: `Σ_{n < N} 64^n exp(-2^n/(4C)) ≤ 10080 (4C)^7`.
-/

open Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

theorem dgPhi_anti {C t r r' : ℝ} (hC : 0 < C) (ht : 0 < t) (hr : 0 ≤ r) (hrr : r ≤ r') :
    dgPhi C t r' ≤ dgPhi C t r := by
  rw [dgPhi_eq, dgPhi_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  rw [neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (dgShape_mono ht hr hrr) hC.le

theorem dgPhi_zero_eq {C t : ℝ} (ht : 0 < t) : dgPhi C t 0 = C * t⁻¹ := by
  rw [dgPhi_eq]
  have : dgShape t 0 = 0 := by
    unfold dgShape
    rw [if_pos ht.le]
    simp
  rw [this]
  simp

/-- `Φ_C(τ, r) ≤ e^{-g(τ, r)/(2C)} Φ_{16C}(τ, r') / 16` for `0 ≤ r' ≤ 2r`. -/
theorem dgPhi_le_mul_dgPhi {C τ r r' : ℝ} (hC : 0 < C) (hτ : 0 < τ) (hr' : 0 ≤ r')
    (hrr : r' ≤ 2 * r) :
    dgPhi C τ r ≤ Real.exp (-(dgShape τ r / (2 * C))) * dgPhi (16 * C) τ r' / 16 := by
  have hr : 0 ≤ r := by linarith
  have h2r := dgShape_half_ge hτ (by linarith : 0 ≤ 2 * r)
  rw [show 2 * r / 2 = r by ring] at h2r
  have hmono := dgShape_mono hτ hr' hrr
  rw [dgPhi_eq, dgPhi_eq]
  have he : Real.exp (-(dgShape τ r / (2 * C))) ≤ Real.exp (-(dgShape τ r' / (16 * C))) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsplit : Real.exp (-(dgShape τ r / C)) =
      Real.exp (-(dgShape τ r / (2 * C))) * Real.exp (-(dgShape τ r / (2 * C))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit]
  have hE := Real.exp_pos (-(dgShape τ r / (2 * C)))
  calc C * τ⁻¹ * (Real.exp (-(dgShape τ r / (2 * C))) * Real.exp (-(dgShape τ r / (2 * C))))
      ≤ C * τ⁻¹ * (Real.exp (-(dgShape τ r / (2 * C))) *
          Real.exp (-(dgShape τ r' / (16 * C)))) := by
        gcongr
    _ = _ := by field_simp

/-- `g(τ, 2^n √τ) ≥ 2^n` for `τ ≥ 1`. -/
theorem two_pow_le_dgShape {τ : ℝ} (hτ : 1 ≤ τ) (n : ℕ) :
    (2 : ℝ) ^ n ≤ dgShape τ (2 ^ n * Real.sqrt τ) := by
  have hτ0 : 0 < τ := by linarith
  have hst : 1 ≤ Real.sqrt τ := by rw [Real.one_le_sqrt]; exact hτ
  have hm := min_le_dgShape hτ0 (by positivity : (0 : ℝ) ≤ 2 ^ n * Real.sqrt τ)
  have h1 : (2 : ℝ) ^ n ≤ (2 ^ n * Real.sqrt τ) ^ 2 / τ := by
    rw [mul_pow, Real.sq_sqrt hτ0.le, mul_div_assoc, div_self hτ0.ne', mul_one, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ n ≤ 2 ^ n * Real.sqrt τ := le_mul_of_one_le_right (by positivity) hst
  exact (le_min h1 h2).trans hm

/-- `Φ_C(t, r) ≤ (9C/4) t^{-1/2} Φ_{2C}(t, r)` for `r ≥ 2t/3`, `t ≥ 1`. -/
theorem dgPhi_le_rpow_mul_dgPhi {C t r : ℝ} (hC : 0 < C) (ht : 1 ≤ t) (hr : 2 * t / 3 ≤ r) :
    dgPhi C t r ≤ 9 * C / 4 * (Real.sqrt t)⁻¹ * dgPhi (2 * C) t r := by
  have ht0 : 0 < t := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hsqt : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left ht0.le]
    nlinarith
  set g := dgShape t r with hg
  have hg4 : 4 * t / 9 ≤ g := by
    have hm := min_le_dgShape ht0 hr0
    have h1 : 4 * t / 9 ≤ r ^ 2 / t := by
      rw [le_div_iff₀ ht0]
      nlinarith
    have h2 : 4 * t / 9 ≤ r := by linarith
    exact (le_min h1 h2).trans hm
  have hexp : Real.exp (-(g / (2 * C))) ≤ 9 * C / (2 * t) := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    have h := Real.add_one_le_exp (g / (2 * C))
    have h2 : 2 * t / (9 * C) ≤ g / (2 * C) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [inv_div]
    linarith
  rw [dgPhi_eq, dgPhi_eq, ← hg]
  have hsplit : Real.exp (-(g / C)) = Real.exp (-(g / (2 * C))) * Real.exp (-(g / (2 * C))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsplit]
  have hE := Real.exp_pos (-(g / (2 * C)))
  calc C * t⁻¹ * (Real.exp (-(g / (2 * C))) * Real.exp (-(g / (2 * C))))
      ≤ C * t⁻¹ * (9 * C / (2 * t) * Real.exp (-(g / (2 * C)))) := by gcongr
    _ ≤ C * t⁻¹ * (9 * C / (2 * Real.sqrt t) * Real.exp (-(g / (2 * C)))) := by
        gcongr
    _ = _ := by
        field_simp
        norm_num

/-- `s^{-1} exp(-r²/(C s)) ≤ (3/(2C')) Φ_{C'}(t, r)` for `r ≤ s ≤ t ≤ 3s/2` and `C ≤ C'`. -/
theorem inv_mul_exp_le_dgPhi {C C' s t r : ℝ} (hC : 0 < C) (hCC : C ≤ C') (hs0 : 0 < s)
    (hrs : r ≤ s) (hst : s ≤ t) (hts : 2 * t ≤ 3 * s) :
    s⁻¹ * Real.exp (-(r ^ 2 / (C * s))) ≤ 3 / (2 * C') * dgPhi C' t r := by
  have ht0 : 0 < t := by linarith
  have hC'0 : 0 < C' := by linarith
  rw [dgPhi_eq]
  have hg : dgShape t r = r ^ 2 / t := by
    unfold dgShape
    rw [if_pos (by linarith)]
  rw [hg]
  have he : Real.exp (-(r ^ 2 / (C * s))) ≤ Real.exp (-(r ^ 2 / t / C')) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
    nlinarith
  have hinv : s⁻¹ ≤ 3 / 2 * t⁻¹ := by
    rw [inv_le_comm₀ hs0 (by positivity)]
    field_simp
    linarith
  calc s⁻¹ * Real.exp (-(r ^ 2 / (C * s))) ≤ 3 / 2 * t⁻¹ * Real.exp (-(r ^ 2 / t / C')) :=
        mul_le_mul hinv he (Real.exp_pos _).le (by positivity)
    _ = 3 / (2 * C') * (C' * t⁻¹ * Real.exp (-(r ^ 2 / t / C'))) := by
        field_simp

/-- `Σ_{n < N} 64^n exp(-2^n/(4C)) ≤ 10080 (4C)^7`. -/
theorem sum_pow_mul_exp_neg_le {C : ℝ} (hC : 0 < C) (N : ℕ) :
    ∑ n ∈ range N, (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C))) ≤ 10080 * (4 * C) ^ 7 := by
  have hpt : ∀ n : ℕ, (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C))) ≤
      5040 * (4 * C) ^ 7 * (1 / 2) ^ n := by
    intro n
    set x := (2 : ℝ) ^ n / (4 * C) with hx
    have hx0 : 0 < x := by positivity
    have h7 : x ^ 7 / 5040 ≤ Real.exp x := by
      have := Real.pow_div_factorial_le_exp (x := x) hx0.le 7
      simpa [Nat.factorial] using this
    have he : Real.exp (-x) ≤ 5040 / x ^ 7 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact h7
    have hx7 : x ^ 7 = (128 : ℝ) ^ n / (4 * C) ^ 7 := by
      rw [hx, div_pow, ← pow_mul, mul_comm n 7, pow_mul]
      norm_num
    calc (64 : ℝ) ^ n * Real.exp (-x) ≤ 64 ^ n * (5040 / x ^ 7) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = 5040 * (4 * C) ^ 7 * (1 / 2) ^ n := by
          rw [hx7]
          have h128 : (128 : ℝ) ^ n = 64 ^ n * 2 ^ n := by
            rw [← mul_pow]
            norm_num
          rw [h128, one_div_pow]
          field_simp
  calc ∑ n ∈ range N, (64 : ℝ) ^ n * Real.exp (-((2 : ℝ) ^ n / (4 * C)))
      ≤ ∑ n ∈ range N, 5040 * (4 * C) ^ 7 * (1 / 2 : ℝ) ^ n := Finset.sum_le_sum fun n _ => hpt n
    _ = 5040 * (4 * C) ^ 7 * ∑ n ∈ range N, (1 / 2 : ℝ) ^ n := by rw [Finset.mul_sum]
    _ ≤ 5040 * (4 * C) ^ 7 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
        rw [div_le_iff_of_neg (by norm_num)]
        linarith
    _ = 10080 * (4 * C) ^ 7 := by ring

/-- **The computation (4.15)**: with Theorem 4 at the points `z` with `|z - y| ≤ s + 1`
(`hB`) and Proposition 2.15 (`hcv`), `Σ_z p(s, x, z) Φ_{C₁}(τ, z - y) ≤ K Φ_{C'}(τ + s, x - y)`
for `1 ≤ τ ≤ s`. -/
theorem sum_openHeat_mul_dgPhi_le {CB Ccv C₁ : ℝ} (hCB : 0 < CB) (hCcv : 0 < Ccv) (hC₁ : 0 < C₁) :
    ∃ K C' : ℝ, 0 < K ∧ 0 < C' ∧ ∀ (ω : Configuration 2) (K' : OpenComponent ω) (x y : Vertex 2)
      (s τ : ℝ), 1 ≤ τ → τ ≤ s → x ∈ K'.supp →
      (∀ z ∈ K'.supp, latticeDist z y ≤ s + 1 → openHeat ω s x z ≤ dgPhi CB s (latticeDist x z)) →
      (∀ z ∈ K'.supp, (latticeDist x z ≤ s → openHeat ω s x z ≤
          Ccv * Real.exp (-(latticeDist x z ^ 2 / (Ccv * s)))) ∧
        (s ≤ latticeDist x z → openHeat ω s x z ≤
          Ccv * Real.exp (-(latticeDist x z / Ccv * (1 + Real.log (latticeDist x z / s)))))) →
      ∀ S : Finset (Vertex 2), ∑ z ∈ S, openHeat ω s x z * dgPhi C₁ τ (latticeDist z y) ≤
        K * dgPhi C' (τ + s) (latticeDist x y) := by
  set C₇ := max (max CB Ccv) (2 * C₁) with hC₇
  have hC₇0 : 0 < C₇ := lt_max_of_lt_left (lt_max_of_lt_left hCB)
  obtain ⟨C₈, hC₈, hconv⟩ := sum_dgPhi_mul_dgPhi_le hC₇0
  set K₁ := max 1 C₁ with hK₁
  refine ⟨K₁, C₈, lt_max_of_lt_left one_pos, hC₈, ?_⟩
  intro ω K' x y s τ hτ1 hτs hx hB hcv S
  have hτ0 : 0 < τ := by linarith
  have hs0 : 0 < s := by linarith
  have hterm : ∀ z, openHeat ω s x z * dgPhi C₁ τ (latticeDist z y) ≤
      K₁ * (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) := by
    intro z
    have hzd := latticeDist_nonneg z y
    have hxz := latticeDist_nonneg x z
    have hφ0 : 0 ≤ dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z) :=
      mul_nonneg (dgPhi_nonneg hC₇0.le hτ0.le _) (dgPhi_nonneg hC₇0.le hs0.le _)
    by_cases hz : z ∈ K'.supp
    · by_cases hnear : latticeDist z y ≤ s + 1
      · have h1 : openHeat ω s x z ≤ dgPhi C₇ s (latticeDist x z) :=
          (hB z hz hnear).trans (dgPhi_mono hCB ((le_max_left _ _).trans (le_max_left _ _)) hs0 hxz)
        have h2 : dgPhi C₁ τ (latticeDist z y) ≤ dgPhi C₇ τ (latticeDist z y) :=
          dgPhi_mono hC₁ ((by linarith : C₁ ≤ 2 * C₁).trans (le_max_right _ _)) hτ0 hzd
        calc openHeat ω s x z * dgPhi C₁ τ (latticeDist z y)
            ≤ dgPhi C₇ s (latticeDist x z) * dgPhi C₇ τ (latticeDist z y) :=
              mul_le_mul h1 h2 (dgPhi_nonneg hC₁.le hτ0.le _) (dgPhi_nonneg hC₇0.le hs0.le _)
          _ = 1 * (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) := by ring
          _ ≤ K₁ * (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hφ0
      · push Not at hnear
        have h1 : openHeat ω s x z ≤ s * dgPhi C₇ s (latticeDist x z) :=
          (openHeat_le_mul_dgPhi hCcv hs0 (hcv z hz)).trans
            (mul_le_mul_of_nonneg_left (dgPhi_mono hCcv
              ((le_max_right _ _).trans (le_max_left _ _)) hs0 hxz) hs0.le)
        have h2 : s * dgPhi C₁ τ (latticeDist z y) ≤ C₁ * dgPhi (2 * C₁) τ (latticeDist z y) :=
          mul_dgPhi_le hC₁ hτ0 hτs (by linarith)
        have h3 : dgPhi (2 * C₁) τ (latticeDist z y) ≤ dgPhi C₇ τ (latticeDist z y) :=
          dgPhi_mono (by positivity) (le_max_right _ _) hτ0 hzd
        calc openHeat ω s x z * dgPhi C₁ τ (latticeDist z y)
            ≤ s * dgPhi C₇ s (latticeDist x z) * dgPhi C₁ τ (latticeDist z y) :=
              mul_le_mul_of_nonneg_right h1 (dgPhi_nonneg hC₁.le hτ0.le _)
          _ = dgPhi C₇ s (latticeDist x z) * (s * dgPhi C₁ τ (latticeDist z y)) := by ring
          _ ≤ dgPhi C₇ s (latticeDist x z) * (C₁ * dgPhi C₇ τ (latticeDist z y)) :=
              mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hC₁.le))
                (dgPhi_nonneg hC₇0.le hs0.le _)
          _ = C₁ * (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) := by ring
          _ ≤ K₁ * (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hφ0
    · rw [openHeat_eq_zero_of_mem_of_notMem hx hz, zero_mul]
      exact mul_nonneg (lt_max_of_lt_left one_pos).le hφ0
  calc ∑ z ∈ S, openHeat ω s x z * dgPhi C₁ τ (latticeDist z y)
      ≤ ∑ z ∈ S, K₁ * (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) :=
        Finset.sum_le_sum fun z _ => hterm z
    _ = K₁ * ∑ z ∈ S, dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z) := by
        rw [Finset.mul_sum]
    _ ≤ K₁ * dgPhi C₈ (τ + s) (latticeDist x y) :=
        mul_le_mul_of_nonneg_left (hconv τ s hτ1 hτs x y S) (lt_max_of_lt_left one_pos).le

end Rigidity.Green
