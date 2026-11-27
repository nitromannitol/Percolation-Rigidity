import Rigidity.Proofs.Corrector.DarioStepTwoDomination

/-!
# The domination of the weight by the finite-range weight on `ℤᵈ`: the real bounds

The three failure probabilities of the domination of the weight at range `R` are brought to the
common form `C R^{2d} e^{-c R^σ}`:

* the far-edge term `K e^{-R/A}` (`far_term_le`), for `c ≤ 1/A` and `σ ≤ 1`;
* the capped-side term `(2R + 1)^d C e^{-c_s 3ⁿ}` for `R < 3 · 3ⁿ` (`side_term_le`), for
  `c ≤ c_s/3` and `σ ≤ 1`;
* the local-gradient term, a union over the `(2(R + 3κR) + 1)^d` points of a box of the finite
  cluster tail `(2R + 1)^d C₁ e^{-c₁ (R+1)^τ}` and the sublinearity tail
  `2 e^{-(R / (C₂ (LR)^{1-δ}))^s}` (`grad_term_le`, with `grad_exponent_eq`), for `σ ≤ τ`,
  `σ ≤ δs`, `c ≤ c₁` and `c ≤ (L^{δ-1}/C₂)^s`.

This is the real part of the planar file `DarioStepTwoDomination`. There `d = 2`, the far-edge
constants are `K = 8 (1 + 2 · 2 · 6κθ)²`, `A = 2 · 6κθ`, the counts `(2R + 1)²` give the power
`R⁴`, the finite cluster tail is `e^{-c₁ √(R+1)}` (`τ = 1/2`) and the Euclidean radius of the box
`B(0, R)` is `3R` (`L = 3`). In `d ≥ 3` the finite cluster tail is `e^{-c₁ (R+1)^{1/d}}`
(`τ = 1/d`) and the Euclidean radius is `2dR` (`L = 2d`); the box radius `R + 3κR` of the
local-gradient term is that of an `ℓ^∞` box and does not depend on `d`.
-/

namespace Rigidity.Corrector.GeneralDim

theorem grad_exponent_eq {R L C₂ δ s : ℝ} (hR : 0 < R) (hL : 0 < L) (hC₂ : 0 < C₂) :
    (R / (C₂ * (L * R) ^ (1 - δ))) ^ s = (L ^ (δ - 1) / C₂) ^ s * R ^ (δ * s) := by
  have h1 : (L * R) ^ (1 - δ) = L ^ (1 - δ) * R ^ (1 - δ) := Real.mul_rpow hL.le hR.le
  have hRδ : 0 < R ^ δ := Real.rpow_pos_of_pos hR δ
  have hLδ : 0 < L ^ δ := Real.rpow_pos_of_pos hL δ
  have h2 : R / (C₂ * (L * R) ^ (1 - δ)) = (L ^ (δ - 1) / C₂) * R ^ δ := by
    rw [h1, Real.rpow_sub hR, Real.rpow_sub hL, Real.rpow_sub hL, Real.rpow_one, Real.rpow_one]
    field_simp
  rw [h2, Real.mul_rpow (by positivity) hRδ.le, ← Real.rpow_mul hR.le]

/-- The far-edge term in the form `K x^a e^{-c x^σ}`. -/
theorem far_term_le {x A K c σ : ℝ} {a : ℕ} (hK : 0 ≤ K) (hx : 1 ≤ x) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hcA : c ≤ 1 / A) :
    K * Real.exp (-(x / A)) ≤ K * x ^ a * Real.exp (-(c * x ^ σ)) := by
  have e : x / A = 1 / A * x := by ring
  rw [e]
  have h := Rigidity.Corrector.exp_neg_le_exp_neg_rpow hx hσ1 hc0 hcA
  have hxa : (1 : ℝ) ≤ x ^ a := one_le_pow₀ hx
  have hE0 : 0 ≤ Real.exp (-(c * x ^ σ)) := (Real.exp_pos _).le
  calc K * Real.exp (-(1 / A * x)) ≤ K * Real.exp (-(c * x ^ σ)) :=
        mul_le_mul_of_nonneg_left h hK
    _ ≤ K * (x ^ a * Real.exp (-(c * x ^ σ))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE0 hxa) hK
    _ = _ := by ring

/-- The capped-side term in the form `C x^{2d} e^{-c x^σ}`. -/
theorem side_term_le {d R n : ℕ} (hR : 1 ≤ R) (hn : R < 3 * 3 ^ n) {cs c σ C : ℝ} (hcs : 0 < cs)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hccs : c ≤ cs / 3) (hC : 0 ≤ C) :
    ((((2 * R + 1) ^ d : ℕ) : ℝ)) * (C * Real.exp (-cs * (3 : ℝ) ^ n)) ≤
      3 ^ d * C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have h3 : (R : ℝ) / 3 ≤ (3 : ℝ) ^ n := by
    have : (R : ℝ) < 3 * 3 ^ n := by exact_mod_cast hn
    linarith
  have hexp : Real.exp (-cs * (3 : ℝ) ^ n) ≤ Real.exp (-(cs / 3 * R)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h3 hcs.le
    have e : cs * (R / 3) = cs / 3 * R := by ring
    linarith
  have h2 := Rigidity.Corrector.exp_neg_le_exp_neg_rpow (a := cs / 3) hx1 hσ1 hc0 hccs
  have hN : ((((2 * R + 1) ^ d : ℕ) : ℝ)) ≤ 3 ^ d * (R : ℝ) ^ (2 * d) := by
    push_cast
    have hb : (2 * (R : ℝ) + 1) ^ d ≤ (3 * (R : ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hp : (R : ℝ) ^ d ≤ (R : ℝ) ^ (2 * d) := pow_le_pow_right₀ hx1 (by omega)
    calc (2 * (R : ℝ) + 1) ^ d ≤ (3 * (R : ℝ)) ^ d := hb
      _ = 3 ^ d * (R : ℝ) ^ d := mul_pow _ _ _
      _ ≤ 3 ^ d * (R : ℝ) ^ (2 * d) := mul_le_mul_of_nonneg_left hp (by positivity)
  calc ((((2 * R + 1) ^ d : ℕ) : ℝ)) * (C * Real.exp (-cs * (3 : ℝ) ^ n))
      ≤ 3 ^ d * (R : ℝ) ^ (2 * d) * (C * Real.exp (-(c * (R : ℝ) ^ σ))) :=
        mul_le_mul hN (mul_le_mul_of_nonneg_left (hexp.trans h2) hC) (by positivity)
          (by positivity)
    _ = _ := by ring

/-- The local-gradient term in the form `C x^{2d} e^{-c x^σ}`. -/
theorem grad_term_le {d R κ : ℕ} (hR : 1 ≤ R) {C₁ c₁ τ s δ L C₂ c σ : ℝ} (hC₁ : 0 ≤ C₁)
    (hL : 0 < L) (hC₂ : 0 < C₂) (hτ : 0 ≤ τ) (hστ : σ ≤ τ) (hσδ : σ ≤ δ * s) (hc0 : 0 ≤ c)
    (hcc₁ : c ≤ c₁) (hcc₃ : c ≤ (L ^ (δ - 1) / C₂) ^ s) :
    ((((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) : ℝ)) *
      ((2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
        2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s)) ≤
      3 ^ d * (1 + 3 * κ) ^ d * (3 ^ d * C₁ + 2) * (R : ℝ) ^ (2 * d) *
        Real.exp (-(c * (R : ℝ) ^ σ)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hx0 : (0 : ℝ) < R := by linarith
  set E : ℝ := Real.exp (-(c * (R : ℝ) ^ σ))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hN : ((((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) : ℝ)) ≤
      3 ^ d * (1 + 3 * κ) ^ d * (R : ℝ) ^ d := by
    push_cast
    have h1 : (1 : ℝ) ≤ (1 + 3 * κ) * R := by nlinarith
    have h2 : 2 * ((R : ℝ) + 3 * κ * R) + 1 ≤ 3 * ((1 + 3 * κ) * R) := by nlinarith
    have h0 : (0 : ℝ) ≤ 2 * ((R : ℝ) + 3 * κ * R) + 1 := by positivity
    calc (2 * ((R : ℝ) + 3 * κ * R) + 1) ^ d ≤ (3 * ((1 + 3 * κ) * R)) ^ d :=
          pow_le_pow_left₀ h0 h2 d
      _ = 3 ^ d * (1 + 3 * κ) ^ d * (R : ℝ) ^ d := by rw [mul_pow, mul_pow]; ring
  have hsq : (R : ℝ) ^ σ ≤ ((R : ℝ) + 1) ^ τ :=
    calc (R : ℝ) ^ σ ≤ (R : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hx1 hστ
      _ ≤ ((R : ℝ) + 1) ^ τ := Real.rpow_le_rpow hx0.le (by linarith) hτ
  have hE1 : Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ)) ≤ E := by
    refine Real.exp_le_exp.2 ?_
    have h0 : 0 ≤ (R : ℝ) ^ σ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcc₁ h0,
      mul_le_mul_of_nonneg_left hsq (hc0.trans hcc₁)]
  have hE2 : Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s) ≤ E := by
    rw [grad_exponent_eq hx0 hL hC₂]
    exact Rigidity.Corrector.exp_neg_rpow_le_exp_neg_rpow hx1 hσδ hc0 hcc₃
  have hM : (2 * (R : ℝ) + 1) ^ d ≤ 3 ^ d * (R : ℝ) ^ d :=
    calc (2 * (R : ℝ) + 1) ^ d ≤ (3 * (R : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = 3 ^ d * (R : ℝ) ^ d := mul_pow _ _ _
  have hRd : (1 : ℝ) ≤ (R : ℝ) ^ d := one_le_pow₀ hx1
  have hY : (2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
      2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s) ≤
      (3 ^ d * C₁ + 2) * (R : ℝ) ^ d * E := by
    calc (2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s)
        ≤ 3 ^ d * (R : ℝ) ^ d * (C₁ * E) + 2 * ((R : ℝ) ^ d * E) := by
          gcongr
          exact hE2.trans (le_mul_of_one_le_left hE0 hRd)
      _ = (3 ^ d * C₁ + 2) * (R : ℝ) ^ d * E := by ring
  have hY0 : 0 ≤ (2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
      2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s) := by positivity
  calc ((((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) : ℝ)) *
        ((2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s))
      ≤ 3 ^ d * (1 + 3 * κ) ^ d * (R : ℝ) ^ d * ((3 ^ d * C₁ + 2) * (R : ℝ) ^ d * E) :=
        mul_le_mul hN hY hY0 (by positivity)
    _ = _ := by ring

end Rigidity.Corrector.GeneralDim
