import Rigidity.Proofs.Green.PointwiseHeatFinalD

/-!
# The heat kernel against the Gaussian with a Gaussian factor, at one configuration

From `|p_t(x, y) - θ^{-1} p̄(t, x - y)| ≤ C₁ (t/2)^{ε - d/2 - 1/2}` (`abs_vsrwHeat_sub_le_rpow` at
`s = t/2`) and the Gaussian upper bound `p_t(x, y) ≤ C₂ t^{-d/2} e^{-D²/(C₃ t)}` (`D = |x - y|`),
for `0 < δ ≤ 1/2` and `ε ≤ δ/2`, the geometric mean with weight `λ = δ/2` gives

  `|p_t(x, y) - θ^{-1} p̄(t, x - y)| ≤ K t^{-d/2 - (1/2 - δ)} e^{-D²/(K t)}`

for `t ≥ 1` (`abs_vsrwHeat_sub_le_gaussian`), with `K` depending only on the constants.
-/

open LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- The constant `K` of the error with a Gaussian factor. -/
noncomputable def gaussFactorConst (d : ℕ) (σ θ C₁ C₂ C₃ δ : ℝ) : ℝ :=
  max ((C₁ * 2 ^ ((d : ℝ) / 2 + 1)) ^ (1 - δ / 2) *
    (C₂ + θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) ^ (δ / 2)) (max C₃ (2 * σ) / (δ / 2))

/-- **The error with a Gaussian factor at one configuration** (Theorem 1 of Dario–Gu). -/
theorem abs_vsrwHeat_sub_le_gaussian {σ θ C₁ C₂ C₃ δ ε t a b D : ℝ} (hσ : 0 < σ) (hθ : 0 < θ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 < C₃) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ δ / 2) (ht : 2 ≤ t) (ha : 0 ≤ a)
    (hbound : b ≤ (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) * Real.exp (-(D ^ 2 / (2 * σ * t))))
    (hb0 : 0 ≤ b)
    (h1 : |a - θ⁻¹ * b| ≤ C₁ * (t / 2) ^ (ε - (d : ℝ) / 2 - 1 / 2))
    (hBar : a ≤ C₂ * t ^ (-((d : ℝ) / 2)) * Real.exp (-(D ^ 2 / (C₃ * t)))) :
    |a - θ⁻¹ * b| ≤ gaussFactorConst d σ θ C₁ C₂ C₃ δ * t ^ (-((d : ℝ) / 2) - (1 / 2 - δ)) *
      Real.exp (-(D ^ 2 / (gaussFactorConst d σ θ C₁ C₂ C₃ δ * t))) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  set C₄ := max C₃ (2 * σ) with hC₄
  have hC₄0 : 0 < C₄ := lt_max_of_lt_left hC₃
  set lam := δ / 2 with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl1 : lam ≤ 1 := by linarith
  -- the first bound in powers of `t`
  have hA : |a - θ⁻¹ * b| ≤ C₁ * 2 ^ ((d : ℝ) / 2 + 1) * t ^ (-((d : ℝ) / 2) - 1 / 2 + ε) := by
    refine h1.trans ?_
    rw [Real.div_rpow ht0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    have h2 : (2 : ℝ) ^ (-(ε - (d : ℝ) / 2 - 1 / 2)) ≤ 2 ^ ((d : ℝ) / 2 + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have e : t ^ (ε - (d : ℝ) / 2 - 1 / 2) = t ^ (-((d : ℝ) / 2) - 1 / 2 + ε) := by
      congr 1; ring
    rw [e]
    calc C₁ * (t ^ (-((d : ℝ) / 2) - 1 / 2 + ε) * 2 ^ (-(ε - (d : ℝ) / 2 - 1 / 2)))
        = C₁ * 2 ^ (-(ε - (d : ℝ) / 2 - 1 / 2)) * t ^ (-((d : ℝ) / 2) - 1 / 2 + ε) := by ring
      _ ≤ _ := by gcongr
  -- the second bound: both terms are Gaussian
  have hE1 : Real.exp (-(D ^ 2 / (C₃ * t))) ≤ Real.exp (-(D ^ 2 / (C₄ * t))) :=
    exp_neg_div_le (sq_nonneg D) (by positivity)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0.le)
  have hE2 : Real.exp (-(D ^ 2 / (2 * σ * t))) ≤ Real.exp (-(D ^ 2 / (C₄ * t))) :=
    exp_neg_div_le (sq_nonneg D) (by positivity)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ht0.le)
  have hB : |a - θ⁻¹ * b| ≤ (C₂ + θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) *
      t ^ (-((d : ℝ) / 2)) * Real.exp (-(D ^ 2 / (C₄ * t))) := by
    have hθb : 0 ≤ θ⁻¹ * b := mul_nonneg (inv_nonneg.2 hθ.le) hb0
    have hab : |a - θ⁻¹ * b| ≤ a + θ⁻¹ * b := by
      rw [abs_le]; constructor <;> linarith
    have hb' : θ⁻¹ * b ≤ θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * t ^ (-((d : ℝ) / 2)) *
        Real.exp (-(D ^ 2 / (C₄ * t))) := by
      have e : (2 * Real.pi * σ * t) ^ (-((d : ℝ) / 2)) =
          (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * t ^ (-((d : ℝ) / 2)) :=
        Real.mul_rpow (by positivity) ht0.le
      rw [e] at hbound
      calc θ⁻¹ * b ≤ θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * t ^ (-((d : ℝ) / 2)) *
            Real.exp (-(D ^ 2 / (2 * σ * t)))) :=
            mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hθ.le)
        _ ≤ θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * t ^ (-((d : ℝ) / 2)) *
            Real.exp (-(D ^ 2 / (C₄ * t)))) := by gcongr
        _ = _ := by ring
    have ha' : a ≤ C₂ * t ^ (-((d : ℝ) / 2)) * Real.exp (-(D ^ 2 / (C₄ * t))) :=
      hBar.trans (by gcongr)
    calc |a - θ⁻¹ * b| ≤ a + θ⁻¹ * b := hab
      _ ≤ _ := by nlinarith [ha', hb']
  have hG := le_of_two_bounds d (abs_nonneg _) ht0 (by positivity) (by positivity) hl0 hl1 hA hB
  -- the exponents
  have hexp : t ^ (-((d : ℝ) / 2) - (1 - lam) * (1 / 2 - ε)) ≤
      t ^ (-((d : ℝ) / 2) - (1 / 2 - δ)) := by
    apply Real.rpow_le_rpow_of_exponent_le ht1
    have : (1 - lam) * (1 / 2 - ε) ≥ 1 / 2 - δ := by
      rw [hlam]; nlinarith
    linarith
  set K := gaussFactorConst d σ θ C₁ C₂ C₃ δ with hK
  have hK1 : (C₁ * 2 ^ ((d : ℝ) / 2 + 1)) ^ (1 - lam) *
      (C₂ + θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) ^ lam ≤ K := le_max_left _ _
  have hK2 : C₄ / lam ≤ K := le_max_right _ _
  have hlpos : 0 < lam := by positivity
  have hexp2 : Real.exp (-(lam * D ^ 2 / (C₄ * t))) ≤ Real.exp (-(D ^ 2 / (K * t))) := by
    have e : lam * D ^ 2 / (C₄ * t) = D ^ 2 / (C₄ / lam * t) := by field_simp
    rw [e]
    exact exp_neg_div_le (sq_nonneg D) (by positivity) (mul_le_mul_of_nonneg_right hK2 ht0.le)
  refine hG.trans ?_
  have h0 : 0 ≤ (C₁ * 2 ^ ((d : ℝ) / 2 + 1)) ^ (1 - lam) *
      (C₂ + θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2))) ^ lam := by positivity
  have hK0 : 0 ≤ K := h0.trans hK1
  calc _ ≤ K * t ^ (-((d : ℝ) / 2) - (1 / 2 - δ)) * Real.exp (-(lam * D ^ 2 / (C₄ * t))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul hK1 hexp (by positivity) hK0
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp2 (by positivity)

end Rigidity.Green
