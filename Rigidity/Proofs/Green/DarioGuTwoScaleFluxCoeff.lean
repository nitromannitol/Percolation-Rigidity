import Rigidity.Proofs.Green.DarioGuGaussianLatticeThird
import Rigidity.Proofs.Green.DarioGuTwoScaleMomentSum

/-!
# The coefficients of Step 3 of Proposition 4.3 of Dario–Gu

In Step 3 of the proof of Proposition 4.3 of Dario–Gu (the quantities `Ξ₁`, `Ξ₂` of (4.31) and
the estimate after (4.32), lines 2340-2346 and 2399-2412 of the source) the flux is tested against
`D_i D_k p̄ ψ² w = (D_i D_k p̄ ψ)(ψ w)`. The coefficient `D_i D_k p̄ ψ` is bounded with the
Gaussian decay once `C ≥ 128σ`:

* `dgWeightTrunc_le_exp_sq`: `ψ_R(x) ≤ exp(|x - y|²/(rC))`;
* `abs_secondDiff_mul_weight_le`: `|D_i D_k p̄ ψ_R|(x) ≤ K r^{-2} exp(-|x - y|²/(64σr))`;
* `abs_secondDiff_mul_weight_sub_le`: `|(D_i D_k p̄ ψ_R)(x + e_j) - (D_i D_k p̄ ψ_R)(x)| ≤
  K r^{-5/2} exp(-|x - y|²/(256σr))`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem dgWeightTrunc_le_exp_sq {C r R : ℝ} (hC : 0 < C) (hr : 0 < r) (hR : 0 ≤ R)
    (y x : Vertex 2) : dgWeightTrunc C r R y x ≤ Real.exp (latticeDist x y ^ 2 / (r * C)) := by
  unfold dgWeightTrunc
  refine Real.exp_le_exp.2 ?_
  have hm0 : 0 ≤ min (latticeDist x y) R := le_min (latticeDist_nonneg _ _) hR
  have h1 : dgShape r (min (latticeDist x y) R) ≤ latticeDist x y ^ 2 / r :=
    (dgShape_le_sq hr hm0).trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hm0 (min_le_left _ _) 2) hr.le)
  rw [← div_div]
  exact div_le_div_of_nonneg_right h1 hC.le

/-- `|D_i D_k p̄ ψ_R|(x) ≤ K r^{-2} exp(-|x - y|²/(64σr))` for `C ≥ 64σ`, `r ≥ 1`. -/
theorem abs_secondDiff_mul_weight_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (C r R : ℝ) (x y : Vertex 2) (i k : Fin 2), 64 * σ ≤ C → 1 ≤ r → 0 ≤ R →
      |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x| ≤
        K / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) := by
  obtain ⟨K, hK, h⟩ := abs_fwdDiff_fwdDiff_latticeGaussian_le hσ
  refine ⟨K, hK, fun C r R x y i k hC hr hR => ?_⟩
  have hr0 : 0 < r := by linarith
  have hC0 : 0 < C := by linarith
  have hψ := dgWeightTrunc_le_exp_sq hC0 hr0 hR y x
  have hψ0 := dgWeightTrunc_pos C r R y x
  rw [abs_mul, abs_of_pos hψ0]
  have hd := sq_nonneg (latticeDist x y)
  have hq : latticeDist x y ^ 2 / (r * C) ≤ latticeDist x y ^ 2 / (64 * σ * r) := by
    apply div_le_div_of_nonneg_left hd (by positivity)
    nlinarith
  calc |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x| * dgWeightTrunc C r R y x
      ≤ (K / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r)))) *
          Real.exp (latticeDist x y ^ 2 / (r * C)) :=
        mul_le_mul (h r x y i k hr) hψ hψ0.le (by positivity)
    _ = K / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r)) +
          latticeDist x y ^ 2 / (r * C)) := by rw [Real.exp_add]; ring
    _ ≤ K / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        have e : latticeDist x y ^ 2 / (32 * σ * r) =
            2 * (latticeDist x y ^ 2 / (64 * σ * r)) := by
          ring
        rw [e]
        linarith

/-- `|(D_i D_k p̄ ψ_R)(x + e_j) - (D_i D_k p̄ ψ_R)(x)| ≤ K r^{-5/2} exp(-|x - y|²/(256σr))` for
`C ≥ 128σ`, `r ≥ 1`. -/
theorem abs_secondDiff_mul_weight_sub_le {σ C : ℝ} (hσ : 0 < σ) (hC : 128 * σ ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r R : ℝ) (x y : Vertex 2) (i k j : Fin 2), 1 ≤ r → 0 ≤ R →
      |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) (x + unit j) *
          dgWeightTrunc C r R y (x + unit j) -
        fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x| ≤
        K / (r ^ 2 * Real.sqrt r) * Real.exp (-(latticeDist x y ^ 2 / (256 * σ * r))) := by
  obtain ⟨K₂, hK₂, h2⟩ := abs_fwdDiff_fwdDiff_latticeGaussian_le hσ
  obtain ⟨K₃, hK₃, h3⟩ := abs_fwdDiff_fwdDiff_fwdDiff_latticeGaussian_le hσ
  have hC0 : 0 < C := by linarith
  set L₂ := K₂ * Real.sqrt (18 / C ^ 2 * Real.exp (15 / C) * (1 + Real.sqrt 2 * (32 * σ)))
    with hL₂
  refine ⟨K₃ * Real.exp (2 / C) + L₂, by positivity, fun r R x y i k j hr hR => ?_⟩
  have hr0 : 0 < r := by linarith
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  set d := latticeDist x y with hddef
  have hd0 : 0 ≤ d := latticeDist_nonneg x y
  set D := fun z => fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) z with hDdef
  set ψ := dgWeightTrunc C r R y with hψdef
  have e : D (x + unit j) * ψ (x + unit j) - D x * ψ x =
      (D (x + unit j) - D x) * ψ (x + unit j) + D x * (ψ (x + unit j) - ψ x) := by ring
  -- the third difference term
  have hT1 : |(D (x + unit j) - D x) * ψ (x + unit j)| ≤
      K₃ * Real.exp (2 / C) / (r ^ 2 * Real.sqrt r) *
        Real.exp (-(d ^ 2 / (64 * σ * r))) := by
    have h3' := h3 r x y i k j hr
    have hd1 : latticeDist (x + unit j) y ≤ d + 1 :=
      by linarith [(abs_le.1 (abs_latticeDist_add_unit_sub_le x y j)).2]
    have hψ1 := dgWeightTrunc_le_exp_sq hC0 hr0 hR y (x + unit j)
    have hψ2 : Real.exp (latticeDist (x + unit j) y ^ 2 / (r * C)) ≤
        Real.exp (2 / C) * Real.exp (d ^ 2 / (64 * σ * r)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hsq : latticeDist (x + unit j) y ^ 2 ≤ 2 * d ^ 2 + 2 := by
        have h0 := latticeDist_nonneg (x + unit j) y
        nlinarith [sq_nonneg (d - 1)]
      have a1 : latticeDist (x + unit j) y ^ 2 / (r * C) ≤ (2 * d ^ 2 + 2) / (r * C) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      have a2 : (2 * d ^ 2 + 2) / (r * C) = 2 * d ^ 2 / (r * C) + 2 / (r * C) := by ring
      have a3 : 2 / (r * C) ≤ 2 / C :=
        div_le_div_of_nonneg_left (by norm_num) hC0 (by nlinarith)
      have a4 : 2 * d ^ 2 / (r * C) ≤ d ^ 2 / (64 * σ * r) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ d ^ 2 * r := by positivity
        nlinarith
      linarith
    have hψ0 := dgWeightTrunc_pos C r R y (x + unit j)
    rw [abs_mul, abs_of_pos hψ0]
    have h3'' : |D (x + unit j) - D x| ≤ K₃ / (r ^ 2 * Real.sqrt r) *
        Real.exp (-(d ^ 2 / (32 * σ * r))) := h3'
    calc |D (x + unit j) - D x| * ψ (x + unit j)
        ≤ (K₃ / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (32 * σ * r)))) *
            (Real.exp (2 / C) * Real.exp (d ^ 2 / (64 * σ * r))) :=
          mul_le_mul h3'' (hψ1.trans hψ2) hψ0.le (by positivity)
      _ = K₃ * Real.exp (2 / C) / (r ^ 2 * Real.sqrt r) *
            Real.exp (-(d ^ 2 / (32 * σ * r)) + d ^ 2 / (64 * σ * r)) := by
          rw [Real.exp_add]; ring
      _ = K₃ * Real.exp (2 / C) / (r ^ 2 * Real.sqrt r) *
            Real.exp (-(d ^ 2 / (64 * σ * r))) := by
          congr 2
          ring
  -- the weight difference term, through its square
  have hT2 : |D x * (ψ (x + unit j) - ψ x)| ≤
      L₂ / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r))) := by
    have hD := h2 r x y i k hr
    have hW := sq_dgWeightTrunc_sub_le hC0 hr hR x y j
    have hDsq : D x ^ 2 ≤ (K₂ / r ^ 2) ^ 2 * Real.exp (-(d ^ 2 / (32 * σ * r))) ^ 2 := by
      rw [← mul_pow, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have hg : Real.exp (-(d ^ 2 / (32 * σ * r))) ^ 2 * Real.exp (4 * d ^ 2 / (C * r)) ≤
        gauss1 (32 * σ * r) d := by
      unfold gauss1
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      push_cast
      have hq : 4 * d ^ 2 / (C * r) ≤ d ^ 2 / (32 * σ * r) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ d ^ 2 * r := by positivity
        nlinarith
      linarith
    have hm := one_add_sq_mul_gauss1_le (by positivity : (0 : ℝ) < 32 * σ) hr0 d
    have hsq : (D x * (ψ (x + unit j) - ψ x)) ^ 2 ≤
        (L₂ / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r)))) ^ 2 := by
      have hsr2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
      have hL2 : L₂ ^ 2 = K₂ ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) *
          (1 + Real.sqrt 2 * (32 * σ))) := by
        rw [hL₂, mul_pow, Real.sq_sqrt (by positivity)]
      have hexp : Real.exp (-(d ^ 2 / (256 * σ * r))) ^ 2 = gauss1 (4 * (32 * σ * r)) d := by
        unfold gauss1
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hW' : (ψ (x + unit j) - ψ x) ^ 2 ≤ 18 / C ^ 2 * Real.exp (15 / C) / r *
          (1 + d ^ 2 / r) * Real.exp (4 * d ^ 2 / (C * r)) := hW
      have p1 : 0 ≤ 18 / C ^ 2 * Real.exp (15 / C) / r := by positivity
      have p2 : 0 ≤ 1 + d ^ 2 / r := by positivity
      calc (D x * (ψ (x + unit j) - ψ x)) ^ 2 = D x ^ 2 * (ψ (x + unit j) - ψ x) ^ 2 := by ring
        _ ≤ ((K₂ / r ^ 2) ^ 2 * Real.exp (-(d ^ 2 / (32 * σ * r))) ^ 2) *
            (18 / C ^ 2 * Real.exp (15 / C) / r * (1 + d ^ 2 / r) *
              Real.exp (4 * d ^ 2 / (C * r))) :=
            mul_le_mul hDsq hW' (sq_nonneg _) (by positivity)
        _ = (K₂ / r ^ 2) ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) / r) * ((1 + d ^ 2 / r) *
            (Real.exp (-(d ^ 2 / (32 * σ * r))) ^ 2 * Real.exp (4 * d ^ 2 / (C * r)))) := by ring
        _ ≤ (K₂ / r ^ 2) ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) / r) * ((1 + d ^ 2 / r) *
            gauss1 (32 * σ * r) d) := by gcongr
        _ ≤ (K₂ / r ^ 2) ^ 2 * (18 / C ^ 2 * Real.exp (15 / C) / r) *
            ((1 + Real.sqrt 2 * (32 * σ)) * gauss1 (4 * (32 * σ * r)) d) := by gcongr
        _ = (L₂ / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r)))) ^ 2 := by
            have hR : (L₂ / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r)))) ^ 2 =
                L₂ ^ 2 / (r ^ 4 * Real.sqrt r ^ 2) * Real.exp (-(d ^ 2 / (256 * σ * r))) ^ 2 := by
              ring
            rw [hR, hsr2, hL2, hexp]
            field_simp
    have := sq_le_sq.1 hsq
    rwa [abs_of_nonneg (by positivity : 0 ≤ L₂ / (r ^ 2 * Real.sqrt r) *
      Real.exp (-(d ^ 2 / (256 * σ * r))))] at this
  have hmono : Real.exp (-(d ^ 2 / (64 * σ * r))) ≤ Real.exp (-(d ^ 2 / (256 * σ * r))) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg d) (by positivity) (by nlinarith)
  change |D (x + unit j) * ψ (x + unit j) - D x * ψ x| ≤ _
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have hT1' : K₃ * Real.exp (2 / C) / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (64 * σ * r))) ≤
      K₃ * Real.exp (2 / C) / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r))) :=
    mul_le_mul_of_nonneg_left hmono (by positivity)
  have e2 : (K₃ * Real.exp (2 / C) + L₂) / (r ^ 2 * Real.sqrt r) *
      Real.exp (-(d ^ 2 / (256 * σ * r))) =
      K₃ * Real.exp (2 / C) / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r))) +
        L₂ / (r ^ 2 * Real.sqrt r) * Real.exp (-(d ^ 2 / (256 * σ * r))) := by ring
  rw [e2]
  linarith

end Rigidity.Green
