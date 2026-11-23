import Rigidity.Proofs.Green.DarioGuGaussianLatticeDiff
import Rigidity.Proofs.Green.DarioGuTwoScaleWeightTrunc
import Rigidity.Proofs.Green.DarioGuGaussianMass

/-!
# Weighted Gaussian moment sums for Step 4 of Proposition 4.3 of Dario–Gu

Step 4 of the proof of Proposition 4.3 of Dario–Gu (lines 2416-2446 of the source) sums the
squares of `f` and `F` against the weight `ψ² = exp(2g/C)`: the Gaussian factor
`exp(-|x - y|²/(32σr))²` of the heat kernel bounds absorbs the weight once `C ≥ 128σ`, and the
growth `(√r + |x - y| + 2)^{2β}` of the corrector (Proposition 2.12) costs `r^β`. This file proves:

* `dgWeightTrunc_sq_le`: `ψ_R(x')² ≤ e^{4/C} exp(4|x - y|²/(Cr))` for `|x' - y| ≤ |x - y| + 1`;
* `sq_dgWeightTrunc_sub_le`: `(ψ_R(x + e_i) - ψ_R(x))² ≤ 18 C^{-2} e^{15/C} r^{-1}
  (1 + |x - y|²/r) exp(4|x - y|²/(Cr))`, from the slope bound `dgShapeSlope_le`;
* `tsum_weightGauss_le`: `Σ_x exp(4|x - y|²/(Cr)) exp(-|x - y|²/(32σr))² (1 + |x - y|²/r)
  (√r + |x - y| + 2)^{2β} ≤ Q r^{1 + β}` for `C ≥ 128σ`, `0 ≤ β ≤ 1`, `r ≥ 1`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- `(1 + d²/r) g_{ar}(d) ≤ (1 + √2 a) g_{4ar}(d)`. -/
theorem one_add_sq_mul_gauss1_le {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (d : ℝ) :
    (1 + d ^ 2 / r) * gauss1 (a * r) d ≤ (1 + Real.sqrt 2 * a) * gauss1 (4 * (a * r)) d := by
  have h1 := sq_mul_gauss1_le (by positivity : 0 < a * r) d
  have h2 := gauss1_mono (by positivity : 0 < a * r) (by nlinarith : a * r ≤ 4 * (a * r)) d
  have h3 : d ^ 2 / r * gauss1 (a * r) d ≤ Real.sqrt 2 * a * gauss1 (4 * (a * r)) d := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hr]
    calc d ^ 2 * gauss1 (a * r) d ≤ Real.sqrt 2 * (a * r) * gauss1 (4 * (a * r)) d := h1
      _ = Real.sqrt 2 * a * gauss1 (4 * (a * r)) d * r := by ring
  calc (1 + d ^ 2 / r) * gauss1 (a * r) d = gauss1 (a * r) d + d ^ 2 / r * gauss1 (a * r) d := by
        ring
    _ ≤ gauss1 (4 * (a * r)) d + Real.sqrt 2 * a * gauss1 (4 * (a * r)) d := add_le_add h2 h3
    _ = (1 + Real.sqrt 2 * a) * gauss1 (4 * (a * r)) d := by ring

/-- `(√r + d + 2)^{2β} ≤ 18 r^β (1 + d²/r)` for `r ≥ 1`, `d ≥ 0`, `0 ≤ β ≤ 1`. -/
theorem rpow_two_mul_le {r d β : ℝ} (hr : 1 ≤ r) (hd : 0 ≤ d) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (Real.sqrt r + d + 2) ^ (2 * β) ≤ 18 * r ^ β * (1 + d ^ 2 / r) := by
  have hr0 : 0 < r := by linarith
  have hs := Real.sqrt_nonneg r
  have hsq := Real.sq_sqrt hr0.le
  have hB : 0 ≤ Real.sqrt r + d + 2 := by positivity
  have hB2 : (Real.sqrt r + d + 2) ^ 2 ≤ 18 * r * (1 + d ^ 2 / r) := by
    have e : 18 * r * (1 + d ^ 2 / r) = 18 * r + 18 * d ^ 2 := by field_simp
    rw [e]
    nlinarith [sq_nonneg (Real.sqrt r - d), sq_nonneg (Real.sqrt r - 2), sq_nonneg (d - 2)]
  have h1 : 1 ≤ 1 + d ^ 2 / r := by
    have : 0 ≤ d ^ 2 / r := by positivity
    linarith
  rw [Real.rpow_mul hB, Real.rpow_two]
  calc ((Real.sqrt r + d + 2) ^ 2) ^ β ≤ (18 * r * (1 + d ^ 2 / r)) ^ β :=
        Real.rpow_le_rpow (by positivity) hB2 hβ0
    _ = (18 : ℝ) ^ β * r ^ β * (1 + d ^ 2 / r) ^ β := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) hr0.le]
    _ ≤ 18 * r ^ β * (1 + d ^ 2 / r) := by
        have a1 : (18 : ℝ) ^ β ≤ 18 := by
          calc (18 : ℝ) ^ β ≤ (18 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
            _ = 18 := Real.rpow_one _
        have a2 : (1 + d ^ 2 / r) ^ β ≤ 1 + d ^ 2 / r := by
          calc (1 + d ^ 2 / r) ^ β ≤ (1 + d ^ 2 / r) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h1 hβ1
            _ = 1 + d ^ 2 / r := Real.rpow_one _
        have a3 : 0 ≤ r ^ β := Real.rpow_nonneg hr0.le _
        have a4 : 0 ≤ (1 + d ^ 2 / r) ^ β := Real.rpow_nonneg (by linarith) _
        calc (18 : ℝ) ^ β * r ^ β * (1 + d ^ 2 / r) ^ β ≤ 18 * r ^ β * (1 + d ^ 2 / r) ^ β := by
              gcongr
          _ ≤ 18 * r ^ β * (1 + d ^ 2 / r) := by gcongr

/-- The slope of the shape: `dgShapeSlope t ρ ≤ 3ρ/t`. -/
theorem dgShapeSlope_le {t ρ : ℝ} (ht : 0 < t) (hρ : 0 ≤ ρ) : dgShapeSlope t ρ ≤ 3 * ρ / t := by
  unfold dgShapeSlope
  split_ifs with h
  · exact div_le_div_of_nonneg_right (by linarith) ht.le
  · push Not at h
    have hq : 1 < ρ / t := by rw [lt_div_iff₀ ht]; linarith
    have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < ρ / t)
    have e : 3 * ρ / t = 3 * (ρ / t) := by ring
    rw [e]
    linarith

/-- `ψ_R(x')² ≤ e^{4/C} exp(4|x - y|²/(Cr))` when `|x' - y| ≤ |x - y| + 1`. -/
theorem dgWeightTrunc_sq_le {C r R : ℝ} (hC : 0 < C) (hr : 1 ≤ r) (hR : 0 ≤ R) {x x' y : Vertex 2}
    (hx : latticeDist x' y ≤ latticeDist x y + 1) :
    dgWeightTrunc C r R y x' ^ 2 ≤
      Real.exp (4 / C) * Real.exp (4 * latticeDist x y ^ 2 / (C * r)) := by
  have hr0 : 0 < r := by linarith
  have hd := latticeDist_nonneg x y
  have hm0 : 0 ≤ min (latticeDist x' y) R := le_min (latticeDist_nonneg _ _) hR
  have hS : dgShape r (min (latticeDist x' y) R) ≤ (2 * latticeDist x y ^ 2 + 2) / r := by
    refine (dgShape_le_sq hr0 hm0).trans (div_le_div_of_nonneg_right ?_ hr0.le)
    have h1 : min (latticeDist x' y) R ≤ latticeDist x y + 1 := (min_le_left _ _).trans hx
    nlinarith [sq_nonneg (latticeDist x y - 1)]
  unfold dgWeightTrunc
  rw [sq, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have e : (2 * latticeDist x y ^ 2 + 2) / r / C * 2 =
      4 * latticeDist x y ^ 2 / (C * r) + 4 / (C * r) := by
    field_simp
    ring
  have h4 : 4 / (C * r) ≤ 4 / C := div_le_div_of_nonneg_left (by norm_num) hC
    (by nlinarith)
  have h5 : dgShape r (min (latticeDist x' y) R) / C ≤ (2 * latticeDist x y ^ 2 + 2) / r / C :=
    div_le_div_of_nonneg_right hS hC.le
  linarith

/-- **The discrete gradient of the weight**: `(ψ_R(x + e_i) - ψ_R(x))² ≤
18 C^{-2} e^{15/C} r^{-1} (1 + |x - y|²/r) exp(4|x - y|²/(Cr))`. -/
theorem sq_dgWeightTrunc_sub_le {C r R : ℝ} (hC : 0 < C) (hr : 1 ≤ r) (hR : 0 ≤ R)
    (x y : Vertex 2) (i : Fin 2) :
    (dgWeightTrunc C r R y (x + unit i) - dgWeightTrunc C r R y x) ^ 2 ≤
      18 / C ^ 2 * Real.exp (15 / C) / r * (1 + latticeDist x y ^ 2 / r) *
        Real.exp (4 * latticeDist x y ^ 2 / (C * r)) := by
  have hr0 : 0 < r := by linarith
  set d := latticeDist x y with hddef
  have hd : 0 ≤ d := latticeDist_nonneg x y
  set ρ := min d R with hρ
  set ρ' := min (latticeDist (x + unit i) y) R with hρ'
  have hρ0 : 0 ≤ ρ := le_min hd hR
  have hρ'0 : 0 ≤ ρ' := le_min (latticeDist_nonneg _ _) hR
  have hρρ : |ρ' - ρ| ≤ 1 :=
    (abs_min_sub_min_le _ _ R).trans (abs_latticeDist_add_unit_sub_le x y i)
  have hsl := abs_dgShape_sub_le_slope hr0 hρ0 hρ'0 hρρ
  have hsl2 : dgShapeSlope r (ρ + 1) ≤ 3 * (d + 1) / r :=
    (dgShapeSlope_le hr0 (by linarith)).trans
      (div_le_div_of_nonneg_right (by linarith [min_le_left d R]) hr0.le)
  set D := 3 * (d + 1) / (C * r) with hD
  have hD0 : 0 ≤ D := by positivity
  have hab : |dgShape r ρ' / C - dgShape r ρ / C| ≤ D := by
    rw [← sub_div, abs_div, abs_of_pos hC, div_le_iff₀ hC, hD]
    have e : 3 * (d + 1) / (C * r) * C = 3 * (d + 1) / r := by field_simp
    rw [e]
    exact hsl.trans hsl2
  have key := sq_exp_sub_exp_le hab
  unfold dgWeightTrunc
  rw [← hρ, ← hρ']
  refine key.trans ?_
  -- the three factors
  have hea : Real.exp (dgShape r ρ / C) ^ 2 ≤ Real.exp (2 * d ^ 2 / (C * r)) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have h1 : dgShape r ρ ≤ d ^ 2 / r :=
      (dgShape_le_sq hr0 hρ0).trans (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hρ0 (min_le_left _ _) 2) hr0.le)
    have e : 2 * d ^ 2 / (C * r) = 2 * (d ^ 2 / r / C) := by field_simp
    rw [e]
    push_cast
    have := div_le_div_of_nonneg_right h1 hC.le
    linarith
  have hD2 : D ^ 2 ≤ 18 / C ^ 2 / r * (1 + d ^ 2 / r) := by
    have e1 : D ^ 2 = 9 * (d + 1) ^ 2 / (C ^ 2 * r ^ 2) := by
      rw [hD]
      ring
    have e : 18 / C ^ 2 / r * (1 + d ^ 2 / r) = (18 * r + 18 * d ^ 2) / (C ^ 2 * r ^ 2) := by
      field_simp
    rw [e1, e]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (d - 1)]) (by positivity)
  have heD : Real.exp D ^ 2 ≤ Real.exp (15 / C) * Real.exp (d ^ 2 / (C * r)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp, hD]
    push_cast
    have h6 : 6 * (d + 1) ≤ d ^ 2 + 15 := by nlinarith [sq_nonneg (d - 3)]
    have e1 : 2 * (3 * (d + 1) / (C * r)) = 6 * (d + 1) / (C * r) := by ring
    have e2 : 15 / C + d ^ 2 / (C * r) = (15 * r + d ^ 2) / (C * r) := by
      field_simp
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hexp : Real.exp (2 * d ^ 2 / (C * r)) * Real.exp (d ^ 2 / (C * r)) ≤
      Real.exp (4 * d ^ 2 / (C * r)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : 0 ≤ d ^ 2 / (C * r) := by positivity
    have e : 2 * d ^ 2 / (C * r) + d ^ 2 / (C * r) = 3 * (d ^ 2 / (C * r)) := by ring
    have e' : 4 * d ^ 2 / (C * r) = 4 * (d ^ 2 / (C * r)) := by ring
    rw [e, e']
    linarith
  have p1 : 0 ≤ Real.exp (dgShape r ρ / C) ^ 2 := by positivity
  have p2 : 0 ≤ D ^ 2 := sq_nonneg _
  have p3 : 0 ≤ Real.exp D ^ 2 := by positivity
  calc Real.exp (dgShape r ρ / C) ^ 2 * (D ^ 2 * Real.exp D ^ 2)
      ≤ Real.exp (2 * d ^ 2 / (C * r)) *
          (18 / C ^ 2 / r * (1 + d ^ 2 / r) *
            (Real.exp (15 / C) * Real.exp (d ^ 2 / (C * r)))) := by
        gcongr
    _ = 18 / C ^ 2 * Real.exp (15 / C) / r * (1 + d ^ 2 / r) *
          (Real.exp (2 * d ^ 2 / (C * r)) * Real.exp (d ^ 2 / (C * r))) := by ring
    _ ≤ 18 / C ^ 2 * Real.exp (15 / C) / r * (1 + d ^ 2 / r) *
          Real.exp (4 * d ^ 2 / (C * r)) := by
        have : 0 ≤ 18 / C ^ 2 * Real.exp (15 / C) / r * (1 + d ^ 2 / r) := by positivity
        exact mul_le_mul_of_nonneg_left hexp this

/-- The summand of the weighted Gaussian moment sums. -/
noncomputable def weightGauss (σ C β r : ℝ) (y x : Vertex 2) : ℝ :=
  Real.exp (4 * latticeDist x y ^ 2 / (C * r)) *
    Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) ^ 2 * (1 + latticeDist x y ^ 2 / r) *
      (Real.sqrt r + latticeDist x y + 2) ^ (2 * β)

theorem weightGauss_nonneg {σ C β r : ℝ} (hr : 0 < r) (y x : Vertex 2) :
    0 ≤ weightGauss σ C β r y x := by
  unfold weightGauss
  have := latticeDist_nonneg x y
  positivity

/-- The pointwise bound of the summand by the lattice Gaussian of variance `256σ`. -/
theorem weightGauss_le {σ C β r : ℝ} (hσ : 0 < σ) (hC : 128 * σ ≤ C) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hr : 1 ≤ r) (y x : Vertex 2) :
    weightGauss σ C β r y x ≤ 18 * (1 + Real.sqrt 2 * (32 * σ)) *
      (1 + Real.sqrt 2 * (4 * (32 * σ))) * (2 * Real.pi * (256 * σ)) * r ^ (1 + β) *
        latticeGaussian (256 * σ) r x y := by
  have hr0 : 0 < r := by linarith
  set d := latticeDist x y with hddef
  have hd : 0 ≤ d := latticeDist_nonneg x y
  have hC0 : 0 < C := by linarith
  -- the weight is absorbed by half of the Gaussian factor
  have h1 : Real.exp (4 * d ^ 2 / (C * r)) * Real.exp (-(d ^ 2 / (32 * σ * r))) ^ 2 ≤
      gauss1 (32 * σ * r) d := by
    unfold gauss1
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    push_cast
    have hq : 4 * d ^ 2 / (C * r) ≤ d ^ 2 / (32 * σ * r) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ d ^ 2 * r := by positivity
      nlinarith
    linarith
  have h2 := one_add_sq_mul_gauss1_le (by positivity : (0 : ℝ) < 32 * σ) hr0 d
  have h3 := one_add_sq_mul_gauss1_le (by positivity : (0 : ℝ) < 4 * (32 * σ)) hr0 d
  have h4 := rpow_two_mul_le hr hd hβ0 hβ1
  have hlat : gauss1 (4 * (4 * (32 * σ) * r)) d =
      2 * Real.pi * (256 * σ) * r * latticeGaussian (256 * σ) r x y := by
    have hne : (2 * Real.pi * (256 * σ) * r) ≠ 0 := by positivity
    rw [latticeGaussian_eq, ← hddef, mul_inv_cancel_left₀ hne,
      show 4 * (4 * (32 * σ) * r) = 2 * (256 * σ) * r by ring]
    rfl
  have hrr : r ^ (1 + β) = r * r ^ β := by rw [Real.rpow_add hr0, Real.rpow_one]
  have g1 := gauss1_pos (32 * σ * r) d
  have hA : 0 ≤ 1 + d ^ 2 / r := by positivity
  have hrβ : 0 ≤ r ^ β := Real.rpow_nonneg hr0.le _
  unfold weightGauss
  rw [← hddef]
  calc Real.exp (4 * d ^ 2 / (C * r)) * Real.exp (-(d ^ 2 / (32 * σ * r))) ^ 2 *
        (1 + d ^ 2 / r) * (Real.sqrt r + d + 2) ^ (2 * β)
      ≤ gauss1 (32 * σ * r) d * (1 + d ^ 2 / r) * (18 * r ^ β * (1 + d ^ 2 / r)) := by
        gcongr
    _ = 18 * r ^ β * ((1 + d ^ 2 / r) * ((1 + d ^ 2 / r) * gauss1 (32 * σ * r) d)) := by ring
    _ ≤ 18 * r ^ β * ((1 + d ^ 2 / r) *
          ((1 + Real.sqrt 2 * (32 * σ)) * gauss1 (4 * (32 * σ * r)) d)) := by
        gcongr
    _ = 18 * r ^ β * (1 + Real.sqrt 2 * (32 * σ)) *
          ((1 + d ^ 2 / r) * gauss1 (4 * (32 * σ) * r) d) := by
        rw [show 4 * (32 * σ * r) = 4 * (32 * σ) * r by ring]
        ring
    _ ≤ 18 * r ^ β * (1 + Real.sqrt 2 * (32 * σ)) *
          ((1 + Real.sqrt 2 * (4 * (32 * σ))) * gauss1 (4 * (4 * (32 * σ) * r)) d) := by
        gcongr
    _ = 18 * (1 + Real.sqrt 2 * (32 * σ)) * (1 + Real.sqrt 2 * (4 * (32 * σ))) *
          (2 * Real.pi * (256 * σ)) * r ^ (1 + β) * latticeGaussian (256 * σ) r x y := by
        rw [hlat, hrr]
        ring

/-- **The weighted Gaussian moment sum**: `Σ_x exp(4|x - y|²/(Cr)) exp(-|x - y|²/(32σr))²
(1 + |x - y|²/r) (√r + |x - y| + 2)^{2β} ≤ Q r^{1 + β}` for `C ≥ 128σ`, `0 ≤ β ≤ 1`, `r ≥ 1`. -/
theorem tsum_weightGauss_le {σ : ℝ} (hσ : 0 < σ) : ∃ Q : ℝ, 0 < Q ∧
    ∀ (C β r : ℝ) (y : Vertex 2), 128 * σ ≤ C → 0 ≤ β → β ≤ 1 → 1 ≤ r →
      Summable (fun x => weightGauss σ C β r y x) ∧
        ∑' x, weightGauss σ C β r y x ≤ Q * r ^ (1 + β) := by
  set A := 18 * (1 + Real.sqrt 2 * (32 * σ)) * (1 + Real.sqrt 2 * (4 * (32 * σ))) *
    (2 * Real.pi * (256 * σ)) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A * max (gaussMassBound (256 * σ)) 1, by positivity,
    fun C β r y hC hβ0 hβ1 hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hσ' : 0 < 256 * σ := by positivity
  have hs := summable_latticeGaussian hσ' hr y
  have hb : ∀ x, weightGauss σ C β r y x ≤ A * r ^ (1 + β) * latticeGaussian (256 * σ) r x y :=
    fun x => weightGauss_le hσ hC hβ0 hβ1 hr y x
  have hsum : Summable fun x => weightGauss σ C β r y x :=
    Summable.of_nonneg_of_le (fun x => weightGauss_nonneg hr0 y x) hb (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  have hrp : 0 ≤ r ^ (1 + β) := Real.rpow_nonneg hr0.le _
  calc ∑' x, weightGauss σ C β r y x ≤ ∑' x, A * r ^ (1 + β) * latticeGaussian (256 * σ) r x y :=
        Summable.tsum_le_tsum hb hsum (hs.mul_left _)
    _ = A * r ^ (1 + β) * ∑' x, latticeGaussian (256 * σ) r x y := tsum_mul_left
    _ ≤ A * r ^ (1 + β) * max (gaussMassBound (256 * σ)) 1 :=
        mul_le_mul_of_nonneg_left ((tsum_latticeGaussian_le hσ' hr y).trans (le_max_left _ _))
          (by positivity)
    _ = A * max (gaussMassBound (256 * σ)) 1 * r ^ (1 + β) := by ring

end Rigidity.Green
