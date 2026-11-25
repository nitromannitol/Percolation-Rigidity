import Rigidity.Proofs.Poincare.SteinSigned
import Rigidity.Proofs.Poincare.GeneralSteinFinal

/-!
# The weighted Littlewood-Paley bound on `ℤ^d` with the constant `O(q)`, for signed data

The extension of `SteinSigned.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`. For `g` supported in a finite
set `S`, `1 < p ≤ 2` with dual exponent `q = p/(p-1)`, `0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1`:

  `Σ_x coshW(x) Γ_g(x)^{p/2} ≤ 2 (C q)^p Σ_x coshW |g|^p`,

`Γ_g(x) = ∫_0^T Σ_i (v_s(x + e_i) - v_s(x))² ds`, `v_s = heatF S g s` (`exists_steinSigned`):
`exists_steinWeighted` for `g⁺` and `g⁻`, with `λT ≤ 6d/5` for `λ = 2d(cosh a - 1)` (from
`cosh a - 1 ≤ (3/5) a²`, Lattice-Probability) and `p/(p-1) = q`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The bound `κ_d = 1 + (6d/5) e^{6d/5}` of the factor `λT e^{λT} + 1`. -/
noncomputable def kappaI (d : ℕ) : ℝ := 1 + 6 * d / 5 * Real.exp (6 * d / 5)

theorem one_le_kappaI (d : ℕ) : 1 ≤ kappaI d := by
  unfold kappaI
  have : 0 ≤ 6 * (d : ℝ) / 5 * Real.exp (6 * d / 5) := by positivity
  linarith

/-- `λ T e^{λT} + 1 ≤ κ_d` for `λ = 2d(cosh a - 1)`, `a² T ≤ 1`. -/
theorem kI_le {a T : ℝ} (ha0 : 0 ≤ a) (ha6 : a ≤ 1 / 6) (hT : 0 ≤ T)
    (haT : a * max (Real.sqrt T) 1 ≤ 1) :
    2 * d * (Real.cosh a - 1) * T * Real.exp (2 * d * T * (Real.cosh a - 1)) + 1 ≤ kappaI d := by
  have hc := LatticeProb.ContinuousTime.cosh_sub_one_le (l := a) (by
    rw [abs_of_nonneg ha0]; linarith)
  have hc0 : 0 ≤ Real.cosh a - 1 := by linarith [Real.one_le_cosh a]
  have haT' : a * Real.sqrt T ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ha0) haT
  have ha2T : a ^ 2 * T ≤ 1 := by
    have h := mul_self_le_mul_self (mul_nonneg ha0 (Real.sqrt_nonneg T)) haT'
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hT, one_mul] at h
    nlinarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcT : (Real.cosh a - 1) * T ≤ 3 / 5 := by nlinarith
  have hlam : 2 * d * (Real.cosh a - 1) * T ≤ 6 * d / 5 := by nlinarith
  have hlam0 : 0 ≤ 2 * d * (Real.cosh a - 1) * T := by positivity
  have he : Real.exp (2 * d * T * (Real.cosh a - 1)) ≤ Real.exp (6 * d / 5) :=
    Real.exp_le_exp.2 (by nlinarith)
  unfold kappaI
  have := mul_le_mul hlam he (Real.exp_pos _).le (by positivity)
  linarith

/-- **The constant of `exists_steinWeighted` is at most `(K_d C q)^p`**, with
`K_d = 16 (d + 1) 3^d κ_d`. -/
theorem steinConstant_le {C p a T : ℝ} (hC : 1 ≤ C) (hp1 : 1 < p) (hp2 : p ≤ 2) (ha0 : 0 ≤ a)
    (ha6 : a ≤ 1 / 6) (hT : 0 ≤ T) (haT : a * max (Real.sqrt T) 1 ≤ 1) :
    (2 / (p * (p - 1))) ^ (p / 2) *
      (((d + 1) * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1))) ^
        ((2 - p) / 2) *
      (2 * d * (Real.cosh a - 1) * T * Real.exp (2 * d * T * (Real.cosh a - 1)) + 1) ^ (p / 2) ≤
    (16 * (d + 1) * 3 ^ d * kappaI d * C * (p / (p - 1))) ^ p := by
  have hp0 : 0 < p := by linarith
  have hp10 : 0 < p - 1 := by linarith
  set q := p / (p - 1) with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hp10]; linarith
  have hw1 : 0 ≤ (2 - p) / 2 := by linarith
  have hw2 : 0 ≤ p / 2 := by linarith
  set κ := kappaI d with hκ
  have hκ1 : 1 ≤ κ := one_le_kappaI d
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have hc : 2 / (p * (p - 1)) ≤ 2 * q := by
    rw [hq, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hc0 : 0 ≤ 2 / (p * (p - 1)) := by positivity
  set D : ℝ := 2 * (d + 1) * C with hD
  have hD1 : 1 ≤ D := by nlinarith
  set B := 4 * 3 ^ d * q * D ^ p with hB
  have hDp : 1 ≤ D ^ p := Real.one_le_rpow hD1 hp0.le
  have hB1 : 1 ≤ B := by
    have : 1 ≤ 4 * 3 ^ d * q := by nlinarith
    nlinarith
  have hKM : ((d + 1) * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) ≤ B := by
    have he := Rigidity.Poincare.exp_le_two_of_le ha6
    have h1 : ((d + 1) * C * Real.exp a) ^ p ≤ D ^ p :=
      Real.rpow_le_rpow (by positivity) (by rw [hD]; nlinarith [Real.exp_pos a]) hp0.le
    have h2 : (2 : ℝ) ^ (p - 1) ≤ 2 := by
      calc (2 : ℝ) ^ (p - 1) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h3 : 2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1) ≤ 4 * 3 ^ d * q := by
      rw [hq, mul_div_assoc, show 4 * 3 ^ d * (p / (p - 1)) = 2 * 3 ^ d * 2 * (p / (p - 1)) by
        ring]
      have : 0 ≤ p / (p - 1) := by positivity
      have h23 : 0 ≤ 2 * (3 : ℝ) ^ d := by positivity
      have := mul_le_mul_of_nonneg_left h2 h23
      nlinarith
    have h4 : 0 ≤ 2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1) := by positivity
    calc ((d + 1) * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1))
        ≤ D ^ p * (4 * 3 ^ d * q) := mul_le_mul h1 h3 h4 (by positivity)
      _ = B := by rw [hB]; ring
  have hKM0 : 0 ≤ ((d + 1) * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) := by
    positivity
  have hKI := kI_le (d := d) ha0 ha6 hT haT
  have hKI0 : 0 ≤ 2 * d * (Real.cosh a - 1) * T * Real.exp (2 * d * T * (Real.cosh a - 1)) + 1 := by
    have : 0 ≤ Real.cosh a - 1 := by linarith [Real.one_le_cosh a]
    positivity
  calc (2 / (p * (p - 1))) ^ (p / 2) *
        (((d + 1) * C * Real.exp a) ^ p * (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1))) ^
          ((2 - p) / 2) *
        (2 * d * (Real.cosh a - 1) * T * Real.exp (2 * d * T * (Real.cosh a - 1)) + 1) ^ (p / 2)
      ≤ (2 * q) ^ (p / 2) * B ^ (p / 2) * κ ^ (p / 2) := by
        have h1 := Real.rpow_le_rpow hc0 hc hw2
        have h2 := (Real.rpow_le_rpow hKM0 hKM hw1).trans
          (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : (2 - p) / 2 ≤ p / 2))
        have h3 := Real.rpow_le_rpow hKI0 hKI hw2
        exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hKM0 _)
          (Real.rpow_nonneg (by linarith) _)) h3 (Real.rpow_nonneg hKI0 _)
          (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
    _ = (2 * q * B * κ) ^ (p / 2) := by
        rw [Real.mul_rpow (by nlinarith : (0 : ℝ) ≤ 2 * q * B) (by linarith : (0 : ℝ) ≤ κ),
          Real.mul_rpow (by linarith : (0 : ℝ) ≤ 2 * q) (by linarith : (0 : ℝ) ≤ B)]
    _ ≤ ((16 * (d + 1) * 3 ^ d * κ * C * q) ^ 2) ^ (p / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ hw2
        have h6 : D ^ p ≤ D ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 hp2
        rw [show D ^ (2 : ℝ) = D ^ 2 by norm_cast] at h6
        rw [hB]
        have hq0 : 0 ≤ q := by linarith
        have hE : 2 * q * (4 * 3 ^ d * q * D ^ 2) * κ ≤
            (16 * (d + 1) * 3 ^ d * κ * C * q) ^ 2 := by
          have e : (16 * (d + 1) * 3 ^ d * κ * C * q) ^ 2 =
              8 * 3 ^ d * κ * (8 * 3 ^ d * κ) * q ^ 2 * D ^ 2 := by
            rw [hD]
            ring
          rw [e]
          have h8 : 1 ≤ 8 * (3 : ℝ) ^ d * κ := by nlinarith
          have hqD : 0 ≤ q ^ 2 * D ^ 2 := by positivity
          have h83 : 0 ≤ 8 * (3 : ℝ) ^ d * κ := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h8 h83]
        calc 2 * q * (4 * 3 ^ d * q * D ^ p) * κ ≤ 2 * q * (4 * 3 ^ d * q * D ^ 2) * κ := by
              gcongr
          _ ≤ _ := hE
    _ = (16 * (d + 1) * 3 ^ d * κ * C * q) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Nat.cast_ofNat,
          show (2 : ℝ) * (p / 2) = p by ring]

/-- **The weighted Littlewood-Paley bound for signed data on `ℤ^d`**, with the constant `O(q)`. -/
theorem exists_steinSigned [NeZero d] : ∃ C : ℝ, 1 ≤ C ∧ ∀ p a T : ℝ, 1 < p → p ≤ 2 → 0 ≤ a →
    a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 → 0 ≤ T → ∀ (S : Finset (Vertex d))
    (g : Vertex d → ℝ), (∀ y ∉ S, g y = 0) →
      ∑' x, ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2)) ≤
        ENNReal.ofReal (2 * (C * (p / (p - 1))) ^ p * ∑ y ∈ S, coshW a y * |g y| ^ p) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_steinWeighted (d := d)
  have hKd : 1 ≤ 16 * ((d : ℝ) + 1) * 3 ^ d * kappaI d := by
    have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have hk := one_le_kappaI d
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (1 : ℝ) ≤ 16 * ((d : ℝ) + 1) := by linarith
    nlinarith [mul_le_mul this h3 zero_le_one (by linarith)]
  refine ⟨16 * (d + 1) * 3 ^ d * kappaI d * C₀, by nlinarith,
    fun p a T hp1 hp2 ha0 ha6 haT hT S g hgS => ?_⟩
  have hp0 : 0 < p := by linarith
  set gp : Vertex d → ℝ := fun y => max (g y) 0 with hgp
  set gm : Vertex d → ℝ := fun y => max (-g y) 0 with hgm
  have hgp0 : ∀ y, 0 ≤ gp y := fun y => le_max_right _ _
  have hgm0 : ∀ y, 0 ≤ gm y := fun y => le_max_right _ _
  have hgpS : ∀ y ∉ S, gp y = 0 := fun y hy => by simp [hgp, hgS y hy]
  have hgmS : ∀ y ∉ S, gm y = 0 := fun y hy => by simp [hgm, hgS y hy]
  have hsplit : ∀ s x, heatF S g s x = heatF S gp s x - heatF S gm s x := by
    intro s x
    unfold heatF
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← mul_sub]
    congr 1
    simp only [hgp, hgm]
    rcases le_total 0 (g y) with hy | hy
    · rw [max_eq_left hy, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hy, max_eq_left (by linarith)]; ring
  set K := (16 * (d + 1) * 3 ^ d * kappaI d * C₀ * (p / (p - 1))) ^ p with hK
  have hbound : ∀ f : Vertex d → ℝ, (∀ y, 0 ≤ f y) → (∀ y ∉ S, f y = 0) →
      ∑' x, ENNReal.ofReal (coshW a x * gam S f T x ^ (p / 2)) ≤
        ENNReal.ofReal (K * ∑ y ∈ S, coshW a y * f y ^ p) := by
    intro f hf hfS
    refine (h p a T hp1 hp2 ha0 ha6 haT hT S f hf hfS).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (steinConstant_le hC₀ hp1 hp2 ha0 ha6 hT haT)
      (Finset.sum_nonneg fun y _ => mul_nonneg (coshW_pos a y).le (Real.rpow_nonneg (hf y) _))
  have hgam : ∀ x, gam S g T x ^ (p / 2) ≤
      2 * (gam S gp T x ^ (p / 2) + gam S gm T x ^ (p / 2)) := by
    intro x
    have hle : gam S g T x ≤ 2 * gam S gp T x + 2 * gam S gm T x := by
      have hi : ∀ f : Vertex d → ℝ, IntervalIntegrable (fun s => ∑ i : Fin d,
          (heatF S f s (x + unit i) - heatF S f s x) ^ 2) volume 0 T := fun f =>
        (continuous_finsetSum _ fun i _ => ((continuous_heatF S f _).sub
          (continuous_heatF S f _)).pow 2).intervalIntegrable _ _
      unfold gam
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hi gp).const_mul 2) ((hi gm).const_mul 2)]
      refine intervalIntegral.integral_mono_on hT (hi g) (((hi gp).const_mul 2).add
        ((hi gm).const_mul 2)) fun s _ => ?_
      simp only [hsplit]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [sq_nonneg (heatF S gp s (x + unit i) - heatF S gp s x +
          (heatF S gm s (x + unit i) - heatF S gm s x))]
    have h0 := gam_nonneg (S := S) (f := g) hT x
    have hp0' := gam_nonneg (S := S) (f := gp) hT x
    have hm0 := gam_nonneg (S := S) (f := gm) hT x
    calc gam S g T x ^ (p / 2) ≤ (2 * gam S gp T x + 2 * gam S gm T x) ^ (p / 2) :=
          Real.rpow_le_rpow h0 hle (by linarith)
      _ = 2 ^ (p / 2) * (gam S gp T x + gam S gm T x) ^ (p / 2) := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]; ring_nf
      _ ≤ 2 * (gam S gp T x ^ (p / 2) + gam S gm T x ^ (p / 2)) := by
          refine mul_le_mul ?_ (Real.rpow_add_le_add_rpow hp0' hm0 (by linarith) (by linarith))
            (Real.rpow_nonneg (by positivity) _) (by norm_num)
          calc (2 : ℝ) ^ (p / 2) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hpm : ∀ y, gp y ^ p + gm y ^ p = |g y| ^ p := by
    intro y
    simp only [hgp, hgm]
    rcases le_total 0 (g y) with hy | hy
    · rw [max_eq_left hy, max_eq_right (by linarith), Real.zero_rpow hp0.ne', add_zero,
        abs_of_nonneg hy]
    · rw [max_eq_right hy, max_eq_left (by linarith), Real.zero_rpow hp0.ne', zero_add,
        abs_of_nonpos hy]
  have hgp1 := hbound gp hgp0 hgpS
  have hgm1 := hbound gm hgm0 hgmS
  have hK0 : 0 ≤ K := by positivity
  calc ∑' x, ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2))
      ≤ ∑' x, (2 * (ENNReal.ofReal (coshW a x * gam S gp T x ^ (p / 2)) +
          ENNReal.ofReal (coshW a x * gam S gm T x ^ (p / 2)))) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        have hω := coshW_pos a x
        rw [← ENNReal.ofReal_add (mul_nonneg hω.le (Real.rpow_nonneg (gam_nonneg hT x) _))
          (mul_nonneg hω.le (Real.rpow_nonneg (gam_nonneg hT x) _)),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left (hgam x) hω.le
        linarith
    _ = 2 * (∑' x, ENNReal.ofReal (coshW a x * gam S gp T x ^ (p / 2)) +
          ∑' x, ENNReal.ofReal (coshW a x * gam S gm T x ^ (p / 2))) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ 2 * (ENNReal.ofReal (K * ∑ y ∈ S, coshW a y * gp y ^ p) +
          ENNReal.ofReal (K * ∑ y ∈ S, coshW a y * gm y ^ p)) := by gcongr
    _ = ENNReal.ofReal (2 * K * ∑ y ∈ S, coshW a y * |g y| ^ p) := by
        have h1 : 0 ≤ ∑ y ∈ S, coshW a y * gp y ^ p := Finset.sum_nonneg fun y _ =>
          mul_nonneg (coshW_pos a y).le (Real.rpow_nonneg (hgp0 y) _)
        have h2 : 0 ≤ ∑ y ∈ S, coshW a y * gm y ^ p := Finset.sum_nonneg fun y _ =>
          mul_nonneg (coshW_pos a y).le (Real.rpow_nonneg (hgm0 y) _)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        rw [← mul_add, ← Finset.sum_add_distrib]
        simp only [← mul_add, hpm]
        ring

end Rigidity.Poincare.GeneralDim
