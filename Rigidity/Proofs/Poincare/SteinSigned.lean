import Rigidity.Proofs.Poincare.SteinFinal
import LatticeProb.Walk.LineKernelGauss

/-!
# The weighted Littlewood-Paley bound with the constant `O(q)`, for signed data

For `g` supported in a finite set `S`, `1 < p ≤ 2` with dual exponent `q = p/(p-1)`,
`0 ≤ a ≤ 1/6`, `a max(√T, 1) ≤ 1`:

  `Σ_x coshW(x) Γ_g(x)^{p/2} ≤ 2 (C q)^p Σ_x coshW |g|^p`,

`Γ_g(x) = ∫_0^T Σ_i (v_s(x + e_i) - v_s(x))² ds`, `v_s = heatF S g s` (`exists_steinSigned`):
`exists_steinWeighted` for `g⁺` and `g⁻`, with `λT ≤ 12/5` (from `cosh a - 1 ≤ (3/5) a²`,
Lattice-Probability) and `p/(p-1) = q`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

theorem exp_le_two_of_le {a : ℝ} (ha : a ≤ 1 / 6) : Real.exp a ≤ 2 := by
  have h := Real.log_two_gt_d9
  calc Real.exp a ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

theorem exp_three_le : Real.exp 3 ≤ 21 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [h3]
  nlinarith [mul_pos h0 h0]

/-- `λ T e^{λT} + 1 ≤ 52` for `λ = 4(cosh a - 1)`, `a² T ≤ 1`. -/
theorem kI_le {a T : ℝ} (ha0 : 0 ≤ a) (ha6 : a ≤ 1 / 6) (hT : 0 ≤ T)
    (haT : a * max (Real.sqrt T) 1 ≤ 1) :
    4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1 ≤ 52 := by
  have hc := LatticeProb.ContinuousTime.cosh_sub_one_le (l := a) (by
    rw [abs_of_nonneg ha0]; linarith)
  have hc0 : 0 ≤ Real.cosh a - 1 := by linarith [Real.one_le_cosh a]
  have haT' : a * Real.sqrt T ≤ 1 := le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) ha0) haT
  have ha2T : a ^ 2 * T ≤ 1 := by
    have h := mul_self_le_mul_self (mul_nonneg ha0 (Real.sqrt_nonneg T)) haT'
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hT, one_mul] at h
    nlinarith
  have hlam : 4 * (Real.cosh a - 1) * T ≤ 12 / 5 := by nlinarith
  have hlam0 : 0 ≤ 4 * (Real.cosh a - 1) * T := by positivity
  have he : Real.exp (4 * T * (Real.cosh a - 1)) ≤ 21 := by
    refine le_trans (Real.exp_le_exp.2 ?_) exp_three_le
    nlinarith
  nlinarith [Real.exp_pos (4 * T * (Real.cosh a - 1))]

/-- **The constant of `exists_steinWeighted` is at most `(636 C q)^p`**. -/
theorem steinConstant_le {C p a T : ℝ} (hC : 1 ≤ C) (hp1 : 1 < p) (hp2 : p ≤ 2) (ha0 : 0 ≤ a)
    (ha6 : a ≤ 1 / 6) (hT : 0 ≤ T) (haT : a * max (Real.sqrt T) 1 ≤ 1) :
    (2 / (p * (p - 1))) ^ (p / 2) *
      (3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1))) ^ ((2 - p) / 2) *
      (4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1) ^ (p / 2) ≤
    (636 * C * (p / (p - 1))) ^ p := by
  have hp0 : 0 < p := by linarith
  have hp10 : 0 < p - 1 := by linarith
  set q := p / (p - 1) with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hp10]; linarith
  have hw1 : 0 ≤ (2 - p) / 2 := by linarith
  have hw2 : 0 ≤ p / 2 := by linarith
  -- the three factors
  have hc : 2 / (p * (p - 1)) ≤ 2 * q := by
    rw [hq, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hc0 : 0 ≤ 2 / (p * (p - 1)) := by positivity
  set B := 108 * q * (6 * C) ^ p with hB
  have h6C : 1 ≤ 6 * C := by linarith
  have h6Cp : 1 ≤ (6 * C) ^ p := Real.one_le_rpow h6C hp0.le
  have hB1 : 1 ≤ B := by nlinarith
  have hKM : 3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1)) ≤ B := by
    have he := exp_le_two_of_le ha6
    have h1 : (3 * C * Real.exp a) ^ p ≤ (6 * C) ^ p :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [Real.exp_pos a]) hp0.le
    have h2 : (2 : ℝ) ^ (p - 1) ≤ 2 := by
      calc (2 : ℝ) ^ (p - 1) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h3 : 18 * 2 ^ (p - 1) * p / (p - 1) ≤ 36 * q := by
      rw [hq, mul_div_assoc, show 36 * (p / (p - 1)) = 18 * 2 * (p / (p - 1)) by ring]
      have : 0 ≤ p / (p - 1) := by positivity
      nlinarith
    have h4 : 0 ≤ 18 * 2 ^ (p - 1) * p / (p - 1) := by positivity
    calc 3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1))
        ≤ 3 * (6 * C) ^ p * (36 * q) := by gcongr
      _ = B := by rw [hB]; ring
  have hKM0 : 0 ≤ 3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1)) := by
    positivity
  have hKI := kI_le ha0 ha6 hT haT
  have hKI0 : 0 ≤ 4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1 := by
    have : 0 ≤ Real.cosh a - 1 := by linarith [Real.one_le_cosh a]
    positivity
  calc (2 / (p * (p - 1))) ^ (p / 2) *
        (3 * (3 * C * Real.exp a) ^ p * (18 * 2 ^ (p - 1) * p / (p - 1))) ^ ((2 - p) / 2) *
        (4 * (Real.cosh a - 1) * T * Real.exp (4 * T * (Real.cosh a - 1)) + 1) ^ (p / 2)
      ≤ (2 * q) ^ (p / 2) * B ^ (p / 2) * 52 ^ (p / 2) := by
        have h1 := Real.rpow_le_rpow hc0 hc hw2
        have h2 := (Real.rpow_le_rpow hKM0 hKM hw1).trans
          (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : (2 - p) / 2 ≤ p / 2))
        have h3 := Real.rpow_le_rpow hKI0 hKI hw2
        exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hKM0 _)
          (Real.rpow_nonneg (by linarith) _)) h3 (Real.rpow_nonneg hKI0 _)
          (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
    _ = (2 * q * B * 52) ^ (p / 2) := by
        rw [Real.mul_rpow (by nlinarith : (0 : ℝ) ≤ 2 * q * B) (by norm_num : (0 : ℝ) ≤ 52),
          Real.mul_rpow (by linarith : (0 : ℝ) ≤ 2 * q) (by linarith : (0 : ℝ) ≤ B)]
    _ ≤ ((636 * C * q) ^ 2) ^ (p / 2) := by
        refine Real.rpow_le_rpow (by positivity) ?_ hw2
        have h6 : (6 * C) ^ p ≤ (6 * C) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h6C hp2
        rw [show (6 * C) ^ (2 : ℝ) = (6 * C) ^ 2 by norm_cast] at h6
        rw [hB]
        have hq0 : 0 ≤ q := by linarith
        nlinarith [mul_nonneg hq0 hq0]
    _ = (636 * C * q) ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Nat.cast_ofNat,
          show (2 : ℝ) * (p / 2) = p by ring]

/-- **The weighted Littlewood-Paley bound for signed data**, with the constant `O(q)`. -/
theorem exists_steinSigned : ∃ C : ℝ, 1 ≤ C ∧ ∀ p a T : ℝ, 1 < p → p ≤ 2 → 0 ≤ a →
    a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 → 0 ≤ T → ∀ (S : Finset (Vertex 2))
    (g : Vertex 2 → ℝ), (∀ y ∉ S, g y = 0) →
      ∑' x, ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2)) ≤
        ENNReal.ofReal (2 * (C * (p / (p - 1))) ^ p * ∑ y ∈ S, coshW a y * |g y| ^ p) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_steinWeighted
  refine ⟨636 * C₀, by linarith, fun p a T hp1 hp2 ha0 ha6 haT hT S g hgS => ?_⟩
  have hp0 : 0 < p := by linarith
  set gp : Vertex 2 → ℝ := fun y => max (g y) 0 with hgp
  set gm : Vertex 2 → ℝ := fun y => max (-g y) 0 with hgm
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
  set K := (636 * C₀ * (p / (p - 1))) ^ p with hK
  have hbound : ∀ f : Vertex 2 → ℝ, (∀ y, 0 ≤ f y) → (∀ y ∉ S, f y = 0) →
      ∑' x, ENNReal.ofReal (coshW a x * gam S f T x ^ (p / 2)) ≤
        ENNReal.ofReal (K * ∑ y ∈ S, coshW a y * f y ^ p) := by
    intro f hf hfS
    refine (h p a T hp1 hp2 ha0 ha6 haT hT S f hf hfS).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (steinConstant_le hC₀ hp1 hp2 ha0 ha6 hT haT)
      (Finset.sum_nonneg fun y _ => mul_nonneg (coshW_pos a y).le (Real.rpow_nonneg (hf y) _))
  -- pointwise comparison of the square functions
  have hgam : ∀ x, gam S g T x ^ (p / 2) ≤
      2 * (gam S gp T x ^ (p / 2) + gam S gm T x ^ (p / 2)) := by
    intro x
    have hle : gam S g T x ≤ 2 * gam S gp T x + 2 * gam S gm T x := by
      have hi : ∀ f : Vertex 2 → ℝ, IntervalIntegrable (fun s => ∑ i : Fin 2,
          (heatF S f s (x + unit i) - heatF S f s x) ^ 2) volume 0 T := fun f =>
        (continuous_finsetSum _ fun i _ => ((continuous_heatF S f _).sub
          (continuous_heatF S f _)).pow 2).intervalIntegrable _ _
      unfold gam
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add ((hi gp).const_mul 2) ((hi gm).const_mul 2)]
      refine intervalIntegral.integral_mono_on hT (hi g) (((hi gp).const_mul 2).add
        ((hi gm).const_mul 2)) fun s _ => ?_
      simp only [hsplit, Fin.sum_univ_two]
      nlinarith [sq_nonneg (heatF S gp s (x + unit 0) - heatF S gp s x +
          (heatF S gm s (x + unit 0) - heatF S gm s x)),
        sq_nonneg (heatF S gp s (x + unit 1) - heatF S gp s x +
          (heatF S gm s (x + unit 1) - heatF S gm s x))]
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

end Rigidity.Poincare
