import Rigidity.Proofs.BarlowLattice.GaussianBound
import Rigidity.Proofs.Green.BondGaussianInputs
import Rigidity.Proofs.Green.BondCarneVaropoulos
import Rigidity.Proofs.WeakPoincare.VeryGood
import Rigidity.Proofs.Barlow.GaussianHolds

/-!
# Barlow's Gaussian upper bound on the infinite cluster of `ℤ^d`

`barlowGaussianUpperBound_holds (hd : 2 ≤ d) : BarlowGaussianUpperBound d`: Theorem 4 of Dario–Gu
(Barlow, *Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004), Theorem 1,
upper bound, with the tail (0.5)) in every dimension `d ≥ 2`, with the prefactor `t^{-d/2}`. It
follows (`barlowGaussianUpperBound_of_veryGood`) from the very good balls of the cluster
(`ClusterVeryGoodBalls d`, Barlow's Theorem 2.18 and Lemma 2.19 for Euclidean balls, proved in
`Rigidity.WeakPoincare.clusterVeryGoodBalls_holds`) and the Carne–Varopoulos bound
(`Rigidity.Green.carneVaropoulos_holds`, the source's Lemma 1.1).

The proof is that of the source's Proposition 6.1 and Theorem 1: for `t ≥ T(y)` the ball
`B(y, 36t)` satisfies the hypotheses of Section 3 (`BarlowRegion`) with `N = (36t)^{1/K}`,
`K = 4d + 12`, so Theorem 3.8 (`BarlowRegion.bondHeat_le_gauss`) bounds `p_t(x, y)` for
`|x - y| ≤ t`; for `|x - y| > t` the Carne–Varopoulos bound gives the second regime of `Φ_C`. The
times of Section 3 are polynomial in `N`: `T_G ≤ c_T N^{4(d+2)}`, which fixes `K`. In dimension
two the result recovers `BarlowGaussianUpperBoundTwo` (`barlowGaussianUpperBoundTwo_of_lattice`).
-/

open scoped Classical
open MeasureTheory Finset LatticeProb.Percolation Rigidity.Green Rigidity.WeakPoincare
open Rigidity.External Rigidity.Proofs.S2

namespace Rigidity.BarlowLattice

variable {d : ℕ}

variable [NeZero d]

/-! ### Polynomial bounds on the times of Section 3 -/

/-- The constant `b` with `T_M ≤ b N^{2(d+2)}`. -/
noncomputable def barlowB (d : ℕ) (CV CP L : ℝ) : ℝ :=
  (1 + 4 * (CP * L ^ d * CV)) ^ 2 + (2 * heatConst d CV CP L) ^ 2

/-- The constant `c_N` with `n_* ≤ c_N N^{2(d+2)}`. -/
noncomputable def barlowCN (d : ℕ) (CV CP L : ℝ) : ℝ := 2 * d * barlowB d CV CP L + 1

/-- The constant `c_T` with `T_G ≤ c_T N^{4(d+2)}`. -/
noncomputable def barlowCT (d : ℕ) (CV CP L Ccv : ℝ) : ℝ :=
  8 * (CP * L ^ d * CV) + 2 + (32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowCN d CV CP L) ^ 2

omit [NeZero d] in
theorem barlowTM_le {CV CP L N : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N) :
    barlowTM d CV CP L N ≤ barlowB d CV CP L * N ^ (2 * (d + 2)) := by
  have hN0 : 0 ≤ N := by linarith
  have hNd : 1 ≤ N ^ (d + 2) := one_le_pow₀ hN
  have hN2 : 1 ≤ N ^ (2 * (d + 2)) := one_le_pow₀ hN
  have hL0 : 0 < L := by linarith
  have ha : 0 ≤ CP * L ^ d * CV := by positivity
  have hT1 : barlowT1 d CV CP L N ≤ (1 + 4 * (CP * L ^ d * CV)) * N ^ (d + 2) := by
    unfold barlowT1 barlowT0
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  have hT1sq : barlowT1 d CV CP L N ^ 2 ≤
      (1 + 4 * (CP * L ^ d * CV)) ^ 2 * N ^ (2 * (d + 2)) := by
    have h0 : 0 ≤ barlowT1 d CV CP L N := zero_le_one.trans (one_le_barlowT1 d CV CP L N)
    calc barlowT1 d CV CP L N ^ 2 ≤ ((1 + 4 * (CP * L ^ d * CV)) * N ^ (d + 2)) ^ 2 :=
          pow_le_pow_left₀ h0 hT1 2
      _ = (1 + 4 * (CP * L ^ d * CV)) ^ 2 * N ^ (2 * (d + 2)) := by ring
  have hH : 0 ≤ (2 * heatConst d CV CP L) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (1 + 4 * (CP * L ^ d * CV)) ^ 2 := sq_nonneg _
  unfold barlowTM barlowB
  refine max_le ?_ ?_
  · nlinarith [mul_nonneg hH (by linarith : (0 : ℝ) ≤ N ^ (2 * (d + 2)) - 1)]
  · nlinarith [mul_nonneg hA (by linarith : (0 : ℝ) ≤ N ^ (2 * (d + 2)) - 1)]

omit [NeZero d] in
theorem barlowNstar_le {CV CP L N : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N) :
    (barlowNstar d CV CP L N : ℝ) ≤ barlowCN d CV CP L * N ^ (2 * (d + 2)) := by
  have hN2 : 1 ≤ N ^ (2 * (d + 2)) := one_le_pow₀ hN
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hTM := one_le_barlowTM d CV CP L N
  have h1 : (barlowNstar d CV CP L N : ℝ) < 2 * d * barlowTM d CV CP L N + 1 := by
    unfold barlowNstar
    exact Nat.ceil_lt_add_one (mul_nonneg (by positivity) (by linarith))
  have h2 := barlowTM_le (d := d) hCV hCP hL hN
  have h3 : 2 * d * barlowTM d CV CP L N ≤ 2 * d * (barlowB d CV CP L * N ^ (2 * (d + 2))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  unfold barlowCN
  nlinarith

omit [NeZero d] in
theorem barlowTG_le {CV CP L N Ccv : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N)
    (hCcv : 0 < Ccv) : barlowTG d CV CP L N Ccv ≤ barlowCT d CV CP L Ccv * N ^ (4 * (d + 2)) := by
  have hN0 : 0 ≤ N := by linarith
  have hN4 : 1 ≤ N ^ (4 * (d + 2)) := one_le_pow₀ hN
  have hNd4 : N ^ (d + 2) ≤ N ^ (4 * (d + 2)) := pow_le_pow_right₀ hN (by omega)
  have hL0 : 0 < L := by linarith
  have ha : 0 ≤ CP * L ^ d * CV := by positivity
  have hκ1 := one_le_barlowKappa d CV CP L
  have hB0 := barlowB0_pos d CV CP L
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hns := barlowNstar_le (d := d) hCV hCP hL hN
  have hCN : 0 ≤ barlowCN d CV CP L := by
    unfold barlowCN barlowB
    positivity
  have hr1sq : barlowR1 d CV CP L N ^ 2 =
      16 * barlowB0 d CV CP L ^ 2 * barlowNstar d CV CP L N := by
    unfold barlowR1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hq : 2 * d * Ccv * barlowR1 d CV CP L N ^ 2 / barlowKappa d CV CP L ^ 2 ≤
      32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowCN d CV CP L * N ^ (2 * (d + 2)) := by
    rw [div_le_iff₀ (by positivity), hr1sq]
    have hκ2 : 1 ≤ barlowKappa d CV CP L ^ 2 := one_le_pow₀ hκ1
    have hpos : 0 ≤ 32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowCN d CV CP L *
        N ^ (2 * (d + 2)) := by positivity
    have s2 : 32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowNstar d CV CP L N ≤
        32 * d * Ccv * barlowB0 d CV CP L ^ 2 * (barlowCN d CV CP L * N ^ (2 * (d + 2))) :=
      mul_le_mul_of_nonneg_left hns (by positivity)
    have s3 := le_mul_of_one_le_right hpos hκ2
    linarith
  have hq0 : 0 ≤ 2 * d * Ccv * barlowR1 d CV CP L N ^ 2 / barlowKappa d CV CP L ^ 2 := by
    positivity
  have hqsq : (2 * d * Ccv * barlowR1 d CV CP L N ^ 2 / barlowKappa d CV CP L ^ 2) ^ 2 ≤
      (32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowCN d CV CP L) ^ 2 * N ^ (4 * (d + 2)) := by
    calc _ ≤ (32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowCN d CV CP L *
            N ^ (2 * (d + 2))) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = _ := by ring
  have hA : 8 * (CP * L ^ d * CV * N ^ (d + 2)) ≤ 8 * (CP * L ^ d * CV) * N ^ (4 * (d + 2)) := by
    have := mul_le_mul_of_nonneg_left hNd4 (by positivity : (0 : ℝ) ≤ 8 * (CP * L ^ d * CV))
    linarith
  have hC : 0 ≤ 8 * (CP * L ^ d * CV) * N ^ (4 * (d + 2)) := by positivity
  have hD : 0 ≤ (32 * d * Ccv * barlowB0 d CV CP L ^ 2 * barlowCN d CV CP L) ^ 2 *
      N ^ (4 * (d + 2)) := by positivity
  unfold barlowTG barlowCT barlowT0
  refine max_le (max_le ?_ ?_) ?_
  · nlinarith
  · nlinarith
  · nlinarith

/-! ### The far estimate from the Carne–Varopoulos bound -/

omit [NeZero d] in
/-- The Carne–Varopoulos bound makes `p_s(x, y) ≤ C e^{-R/(324C)}` at distance `R/18` up to time
`R` (the role of the source's Lemma 1.1(b)). -/
theorem far_of_carneVaropoulos {Ccv : ℝ} (hCcv : 0 < Ccv)
    (hCV : ∀ (ω : Configuration d) (K : OpenComponent ω), K.supp.Infinite →
      ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t →
        (latticeDist x y ≤ t →
          bondHeat ω t x y ≤ Ccv * Real.exp (-(latticeDist x y ^ 2 / (Ccv * t)))) ∧
        (t ≤ latticeDist x y →
          bondHeat ω t x y ≤
            Ccv * Real.exp (-(latticeDist x y / Ccv * (1 + Real.log (latticeDist x y / t))))))
    {ω : Configuration d} {K : OpenComponent ω} (hK : K.supp.Infinite) {R : ℝ} (hR : 0 < R) :
    ∀ x ∈ K.supp, ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x →
      bondHeat ω s x y ≤ Ccv * Real.exp (-(R / (324 * Ccv))) := by
  intro x hx s hs0 hsR y hy
  have hpos : 0 < Ccv * Real.exp (-(R / (324 * Ccv))) := by positivity
  have hd : R / 18 ≤ latticeDist x y := by rw [latticeDist_comm]; exact hy
  rcases hs0.eq_or_lt with rfl | hs
  · rw [bondHeat_zero, if_neg]
    · exact hpos.le
    · intro hxy
      rw [hxy, latticeDist_self] at hd
      linarith
  · by_cases hyK : y ∈ K.supp
    · obtain ⟨h1, h2⟩ := hCV ω K hK x hx y hyK s hs
      by_cases hds : latticeDist x y ≤ s
      · refine (h1 hds).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCcv.le)
        apply neg_le_neg
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hd2 : (R / 18) ^ 2 ≤ latticeDist x y ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
        have e1 : Ccv * R ^ 2 ≤ 324 * Ccv * latticeDist x y ^ 2 := by
          have := mul_le_mul_of_nonneg_left hd2 (by positivity : (0 : ℝ) ≤ 324 * Ccv)
          have e : 324 * Ccv * (R / 18) ^ 2 = Ccv * R ^ 2 := by ring
          linarith
        have e2 : Ccv * R * s ≤ Ccv * R * R :=
          mul_le_mul_of_nonneg_left hsR (by positivity)
        have e3 : R * (Ccv * s) = Ccv * R * s := by ring
        have e4 : Ccv * R * R = Ccv * R ^ 2 := by ring
        have e5 : latticeDist x y ^ 2 * (324 * Ccv) = 324 * Ccv * latticeDist x y ^ 2 := by ring
        linarith
      · have hsd : s ≤ latticeDist x y := le_of_lt (lt_of_not_ge hds)
        refine (h2 hsd).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCcv.le)
        apply neg_le_neg
        have hlog : 0 ≤ Real.log (latticeDist x y / s) :=
          Real.log_nonneg ((one_le_div hs).2 hsd)
        have h3 : R / (324 * Ccv) ≤ latticeDist x y / Ccv := by
          rw [div_le_div_iff₀ (mul_pos (by norm_num) hCcv) hCcv]
          nlinarith
        have h4 : latticeDist x y / Ccv ≤
            latticeDist x y / Ccv * (1 + Real.log (latticeDist x y / s)) := by
          have : 0 ≤ latticeDist x y / Ccv := div_nonneg (latticeDist_nonneg x y) hCcv.le
          nlinarith
        linarith
    · rw [bondHeat_eq_zero_of_mem_of_notMem hx hyK]
      exact hpos.le

/-! ### The comparison with `Φ_C` -/

/-- `e^{-x} ≤ n!/xⁿ` for `x > 0`. -/
theorem exp_neg_le_factorial_div_pow (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ n.factorial / x ^ n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [Real.exp_neg, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (Real.exp_pos x)]
  rw [div_le_iff₀ hf] at h
  linarith

omit [NeZero d] in
theorem le_dgPhiDim_of_gauss {q CG cG Cg t r : ℝ} (hCG : CG ≤ Cg) (hcG : 1 / Cg ≤ cG)
    (hCg : 0 < Cg) (ht : 0 < t) (hr : r ≤ t)
    (hq : q ≤ CG / Real.sqrt t ^ d * Real.exp (-(cG * r ^ 2 / t))) : q ≤ dgPhiDim d Cg t r := by
  rw [dgPhiDim, dgExponent, if_pos hr]
  have he : Real.exp (-(cG * r ^ 2 / t)) ≤ Real.exp (-(r ^ 2 / (Cg * t))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have e : r ^ 2 / (Cg * t) = 1 / Cg * r ^ 2 / t := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcG (sq_nonneg _)) ht.le
  have hst : 0 < Real.sqrt t ^ d := by positivity
  calc q ≤ CG / Real.sqrt t ^ d * Real.exp (-(cG * r ^ 2 / t)) := hq
    _ ≤ Cg / Real.sqrt t ^ d * Real.exp (-(r ^ 2 / (Cg * t))) := by gcongr
    _ = Cg * (Real.sqrt t ^ d)⁻¹ * Real.exp (-(r ^ 2 / (Cg * t))) := by rw [div_eq_mul_inv]

omit [NeZero d] in
theorem le_dgPhiDim_of_far {q Ccv Cg t r : ℝ} (hCcv : 0 < Ccv)
    (h2 : Ccv * (d.factorial * (2 * Ccv) ^ d) ≤ Cg) (h3 : 2 * Ccv ≤ Cg) (ht1 : 1 ≤ t)
    (htr : t < r) (hq : q ≤ Ccv * Real.exp (-(r / Ccv * (1 + Real.log (r / t))))) :
    q ≤ dgPhiDim d Cg t r := by
  have ht : 0 < t := by linarith
  have hr : ¬ r ≤ t := not_le.2 htr
  rw [dgPhiDim, dgExponent, if_neg hr]
  set Λ := Real.log (r / t) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hr0 : 0 < r := by linarith
  have hst : 0 < Real.sqrt t ^ d := by positivity
  have hsplit : Real.exp (-(r / Ccv * (1 + Λ))) =
      Real.exp (-(r / (2 * Ccv) * (1 + Λ))) * Real.exp (-(r / (2 * Ccv) * (1 + Λ))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hA : Real.exp (-(r / (2 * Ccv) * (1 + Λ))) ≤
      d.factorial * (2 * Ccv) ^ d / Real.sqrt t ^ d := by
    have h4 : Real.exp (-(r / (2 * Ccv) * (1 + Λ))) ≤ Real.exp (-(t / (2 * Ccv))) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have h5 : t / (2 * Ccv) ≤ r / (2 * Ccv) := div_le_div_of_nonneg_right htr.le (by positivity)
      have h6 : 0 ≤ r / (2 * Ccv) := by positivity
      nlinarith
    refine h4.trans ((exp_neg_le_factorial_div_pow d (by positivity)).trans ?_)
    rw [div_pow, div_div_eq_mul_div]
    refine div_le_div_of_nonneg_left (by positivity) hst ?_
    refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ d
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hB : Real.exp (-(r / (2 * Ccv) * (1 + Λ))) ≤ Real.exp (-(r / Cg * (1 + Λ))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have h5 : r / Cg ≤ r / (2 * Ccv) := div_le_div_of_nonneg_left hr0.le (by positivity) h3
    nlinarith
  calc q ≤ Ccv * Real.exp (-(r / Ccv * (1 + Λ))) := hq
    _ = Ccv * Real.exp (-(r / (2 * Ccv) * (1 + Λ))) * Real.exp (-(r / (2 * Ccv) * (1 + Λ))) := by
        rw [hsplit]; ring
    _ ≤ Ccv * (d.factorial * (2 * Ccv) ^ d / Real.sqrt t ^ d) *
          Real.exp (-(r / Cg * (1 + Λ))) := by gcongr
    _ = Ccv * (d.factorial * (2 * Ccv) ^ d) * (Real.sqrt t ^ d)⁻¹ *
          Real.exp (-(r / Cg * (1 + Λ))) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ Cg * (Real.sqrt t ^ d)⁻¹ * Real.exp (-(r / Cg * (1 + Λ))) := by gcongr

/-! ### The numerical conditions on the radius -/

/-- The exponent `K = 4d + 12` of the radius `R = N^K`. -/
def barlowK (d : ℕ) : ℕ := 4 * d + 12

/-- The threshold `(4 C d! (324 C)^d)²` of the bound `4 ε R^{d/2} ≤ 1`. -/
noncomputable def barlowEps (d : ℕ) (Ccv : ℝ) : ℝ := (4 * Ccv * (d.factorial * (324 * Ccv) ^ d)) ^ 2

/-- The threshold `u₀` on `N = R^{1/K}`. -/
noncomputable def barlowU0 (d : ℕ) (CV CP L Ccv : ℝ) : ℝ :=
  max (max 18 (36 * barlowCT d CV CP L Ccv + 1))
    (max (barlowCN d CV CP L + 1) (max (324 * Ccv ^ 2 * CV ^ 2 + 1) (barlowEps d Ccv + 1)))

theorem barlowU0_ge (d : ℕ) (CV CP L Ccv : ℝ) :
    18 ≤ barlowU0 d CV CP L Ccv ∧ 36 * barlowCT d CV CP L Ccv + 1 ≤ barlowU0 d CV CP L Ccv ∧
      barlowCN d CV CP L + 1 ≤ barlowU0 d CV CP L Ccv ∧
      324 * Ccv ^ 2 * CV ^ 2 + 1 ≤ barlowU0 d CV CP L Ccv ∧
      barlowEps d Ccv + 1 ≤ barlowU0 d CV CP L Ccv := by
  unfold barlowU0
  refine ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- For `u ≥ u₀` and `R = u^K`, the numerical hypotheses of Section 3 hold with `N = u` and
`ε = C e^{-R/(324C)}`. -/
theorem barlow_numeric {CV CP L Ccv u : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L)
    (hCcv : 0 < Ccv) (hu : barlowU0 d CV CP L Ccv ≤ u) :
    9 ≤ u ^ barlowK d ∧ u ≤ u ^ barlowK d / 18 ∧
      Ccv * Real.exp (-(u ^ barlowK d / (324 * Ccv))) * u ^ d * CV ^ 2 ≤ 5 ^ d ∧
      4 * (Ccv * Real.exp (-(u ^ barlowK d / (324 * Ccv)))) * Real.sqrt (u ^ barlowK d) ^ d ≤ 1 ∧
      (barlowNstar d CV CP L u : ℝ) ≤ d * u ^ barlowK d ∧
      barlowTG d CV CP L u Ccv ≤ u ^ barlowK d / 36 := by
  obtain ⟨h18, hT, hN, he1, he2⟩ := barlowU0_ge d CV CP L Ccv
  have hu18 : 18 ≤ u := h18.trans hu
  have hu1 : 1 ≤ u := by linarith
  have hpow : ∀ n : ℕ, 1 ≤ n → u ≤ u ^ n := fun n hn => le_self_pow₀ hu1 (by omega)
  have hd1 : (1 : ℝ) ≤ d := one_le_dim_real
  have hK1 : 1 ≤ barlowK d := by unfold barlowK; omega
  set R := u ^ barlowK d with hR
  have hR0 : 0 < R := by positivity
  have huR : u ≤ R := hpow _ hK1
  have hx0 : 0 < R / (324 * Ccv) := by positivity
  have hsplit : ∀ m : ℕ, m ≤ barlowK d → R = u ^ (barlowK d - m) * u ^ m := fun m hm => by
    rw [hR, ← pow_add, Nat.sub_add_cancel hm]
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · have e := hsplit 1 hK1
    have h1 : u ≤ u ^ (barlowK d - 1) := hpow _ (by unfold barlowK; omega)
    rw [pow_one] at e
    rw [e, le_div_iff₀ (by norm_num)]
    nlinarith
  · have hex := Barlow.exp_neg_le_one_div hx0
    have h1 : Ccv * Real.exp (-(R / (324 * Ccv))) ≤ Ccv * (324 * Ccv / R) := by
      refine mul_le_mul_of_nonneg_left (hex.trans (le_of_eq ?_)) hCcv.le
      rw [one_div_div]
    have e := hsplit d (by unfold barlowK; omega)
    have h7 : 324 * Ccv ^ 2 * CV ^ 2 ≤ u ^ (barlowK d - d) := by
      have := hpow (barlowK d - d) (by unfold barlowK; omega)
      linarith
    have hud : 0 ≤ u ^ d := by positivity
    have hR' : 324 * Ccv ^ 2 * CV ^ 2 * u ^ d ≤ R := by
      rw [e]
      exact mul_le_mul_of_nonneg_right h7 hud
    have h5 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    calc Ccv * Real.exp (-(R / (324 * Ccv))) * u ^ d * CV ^ 2
        ≤ Ccv * (324 * Ccv / R) * u ^ d * CV ^ 2 := by gcongr
      _ = 324 * Ccv ^ 2 * CV ^ 2 * u ^ d / R := by ring
      _ ≤ 1 := by rw [div_le_iff₀ hR0]; linarith
      _ ≤ 5 ^ d := h5
  · have hex := exp_neg_le_factorial_div_pow d hx0
    set E := 4 * Ccv * (d.factorial * (324 * Ccv) ^ d) with hE
    have hE0 : 0 ≤ E := by positivity
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
    have hsRd : 0 < Real.sqrt R ^ d := by positivity
    have hRd : R ^ d = Real.sqrt R ^ d * Real.sqrt R ^ d := by
      rw [← mul_pow, Real.mul_self_sqrt hR0.le]
    have hER : E ≤ Real.sqrt R ^ d := by
      have h1 : E ^ 2 ≤ R := by
        have : barlowEps d Ccv = E ^ 2 := rfl
        linarith
      have h2 : E ≤ Real.sqrt R := by
        rw [← Real.sqrt_sq hE0]
        exact Real.sqrt_le_sqrt h1
      have h3 : 1 ≤ Real.sqrt R := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith)
      exact h2.trans (le_self_pow₀ h3 (NeZero.ne d))
    have h1 : 4 * (Ccv * Real.exp (-(R / (324 * Ccv)))) * Real.sqrt R ^ d ≤
        4 * (Ccv * (d.factorial / (R / (324 * Ccv)) ^ d)) * Real.sqrt R ^ d := by gcongr
    have h2 : 4 * (Ccv * (d.factorial / (R / (324 * Ccv)) ^ d)) * Real.sqrt R ^ d =
        E / Real.sqrt R ^ d := by
      rw [hE, div_pow, hRd]
      field_simp
    rw [h2] at h1
    have h3 : E / Real.sqrt R ^ d ≤ 1 := by
      rw [div_le_one hsRd]
      exact hER
    linarith
  · have h1 := barlowNstar_le (d := d) hCV hCP hL hu1
    have e := hsplit (2 * (d + 2)) (by unfold barlowK; omega)
    have h9 : barlowCN d CV CP L ≤ u ^ (barlowK d - 2 * (d + 2)) := by
      have := hpow (barlowK d - 2 * (d + 2)) (by unfold barlowK; omega)
      linarith
    have h8 : 0 ≤ u ^ (2 * (d + 2)) := by positivity
    have h10 : barlowCN d CV CP L * u ^ (2 * (d + 2)) ≤ R := by
      rw [e]
      exact mul_le_mul_of_nonneg_right h9 h8
    have h11 : R ≤ d * R := le_mul_of_one_le_left hR0.le hd1
    linarith
  · have h1 := barlowTG_le (d := d) hCV hCP hL hu1 hCcv
    have e := hsplit (4 * (d + 2)) (by unfold barlowK; omega)
    have h9 : 36 * barlowCT d CV CP L Ccv ≤ u ^ (barlowK d - 4 * (d + 2)) := by
      have := hpow (barlowK d - 4 * (d + 2)) (by unfold barlowK; omega)
      linarith
    have h16 : 0 ≤ u ^ (4 * (d + 2)) := by positivity
    have : barlowCT d CV CP L Ccv * u ^ (4 * (d + 2)) ≤ R / 36 := by
      rw [le_div_iff₀ (by norm_num), e]
      nlinarith [mul_le_mul_of_nonneg_right h9 h16]
    linarith

/-! ### The Gaussian upper bound -/

/-- **Barlow 2004, Theorem 1** (upper bound with the tail (0.5)) in the form of Dario–Gu,
Theorem 4, in dimension `d`, from the very good balls of the cluster. -/
theorem barlowGaussianUpperBound_of_veryGood (hVG : ClusterVeryGoodBalls d) :
    BarlowGaussianUpperBound d := by
  intro p hpc hp1
  obtain ⟨C0, L, hC0, hL, hvg⟩ := hVG p hpc hp1
  obtain ⟨s, Cs, hs, hCs, hVGp⟩ :=
    hvg (1 / (barlowK d : ℝ)) 1 (by unfold barlowK; positivity) le_rfl
  set CV := C0⁻¹ with hCVdef
  have hCV : 0 < CV := inv_pos.2 hC0
  obtain ⟨Ccv, hCcv, hCVb⟩ := carneVaropoulos_holds (d := d)
  set u0 := barlowU0 d CV C0 L Ccv with hu0
  have hu018 : 18 ≤ u0 := (barlowU0_ge d CV C0 L Ccv).1
  set k0 : ℝ := u0 ^ barlowK d / 36 with hk0
  have hk0pos : 0 < k0 := by positivity
  have hk01 : 1 ≤ k0 := by
    rw [hk0, le_div_iff₀ (by norm_num)]
    have h2 : u0 ^ 2 ≤ u0 ^ barlowK d :=
      pow_le_pow_right₀ (by linarith) (by unfold barlowK; omega)
    nlinarith
  set cG := barlowcG d CV C0 L Ccv with hcG
  set CG := barlowCG d CV C0 L Ccv with hCG
  have hcG0 : 0 < cG := barlowcG_pos d CV C0 L hCcv
  set Cg := max (max CG (1 / cG)) (max (Ccv * (d.factorial * (2 * Ccv) ^ d)) (2 * Ccv)) with hCg
  have hCg1 : CG ≤ Cg := (le_max_left _ _).trans (le_max_left _ _)
  have hCg2 : 1 / cG ≤ Cg := (le_max_right _ _).trans (le_max_left _ _)
  have hCg3 : Ccv * (d.factorial * (2 * Ccv) ^ d) ≤ Cg :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCg4 : 2 * Ccv ≤ Cg := (le_max_right _ _).trans (le_max_right _ _)
  have hCgpos : 0 < Cg := lt_of_lt_of_le (by positivity) hCg4
  have hinv : 1 / Cg ≤ cG := by
    rw [div_le_iff₀ hCgpos]
    rw [div_le_iff₀ hcG0] at hCg2
    linarith
  set θT := max (1 / 36 * Cs) (k0 * 3 ^ (1 / s)) * 4 ^ (1 / s) with hθT
  refine ⟨s, max Cg θT, hs, lt_of_lt_of_le hCgpos (le_max_left _ _), fun y => ?_⟩
  obtain ⟨S, hSm, hS0, hSos, hSae⟩ := hVGp y
  have hTm : Measurable fun ω => max (1 / 36 * S ω) k0 :=
    (measurable_const.mul hSm).max measurable_const
  refine ⟨fun ω => max (1 / 36 * S ω) k0, hTm, fun ω => le_max_of_le_right hk0pos.le, ?_, ?_⟩
  · have h1 := IsOsBond.const_mul (c := 1 / 36) (by norm_num) hSos
    have h2 := isOsBond_const (d := d) (p := p) (κ := k0) hk0pos hs
    have h3 := IsOsBond.max hs (by positivity) (by positivity) (measurable_const.mul hSm)
      measurable_const h1 h2
    exact IsOsBond.mono_scale hs (by positivity) (le_max_right _ _) hTm h3
  · filter_upwards [hSae] with ω hω
    intro h hy t ht hTt x hx
    have hKinf := uniqueInfiniteComponent_infinite h
    have hk0t : k0 ≤ t := (le_max_right _ _).trans hTt
    have ht1 : 1 ≤ t := hk01.trans hk0t
    refine le_trans ?_
      (dgPhiDim_mono d (C := Cg) hCgpos (le_max_left _ _) ht (latticeDist_nonneg x y))
    obtain ⟨hcv1, hcv2⟩ := hCVb ω (uniqueInfiniteComponent h) hKinf x hx y hy t ht
    by_cases hd : latticeDist x y ≤ t
    · set R := 36 * t with hR
      have hR0 : 0 < R := by positivity
      have hK0 : (0 : ℝ) < barlowK d := by unfold barlowK; positivity
      set u := R ^ ((1 : ℝ) / barlowK d) with hu
      have hu0' : 0 ≤ u := by positivity
      have hRu : R = u ^ barlowK d := by
        rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
        have e : (1 : ℝ) / barlowK d * barlowK d = 1 := by field_simp
        rw [e, Real.rpow_one]
      have hSR : S ω ≤ R := by
        have := (le_max_left _ _).trans hTt
        rw [hR]
        linarith
      have huu0 : u0 ≤ u := by
        have h1 : u0 ^ barlowK d ≤ u ^ barlowK d := by
          rw [← hRu, hR]
          rw [hk0] at hk0t
          linarith
        exact le_of_pow_le_pow_left₀ (by unfold barlowK; omega) hu0' h1
      obtain ⟨hR9, hNR, hεN, hεR, hns, hTG⟩ :=
        barlow_numeric (d := d) (L := L) hCV hC0 hL hCcv huu0
      rw [← hRu] at hR9 hNR hεN hεR hns hTG
      have hreg : BarlowRegion ω (uniqueInfiniteComponent h) CV C0 L y R u
          (Ccv * Real.exp (-(R / (324 * Ccv)))) :=
        ⟨hCV, hC0, hL, by linarith, hNR,
          fun z hz r hur _ => (hω h R hSR z (by rw [one_mul]; exact hz) r hur).1,
          by positivity, far_of_carneVaropoulos hCcv hCVb hKinf hR0, hεN, hεR⟩
      have htT : barlowTG d CV C0 L u Ccv ≤ t := by rw [hR] at hTG; linarith
      have hg := hreg.bondHeat_le_gauss hR9 hns hCcv
        (fun a ha b hb s' hs' hab =>
          ((hCVb ω (uniqueInfiniteComponent h) hKinf a ha b hb s' hs').1 hab)) hx hy
        (by linarith) (by rw [latticeDist_self]; linarith) htT
        (by linarith) hd
      exact le_dgPhiDim_of_gauss hCg1 hinv hCgpos ht hd hg
    · have htd : t < latticeDist x y := lt_of_not_ge hd
      exact le_dgPhiDim_of_far hCcv hCg3 hCg4 ht1 htd (hcv2 htd.le)

/-- **The Gaussian upper bound of Barlow** (Dario–Gu, Theorem 4; Barlow 2004, Theorem 1 with the
tail (0.5)) on the infinite cluster of `ℤ^d`, `d ≥ 2`, with no hypothesis. -/
theorem barlowGaussianUpperBound_holds (hd : 2 ≤ d) : BarlowGaussianUpperBound d :=
  barlowGaussianUpperBound_of_veryGood (clusterVeryGoodBalls_holds hd)

/-- The planar Gaussian upper bound `BarlowGaussianUpperBoundTwo` as the case `d = 2`. -/
theorem barlowGaussianUpperBoundTwo_of_lattice : BarlowGaussianUpperBoundTwo :=
  barlowGaussianUpperBoundTwo_of_dim (barlowGaussianUpperBound_holds (d := 2) le_rfl)

end Rigidity.BarlowLattice
