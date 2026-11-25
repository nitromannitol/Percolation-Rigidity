import Rigidity.Proofs.Barlow.GaussianBound
import Rigidity.Proofs.Green.DarioGuPhiCalculus
import Rigidity.Proofs.Green.PlanarCarneVaropoulos
import PercolationClusterHomogenization.Proofs.Density.ScaleInputsFaithful

/-!
# Barlow's Gaussian upper bound on the planar infinite cluster

`barlowGaussianUpperBoundTwo_of_veryGood`: the input `BarlowGaussianUpperBoundTwo` (Theorem 4 of
Dario–Gu = Barlow, *Random walks on supercritical percolation clusters*, Ann. Probab. 32 (2004),
Theorem 1, upper bound, with the tail (0.5)) follows from the very good balls of the cluster
(`ClusterVeryGoodBallsTwo`: Barlow's Theorem 2.18 and Lemma 2.19, for Euclidean balls) and the
Carne–Varopoulos bound (`carneVaropoulosTwo_holds`, the source's Lemma 1.1).

The proof is that of the source's Proposition 6.1 and Theorem 1: for `t ≥ T(y)` the ball
`B(y, 36t)` satisfies the hypotheses of Section 3 (`BarlowRegion`) with `N = (36t)^{1/64}`, so
Theorem 3.8 (`BarlowRegion.openHeat_le_gauss`) bounds `p_t(x, y)` for `|x - y| ≤ t`; for
`|x - y| > t` the Carne–Varopoulos bound gives the second regime of `Φ_C`.
-/

open scoped Classical
open MeasureTheory Finset LatticeProb.Percolation Rigidity.Green Rigidity.External
open Rigidity.Proofs.S2

namespace Rigidity.Barlow

/-- **Very good balls of the planar infinite cluster** (Barlow 2004, Theorem 2.18(c) and
Lemma 2.19, for Euclidean balls): for every `θ ∈ (0, 1]` there are constants and, for every `y`,
a scale `S(y) ≤ O_s(C)` such that almost surely, for `R ≥ S(y)`, every ball `B(z, r)` of the
infinite cluster with `|z - y| ≤ R` and `r ≥ R^θ` is good. -/
def ClusterVeryGoodBallsTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∃ CV CP L s C : ℝ, 0 < CV ∧ 0 < CP ∧ 1 ≤ L ∧ 0 < s ∧ 0 < C ∧
      ∀ y : Vertex 2, ∃ S : Configuration 2 → ℝ, Measurable S ∧ (∀ ω, 0 ≤ S ω) ∧
        IsOsBond 2 p S s C ∧ ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ R : ℝ, S ω ≤ R → ∀ z : Vertex 2, latticeDist z y ≤ R → ∀ r : ℝ, R ^ θ ≤ r →
            IsGoodBall ω (uniqueInfiniteComponent h) CV CP L z r

/-! ### Polynomial bounds on the times of Section 3 -/

/-- The constant `b` with `T_M ≤ b N⁸`. -/
noncomputable def barlowB (CV CP L : ℝ) : ℝ :=
  (1 + 4 * (CP * L ^ 2 * CV)) ^ 2 + 4 * diagConst CV CP L

/-- The constant `c_N` with `n_* ≤ c_N N⁸`. -/
noncomputable def barlowCN (CV CP L : ℝ) : ℝ := 4 * barlowB CV CP L + 1

/-- The constant `c_T` with `T_G ≤ c_T N^16`. -/
noncomputable def barlowCT (CV CP L Ccv : ℝ) : ℝ :=
  8 * (CP * L ^ 2 * CV) + 2 + (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L) ^ 2

theorem barlowTM_le {CV CP L N : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hN : 1 ≤ N) :
    barlowTM CV CP L N ≤ barlowB CV CP L * N ^ 8 := by
  have hN4 : 1 ≤ N ^ 4 := one_le_pow₀ hN
  have hN8 : 1 ≤ N ^ 8 := one_le_pow₀ hN
  have ha : 0 ≤ CP * L ^ 2 * CV := by positivity
  have hT1 : barlowT1 CV CP L N ≤ (1 + 4 * (CP * L ^ 2 * CV)) * N ^ 4 := by
    unfold barlowT1 barlowT0
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  have hT1sq : barlowT1 CV CP L N ^ 2 ≤ (1 + 4 * (CP * L ^ 2 * CV)) ^ 2 * N ^ 8 := by
    have h0 : 0 ≤ barlowT1 CV CP L N := zero_le_one.trans (one_le_barlowT1 CV CP L N)
    calc barlowT1 CV CP L N ^ 2 ≤ ((1 + 4 * (CP * L ^ 2 * CV)) * N ^ 4) ^ 2 :=
          pow_le_pow_left₀ h0 hT1 2
      _ = (1 + 4 * (CP * L ^ 2 * CV)) ^ 2 * N ^ 8 := by ring
  have hD : 0 ≤ 4 * diagConst CV CP L := by linarith [one_le_diagConst CV CP L]
  unfold barlowTM barlowB
  refine max_le ?_ ?_
  · nlinarith [sq_nonneg (1 + 4 * (CP * L ^ 2 * CV))]
  · nlinarith [sq_nonneg (1 + 4 * (CP * L ^ 2 * CV))]

theorem barlowNstar_le {CV CP L N : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hN : 1 ≤ N) :
    (barlowNstar CV CP L N : ℝ) ≤ barlowCN CV CP L * N ^ 8 := by
  have hN8 : 1 ≤ N ^ 8 := one_le_pow₀ hN
  have h1 : (barlowNstar CV CP L N : ℝ) < 4 * barlowTM CV CP L N + 1 := by
    unfold barlowNstar
    exact Nat.ceil_lt_add_one (by
      have := (one_le_barlowT1 CV CP L N)
      have : 0 ≤ barlowTM CV CP L N := le_trans (by positivity) (le_max_left _ _)
      linarith)
  have h2 := barlowTM_le (L := L) hCV hCP hN
  unfold barlowCN
  nlinarith

theorem barlowTG_le {CV CP L N Ccv : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hN : 1 ≤ N)
    (hCcv : 0 < Ccv) : barlowTG CV CP L N Ccv ≤ barlowCT CV CP L Ccv * N ^ 16 := by
  have hN4 : 1 ≤ N ^ 4 := one_le_pow₀ hN
  have hN16 : 1 ≤ N ^ 16 := one_le_pow₀ hN
  have hN416 : N ^ 4 ≤ N ^ 16 := pow_le_pow_right₀ hN (by norm_num)
  have ha : 0 ≤ CP * L ^ 2 * CV := by positivity
  have hκ1 := one_le_barlowKappa CV CP L
  have hB0 := barlowB0_pos CV CP L
  have hns := barlowNstar_le (L := L) hCV hCP hN
  have hr1sq : barlowR1 CV CP L N ^ 2 = 16 * barlowB0 CV CP L ^ 2 * barlowNstar CV CP L N := by
    unfold barlowR1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hq : 4 * Ccv * barlowR1 CV CP L N ^ 2 / barlowKappa CV CP L ^ 2 ≤
      64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L * N ^ 8 := by
    rw [div_le_iff₀ (by positivity), hr1sq]
    have hκ2 : 1 ≤ barlowKappa CV CP L ^ 2 := one_le_pow₀ hκ1
    have hpos : 0 ≤ 64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L * N ^ 8 := by
      have : 0 ≤ barlowCN CV CP L := by
        unfold barlowCN barlowB
        have := one_le_diagConst CV CP L
        positivity
      positivity
    have s1 : 4 * Ccv * (16 * barlowB0 CV CP L ^ 2 * barlowNstar CV CP L N) =
        64 * Ccv * barlowB0 CV CP L ^ 2 * barlowNstar CV CP L N := by ring
    have s2 : 64 * Ccv * barlowB0 CV CP L ^ 2 * barlowNstar CV CP L N ≤
        64 * Ccv * barlowB0 CV CP L ^ 2 * (barlowCN CV CP L * N ^ 8) :=
      mul_le_mul_of_nonneg_left hns (by positivity)
    have s3 : 64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L * N ^ 8 ≤
        64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L * N ^ 8 * barlowKappa CV CP L ^ 2 :=
      le_mul_of_one_le_right hpos hκ2
    have s4 : 64 * Ccv * barlowB0 CV CP L ^ 2 * (barlowCN CV CP L * N ^ 8) =
        64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L * N ^ 8 := by ring
    linarith
  have hq0 : 0 ≤ 4 * Ccv * barlowR1 CV CP L N ^ 2 / barlowKappa CV CP L ^ 2 := by positivity
  have hqsq : (4 * Ccv * barlowR1 CV CP L N ^ 2 / barlowKappa CV CP L ^ 2) ^ 2 ≤
      (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L) ^ 2 * N ^ 16 := by
    calc _ ≤ (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L * N ^ 8) ^ 2 :=
          pow_le_pow_left₀ hq0 hq 2
      _ = _ := by ring
  have hsq0 : 0 ≤ (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L) ^ 2 := sq_nonneg _
  have hA : 8 * (CP * L ^ 2 * CV * N ^ 4) ≤ 8 * (CP * L ^ 2 * CV) * N ^ 16 := by
    have := mul_le_mul_of_nonneg_left hN416 (by positivity : (0 : ℝ) ≤ 8 * (CP * L ^ 2 * CV))
    linarith
  have hB : 8 * (CP * L ^ 2 * CV) * N ^ 16 + 2 * N ^ 16 +
      (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L) ^ 2 * N ^ 16 =
      (8 * (CP * L ^ 2 * CV) + 2 + (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L) ^ 2) *
        N ^ 16 := by ring
  have hC : 0 ≤ 8 * (CP * L ^ 2 * CV) * N ^ 16 := by positivity
  have hD : 0 ≤ (64 * Ccv * barlowB0 CV CP L ^ 2 * barlowCN CV CP L) ^ 2 * N ^ 16 := by
    positivity
  unfold barlowTG barlowCT barlowT0
  refine max_le (max_le ?_ ?_) ?_
  · linarith
  · linarith
  · linarith

/-! ### The far estimate from the Carne–Varopoulos bound -/

theorem exp_neg_le_one_div {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx (by linarith [Real.add_one_le_exp x])

theorem exp_neg_le_two_div_sq {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 2 / x ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hx.le
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  nlinarith

/-- The Carne–Varopoulos bound makes `p_s(x, y) ≤ C e^{-R/(324C)}` at distance `R/18` up to time
`R` (the role of the source's Lemma 1.1(b)). -/
theorem far_of_carneVaropoulos {Ccv : ℝ} (hCcv : 0 < Ccv)
    (hCV : ∀ (ω : Configuration 2) (K : OpenComponent ω), K.supp.Infinite →
      ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t →
        (‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ≤ t →
          openHeat ω t x y ≤
            Ccv * Real.exp (-(‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ 2 /
              (Ccv * t)))) ∧
        (t ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ →
          openHeat ω t x y ≤
            Ccv * Real.exp (-(‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ / Ccv *
              (1 + Real.log (‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ / t))))))
    {ω : Configuration 2} {K : OpenComponent ω} (hK : K.supp.Infinite) {R : ℝ} (hR : 0 < R) :
    ∀ x ∈ K.supp, ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x →
      openHeat ω s x y ≤ Ccv * Real.exp (-(R / (324 * Ccv))) := by
  intro x hx s hs0 hsR y hy
  have hpos : 0 < Ccv * Real.exp (-(R / (324 * Ccv))) := by positivity
  have hd : R / 18 ≤ latticeDist x y := by rw [latticeDist_comm]; exact hy
  rcases hs0.eq_or_lt with rfl | hs
  · rw [openHeat_zero, if_neg]
    · exact hpos.le
    · intro hxy
      rw [hxy] at hd
      simp [latticeDist] at hd
      linarith
  · by_cases hyK : y ∈ K.supp
    · obtain ⟨h1, h2⟩ := hCV ω K hK x hx y hyK s hs
      have hnorm : ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ = latticeDist x y :=
        rfl
      rw [hnorm] at h1 h2
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
        have h4 : latticeDist x y / Ccv ≤ latticeDist x y / Ccv * (1 + Real.log (latticeDist x y / s)) := by
          have : 0 ≤ latticeDist x y / Ccv := div_nonneg (latticeDist_nonneg x y) hCcv.le
          nlinarith
        linarith
    · rw [openHeat_eq_zero_of_mem_of_notMem hx hyK]
      exact hpos.le

/-! ### The comparison with `Φ_C` -/

theorem le_dgPhi_of_gauss {q CG cG Cg t d : ℝ} (hCG : CG ≤ Cg) (hcG : 1 / Cg ≤ cG)
    (hCg : 0 < Cg) (ht : 0 < t) (hd : d ≤ t) (hq : q ≤ CG / t * Real.exp (-(cG * d ^ 2 / t))) :
    q ≤ dgPhi Cg t d := by
  rw [dgPhi, dgExponent, if_pos hd]
  have he : Real.exp (-(cG * d ^ 2 / t)) ≤ Real.exp (-(d ^ 2 / (Cg * t))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have e : d ^ 2 / (Cg * t) = 1 / Cg * d ^ 2 / t := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcG (sq_nonneg _)) ht.le
  calc q ≤ CG / t * Real.exp (-(cG * d ^ 2 / t)) := hq
    _ ≤ Cg / t * Real.exp (-(d ^ 2 / (Cg * t))) := by gcongr
    _ = Cg * t⁻¹ * Real.exp (-(d ^ 2 / (Cg * t))) := by rw [div_eq_mul_inv]

theorem le_dgPhi_of_far {q Ccv Cg t d : ℝ} (hCcv : 0 < Ccv) (h2 : 2 * Ccv ^ 2 ≤ Cg)
    (h3 : 2 * Ccv ≤ Cg) (ht : 0 < t) (htd : t < d)
    (hq : q ≤ Ccv * Real.exp (-(d / Ccv * (1 + Real.log (d / t))))) : q ≤ dgPhi Cg t d := by
  have hd : ¬ d ≤ t := not_le.2 htd
  rw [dgPhi, dgExponent, if_neg hd]
  set Λ := Real.log (d / t) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
  have hd0 : 0 < d := by linarith
  have hsplit : Real.exp (-(d / Ccv * (1 + Λ))) =
      Real.exp (-(d / (2 * Ccv) * (1 + Λ))) * Real.exp (-(d / (2 * Ccv) * (1 + Λ))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hA : Real.exp (-(d / (2 * Ccv) * (1 + Λ))) ≤ 2 * Ccv / t := by
    have h4 : Real.exp (-(d / (2 * Ccv) * (1 + Λ))) ≤ Real.exp (-(t / (2 * Ccv))) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have h5 : t / (2 * Ccv) ≤ d / (2 * Ccv) := div_le_div_of_nonneg_right htd.le (by positivity)
      have h6 : 0 ≤ d / (2 * Ccv) := by positivity
      nlinarith
    refine h4.trans ((exp_neg_le_one_div (by positivity)).trans (le_of_eq ?_))
    rw [one_div_div]
  have hB : Real.exp (-(d / (2 * Ccv) * (1 + Λ))) ≤ Real.exp (-(d / Cg * (1 + Λ))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have h5 : d / Cg ≤ d / (2 * Ccv) := div_le_div_of_nonneg_left hd0.le (by positivity) h3
    nlinarith
  calc q ≤ Ccv * Real.exp (-(d / Ccv * (1 + Λ))) := hq
    _ = Ccv * Real.exp (-(d / (2 * Ccv) * (1 + Λ))) * Real.exp (-(d / (2 * Ccv) * (1 + Λ))) := by
        rw [hsplit]; ring
    _ ≤ Ccv * (2 * Ccv / t) * Real.exp (-(d / Cg * (1 + Λ))) := by gcongr
    _ = 2 * Ccv ^ 2 * t⁻¹ * Real.exp (-(d / Cg * (1 + Λ))) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ Cg * t⁻¹ * Real.exp (-(d / Cg * (1 + Λ))) := by gcongr

/-! ### The numerical conditions on the radius -/

/-- The threshold `u₀` on `N = R^{1/64}`. -/
noncomputable def barlowU0 (CV CP L Ccv : ℝ) : ℝ :=
  max (max 18 (36 * barlowCT CV CP L Ccv + 1))
    (max (barlowCN CV CP L + 1) (max (324 * Ccv ^ 2 * CV ^ 2 + 1) (8 * 324 ^ 2 * Ccv ^ 3 + 1)))

theorem barlowU0_ge (CV CP L Ccv : ℝ) :
    18 ≤ barlowU0 CV CP L Ccv ∧ 36 * barlowCT CV CP L Ccv + 1 ≤ barlowU0 CV CP L Ccv ∧
      barlowCN CV CP L + 1 ≤ barlowU0 CV CP L Ccv ∧
      324 * Ccv ^ 2 * CV ^ 2 + 1 ≤ barlowU0 CV CP L Ccv ∧
      8 * 324 ^ 2 * Ccv ^ 3 + 1 ≤ barlowU0 CV CP L Ccv := by
  unfold barlowU0
  refine ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- For `u ≥ u₀` and `R = u⁶⁴`, the numerical hypotheses of Section 3 hold with `N = u` and
`ε = C e^{-R/(324C)}`. -/
theorem barlow_numeric {CV CP L Ccv u : ℝ} (hCV : 0 < CV) (hCP : 0 < CP) (hCcv : 0 < Ccv)
    (hu : barlowU0 CV CP L Ccv ≤ u) :
    9 ≤ u ^ 64 ∧ u ≤ u ^ 64 / 18 ∧
      Ccv * Real.exp (-(u ^ 64 / (324 * Ccv))) * u ^ 2 * CV ^ 2 ≤ 25 ∧
      4 * (Ccv * Real.exp (-(u ^ 64 / (324 * Ccv)))) * u ^ 64 ≤ 1 ∧
      (barlowNstar CV CP L u : ℝ) ≤ 2 * u ^ 64 ∧
      barlowTG CV CP L u Ccv ≤ u ^ 64 / 36 := by
  obtain ⟨h18, hT, hN, he1, he2⟩ := barlowU0_ge CV CP L Ccv
  have hu18 : 18 ≤ u := h18.trans hu
  have hu1 : 1 ≤ u := by linarith
  have hpow : ∀ n : ℕ, 1 ≤ n → u ≤ u ^ n := fun n hn => le_self_pow₀ hu1 (by omega)
  set R := u ^ 64 with hR
  have hR0 : 0 < R := by positivity
  have hu64 : u ≤ R := hpow 64 (by norm_num)
  have hx0 : 0 < R / (324 * Ccv) := by positivity
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · have h63 : u ≤ u ^ 63 := hpow 63 (by norm_num)
    have e : R = u ^ 63 * u := by rw [hR]; ring
    rw [e]
    nlinarith
  · have hex := exp_neg_le_one_div hx0
    have h1 : Ccv * Real.exp (-(R / (324 * Ccv))) ≤ Ccv * (324 * Ccv / R) := by
      refine mul_le_mul_of_nonneg_left (hex.trans (le_of_eq ?_)) hCcv.le
      rw [one_div_div]
    have h62 : u ≤ u ^ 62 := hpow 62 (by norm_num)
    have e : R = u ^ 62 * u ^ 2 := by rw [hR]; ring
    have hR' : 324 * Ccv ^ 2 * CV ^ 2 * u ^ 2 ≤ 25 * R := by
      rw [e]
      have hu2 : 0 ≤ u ^ 2 := by positivity
      have h7 : 324 * Ccv ^ 2 * CV ^ 2 ≤ u ^ 62 := by linarith
      nlinarith
    have hε0 : 0 ≤ Ccv * Real.exp (-(R / (324 * Ccv))) := by positivity
    calc Ccv * Real.exp (-(R / (324 * Ccv))) * u ^ 2 * CV ^ 2
        ≤ Ccv * (324 * Ccv / R) * u ^ 2 * CV ^ 2 := by gcongr
      _ = 324 * Ccv ^ 2 * CV ^ 2 * u ^ 2 / R := by ring
      _ ≤ 25 := by rw [div_le_iff₀ hR0]; linarith
  · have hex := exp_neg_le_two_div_sq hx0
    have h1 : 4 * (Ccv * Real.exp (-(R / (324 * Ccv)))) * R ≤
        8 * Ccv * R / (R / (324 * Ccv)) ^ 2 := by
      calc 4 * (Ccv * Real.exp (-(R / (324 * Ccv)))) * R
          ≤ 4 * (Ccv * (2 / (R / (324 * Ccv)) ^ 2)) * R := by gcongr
        _ = 8 * Ccv * R / (R / (324 * Ccv)) ^ 2 := by ring
    have h2 : 8 * Ccv * R / (R / (324 * Ccv)) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity), div_pow, le_div_iff₀ (by positivity)]
      have hRb : 8 * 324 ^ 2 * Ccv ^ 3 ≤ R := by linarith
      nlinarith
    linarith
  · have h1 := barlowNstar_le (L := L) hCV hCP hu1
    have h56 : u ≤ u ^ 56 := hpow 56 (by norm_num)
    have e : R = u ^ 56 * u ^ 8 := by rw [hR]; ring
    have h8 : 0 ≤ u ^ 8 := by positivity
    have h9 : barlowCN CV CP L ≤ u ^ 56 := by linarith
    have : barlowCN CV CP L * u ^ 8 ≤ R := by rw [e]; nlinarith
    linarith
  · have h1 := barlowTG_le (L := L) hCV hCP hu1 hCcv
    have h48 : u ≤ u ^ 48 := hpow 48 (by norm_num)
    have e : R = u ^ 48 * u ^ 16 := by rw [hR]; ring
    have h16 : 0 ≤ u ^ 16 := by positivity
    have h9 : 36 * barlowCT CV CP L Ccv ≤ u ^ 48 := by linarith
    have : barlowCT CV CP L Ccv * u ^ 16 ≤ R / 36 := by
      rw [le_div_iff₀ (by norm_num), e]
      nlinarith
    linarith

/-! ### The Gaussian upper bound -/

/-- **Barlow 2004, Theorem 1** (upper bound with the tail (0.5)) in the form of Dario–Gu,
Theorem 4, from the very good balls of the cluster: `BarlowGaussianUpperBoundTwo`. -/
theorem barlowGaussianUpperBoundTwo_of_veryGood (hVG : ClusterVeryGoodBallsTwo) :
    BarlowGaussianUpperBoundTwo := by
  intro p hpc hp1
  obtain ⟨CV, CP, L, s, Cs, hCV, hCP, hL, hs, hCs, hVGp⟩ :=
    hVG p hpc hp1 (1 / 64) (by norm_num) (by norm_num)
  obtain ⟨Ccv, hCcv, hCVb⟩ := carneVaropoulosTwo_holds
  set u0 := barlowU0 CV CP L Ccv with hu0
  have hu018 : 18 ≤ u0 := (barlowU0_ge CV CP L Ccv).1
  set k0 : ℝ := u0 ^ 64 / 36 with hk0
  have hk0pos : 0 < k0 := by positivity
  set cG := barlowcG CV CP L Ccv with hcG
  set CG := barlowCG CV CP L Ccv with hCG
  have hcG0 : 0 < cG := barlowcG_pos CV CP L hCcv
  set Cg := max (max CG (1 / cG)) (max (2 * Ccv ^ 2) (2 * Ccv)) with hCg
  have hCg1 : CG ≤ Cg := (le_max_left _ _).trans (le_max_left _ _)
  have hCg2 : 1 / cG ≤ Cg := (le_max_right _ _).trans (le_max_left _ _)
  have hCg3 : 2 * Ccv ^ 2 ≤ Cg := (le_max_left _ _).trans (le_max_right _ _)
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
    have h2 := isOsBond_const (d := 2) (p := p) (κ := k0) hk0pos hs
    have h3 := IsOsBond.max hs (by positivity) (by positivity) (measurable_const.mul hSm)
      measurable_const h1 h2
    exact IsOsBond.mono_scale hs (by positivity) (le_max_right _ _) hTm h3
  · filter_upwards [hSae] with ω hω
    intro h hy t ht hTt x hx
    have hKinf := uniqueInfiniteComponent_infinite h
    refine le_trans ?_ (dgPhi_mono (C := Cg) hCgpos (le_max_left _ _) ht (latticeDist_nonneg x y))
    obtain ⟨hcv1, hcv2⟩ := hCVb ω (uniqueInfiniteComponent h) hKinf x hx y hy t ht
    by_cases hd : latticeDist x y ≤ t
    · set R := 36 * t with hR
      have hR0 : 0 < R := by positivity
      set u := R ^ ((1 : ℝ) / 64) with hu
      have hu0' : 0 ≤ u := by positivity
      have hRu : R = u ^ 64 := by
        rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
        norm_num
      have hk0t : k0 ≤ t := (le_max_right _ _).trans hTt
      have hSR : S ω ≤ R := by
        have := (le_max_left _ _).trans hTt
        rw [hR]
        linarith
      have huu0 : u0 ≤ u := by
        have h1 : u0 ^ 64 ≤ u ^ 64 := by
          rw [← hRu, hR]
          rw [hk0] at hk0t
          linarith
        exact le_of_pow_le_pow_left₀ (by norm_num) hu0' h1
      obtain ⟨hR9, hNR, hεN, hεR, hns, hTG⟩ := barlow_numeric (L := L) hCV hCP hCcv huu0
      rw [← hRu] at hR9 hNR hεN hεR hns hTG
      have hreg : BarlowRegion ω (uniqueInfiniteComponent h) CV CP L y R u
          (Ccv * Real.exp (-(R / (324 * Ccv)))) :=
        ⟨hCV, hCP, hL, by linarith, hNR, fun z hz r hur _ => hω h R hSR z hz r hur,
          by positivity, far_of_carneVaropoulos hCcv hCVb hKinf hR0, hεN, hεR⟩
      have htT : barlowTG CV CP L u Ccv ≤ t := by rw [hR] at hTG; linarith
      have hg := hreg.openHeat_le_gauss hR9 hns hCcv
        (fun a ha b hb s' hs' hab =>
          ((hCVb ω (uniqueInfiniteComponent h) hKinf a ha b hb s' hs').1 hab)) hx hy
        (by linarith) (by rw [show latticeDist y y = 0 by simp [latticeDist]]; linarith) htT
        (by linarith) hd
      exact le_dgPhi_of_gauss hCg1 hinv hCgpos ht hd hg
    · have htd : t < latticeDist x y := lt_of_not_ge hd
      exact le_dgPhi_of_far hCcv hCg3 hCg4 ht htd (hcv2 htd.le)

end Rigidity.Barlow
