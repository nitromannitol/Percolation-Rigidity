import Rigidity.Proofs.BarlowLattice.GaussianTail
import Rigidity.Proofs.Barlow.GaussianBound

/-!
# The Gaussian upper bound in a very good ball

**Barlow 2004, Theorem 3.8** (*Random walks on supercritical percolation clusters*, Ann. Probab. 32
(2004)) for the variable speed random walk on the open graph of a configuration of `ℤ^d`, under the
hypotheses `BarlowRegion` of Section 3 and a Carne–Varopoulos bound: for points `x, y` of `K`
within `R/3` of `x₀`, `T_G ≤ t ≤ R/36` and `|x - y| ≤ t`,

  `p_t(x, y) ≤ C_G t^{-d/2} exp(-c_G |x - y|²/t)`   (`BarlowRegion.bondHeat_le_gauss`).

The source decomposes the walk at the exit time from `B(x, |x - y|/2)`; here the decomposition is
the Chapman–Kolmogorov equation at time `t/2`, with the displacement tails of `tsum_far_le` at both
endpoints and the on-diagonal bound `heat_le`. As in the source, the Carne–Varopoulos bound (the
source's (1.5)) covers the distances `|x - y|` for which the exit estimate is not available.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green Rigidity.WeakPoincare

namespace Rigidity.BarlowLattice

variable {d : ℕ}

variable [NeZero d] {ω : Configuration d}

/-- The time from which the Gaussian bound holds. -/
noncomputable def barlowTG (d : ℕ) (CV CP L N Ccv : ℝ) : ℝ :=
  max (max (8 * barlowT0 d CV CP L N) 2)
    ((2 * d * Ccv * barlowR1 d CV CP L N ^ 2 / barlowKappa d CV CP L ^ 2) ^ 2)

/-- The Gaussian constant `c_G`. -/
noncomputable def barlowcG (d : ℕ) (CV CP L Ccv : ℝ) : ℝ :=
  min (min (barlowC6 d CV CP L) 1 / 2) (1 / (2 * Ccv))

/-- The constant `H₂ = 2^{d/2} H` of the on-diagonal bound at time `t/2`. -/
noncomputable def barlowH2 (d : ℕ) (CV CP L : ℝ) : ℝ := Real.sqrt 2 ^ d * heatConst d CV CP L

/-- The prefactor `C_G`. -/
noncomputable def barlowCG (d : ℕ) (CV CP L Ccv : ℝ) : ℝ :=
  max (max (heatConst d CV CP L *
      Real.exp (4 * barlowcG d CV CP L Ccv * barlowKappa d CV CP L ^ 2))
    (14 * barlowH2 d CV CP L / 3)) Ccv

theorem one_le_barlowH2 (d : ℕ) (CV CP L : ℝ) : 1 ≤ barlowH2 d CV CP L := by
  unfold barlowH2
  have h1 : 1 ≤ Real.sqrt 2 ^ d :=
    one_le_pow₀ (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num))
  have h2 := one_le_heatConst d CV CP L
  nlinarith

theorem barlowcG_pos (d : ℕ) (CV CP L : ℝ) {Ccv : ℝ} (hC : 0 < Ccv) : 0 < barlowcG d CV CP L Ccv := by
  unfold barlowcG
  have := barlowC6_pos d CV CP L
  refine lt_min (by positivity) (by positivity)

namespace BarlowRegion

variable {K : OpenComponent ω} {CV CP L : ℝ} {x0 : Vertex d} {R N ε : ℝ}

/-- Small distances: `p_t(x, y) ≤ H t^{-d/2}`. -/
theorem gauss_near (h : BarlowRegion ω K CV CP L x0 R N ε) {x y : Vertex d} (hx : x ∈ K.supp)
    (hx0 : latticeDist x x0 ≤ 7 * R / 9) {t : ℝ} (ht : 4 * barlowT0 d CV CP L N ≤ t) (htR : t ≤ R) :
    bondHeat ω t x y ≤ heatConst d CV CP L / Real.sqrt t ^ d :=
  h.heat_le hx hx0 y ht htR

/-- Large distances: the Carne–Varopoulos bound gives `p_t(x, y) ≤ C t^{-d/2} e^{-|x - y|²/(2Ct)}`
when `|x - y| > κ t / r₁` and `t ≥ (2d C r₁²/κ²)²`. -/
theorem gauss_far {Ccv κ r1 : ℝ} (hCcv : 0 < Ccv) (hκ : 1 ≤ κ) (hr1 : 0 < r1) {x y : Vertex d}
    {t : ℝ} (ht : 0 < t) (htsq : (2 * d * Ccv * r1 ^ 2 / κ ^ 2) ^ 2 ≤ t)
    (hcv : bondHeat ω t x y ≤ Ccv * Real.exp (-(latticeDist x y ^ 2 / (Ccv * t))))
    (hC : κ * (t / 2) < latticeDist x y / 2 * r1) :
    bondHeat ω t x y ≤ Ccv / Real.sqrt t ^ d * Real.exp (-(latticeDist x y ^ 2 / (2 * Ccv * t))) := by
  set dxy := latticeDist x y with hdxy
  have hd1 : (1 : ℝ) ≤ d := one_le_dim_real
  have hlog : d / 2 * Real.log t ≤ dxy ^ 2 / (2 * Ccv * t) := by
    have hsqt : 2 * d * Ccv * r1 ^ 2 / κ ^ 2 ≤ Real.sqrt t := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * d * Ccv * r1 ^ 2 / κ ^ 2)]
      exact Real.sqrt_le_sqrt htsq
    have hdl : κ * t / r1 < dxy := by
      rw [div_lt_iff₀ hr1]
      linarith
    have hd2 : (κ * t / r1) ^ 2 ≤ dxy ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdl.le 2
    have e : (κ * t / r1) ^ 2 / (2 * Ccv * t) = κ ^ 2 * t / (2 * Ccv * r1 ^ 2) := by
      field_simp
    have h2 : κ ^ 2 * t / (2 * Ccv * r1 ^ 2) ≤ dxy ^ 2 / (2 * Ccv * t) := by
      rw [← e]
      exact div_le_div_of_nonneg_right hd2 (by positivity)
    have h3 : d * Real.sqrt t ≤ κ ^ 2 * t / (2 * Ccv * r1 ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have hs := Real.sq_sqrt ht.le
      have hsp : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      rw [div_le_iff₀ (by positivity)] at hsqt
      nlinarith
    have h4 := Barlow.log_le_two_mul_sqrt ht
    have h5 : d / 2 * Real.log t ≤ d / 2 * (2 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith
  have hst : 0 < Real.sqrt t ^ d := by positivity
  have hinv : Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) ≤ 1 / Real.sqrt t ^ d := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ hst
    calc Real.sqrt t ^ d = Real.exp (Real.log (Real.sqrt t ^ d)) := (Real.exp_log hst).symm
      _ ≤ Real.exp (dxy ^ 2 / (2 * Ccv * t)) := by
          apply Real.exp_le_exp.2
          rw [Real.log_pow, Real.log_sqrt ht.le]
          linarith
  have hsplit : Real.exp (-(dxy ^ 2 / (Ccv * t))) =
      Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) * Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc bondHeat ω t x y ≤ Ccv * Real.exp (-(dxy ^ 2 / (Ccv * t))) := hcv
    _ = Ccv * Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) * Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) := by
        rw [hsplit]; ring
    _ ≤ Ccv * (1 / Real.sqrt t ^ d) * Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) := by gcongr
    _ = Ccv / Real.sqrt t ^ d * Real.exp (-(dxy ^ 2 / (2 * Ccv * t))) := by rw [mul_one_div]

set_option maxHeartbeats 400000 in
/-- Intermediate distances: Chapman–Kolmogorov at `t/2` and the displacement tails give
`p_t(x, y) ≤ (14 H₂/3) t^{-d/2} e^{-min(c₆, 1) |x - y|²/(2t)}`. -/
theorem gauss_mid (h : BarlowRegion ω K CV CP L x0 R N ε) (hR9 : 9 ≤ R)
    (hns : (barlowNstar d CV CP L N : ℝ) ≤ d * R) {x y : Vertex d} (hx : x ∈ K.supp)
    (hy : y ∈ K.supp) (hx0 : latticeDist x x0 ≤ R / 3) (hy0 : latticeDist y x0 ≤ R / 3) {t : ℝ}
    (ht2 : 2 ≤ t) (ht8 : 8 * barlowT0 d CV CP L N ≤ t) (htR : t ≤ R / 36)
    (hxy : latticeDist x y ≤ t) (hρκ : barlowKappa d CV CP L ≤ latticeDist x y / 2)
    (hBr : latticeDist x y / 2 * barlowR1 d CV CP L N ≤ barlowKappa d CV CP L * (t / 2)) :
    bondHeat ω t x y ≤ 14 * barlowH2 d CV CP L / 3 / Real.sqrt t ^ d *
      Real.exp (-(min (barlowC6 d CV CP L) 1 * latticeDist x y ^ 2 / (2 * t))) := by
  set H := heatConst d CV CP L with hH
  set H2 := barlowH2 d CV CP L with hH2
  set c6 := barlowC6 d CV CP L with hc6
  have hc60 : 0 < c6 := barlowC6_pos d CV CP L
  have hH21 : 1 ≤ H2 := one_le_barlowH2 d CV CP L
  have ht0 : 0 < t := by linarith
  have hRt : t ≤ R := by linarith
  have hx7 : latticeDist x x0 ≤ 7 * R / 9 := by linarith
  have hy7 : latticeDist y x0 ≤ 7 * R / 9 := by linarith
  have hd0 : 0 ≤ latticeDist x y := latticeDist_nonneg x y
  set ρ := latticeDist x y / 2 with hρ
  have ht2' : 1 ≤ t / 2 := by linarith
  have ht2R : t / 2 ≤ R / 36 := by linarith
  have hρR : ρ ≤ R / 9 := by linarith
  have hT4 : 4 * barlowT0 d CV CP L N ≤ t / 2 := by linarith
  have e2 : H / Real.sqrt (t / 2) ^ d = H2 / Real.sqrt t ^ d := by
    have hs2 : 0 < Real.sqrt 2 ^ d := by positivity
    have hst : 0 < Real.sqrt t ^ d := by positivity
    rw [Real.sqrt_div' t (by norm_num : (0 : ℝ) ≤ 2), div_pow, hH2, barlowH2, ← hH]
    field_simp
  have hX : ∀ z, bondHeat ω (t / 2) x z ≤ H2 / Real.sqrt t ^ d := fun z => by
    have := h.heat_le hx hx7 z hT4 (by linarith only [hRt, ht0])
    rwa [e2] at this
  have hY : ∀ z, bondHeat ω (t / 2) y z ≤ H2 / Real.sqrt t ^ d := fun z => by
    have := h.heat_le hy hy7 z hT4 (by linarith only [hRt, ht0])
    rwa [e2] at this
  have ht2n : (0 : ℝ) ≤ t / 2 := by linarith
  have hCK := hasSum_bondHeat_mul ω ht2n ht2n x y
  rw [show t / 2 + t / 2 = t by ring] at hCK
  have hsx : Summable fun z => (if ρ ≤ latticeDist x z then bondHeat ω (t / 2) x z else 0) :=
    (hasSum_bondHeat ω ht2n x).summable.of_nonneg_of_le
      (fun z => by split_ifs; exacts [bondHeat_nonneg ω ht2n x z, le_rfl])
      (fun z => by split_ifs; exacts [le_rfl, bondHeat_nonneg ω ht2n x z])
  have hsy : Summable fun z => (if ρ ≤ latticeDist y z then bondHeat ω (t / 2) y z else 0) :=
    (hasSum_bondHeat ω ht2n y).summable.of_nonneg_of_le
      (fun z => by split_ifs; exacts [bondHeat_nonneg ω ht2n y z, le_rfl])
      (fun z => by split_ifs; exacts [le_rfl, bondHeat_nonneg ω ht2n y z])
  have h4D : 0 ≤ H2 / Real.sqrt t ^ d := by positivity
  have hpt : ∀ z, bondHeat ω (t / 2) x z * bondHeat ω (t / 2) z y ≤
      H2 / Real.sqrt t ^ d * ((if ρ ≤ latticeDist x z then bondHeat ω (t / 2) x z else 0) +
        (if ρ ≤ latticeDist y z then bondHeat ω (t / 2) y z else 0)) := by
    intro z
    have hxz := bondHeat_nonneg ω ht2n x z
    have hyz := bondHeat_nonneg ω ht2n y z
    rw [bondHeat_symm ω (t / 2) z y]
    have hiy : 0 ≤ (if ρ ≤ latticeDist y z then bondHeat ω (t / 2) y z else 0) := by
      split_ifs; exacts [hyz, le_rfl]
    have hix : 0 ≤ (if ρ ≤ latticeDist x z then bondHeat ω (t / 2) x z else 0) := by
      split_ifs; exacts [hxz, le_rfl]
    by_cases h1 : ρ ≤ latticeDist x z
    · rw [if_pos h1]
      have h5 := mul_le_mul_of_nonneg_left (hY z) hxz
      have h6 := mul_nonneg h4D hiy
      nlinarith only [h5, h6]
    · have h2 : ρ ≤ latticeDist y z := by
        have htri := latticeDist_triangle' x z y
        have e1 := latticeDist_comm z y
        have e3 := latticeDist_comm z x
        have h1' : latticeDist x z < ρ := lt_of_not_ge h1
        linarith only [htri, e1, e3, h1', hρ]
      rw [if_pos h2]
      have h5 := mul_le_mul_of_nonneg_right (hX z) hyz
      have h6 := mul_nonneg h4D hix
      nlinarith only [h5, h6]
  have hle := hasSum_le hpt hCK ((hsx.add hsy).mul_left (H2 / Real.sqrt t ^ d)).hasSum
  rw [tsum_mul_left, hsx.tsum_add hsy] at hle
  have hTx := h.tsum_far_le hR9 hns hx hx0 ht2' ht2R hρκ hBr hρR
  have hTy := h.tsum_far_le hR9 hns hy hy0 ht2' ht2R hρκ hBr hρR
  have e1 : c6 * ρ ^ 2 / (t / 2) = c6 * latticeDist x y ^ 2 / (2 * t) := by
    rw [hρ]
    ring
  rw [e1] at hTx hTy
  set m6 := min c6 1 with hm6
  have hm6c : m6 ≤ c6 := min_le_left _ _
  have hm61 : m6 ≤ 1 := min_le_right _ _
  have hm60 : 0 ≤ m6 := le_min hc60.le zero_le_one
  have hm : m6 * latticeDist x y ^ 2 / (2 * t) ≤ c6 * latticeDist x y ^ 2 / (2 * t) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm6c (sq_nonneg _)) (by positivity)
  have hm1 : m6 * latticeDist x y ^ 2 / (2 * t) ≤ t / 2 := by
    have hd2 : latticeDist x y ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hd0 hxy 2
    rw [div_le_iff₀ (by positivity)]
    have h7 : m6 * latticeDist x y ^ 2 ≤ 1 * t ^ 2 :=
      mul_le_mul hm61 hd2 (sq_nonneg _) zero_le_one
    nlinarith only [h7, ht0]
  have hE1 : Real.exp (-(c6 * latticeDist x y ^ 2 / (2 * t))) ≤
      Real.exp (-(m6 * latticeDist x y ^ 2 / (2 * t))) :=
    Real.exp_le_exp.2 (by linarith only [hm])
  have hE2 : Real.exp (-(t / 2)) ≤ Real.exp (-(m6 * latticeDist x y ^ 2 / (2 * t))) :=
    Real.exp_le_exp.2 (by linarith only [hm1])
  have hsum : (∑' z, (if ρ ≤ latticeDist x z then bondHeat ω (t / 2) x z else 0)) +
      (∑' z, (if ρ ≤ latticeDist y z then bondHeat ω (t / 2) y z else 0)) ≤
      14 / 3 * Real.exp (-(m6 * latticeDist x y ^ 2 / (2 * t))) := by
    linarith only [hTx, hTy, hE1, hE2]
  calc bondHeat ω t x y ≤ H2 / Real.sqrt t ^ d * ((∑' z, (if ρ ≤ latticeDist x z then
        bondHeat ω (t / 2) x z else 0)) +
      (∑' z, (if ρ ≤ latticeDist y z then bondHeat ω (t / 2) y z else 0))) := hle
    _ ≤ H2 / Real.sqrt t ^ d * (14 / 3 * Real.exp (-(m6 * latticeDist x y ^ 2 / (2 * t)))) :=
        mul_le_mul_of_nonneg_left hsum h4D
    _ = 14 * H2 / 3 / Real.sqrt t ^ d * Real.exp (-(m6 * latticeDist x y ^ 2 / (2 * t))) := by
        ring

/-- **Barlow 2004, Theorem 3.8** in dimension `d`: `p_t(x, y) ≤ C_G t^{-d/2} e^{-c_G |x - y|²/t}`. -/
theorem bondHeat_le_gauss (h : BarlowRegion ω K CV CP L x0 R N ε) (hR9 : 9 ≤ R)
    (hns : (barlowNstar d CV CP L N : ℝ) ≤ d * R) {Ccv : ℝ} (hCcv : 0 < Ccv)
    (hcv : ∀ a ∈ K.supp, ∀ b ∈ K.supp, ∀ s : ℝ, 0 < s → latticeDist a b ≤ s →
      bondHeat ω s a b ≤ Ccv * Real.exp (-(latticeDist a b ^ 2 / (Ccv * s))))
    {x y : Vertex d} (hx : x ∈ K.supp) (hy : y ∈ K.supp) (hx0 : latticeDist x x0 ≤ R / 3)
    (hy0 : latticeDist y x0 ≤ R / 3) {t : ℝ} (htT : barlowTG d CV CP L N Ccv ≤ t)
    (htR : t ≤ R / 36) (hxy : latticeDist x y ≤ t) :
    bondHeat ω t x y ≤
      barlowCG d CV CP L Ccv / Real.sqrt t ^ d *
        Real.exp (-(barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t)) := by
  have hcG0 : 0 < barlowcG d CV CP L Ccv := barlowcG_pos d CV CP L hCcv
  have hd1 : (1 : ℝ) ≤ d := one_le_dim_real
  have hcG6 : barlowcG d CV CP L Ccv ≤ min (barlowC6 d CV CP L) 1 / 2 := min_le_left _ _
  have hcGC : barlowcG d CV CP L Ccv ≤ 1 / (2 * Ccv) := min_le_right _ _
  have hκ1 : 1 ≤ barlowKappa d CV CP L := one_le_barlowKappa d CV CP L
  have hr10 : 0 < barlowR1 d CV CP L N := lt_of_lt_of_le
    (by linarith [barlowB0_pos d CV CP L]) (four_mul_barlowB0_le_barlowR1 d CV CP L N)
  have ht8 : 8 * barlowT0 d CV CP L N ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans htT)
  have ht2 : 2 ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans htT)
  have htsq : (2 * d * Ccv * barlowR1 d CV CP L N ^ 2 / barlowKappa d CV CP L ^ 2) ^ 2 ≤ t :=
    (le_max_right _ _).trans htT
  have ht0 : 0 < t := by linarith
  have hd0 : 0 ≤ latticeDist x y := latticeDist_nonneg x y
  have hH1 : 1 ≤ heatConst d CV CP L := one_le_heatConst d CV CP L
  have hH21 : 1 ≤ barlowH2 d CV CP L := one_le_barlowH2 d CV CP L
  have hst : 0 < Real.sqrt t ^ d := by positivity
  have hCG1 : heatConst d CV CP L *
      Real.exp (4 * barlowcG d CV CP L Ccv * barlowKappa d CV CP L ^ 2)
      ≤ barlowCG d CV CP L Ccv := (le_max_left _ _).trans (le_max_left _ _)
  have hCG2 : 14 * barlowH2 d CV CP L / 3 ≤ barlowCG d CV CP L Ccv :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hCG3 : Ccv ≤ barlowCG d CV CP L Ccv := le_max_right _ _
  by_cases hA : latticeDist x y < 2 * barlowKappa d CV CP L
  · have hT00 : 0 ≤ barlowT0 d CV CP L N := by
      unfold barlowT0
      have := h.hCP; have := h.hCV
      have : 0 < L := by linarith [h.hL]
      have : 0 < N := by linarith [h.hN]
      positivity
    have h1 := h.gauss_near (y := y) (t := t) hx (by linarith) (by linarith) (by linarith)
    have hexp : 1 ≤ Real.exp (4 * barlowcG d CV CP L Ccv * barlowKappa d CV CP L ^ 2) *
        Real.exp (-(barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hd2 : latticeDist x y ^ 2 ≤ 4 * barlowKappa d CV CP L ^ 2 := by nlinarith
      have h3 : barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t ≤
          barlowcG d CV CP L Ccv * latticeDist x y ^ 2 := div_le_self (by positivity) (by linarith)
      have h4 := mul_le_mul_of_nonneg_left hd2 hcG0.le
      linarith
    calc bondHeat ω t x y ≤ heatConst d CV CP L / Real.sqrt t ^ d := h1
      _ ≤ heatConst d CV CP L / Real.sqrt t ^ d * (Real.exp (4 * barlowcG d CV CP L Ccv *
            barlowKappa d CV CP L ^ 2) *
              Real.exp (-(barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t))) :=
          le_mul_of_one_le_right (by positivity) hexp
      _ = heatConst d CV CP L *
            Real.exp (4 * barlowcG d CV CP L Ccv * barlowKappa d CV CP L ^ 2) /
            Real.sqrt t ^ d * Real.exp (-(barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t)) := by
          ring
      _ ≤ _ := by gcongr
  · have hρκ : barlowKappa d CV CP L ≤ latticeDist x y / 2 := by linarith
    by_cases hC : barlowKappa d CV CP L * (t / 2) < latticeDist x y / 2 * barlowR1 d CV CP L N
    · have h1 := gauss_far (ω := ω) hCcv hκ1 hr10 ht0 htsq (hcv x hx y hy t ht0 hxy) hC
      have hcmp : Real.exp (-(latticeDist x y ^ 2 / (2 * Ccv * t))) ≤
          Real.exp (-(barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t)) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        have e : latticeDist x y ^ 2 / (2 * Ccv * t) = 1 / (2 * Ccv) * latticeDist x y ^ 2 / t := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcGC (sq_nonneg _)) ht0.le
      calc bondHeat ω t x y ≤ Ccv / Real.sqrt t ^ d *
            Real.exp (-(latticeDist x y ^ 2 / (2 * Ccv * t))) := h1
        _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hCG3 hst.le) hcmp (Real.exp_pos _).le
            (div_nonneg (by linarith) hst.le)
    · have h1 := h.gauss_mid hR9 hns hx hy hx0 hy0 ht2 ht8 htR hxy hρκ (le_of_not_gt hC)
      have hcmp : Real.exp (-(min (barlowC6 d CV CP L) 1 * latticeDist x y ^ 2 / (2 * t))) ≤
          Real.exp (-(barlowcG d CV CP L Ccv * latticeDist x y ^ 2 / t)) := by
        apply Real.exp_le_exp.2
        apply neg_le_neg
        have e : min (barlowC6 d CV CP L) 1 * latticeDist x y ^ 2 / (2 * t) =
            min (barlowC6 d CV CP L) 1 / 2 * latticeDist x y ^ 2 / t := by
          field_simp
        rw [e]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcG6 (sq_nonneg _)) ht0.le
      calc bondHeat ω t x y ≤ 14 * barlowH2 d CV CP L / 3 / Real.sqrt t ^ d *
            Real.exp (-(min (barlowC6 d CV CP L) 1 * latticeDist x y ^ 2 / (2 * t))) := h1
        _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hCG2 hst.le) hcmp (Real.exp_pos _).le
            (div_nonneg (by linarith) hst.le)

end BarlowRegion

end Rigidity.BarlowLattice
