import Rigidity.Proofs.Green.DarioGuTwoScaleStepFive
import Rigidity.Proofs.Green.DarioGuTwoScaleHeatEq

/-!
# Domination of the two-scale expansion uniformly in time

The summability layer of the proof of Proposition 4.3 of Dario–Gu: on a time interval `[a, b]`
with `a > 0`, the two-scale expansion `h(s, x, y)` of (4.1) and its time derivative are dominated
on the cluster by a fixed square summable function, the neighbour envelope of the Gaussian
envelope `λ_c(x) = (1 + |x - y|)³ exp(-|x - y|²/c)` (`gaussEnv`), once the corrector grows at most
linearly on the cluster:

* `summable_pow_mul_exp_neg_sq`, `summable_sq_gaussEnv`: lattice sums of Gaussians with polynomial
  weights (from `sum_exp_neg_sq_div_le` and `mul_exp_neg_sq_le`);
* `latticeGaussian_le_of_mem`, `abs_latticeGaussianTimeDeriv_le`: `p̄(s, ·)` and `∂_s p̄(s, ·)` for
  `s ∈ [a, b]`;
* `abs_twoScale_le`: `|P(x) + Σ_k D_k P(x) χ_k(x)| ≤ M (1 + 2A) nbrEnv λ_c (x)` if
  `|P| ≤ M (1 + |· - y|)² exp(-|· - y|²/c)` and `|χ_k(x)| ≤ A (1 + |x - y|)`;
* `abs_dgTwoScale_le`, `abs_dgTwoScale_deriv_le`: the bounds for `h` and `∂_s h`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem summable_exp_neg_sq_div {c : ℝ} (hc : 0 < c) (y : Vertex 2) :
    Summable fun x => Real.exp (-(latticeDist x y ^ 2 / c)) := by
  refine summable_of_sum_le (c := 4 * Real.exp (1 / c / 2) * (1 + 1 / (1 / c)) ^ 2 * 1)
    (fun x => (Real.exp_pos _).le) (fun S => ?_)
  have h := sum_exp_neg_sq_div_le (c := 1 / c) (t := 1) (by positivity) le_rfl y S
  refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) h
  congr 1
  ring

theorem summable_pow_mul_exp_neg_sq (y : Vertex 2) (m : ℕ) : ∀ {c : ℝ}, 0 < c →
    Summable fun x => latticeDist x y ^ m * Real.exp (-(latticeDist x y ^ 2 / c)) := by
  induction m with
  | zero =>
    intro c hc
    simpa only [pow_zero, one_mul] using summable_exp_neg_sq_div hc y
  | succ m ih =>
    intro c hc
    refine Summable.of_nonneg_of_le
      (fun x => by have := latticeDist_nonneg x y; positivity) (fun x => ?_)
      ((ih (c := 2 * c) (by positivity)).mul_left (Real.sqrt c))
    have hd := latticeDist_nonneg x y
    calc latticeDist x y ^ (m + 1) * Real.exp (-(latticeDist x y ^ 2 / c))
        = latticeDist x y ^ m * (latticeDist x y * Real.exp (-(latticeDist x y ^ 2 / c))) := by
          ring
      _ ≤ latticeDist x y ^ m * (Real.sqrt c * Real.exp (-(latticeDist x y ^ 2 / (2 * c)))) :=
          mul_le_mul_of_nonneg_left (mul_exp_neg_sq_le hc hd) (by positivity)
      _ = Real.sqrt c * (latticeDist x y ^ m * Real.exp (-(latticeDist x y ^ 2 / (2 * c)))) := by
          ring

/-- The Gaussian envelope `λ_c(x) = (1 + |x - y|)³ exp(-|x - y|²/c)`. -/
noncomputable def gaussEnv (c : ℝ) (y x : Vertex 2) : ℝ :=
  (1 + latticeDist x y) ^ 3 * Real.exp (-(latticeDist x y ^ 2 / c))

theorem gaussEnv_nonneg (c : ℝ) (y x : Vertex 2) : 0 ≤ gaussEnv c y x := by
  unfold gaussEnv
  have := latticeDist_nonneg x y
  positivity

theorem summable_sq_gaussEnv {c : ℝ} (hc : 0 < c) (y : Vertex 2) :
    Summable fun x => gaussEnv c y x ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    (((summable_pow_mul_exp_neg_sq y 0 (c := c / 2) (by positivity)).add
      (summable_pow_mul_exp_neg_sq y 6 (c := c / 2) (by positivity))).mul_left 64)
  have hd := latticeDist_nonneg x y
  set d := latticeDist x y
  have hE : Real.exp (-(d ^ 2 / c)) ^ 2 = Real.exp (-(d ^ 2 / (c / 2))) := by
    rw [sq, ← Real.exp_add, div_div_eq_mul_div]
    congr 1
    ring
  have e : gaussEnv c y x ^ 2 = (1 + d) ^ 6 * Real.exp (-(d ^ 2 / (c / 2))) := by
    unfold gaussEnv
    rw [mul_pow, hE]
    ring
  have h6 : (1 + d) ^ 6 ≤ 64 * (d ^ 0 + d ^ 6) := by
    have h0 : (0 : ℝ) ≤ d ^ 6 := by positivity
    rw [pow_zero]
    rcases le_total d 1 with h | h
    · have h1 : (1 + d) ^ 6 ≤ 2 ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
      norm_num at h1
      linarith
    · have h1 : (1 + d) ^ 6 ≤ (2 * d) ^ 6 := pow_le_pow_left₀ (by positivity) (by linarith) 6
      rw [mul_pow] at h1
      norm_num at h1
      linarith
  rw [e]
  calc (1 + d) ^ 6 * Real.exp (-(d ^ 2 / (c / 2))) ≤
        64 * (d ^ 0 + d ^ 6) * Real.exp (-(d ^ 2 / (c / 2))) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = 64 * (d ^ 0 * Real.exp (-(d ^ 2 / (c / 2))) + d ^ 6 * Real.exp (-(d ^ 2 / (c / 2)))) := by
        ring

/-- `p̄(s, x - y) ≤ (2πσa)^{-1} exp(-|x - y|²/(2σb))` for `s ∈ [a, b]`, `a > 0`. -/
theorem latticeGaussian_le_of_mem {σ a b s : ℝ} (hσ : 0 < σ) (ha : 0 < a) (has : a ≤ s)
    (hsb : s ≤ b) (x y : Vertex 2) :
    latticeGaussian σ s x y ≤
      (2 * Real.pi * σ * a)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * b))) := by
  have hs : 0 < s := ha.trans_le has
  unfold latticeGaussian gaussianHeat
  change (2 * Real.pi * σ * s)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * s))) ≤ _
  refine mul_le_mul (inv_anti₀ (by positivity) (by gcongr)) (Real.exp_le_exp.2 (neg_le_neg ?_))
    (Real.exp_pos _).le (by positivity)
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)

theorem latticeGaussian_nonneg' {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x y : Vertex 2) :
    0 ≤ latticeGaussian σ s x y :=
  gaussianHeat_nonneg hσ hs.le _

/-- `|∂_s p̄(s, x - y)| ≤ (2πσa)^{-1} (1/(2σa²) + 1/a) (1 + |x - y|)² exp(-|x - y|²/(2σb))`
for `s ∈ [a, b]`, `a > 0`. -/
theorem abs_latticeGaussianTimeDeriv_le {σ a b s : ℝ} (hσ : 0 < σ) (ha : 0 < a) (has : a ≤ s)
    (hsb : s ≤ b) (x y : Vertex 2) :
    |latticeGaussianTimeDeriv σ s x y| ≤ (2 * Real.pi * σ * a)⁻¹ * (1 / (2 * σ * a ^ 2) + 1 / a) *
      ((1 + latticeDist x y) ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * b)))) := by
  have hs : 0 < s := ha.trans_le has
  have hd := latticeDist_nonneg x y
  have hg := latticeGaussian_le_of_mem hσ ha has hsb x y
  have hg0 := latticeGaussian_nonneg' hσ hs x y
  have e : latticeGaussianTimeDeriv σ s x y = latticeGaussian σ s x y *
      (latticeDist x y ^ 2 / (2 * σ * s ^ 2) - 1 / s) := rfl
  rw [e, abs_mul, abs_of_nonneg hg0]
  have h1 : |latticeDist x y ^ 2 / (2 * σ * s ^ 2) - 1 / s| ≤
      (1 / (2 * σ * a ^ 2) + 1 / a) * (1 + latticeDist x y) ^ 2 := by
    have k1 : latticeDist x y ^ 2 / (2 * σ * s ^ 2) ≤ latticeDist x y ^ 2 / (2 * σ * a ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)
    have k2 : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha has
    have k3 : 0 ≤ latticeDist x y ^ 2 / (2 * σ * s ^ 2) := by positivity
    have k4 : 0 ≤ 1 / s := by positivity
    have k5 : latticeDist x y ^ 2 / (2 * σ * a ^ 2) =
        1 / (2 * σ * a ^ 2) * latticeDist x y ^ 2 := by ring
    have k6 : latticeDist x y ^ 2 ≤ (1 + latticeDist x y) ^ 2 := by nlinarith
    have k7 : (1 : ℝ) ≤ (1 + latticeDist x y) ^ 2 := by nlinarith
    have k8 : 0 ≤ 1 / (2 * σ * a ^ 2) := by positivity
    have k9 : 0 ≤ 1 / a := by positivity
    have k10 := mul_le_mul_of_nonneg_left k6 k8
    have k11 := mul_le_mul_of_nonneg_left k7 k9
    rw [abs_le]
    constructor <;> nlinarith
  calc latticeGaussian σ s x y * |latticeDist x y ^ 2 / (2 * σ * s ^ 2) - 1 / s|
      ≤ ((2 * Real.pi * σ * a)⁻¹ * Real.exp (-(latticeDist x y ^ 2 / (2 * σ * b)))) *
          ((1 / (2 * σ * a ^ 2) + 1 / a) * (1 + latticeDist x y) ^ 2) :=
        mul_le_mul hg h1 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **The two-scale form is dominated by the neighbour envelope of `λ_c`.** -/
theorem abs_twoScale_le {P : Vertex 2 → ℝ} {χ : Fin 2 → Vertex 2 → ℝ} {M A c : ℝ}
    {y x : Vertex 2} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hP : ∀ z, |P z| ≤ M * ((1 + latticeDist z y) ^ 2 * Real.exp (-(latticeDist z y ^ 2 / c))))
    (hχ : ∀ k, |χ k x| ≤ A * (1 + latticeDist x y)) :
    |P x + ∑ k : Fin 2, (P (x + unit k) - P x) * χ k x| ≤
      M * (1 + 2 * A) * nbrEnv (gaussEnv c y) x := by
  set g := gaussEnv c y with hg
  set L : Vertex 2 → ℝ := fun z =>
    (1 + latticeDist z y) ^ 2 * Real.exp (-(latticeDist z y ^ 2 / c)) with hL
  have hd : ∀ z, 0 ≤ latticeDist z y := fun z => latticeDist_nonneg z y
  have hL0 : ∀ z, 0 ≤ L z := fun z => by simp only [hL]; positivity
  have hgL : ∀ z, g z = (1 + latticeDist z y) * L z := fun z => by
    simp only [hg, hL, gaussEnv]
    ring
  have hLg : ∀ z, L z ≤ g z := fun z => by
    rw [hgL z]
    have := hd z
    nlinarith [hL0 z]
  have hsh : ∀ k : Fin 2, (1 + latticeDist x y) * L (x + unit k) ≤ 2 * g (x + unit k) := by
    intro k
    have h1 : latticeDist x y ≤ latticeDist (x + unit k) y + 1 := by
      have := latticeDist_triangle x (x + unit k) y
      have h2 : latticeDist (x + unit k) x = 1 := latticeDist_add_single x k
      linarith
    rw [hgL]
    have := hL0 (x + unit k)
    have := hd (x + unit k)
    nlinarith
  have hk : ∀ k : Fin 2, |(P (x + unit k) - P x) * χ k x| ≤
      M * A * (2 * g (x + unit k) + g x) := by
    intro k
    rw [abs_mul]
    have h1 : |P (x + unit k) - P x| ≤ M * (L (x + unit k) + L x) := by
      have := abs_add_le (P (x + unit k)) (-(P x))
      rw [abs_neg, ← sub_eq_add_neg] at this
      have a1 := hP (x + unit k)
      have a2 := hP x
      simp only [hL] at a1 a2 ⊢
      linarith
    have h2 := mul_le_mul h1 (hχ k) (abs_nonneg _) (by have := hL0 x; positivity)
    have h3 := hsh k
    have h4 : (1 + latticeDist x y) * L x = g x := (hgL x).symm
    have hMA : 0 ≤ M * A := mul_nonneg hM hA
    calc |P (x + unit k) - P x| * |χ k x| ≤ M * (L (x + unit k) + L x) * (A * (1 + latticeDist x y)) :=
          h2
      _ = M * A * ((1 + latticeDist x y) * L (x + unit k) + (1 + latticeDist x y) * L x) := by
          ring
      _ ≤ M * A * (2 * g (x + unit k) + g x) := by
          rw [h4]
          exact mul_le_mul_of_nonneg_left (by linarith) hMA
  have hP0 : |P x| ≤ M * g x := (hP x).trans (mul_le_mul_of_nonneg_left (hLg x) hM)
  have hsum : |P x + ∑ k : Fin 2, (P (x + unit k) - P x) * χ k x| ≤
      M * g x + (M * A * (2 * g (x + unit 0) + g x) + M * A * (2 * g (x + unit 1) + g x)) := by
    refine (abs_add_le _ _).trans (add_le_add hP0 ?_)
    rw [Fin.sum_univ_two]
    exact (abs_add_le _ _).trans (add_le_add (hk 0) (hk 1))
  refine hsum.trans ?_
  simp only [nbrEnv, Fin.sum_univ_two]
  have g1 := gaussEnv_nonneg c y (x + unit 0)
  have g2 := gaussEnv_nonneg c y (x - unit 0)
  have g3 := gaussEnv_nonneg c y (x + unit 1)
  have g4 := gaussEnv_nonneg c y (x - unit 1)
  have g5 := gaussEnv_nonneg c y x
  have hMA : 0 ≤ M * A := mul_nonneg hM hA
  have m1 := mul_nonneg hM g1
  have m2 := mul_nonneg hM g2
  have m3 := mul_nonneg hM g3
  have m4 := mul_nonneg hM g4
  have m5 := mul_nonneg hM g5
  have n2 := mul_nonneg hMA g2
  have n4 := mul_nonneg hMA g4
  have n5 := mul_nonneg hMA g5
  nlinarith

end Rigidity.Green
