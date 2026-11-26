import Rigidity.Proofs.Green.GaussianProductD

/-!
# Moving the centre of a Gaussian kernel

* `exp_neg_sub_exp_neg_le`: `e^{-a} - e^{-b} ≤ (b - a) e^{-a}`;
* `abs_gaussianHeatD_sub_le`: for `|u - v| ≤ ρ`,
  `|p̄(s, u) - p̄(s, v)| ≤ ρ (2|u| + ρ)/(2σs) e^{ρ²/(2σs)} (2πσs)^{-d/2} e^{-|u|²/(4σs)}`;
* `mul_exp_neg_sq_div_le`: `x e^{-x²/c} ≤ √c` for `x ≥ 0`, `c > 0`.

Summed over the lattice these move the centre of the Gaussian at the midpoint of two lattice
points to the nearest lattice point at a cost `O(s^{-1/2})` in the mass.
-/

namespace Rigidity.Green

theorem exp_neg_sub_exp_neg_le (a b : ℝ) :
    Real.exp (-a) - Real.exp (-b) ≤ (b - a) * Real.exp (-a) := by
  have h := Real.add_one_le_exp (-(b - a))
  have e : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have := Real.exp_pos (-a)
  nlinarith

theorem abs_exp_neg_sub_exp_neg_le_of_ge {a b m : ℝ} (ha : m ≤ a) (hb : m ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |b - a| * Real.exp (-m) := by
  rcases le_total a b with hab | hab
  · have h1 := exp_neg_sub_exp_neg_le a b
    have h2 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    calc _ ≤ (b - a) * Real.exp (-a) := h1
      _ ≤ (b - a) * Real.exp (-m) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by linarith)
  · have h1 := exp_neg_sub_exp_neg_le b a
    have h2 : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    calc _ = Real.exp (-b) - Real.exp (-a) := by ring
      _ ≤ (a - b) * Real.exp (-b) := h1
      _ ≤ (a - b) * Real.exp (-m) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by linarith)
      _ = _ := by ring

theorem mul_exp_neg_sq_div_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    x * Real.exp (-(x ^ 2 / c)) ≤ Real.sqrt c := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsc2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  rcases le_total x (Real.sqrt c) with h | h
  · calc x * Real.exp (-(x ^ 2 / c)) ≤ x * 1 :=
          mul_le_mul_of_nonneg_left (by rw [Real.exp_le_one_iff, neg_nonpos]; positivity) hx
      _ ≤ _ := by linarith
  · have h1 := Real.add_one_le_exp (x ^ 2 / c)
    have hE : x ^ 2 / c ≤ Real.exp (x ^ 2 / c) := by linarith
    have hx2 : x * Real.sqrt c ≤ x ^ 2 / c * Real.sqrt c ^ 2 := by
      rw [hsc2, div_mul_cancel₀ _ hc.ne']; nlinarith
    have : x ≤ Real.sqrt c * Real.exp (x ^ 2 / c) := by
      have h3 : x * Real.sqrt c ≤ Real.exp (x ^ 2 / c) * Real.sqrt c ^ 2 :=
        hx2.trans (mul_le_mul_of_nonneg_right hE (sq_nonneg _))
      nlinarith
    calc x * Real.exp (-(x ^ 2 / c)) ≤ Real.sqrt c * Real.exp (x ^ 2 / c) *
          Real.exp (-(x ^ 2 / c)) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = Real.sqrt c := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

variable {d : ℕ}

/-- **Moving the centre of a Gaussian kernel.** -/
theorem abs_gaussianHeatD_sub_le {σ s ρ : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hρ : 0 ≤ ρ)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : ‖u - v‖ ≤ ρ) :
    |gaussianHeatD d σ s u - gaussianHeatD d σ s v| ≤
      ρ * (2 * ‖u‖ + ρ) / (2 * σ * s) * Real.exp (ρ ^ 2 / (2 * σ * s)) *
        ((2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖u‖ ^ 2 / (4 * σ * s)))) := by
  unfold gaussianHeatD
  have hc : 0 < 2 * σ * s := by positivity
  set P := (2 * Real.pi * σ * s) ^ (-((d : ℝ) / 2)) with hP
  have hP0 : 0 ≤ P := by positivity
  have hnu := norm_nonneg u
  have hnv := norm_nonneg v
  have htri1 : ‖v‖ ≤ ‖u‖ + ρ := by
    have := norm_sub_norm_le v u
    rw [norm_sub_rev] at this
    linarith [norm_sub_rev u v]
  have htri2 : ‖u‖ ≤ ‖v‖ + ρ := by
    have := norm_sub_norm_le u v
    linarith
  set m := (‖u‖ ^ 2 / 2 - ρ ^ 2) / (2 * σ * s) with hm
  have hma : m ≤ ‖u‖ ^ 2 / (2 * σ * s) := by
    rw [hm]; apply div_le_div_of_nonneg_right _ hc.le; nlinarith
  have hmb : m ≤ ‖v‖ ^ 2 / (2 * σ * s) := by
    rw [hm]; apply div_le_div_of_nonneg_right _ hc.le
    nlinarith [sq_nonneg (‖v‖ - ρ), pow_le_pow_left₀ hnu htri2 2]
  have hdiff : |‖v‖ ^ 2 / (2 * σ * s) - ‖u‖ ^ 2 / (2 * σ * s)| ≤ ρ * (2 * ‖u‖ + ρ) / (2 * σ * s) := by
    rw [← sub_div, abs_div, abs_of_pos hc]
    apply div_le_div_of_nonneg_right _ hc.le
    rw [abs_le]
    constructor <;> nlinarith
  have hexp := abs_exp_neg_sub_exp_neg_le_of_ge hma hmb
  have hem : Real.exp (-m) = Real.exp (ρ ^ 2 / (2 * σ * s)) *
      Real.exp (-(‖u‖ ^ 2 / (4 * σ * s))) := by
    rw [← Real.exp_add, hm]
    congr 1
    field_simp
    ring
  rw [← mul_sub, abs_mul, abs_of_nonneg hP0]
  calc P * |Real.exp (-(‖u‖ ^ 2 / (2 * σ * s))) - Real.exp (-(‖v‖ ^ 2 / (2 * σ * s)))|
      ≤ P * (|‖v‖ ^ 2 / (2 * σ * s) - ‖u‖ ^ 2 / (2 * σ * s)| * Real.exp (-m)) :=
        mul_le_mul_of_nonneg_left hexp hP0
    _ ≤ P * (ρ * (2 * ‖u‖ + ρ) / (2 * σ * s) * Real.exp (-m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiff (Real.exp_pos _).le) hP0
    _ = _ := by rw [hem]; ring

end Rigidity.Green
