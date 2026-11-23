import Rigidity.Proofs.Green.DarioGuGaussian

/-!
# Differences of the one-dimensional Gaussian

Step 4 of the proof of Proposition 4.3 of Dario–Gu compares the discrete and the continuous
derivatives of the heat kernel `p̄`. The planar kernel is a product of one-dimensional Gaussians
`g(u) = exp(-u²/c)` (`gauss1`, `c = 2σt`), whose derivatives are explicit:
`g' = -(2u/c) g`, `g'' = (4u²/c² - 2/c) g`, `g''' = (-8u³/c³ + 12u/c²) g`. By the mean value
theorem the lattice differences are values of the derivatives:

* `exists_sub_eq_gauss1'`: `g(n + 1) - g(n) = g'(ξ)`, `ξ ∈ (n, n + 1)`;
* `exists_secondDiff_eq`: `g(n + 2) - 2g(n + 1) + g(n) = g''(ξ)`, `ξ ∈ (n, n + 2)`;
* `exists_secondDiff_sub_eq`: `g(n + 2) - 2g(n + 1) + g(n) - g''(n) = (ξ - n) g'''(ζ)`,
  `ζ ∈ (n, n + 2)`, `ξ - n ∈ (0, 2)`;
* `abs_gauss1'_le`, `abs_gauss1''_le`, `abs_gauss1'''_le`: `|g^{(k)}(u)| ≤ K_k c^{-k/2} exp(-u²/(8c))`.
-/

namespace Rigidity.Green

/-- The one-dimensional Gaussian `g(u) = exp(-u²/c)`. -/
noncomputable def gauss1 (c u : ℝ) : ℝ := Real.exp (-(u ^ 2 / c))

/-- `g'(u) = -(2u/c) g(u)`. -/
noncomputable def gauss1' (c u : ℝ) : ℝ := -(2 * u / c) * gauss1 c u

/-- `g''(u) = (4u²/c² - 2/c) g(u)`. -/
noncomputable def gauss1'' (c u : ℝ) : ℝ := (4 * u ^ 2 / c ^ 2 - 2 / c) * gauss1 c u

/-- `g'''(u) = (-8u³/c³ + 12u/c²) g(u)`. -/
noncomputable def gauss1''' (c u : ℝ) : ℝ := (-(8 * u ^ 3 / c ^ 3) + 12 * u / c ^ 2) * gauss1 c u

theorem gauss1_pos (c u : ℝ) : 0 < gauss1 c u := Real.exp_pos _

theorem hasDerivAt_gauss1 (c u : ℝ) :
    HasDerivAt (gauss1 c) (gauss1' c u) u := by
  have h := (((hasDerivAt_pow 2 u).div_const c).neg).exp
  refine h.congr_deriv ?_
  unfold gauss1' gauss1
  simp only [Pi.neg_apply]
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  push_cast
  ring

theorem hasDerivAt_gauss1' {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (gauss1' c) (gauss1'' c u) u := by
  have h := (((hasDerivAt_id u).const_mul 2).div_const c).neg.mul (hasDerivAt_gauss1 c u)
  refine h.congr_deriv ?_
  unfold gauss1'' gauss1' gauss1
  simp only [Pi.neg_apply, id]
  field_simp
  ring

theorem hasDerivAt_gauss1'' {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    HasDerivAt (gauss1'' c) (gauss1''' c u) u := by
  have h := ((((hasDerivAt_pow 2 u).const_mul 4).div_const (c ^ 2)).sub_const (2 / c)).mul
    (hasDerivAt_gauss1 c u)
  refine h.congr_deriv ?_
  unfold gauss1''' gauss1' gauss1
  field_simp
  ring

/-- `g(n + 1) - g(n) = g'(ξ)` for some `ξ ∈ (n, n + 1)`. -/
theorem exists_sub_eq_gauss1' (c n : ℝ) :
    ∃ ξ ∈ Set.Ioo n (n + 1), gauss1 c (n + 1) - gauss1 c n = gauss1' c ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (gauss1 c) (gauss1' c) (by linarith : n < n + 1)
    (fun u _ => (hasDerivAt_gauss1 c u).continuousAt.continuousWithinAt)
    (fun u _ => hasDerivAt_gauss1 c u)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, add_sub_cancel_left, div_one]

/-- `g'(n + 1) - g'(n) = g''(ξ)` for some `ξ ∈ (n, n + 1)`. -/
theorem exists_sub_eq_gauss1'' {c : ℝ} (hc : c ≠ 0) (n : ℝ) :
    ∃ ξ ∈ Set.Ioo n (n + 1), gauss1' c (n + 1) - gauss1' c n = gauss1'' c ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope (gauss1' c) (gauss1'' c)
    (by linarith : n < n + 1)
    (fun u _ => (hasDerivAt_gauss1' hc u).continuousAt.continuousWithinAt)
    (fun u _ => hasDerivAt_gauss1' hc u)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, add_sub_cancel_left, div_one]

/-- `g''(b) - g''(a) = (b - a) g'''(ζ)` for some `ζ ∈ (a, b)`. -/
theorem exists_sub_eq_gauss1''' {c : ℝ} (hc : c ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ ζ ∈ Set.Ioo a b, gauss1'' c b - gauss1'' c a = (b - a) * gauss1''' c ζ := by
  obtain ⟨ζ, hζ, h⟩ := exists_hasDerivAt_eq_slope (gauss1'' c) (gauss1''' c) hab
    (fun u _ => (hasDerivAt_gauss1'' hc u).continuousAt.continuousWithinAt)
    (fun u _ => hasDerivAt_gauss1'' hc u)
  refine ⟨ζ, hζ, ?_⟩
  rw [h]
  field_simp [(sub_pos.2 hab).ne']

/-- `g(n + 2) - 2 g(n + 1) + g(n) = g''(ξ)` for some `ξ ∈ (n, n + 2)`. -/
theorem exists_secondDiff_eq {c : ℝ} (hc : c ≠ 0) (n : ℝ) :
    ∃ ξ ∈ Set.Ioo n (n + 2),
      gauss1 c (n + 2) - 2 * gauss1 c (n + 1) + gauss1 c n = gauss1'' c ξ := by
  have hd : ∀ u, HasDerivAt (fun u => gauss1 c (u + 1) - gauss1 c u)
      (gauss1' c (u + 1) - gauss1' c u) u := fun u =>
    ((hasDerivAt_gauss1 c (u + 1)).comp_add_const u 1).sub (hasDerivAt_gauss1 c u)
  obtain ⟨η, hη, h⟩ := exists_hasDerivAt_eq_slope (fun u => gauss1 c (u + 1) - gauss1 c u)
    (fun u => gauss1' c (u + 1) - gauss1' c u) (by linarith : n < n + 1)
    (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => hd u)
  obtain ⟨ξ, hξ, h2⟩ := exists_sub_eq_gauss1'' hc η
  refine ⟨ξ, ⟨by linarith [hη.1, hξ.1], by linarith [hη.2, hξ.2]⟩, ?_⟩
  rw [← h2, h, add_sub_cancel_left, div_one, show n + 1 + 1 = n + 2 by ring]
  ring

/-- `g(n + 2) - 2 g(n + 1) + g(n) - g''(n) = (ξ - n) g'''(ζ)` with `0 < ξ - n < 2` and
`ζ ∈ (n, n + 2)`. -/
theorem exists_secondDiff_sub_eq {c : ℝ} (hc : c ≠ 0) (n : ℝ) :
    ∃ ξ ζ : ℝ, 0 < ξ - n ∧ ξ - n < 2 ∧ ζ ∈ Set.Ioo n (n + 2) ∧
      gauss1 c (n + 2) - 2 * gauss1 c (n + 1) + gauss1 c n - gauss1'' c n =
        (ξ - n) * gauss1''' c ζ := by
  obtain ⟨ξ, hξ, h⟩ := exists_secondDiff_eq hc n
  obtain ⟨ζ, hζ, h2⟩ := exists_sub_eq_gauss1''' hc hξ.1
  refine ⟨ξ, ζ, by linarith [hξ.1], by linarith [hξ.2], ⟨hζ.1, hζ.2.trans hξ.2⟩, ?_⟩
  rw [h, h2]

/-- `|u| exp(-u²/c) ≤ √c exp(-u²/(2c))`. -/
theorem abs_mul_gauss1_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |u| * gauss1 c u ≤ Real.sqrt c * gauss1 (2 * c) u := by
  unfold gauss1
  have h := mul_exp_neg_sq_le hc (abs_nonneg u)
  rwa [sq_abs] at h

theorem gauss1_mono {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') (u : ℝ) : gauss1 c u ≤ gauss1 c' u := by
  unfold gauss1
  exact Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg u) hc hcc))

/-- `|g'(u)| ≤ 2 c^{-1/2} exp(-u²/(8c))`. -/
theorem abs_gauss1'_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |gauss1' c u| ≤ 2 / Real.sqrt c * gauss1 (8 * c) u := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have h1 := abs_mul_gauss1_le hc u
  have h2 := gauss1_mono (by positivity : 0 < 2 * c) (by linarith : 2 * c ≤ 8 * c) u
  unfold gauss1'
  rw [abs_mul, abs_of_pos (gauss1_pos c u), abs_neg, abs_div, abs_mul, abs_of_pos hc,
    abs_two]
  have e : 2 * |u| / c * gauss1 c u = 2 / c * (|u| * gauss1 c u) := by ring
  have e2 : 2 / c * Real.sqrt c = 2 / Real.sqrt c := by
    rw [div_mul_eq_mul_div, div_eq_div_iff hc.ne' hsc.ne', mul_assoc, Real.mul_self_sqrt hc.le]
  rw [e]
  calc 2 / c * (|u| * gauss1 c u) ≤ 2 / c * (Real.sqrt c * gauss1 (2 * c) u) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 / Real.sqrt c * gauss1 (2 * c) u := by rw [← mul_assoc, e2]
    _ ≤ 2 / Real.sqrt c * gauss1 (8 * c) u := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `u² exp(-u²/c) ≤ √2 c exp(-u²/(4c))`. -/
theorem sq_mul_gauss1_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    u ^ 2 * gauss1 c u ≤ Real.sqrt 2 * c * gauss1 (4 * c) u := by
  have h1 := abs_mul_gauss1_le hc u
  have h2 := abs_mul_gauss1_le (by positivity : 0 < 2 * c) u
  have e : u ^ 2 * gauss1 c u = |u| * (|u| * gauss1 c u) := by
    rw [← mul_assoc, ← sq, sq_abs]
  rw [e]
  calc |u| * (|u| * gauss1 c u) ≤ |u| * (Real.sqrt c * gauss1 (2 * c) u) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = Real.sqrt c * (|u| * gauss1 (2 * c) u) := by ring
    _ ≤ Real.sqrt c * (Real.sqrt (2 * c) * gauss1 (2 * (2 * c)) u) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * c * gauss1 (4 * c) u := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), show 2 * (2 * c) = 4 * c by ring]
        have hcc := Real.mul_self_sqrt hc.le
        have e2 : Real.sqrt c * (Real.sqrt 2 * Real.sqrt c * gauss1 (4 * c) u) =
            Real.sqrt 2 * (Real.sqrt c * Real.sqrt c) * gauss1 (4 * c) u := by ring
        rw [e2, hcc]

/-- `|g''(u)| ≤ 8 c^{-1} exp(-u²/(8c))`. -/
theorem abs_gauss1''_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |gauss1'' c u| ≤ 8 / c * gauss1 (8 * c) u := by
  have h1 := sq_mul_gauss1_le hc u
  have h2 := gauss1_mono (by positivity : 0 < 4 * c) (by linarith : 4 * c ≤ 8 * c) u
  have h3 := gauss1_mono hc (by linarith : c ≤ 8 * c) u
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hg := gauss1_pos c u
  have hg8 := gauss1_pos (8 * c) u
  unfold gauss1''
  rw [abs_mul, abs_of_pos hg]
  have hb : |4 * u ^ 2 / c ^ 2 - 2 / c| ≤ 4 * u ^ 2 / c ^ 2 + 2 / c := by
    have : 0 ≤ 4 * u ^ 2 / c ^ 2 := by positivity
    have : 0 ≤ 2 / c := by positivity
    rw [abs_le]
    constructor <;> linarith
  calc |4 * u ^ 2 / c ^ 2 - 2 / c| * gauss1 c u ≤ (4 * u ^ 2 / c ^ 2 + 2 / c) * gauss1 c u :=
        mul_le_mul_of_nonneg_right hb hg.le
    _ = 4 / c ^ 2 * (u ^ 2 * gauss1 c u) + 2 / c * gauss1 c u := by ring
    _ ≤ 4 / c ^ 2 * (Real.sqrt 2 * c * gauss1 (8 * c) u) + 2 / c * gauss1 (8 * c) u :=
        add_le_add (mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2
          (by positivity))) (by positivity)) (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = (4 * Real.sqrt 2 + 2) / c * gauss1 (8 * c) u := by
        field_simp
    _ ≤ 8 / c * gauss1 (8 * c) u := by
        gcongr
        linarith

/-- `|u|³ exp(-u²/c) ≤ 2√2 c^{3/2} exp(-u²/(8c))`. -/
theorem abs_pow_three_mul_gauss1_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |u| ^ 3 * gauss1 c u ≤ 2 * Real.sqrt 2 * c * Real.sqrt c * gauss1 (8 * c) u := by
  have h1 := abs_mul_gauss1_le hc u
  have h2 := sq_mul_gauss1_le (by positivity : 0 < 2 * c) u
  have e : |u| ^ 3 * gauss1 c u = u ^ 2 * (|u| * gauss1 c u) := by
    rw [show |u| ^ 3 = |u| ^ 2 * |u| by ring, sq_abs]
    ring
  rw [e]
  calc u ^ 2 * (|u| * gauss1 c u) ≤ u ^ 2 * (Real.sqrt c * gauss1 (2 * c) u) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = Real.sqrt c * (u ^ 2 * gauss1 (2 * c) u) := by ring
    _ ≤ Real.sqrt c * (Real.sqrt 2 * (2 * c) * gauss1 (4 * (2 * c)) u) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt 2 * c * Real.sqrt c * gauss1 (8 * c) u := by
        rw [show 4 * (2 * c) = 8 * c by ring]
        ring

/-- `|g'''(u)| ≤ 40 c^{-3/2} exp(-u²/(8c))`. -/
theorem abs_gauss1'''_le {c : ℝ} (hc : 0 < c) (u : ℝ) :
    |gauss1''' c u| ≤ 40 / (c * Real.sqrt c) * gauss1 (8 * c) u := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have h3 := abs_pow_three_mul_gauss1_le hc u
  have h1 := abs_mul_gauss1_le hc u
  have h1' := gauss1_mono (by positivity : 0 < 2 * c) (by linarith : 2 * c ≤ 8 * c) u
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hg := gauss1_pos c u
  have hg8 := gauss1_pos (8 * c) u
  have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  unfold gauss1'''
  rw [abs_mul, abs_of_pos hg]
  have hb : |-(8 * u ^ 3 / c ^ 3) + 12 * u / c ^ 2| ≤ 8 * |u| ^ 3 / c ^ 3 + 12 * |u| / c ^ 2 := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_neg, abs_div, abs_div, abs_mul, abs_mul, abs_pow, abs_of_pos (pow_pos hc 3),
      abs_of_pos (pow_pos hc 2)]
    norm_num
  calc |-(8 * u ^ 3 / c ^ 3) + 12 * u / c ^ 2| * gauss1 c u
      ≤ (8 * |u| ^ 3 / c ^ 3 + 12 * |u| / c ^ 2) * gauss1 c u :=
        mul_le_mul_of_nonneg_right hb hg.le
    _ = 8 / c ^ 3 * (|u| ^ 3 * gauss1 c u) + 12 / c ^ 2 * (|u| * gauss1 c u) := by ring
    _ ≤ 8 / c ^ 3 * (2 * Real.sqrt 2 * c * Real.sqrt c * gauss1 (8 * c) u) +
          12 / c ^ 2 * (Real.sqrt c * gauss1 (8 * c) u) :=
        add_le_add (mul_le_mul_of_nonneg_left h3 (by positivity))
          (mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h1' hsc.le))
            (by positivity))
    _ = (16 * Real.sqrt 2 + 12) / (c * Real.sqrt c) * gauss1 (8 * c) u := by
        set r := Real.sqrt c with hr
        have hr0 : r ≠ 0 := hsc.ne'
        have hc' : c = r ^ 2 := (Real.sq_sqrt hc.le).symm
        rw [hc']
        field_simp
        ring
    _ ≤ 40 / (c * Real.sqrt c) * gauss1 (8 * c) u := by
        gcongr
        linarith

end Rigidity.Green
