import Rigidity.Steps.S2.GreenGradientHomogenization
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Proposition 2.6, step:2.6-continuum: gradient and Taylor bounds for the homogenized Green function

`ContinuumGreenStep` (eqs. (green-gradient-estimate), (green-hessian-estimate),
(green-taylor-expansion) of the corrected draft): `‖∇Ḡ(v)‖ ≤ C |v|^{1-d}` and, for `2|w| ≤ |v|`,
`|Ḡ(v + w) - Ḡ(v) - ∇Ḡ(v)·w| ≤ C |w|² |v|^{-d}`.

The homogenized Green function is radial, `Ḡ(v) = Φ(|v|²)` off the pole with
`Φ'(t) = -β t^{-d/2}` (`greenBar_eq_radial`). For such a function, the chain rule gives the
gradient `∇Ḡ(v) = -2β |v|^{-d} v` (`hasFDerivAt_of_radial`), and the Taylor remainder is bounded by
applying the mean value inequality twice along the segment `t ↦ v + t w`, on which
`|v + t w| ≥ |v| / 2` (`taylor_of_radial`).
-/

namespace Rigidity.Proofs.S2

open Set Filter LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2
open scoped RealInnerProductSpace

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : E → ℝ} {Φ : ℝ → ℝ} {β m : ℝ}

/-- The gradient of a radial function `F(v) = Φ(|v|²)` with `Φ'(t) = -β t^{-m}`, off the
origin. -/
theorem hasFDerivAt_of_radial (hF : ∀ v, v ≠ 0 → F v = Φ (‖v‖ ^ 2))
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (-β * t ^ (-m)) t) {v : E} (hv : v ≠ 0) :
    HasFDerivAt F ((-β * (‖v‖ ^ 2) ^ (-m)) • (2 • innerSL ℝ v)) v := by
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  have h := HasDerivAt.comp_hasFDerivAt (f := fun u : E => ‖u‖ ^ 2) v (hΦ _ hn)
    (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hv] with u hu
  exact hF u hu

/-- The gradient bound `‖∇F(v)‖ ≤ 2 |β| (|v|²)^{-m} |v|` for a radial function. -/
theorem norm_fderiv_of_radial (hF : ∀ v, v ≠ 0 → F v = Φ (‖v‖ ^ 2))
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (-β * t ^ (-m)) t) {v : E} (hv : v ≠ 0) :
    ‖fderiv ℝ F v‖ ≤ 2 * |β| * (‖v‖ ^ 2) ^ (-m) * ‖v‖ := by
  rw [(hasFDerivAt_of_radial hF hΦ hv).fderiv]
  have hn : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  have h2 : ‖(2 • innerSL ℝ v : E →L[ℝ] ℝ)‖ ≤ 2 * ‖v‖ := by
    refine norm_nsmul_le.trans ?_
    rw [innerSL_apply_norm]
    norm_num
  calc ‖(-β * (‖v‖ ^ 2) ^ (-m)) • (2 • innerSL ℝ v)‖
        = |β| * (‖v‖ ^ 2) ^ (-m) * ‖(2 • innerSL ℝ v : E →L[ℝ] ℝ)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
            abs_of_pos (Real.rpow_pos_of_pos hn _)]
    _ ≤ |β| * (‖v‖ ^ 2) ^ (-m) * (2 * ‖v‖) := by
          gcongr
    _ = 2 * |β| * (‖v‖ ^ 2) ^ (-m) * ‖v‖ := by ring

/-- The Taylor bound `|F(v + w) - F(v) - ∇F(v)·w| ≤ |β| (36m + 2) 4^m |w|² (|v|²)^{-m}` for a
radial function `F(v) = Φ(|v|²)` with `Φ'(t) = -β t^{-m}`, when `2|w| ≤ |v|`. -/
theorem taylor_of_radial (hF : ∀ v, v ≠ 0 → F v = Φ (‖v‖ ^ 2))
    (hΦ : ∀ t, 0 < t → HasDerivAt Φ (-β * t ^ (-m)) t) (hm : 0 ≤ m) {v w : E} (hv : v ≠ 0)
    (hw : 2 * ‖w‖ ≤ ‖v‖) :
    |F (v + w) - F v - fderiv ℝ F v w| ≤
      |β| * (36 * m + 2) * 4 ^ m * ‖w‖ ^ 2 * (‖v‖ ^ 2) ^ (-m) := by
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hn : 0 < ‖v‖ ^ 2 := pow_pos hv0 2
  have hb : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  -- the squared norm along the segment, and its derivative
  let q : ℝ → ℝ := fun t => ‖v‖ ^ 2 + (2 * ⟪v, w⟫ * t + ‖w‖ ^ 2 * t ^ 2)
  let q' : ℝ → ℝ := fun t => 2 * ⟪v, w⟫ + 2 * ‖w‖ ^ 2 * t
  have hq : ∀ t : ℝ, ‖v + t • w‖ ^ 2 = q t := by
    intro t
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hqL : ∀ t ∈ Icc (0 : ℝ) 1, ‖v‖ ^ 2 / 4 ≤ q t := by
    intro t ht
    have h1 : ‖v‖ ≤ ‖v + t • w‖ + ‖t • w‖ := by
      simpa using norm_sub_le (v + t • w) (t • w)
    have h2 : ‖t • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have h3 : ‖v‖ / 2 ≤ ‖v + t • w‖ := by linarith
    calc ‖v‖ ^ 2 / 4 = (‖v‖ / 2) ^ 2 := by ring
      _ ≤ ‖v + t • w‖ ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
      _ = q t := hq t
  have hqpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < q t := fun t ht =>
    lt_of_lt_of_le (by positivity) (hqL t ht)
  have hq'sq : ∀ t ∈ Icc (0 : ℝ) 1, q' t ^ 2 ≤ 9 * ‖v‖ ^ 2 * ‖w‖ ^ 2 := by
    intro t ht
    have ha := abs_le.mp (abs_real_inner_le_norm v w)
    have hw2 : 2 * ‖w‖ ^ 2 ≤ ‖v‖ * ‖w‖ := by
      have := mul_le_mul_of_nonneg_right hw (norm_nonneg w)
      nlinarith
    have ht1 : ‖w‖ ^ 2 * t ≤ ‖w‖ ^ 2 := mul_le_of_le_one_right hb ht.2
    have ht0 : 0 ≤ ‖w‖ ^ 2 * t := mul_nonneg hb ht.1
    have h := sq_le_sq' (show -(3 * (‖v‖ * ‖w‖)) ≤ q' t by simp only [q']; linarith)
      (show q' t ≤ 3 * (‖v‖ * ‖w‖) by simp only [q']; linarith)
    linarith
  have hqd : ∀ t : ℝ, HasDerivAt q (q' t) t := by
    intro t
    have h := (((hasDerivAt_id' t).const_mul (2 * ⟪v, w⟫)).add
      ((hasDerivAt_pow 2 t).const_mul (‖w‖ ^ 2))).const_add (‖v‖ ^ 2)
    refine h.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hq'd : ∀ t : ℝ, HasDerivAt q' (2 * ‖w‖ ^ 2) t := by
    intro t
    have h := ((hasDerivAt_id' t).const_mul (2 * ‖w‖ ^ 2)).const_add (2 * ⟪v, w⟫)
    exact h.congr_deriv (mul_one _)
  -- first and second derivatives of `g t = Φ (q t)`
  let g' : ℝ → ℝ := fun t => -β * q t ^ (-m) * q' t
  let g'' : ℝ → ℝ := fun t =>
    -β * (q' t * -m * q t ^ (-m - 1)) * q' t + -β * q t ^ (-m) * (2 * ‖w‖ ^ 2)
  have hgd : ∀ t, 0 < q t → HasDerivAt (fun t => Φ (q t)) (g' t) t := fun t ht =>
    (hΦ _ ht).comp t (hqd t)
  have hg'd : ∀ t, 0 < q t → HasDerivAt g' (g'' t) t := fun t ht =>
    ((((hqd t).rpow_const (Or.inl ht.ne')).const_mul (-β)).mul (hq'd t))
  set D := |β| * (36 * m + 2) * 4 ^ m * ‖w‖ ^ 2 * (‖v‖ ^ 2) ^ (-m) with hD
  have hD0 : 0 ≤ D := by positivity
  have hg''le : ∀ t ∈ Icc (0 : ℝ) 1, |g'' t| ≤ D := by
    intro t ht
    have hQ := hqL t ht
    have hQpos := hqpos t ht
    have hP : 0 < q t ^ (-m) := Real.rpow_pos_of_pos hQpos _
    have hPle : q t ^ (-m) ≤ (‖v‖ ^ 2) ^ (-m) * 4 ^ m := by
      calc q t ^ (-m) ≤ (‖v‖ ^ 2 / 4) ^ (-m) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hQ (by linarith)
        _ = (‖v‖ ^ 2) ^ (-m) * 4 ^ m := by
            rw [Real.div_rpow hn.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
              div_inv_eq_mul]
    have hsq : q' t ^ 2 / q t ≤ 36 * ‖w‖ ^ 2 := by
      rw [div_le_iff₀ hQpos]
      nlinarith [hq'sq t ht, mul_le_mul_of_nonneg_right hQ hb]
    have hX0 : 0 ≤ m * (q' t ^ 2 / q t) := mul_nonneg hm (by positivity)
    have hX : m * (q' t ^ 2 / q t) ≤ m * (36 * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hsq hm
    have heq : g'' t = β * q t ^ (-m) * (m * (q' t ^ 2 / q t) - 2 * ‖w‖ ^ 2) := by
      simp only [g'']
      rw [Real.rpow_sub_one hQpos.ne']
      ring
    have hY : |m * (q' t ^ 2 / q t) - 2 * ‖w‖ ^ 2| ≤ (36 * m + 2) * ‖w‖ ^ 2 :=
      abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    rw [heq, abs_mul, abs_mul, abs_of_pos hP]
    calc |β| * q t ^ (-m) * |m * (q' t ^ 2 / q t) - 2 * ‖w‖ ^ 2|
        ≤ |β| * ((‖v‖ ^ 2) ^ (-m) * 4 ^ m) * ((36 * m + 2) * ‖w‖ ^ 2) := by
          gcongr
      _ = D := by rw [hD]; ring
  -- the mean value inequality, twice
  have hMV1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t - g' 0‖ ≤ D * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := g') (f' := g'')
      (fun t ht => (hg'd t (hqpos t ht)).hasDerivWithinAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hg''le t (Ico_subset_Icc_self ht))
  have hφd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t => Φ (q t) - t * g' 0)
      (g' t - 1 * g' 0) (Icc 0 1) t := fun t ht =>
    ((hgd t (hqpos t ht)).sub ((hasDerivAt_id' t).mul_const (g' 0))).hasDerivWithinAt
  have hMV2 := norm_image_sub_le_of_norm_deriv_le_segment' (C := D) hφd
    (fun t ht => by
      rw [one_mul]
      refine (hMV1 t (Ico_subset_Icc_self ht)).trans ?_
      have := ht.2.le
      nlinarith [ht.1]) 1 ⟨zero_le_one, le_rfl⟩
  -- identification of the endpoints and of the gradient term
  have hq1 : ‖v + w‖ ^ 2 = q 1 := by simpa using hq 1
  have hvw : v + w ≠ 0 := by
    intro h
    have h1 := hqL 1 ⟨zero_le_one, le_rfl⟩
    rw [← hq1, h, norm_zero] at h1
    have : 0 < ‖v‖ ^ 2 / 4 := by positivity
    norm_num at h1
    linarith
  have hq0 : q 0 = ‖v‖ ^ 2 := by simp [q]
  have hfd : fderiv ℝ F v w = g' 0 := by
    rw [(hasFDerivAt_of_radial hF hΦ hv).fderiv]
    simp [g', q', hq0]
  have key : F (v + w) - F v - fderiv ℝ F v w =
      (Φ (q 1) - 1 * g' 0) - (Φ (q 0) - 0 * g' 0) := by
    rw [hF _ hvw, hF _ hv, hq1, hq0, hfd]
    ring
  rw [key, ← Real.norm_eq_abs]
  linarith

end Radial

/-- The homogenized Green function is radial: `Ḡ(v) = Φ(|v|²)` off the pole, with
`Φ'(t) = -β t^{-d/2}` (`Φ(t) = -log t / (4πκ)` if `d = 2`, `Φ(t) = K t^{(2-d)/2}` if `d ≥ 3`). -/
theorem greenBar_eq_radial {d : ℕ} (hd : 2 ≤ d) (κ : {a : ℝ // 0 < a}) :
    ∃ (Φ : ℝ → ℝ) (β : ℝ), (∀ v, v ≠ 0 → greenBar d hd κ v = Φ (‖v‖ ^ 2)) ∧
      ∀ t : ℝ, 0 < t → HasDerivAt Φ (-β * t ^ (-((d : ℝ) / 2))) t := by
  have hκ := κ.2
  by_cases h2 : d = 2
  · subst h2
    refine ⟨fun t => -Real.log t / (4 * Real.pi * κ.val), 1 / (4 * Real.pi * κ.val), ?_, ?_⟩
    · intro v hv
      unfold greenBar continuumGreen
      rw [dif_pos hv, if_pos rfl]
      dsimp only
      rw [Real.log_pow]
      push_cast
      field_simp
      ring
    · intro t ht
      have h := ((Real.hasDerivAt_log ht.ne').neg).div_const (4 * Real.pi * κ.val)
      refine h.congr_deriv ?_
      rw [show -(((2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
      ring
  · set K := Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.rpow Real.pi ((d : ℝ) / 2) * κ.val)
    refine ⟨fun t => K * t ^ ((2 - (d : ℝ)) / 2), K * ((d : ℝ) - 2) / 2, ?_, ?_⟩
    · intro v hv
      unfold greenBar continuumGreen
      rw [dif_pos hv, if_neg h2]
      show K * ‖v‖ ^ (2 - (d : ℝ)) = K * (‖v‖ ^ 2) ^ ((2 - (d : ℝ)) / 2)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 2
      push_cast
      ring
    · intro t ht
      have h := (Real.hasDerivAt_rpow_const (p := (2 - (d : ℝ)) / 2) (Or.inl ht.ne')).const_mul K
      refine h.congr_deriv ?_
      rw [show (2 - (d : ℝ)) / 2 - 1 = -((d : ℝ) / 2) by ring]
      ring

/-- `(|v|²)^{-d/2} = |v|^{-d}`. -/
theorem sq_rpow_neg_half {d : ℕ} (r : ℝ) (hr : 0 ≤ r) :
    (r ^ 2) ^ (-((d : ℝ) / 2)) = r ^ (-(d : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

/-- step:2.6-continuum: `‖∇Ḡ(v)‖ ≤ C |v|^{1-d}` and, for `2|w| ≤ |v|`,
`|Ḡ(v + w) - Ḡ(v) - ∇Ḡ(v)·w| ≤ C |w|² |v|^{-d}`. -/
theorem continuumGreenStep (d : ℕ) (hd : 2 ≤ d) : ContinuumGreenStep d hd := by
  intro κ
  obtain ⟨Φ, β, hF, hΦ⟩ := greenBar_eq_radial hd κ
  have hm : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hB : 0 ≤ |β| * (36 * ((d : ℝ) / 2) + 2) * 4 ^ ((d : ℝ) / 2) := by positivity
  refine ⟨2 * |β| + |β| * (36 * ((d : ℝ) / 2) + 2) * 4 ^ ((d : ℝ) / 2) + 1, by positivity,
    fun v hv => ⟨?_, fun w hw => ?_⟩⟩
  · have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h := norm_fderiv_of_radial hF hΦ hv
    rw [sq_rpow_neg_half _ (norm_nonneg v)] at h
    calc ‖fderiv ℝ (greenBar d hd κ) v‖ ≤ 2 * |β| * ‖v‖ ^ (-(d : ℝ)) * ‖v‖ := h
      _ = 2 * |β| * ‖v‖ ^ (1 - (d : ℝ)) := by
          rw [sub_eq_add_neg, Real.rpow_add hv0, Real.rpow_one]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · have h := taylor_of_radial hF hΦ hm hv hw
    rw [sq_rpow_neg_half _ (norm_nonneg v)] at h
    refine h.trans ?_
    have hX : 0 ≤ ‖v‖ ^ (-(d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hX
    linarith [abs_nonneg β]

end Rigidity.Proofs.S2
