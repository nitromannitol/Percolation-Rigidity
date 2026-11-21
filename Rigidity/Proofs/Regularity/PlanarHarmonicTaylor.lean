import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

/-!
# First-order Taylor expansion of planar harmonic functions

A function `f : ℂ → ℝ` harmonic on the disc `B_R(c)` with `|f| ≤ M` there is the real part of a
holomorphic function `F` (`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`). The
Borel–Carathéodory theorem bounds `G = F - F(c)` by `4 M` on `B_{R/2}(c)`
(`norm_le_of_re_le_of_eq_zero`), the Cauchy estimate bounds `G''` by `128 M / R²` on `B_{R/4}(c)`,
and the mean value inequality gives the first-order Taylor expansion of `f` at `c`:
`|f(x) - f(c) - Re(q (x - c))| ≤ 128 M |x - c|² / R²` on `B_{R/4}(c)`
(`abs_sub_taylor_le_of_harmonicOnNhd`), the interior `C^{1,1}` estimate of harmonic functions
used for the excess decay of order one in the plane. The Cauchy estimate for `G'''` gives the
second-order expansion `|f(x) - f(c) - Re(q₁ (x - c)) - Re(q₂ (x - c)²)| ≤ 1536 M |x - c|³ / R³`
(`abs_sub_taylor_two_le_of_harmonicOnNhd`), used for the excess decay of order two.
-/

open Complex Metric

namespace Rigidity.Proofs.Regularity

/-- **Borel–Carathéodory on a disc.** A holomorphic `G` on `B_R(c)` with `G(c) = 0` and
`Re G ≤ M` is bounded by `2 M` on `B_{R/2}(c)`. -/
theorem norm_le_of_re_le_of_eq_zero {G : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hG : DifferentiableOn ℂ G (ball c R)) (hre : ∀ y ∈ ball c R, (G y).re ≤ M) (h0 : G c = 0)
    {y : ℂ} (hy : y ∈ ball c (R / 2)) : ‖G y‖ ≤ 2 * M := by
  set H : ℂ → ℂ := fun w => G (w + c) with hHdef
  have hmem : ∀ w ∈ ball (0 : ℂ) R, w + c ∈ ball c R := fun w hw => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    rw [mem_ball, dist_zero_right] at hw
    exact hw
  have hH : DifferentiableOn ℂ H (ball 0 R) := by
    intro w hw
    have hwc := hmem w hw
    exact (((hG (w + c) hwc).differentiableAt (isOpen_ball.mem_nhds hwc)).comp w
      (differentiableAt_id.add_const c)).differentiableWithinAt
  have hmaps : Set.MapsTo H (ball 0 R) {z | z.re ≤ M} := fun w hw => hre (w + c) (hmem w hw)
  have hyc : ‖y - c‖ < R / 2 := by rw [← dist_eq_norm]; exact mem_ball.1 hy
  have hw : y - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]; linarith
  have h := borelCaratheodory_zero hM hH hmaps hR hw (by simp [hHdef, h0])
  have e : H (y - c) = G y := by simp [hHdef]
  rw [e] at h
  have hpos : 0 < R - ‖y - c‖ := by linarith
  calc ‖G y‖ ≤ 2 * M * ‖y - c‖ / (R - ‖y - c‖) := h
    _ ≤ 2 * M := by
        rw [div_le_iff₀ hpos]
        nlinarith [norm_nonneg (y - c)]

/-- **First-order Taylor expansion of a planar harmonic function.** -/
theorem abs_sub_taylor_le_of_harmonicOnNhd {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (hf : InnerProductSpace.HarmonicOnNhd f (ball c R))
    (hfM : ∀ y ∈ ball c R, |f y| ≤ M) :
    ∃ q : ℂ, ∀ x ∈ ball c (R / 4),
      |f x - f c - (q * (x - c)).re| ≤ 128 * M * ‖x - c‖ ^ 2 / R ^ 2 := by
  obtain ⟨F, hFa, hFre⟩ := hf.exists_analyticOnNhd_ball_re_eq
  have hc : c ∈ ball c R := mem_ball_self hR
  set G : ℂ → ℂ := fun y => F y - F c with hGdef
  have hGa : AnalyticOnNhd ℂ G (ball c R) := hFa.sub analyticOnNhd_const
  have hGd : DifferentiableOn ℂ G (ball c R) := hGa.differentiableOn
  have hGre : ∀ y ∈ ball c R, (G y).re = f y - f c := fun y hy => by
    simp only [hGdef, sub_re]
    have h1 : (F y).re = f y := hFre hy
    have h2 : (F c).re = f c := hFre hc
    rw [h1, h2]
  have hG0 : G c = 0 := by simp [hGdef]
  have hre : ∀ y ∈ ball c R, (G y).re ≤ 2 * M := fun y hy => by
    rw [hGre y hy]
    have h1 := hfM y hy
    have h2 := hfM c hc
    have := (abs_le.1 h1).2
    have := (abs_le.1 h2).1
    linarith
  set D := deriv G with hD
  set K : ℝ := 128 * M / R ^ 2 with hK
  have hDa : AnalyticOnNhd ℂ D (ball c R) := hGa.deriv
  -- the Cauchy estimate for `G''` on `B_{R/4}(c)`
  have hD' : ∀ y ∈ ball c (R / 4), ‖deriv D y‖ ≤ K := by
    intro y hy
    have hyc : dist y c < R / 4 := mem_ball.1 hy
    have hsub : closedBall y (R / 4) ⊆ ball c R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      linarith [dist_triangle w y c]
    have hcl := hGd.diffContOnCl_ball hsub
    have hbound : ∀ w ∈ sphere y (R / 4), ‖G w‖ ≤ 2 * (2 * M) := by
      intro w hw
      rw [mem_sphere] at hw
      refine norm_le_of_re_le_of_eq_zero hR (by positivity) hGd hre hG0 ?_
      rw [mem_ball]
      linarith [dist_triangle w y c]
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 (by positivity) hcl
      hbound
    rw [iteratedDeriv_succ, iteratedDeriv_one] at h
    calc ‖deriv D y‖ ≤ (Nat.factorial 2 : ℝ) * (2 * (2 * M)) / (R / 4) ^ 2 := h
      _ = K := by rw [hK]; norm_num; field_simp; ring
  refine ⟨D c, fun x hx => ?_⟩
  have hxc : ‖x - c‖ < R / 4 := by rw [← dist_eq_norm]; exact mem_ball.1 hx
  set t := ‖x - c‖ with ht
  have hball : closedBall c t ⊆ ball c (R / 4) := closedBall_subset_ball hxc
  have hballR : ball c (R / 4) ⊆ ball c R := ball_subset_ball (by linarith)
  -- `D` is `K`-Lipschitz on `closedBall c t`
  have hLip : ∀ y ∈ closedBall c t, ‖D y - D c‖ ≤ K * ‖y - c‖ := by
    intro y hy
    exact (convex_ball c (R / 4)).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hDa w (hballR hw)).differentiableAt) hD' (mem_ball_self (by linarith))
      (hball hy)
  -- the remainder `g y = G y - D c (y - c)`
  set g : ℂ → ℂ := fun y => G y - D c * (y - c) with hgdef
  have hg : ∀ y ∈ closedBall c t, HasDerivAt g (D y - D c) y := by
    intro y hy
    have hGy : HasDerivAt G (D y) y :=
      (hGa y (hballR (hball hy))).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun y : ℂ => D c * (y - c)) (D c * 1) y :=
      ((hasDerivAt_id y).sub_const c).const_mul (D c)
    rw [mul_one] at h2
    exact hGy.sub h2
  have hgb : ∀ y ∈ closedBall c t, ‖deriv g y‖ ≤ K * t := by
    intro y hy
    rw [(hg y hy).deriv]
    refine (hLip y hy).trans ?_
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact mem_closedBall.1 hy) hK0
  have hmv := (convex_closedBall c t).norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hg y hy).differentiableAt) hgb (mem_closedBall_self (norm_nonneg _))
    (mem_closedBall.2 (by rw [dist_eq_norm]))
  have hgc : g c = 0 := by simp [hgdef, hG0]
  rw [hgc, sub_zero] at hmv
  have hre_eq : f x - f c - (D c * (x - c)).re = (g x).re := by
    simp only [hgdef, sub_re]
    rw [hGre x (hballR hx)]
  rw [hre_eq]
  calc |(g x).re| ≤ ‖g x‖ := abs_re_le_norm _
    _ ≤ K * t * ‖x - c‖ := hmv
    _ = 128 * M * ‖x - c‖ ^ 2 / R ^ 2 := by rw [hK, ht]; ring

/-- The first-order Taylor expansion of a planar harmonic function, for every bound `M ≥ 0`. -/
theorem abs_sub_taylor_le_of_harmonicOnNhd' {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hf : InnerProductSpace.HarmonicOnNhd f (ball c R))
    (hfM : ∀ y ∈ ball c R, |f y| ≤ M) :
    ∃ q : ℂ, ∀ x ∈ ball c (R / 4),
      |f x - f c - (q * (x - c)).re| ≤ 128 * M * ‖x - c‖ ^ 2 / R ^ 2 := by
  rcases hM.eq_or_lt with h0 | hpos
  · refine ⟨0, fun x hx => ?_⟩
    have hx' : x ∈ ball c R := ball_subset_ball (by linarith) hx
    have h1 : f x = 0 := abs_nonpos_iff.1 (h0 ▸ hfM x hx')
    have h2 : f c = 0 := abs_nonpos_iff.1 (h0 ▸ hfM c (mem_ball_self hR))
    rw [h1, h2, ← h0]
    simp
  · exact abs_sub_taylor_le_of_harmonicOnNhd hR hpos hf hfM

/-- **Second-order Taylor expansion of a planar harmonic function.** -/
theorem abs_sub_taylor_two_le_of_harmonicOnNhd {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (hf : InnerProductSpace.HarmonicOnNhd f (ball c R))
    (hfM : ∀ y ∈ ball c R, |f y| ≤ M) :
    ∃ q₁ q₂ : ℂ, ∀ x ∈ ball c (R / 4),
      |f x - f c - (q₁ * (x - c)).re - (q₂ * (x - c) ^ 2).re| ≤
        1536 * M * ‖x - c‖ ^ 3 / R ^ 3 := by
  obtain ⟨F, hFa, hFre⟩ := hf.exists_analyticOnNhd_ball_re_eq
  have hc : c ∈ ball c R := mem_ball_self hR
  set G : ℂ → ℂ := fun y => F y - F c with hGdef
  have hGa : AnalyticOnNhd ℂ G (ball c R) := hFa.sub analyticOnNhd_const
  have hGd : DifferentiableOn ℂ G (ball c R) := hGa.differentiableOn
  have hGre : ∀ y ∈ ball c R, (G y).re = f y - f c := fun y hy => by
    simp only [hGdef, sub_re]
    have h1 : (F y).re = f y := hFre hy
    have h2 : (F c).re = f c := hFre hc
    rw [h1, h2]
  have hG0 : G c = 0 := by simp [hGdef]
  have hre : ∀ y ∈ ball c R, (G y).re ≤ 2 * M := fun y hy => by
    rw [hGre y hy]
    have := (abs_le.1 (hfM y hy)).2
    have := (abs_le.1 (hfM c hc)).1
    linarith
  set D := deriv G with hD
  set D₂ := deriv D with hD₂
  set K : ℝ := 1536 * M / R ^ 3 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hDa : AnalyticOnNhd ℂ D (ball c R) := hGa.deriv
  have hD₂a : AnalyticOnNhd ℂ D₂ (ball c R) := hDa.deriv
  have hD₃ : ∀ y ∈ ball c (R / 4), ‖deriv D₂ y‖ ≤ K := by
    intro y hy
    have hyc : dist y c < R / 4 := mem_ball.1 hy
    have hsub : closedBall y (R / 4) ⊆ ball c R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      linarith [dist_triangle w y c]
    have hcl := hGd.diffContOnCl_ball hsub
    have hbound : ∀ w ∈ sphere y (R / 4), ‖G w‖ ≤ 2 * (2 * M) := by
      intro w hw
      rw [mem_sphere] at hw
      refine norm_le_of_re_le_of_eq_zero hR (by positivity) hGd hre hG0 ?_
      rw [mem_ball]
      linarith [dist_triangle w y c]
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3 (by positivity) hcl
      hbound
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at h
    calc ‖deriv D₂ y‖ ≤ (Nat.factorial 3 : ℝ) * (2 * (2 * M)) / (R / 4) ^ 3 := h
      _ = K := by rw [hK]; norm_num; field_simp; ring
  refine ⟨D c, D₂ c / 2, fun x hx => ?_⟩
  have hxc : ‖x - c‖ < R / 4 := by rw [← dist_eq_norm]; exact mem_ball.1 hx
  set t := ‖x - c‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hball : closedBall c t ⊆ ball c (R / 4) := closedBall_subset_ball hxc
  have hballR : ball c (R / 4) ⊆ ball c R := ball_subset_ball (by linarith)
  have hyt : ∀ y ∈ closedBall c t, ‖y - c‖ ≤ t := fun y hy => by
    rw [← dist_eq_norm]; exact mem_closedBall.1 hy
  -- `D₂` is `K`-Lipschitz on `closedBall c t`
  have hLip : ∀ y ∈ closedBall c t, ‖D₂ y - D₂ c‖ ≤ K * t := by
    intro y hy
    have := (convex_ball c (R / 4)).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hD₂a w (hballR hw)).differentiableAt) hD₃ (mem_ball_self (by linarith))
      (hball hy)
    exact this.trans (mul_le_mul_of_nonneg_left (hyt y hy) hK0)
  -- the first remainder `h₁ y = D y - D c - D₂ c (y - c)`
  set h₁ : ℂ → ℂ := fun y => D y - D c - D₂ c * (y - c) with hh₁
  have hh₁d : ∀ y ∈ closedBall c t, HasDerivAt h₁ (D₂ y - D₂ c) y := by
    intro y hy
    have hDy : HasDerivAt D (D₂ y) y := (hDa y (hballR (hball hy))).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun y : ℂ => D₂ c * (y - c)) (D₂ c * 1) y :=
      ((hasDerivAt_id y).sub_const c).const_mul (D₂ c)
    rw [mul_one] at h2
    exact (hDy.sub_const (D c)).sub h2
  have hh₁b : ∀ y ∈ closedBall c t, ‖h₁ y‖ ≤ K * t * t := by
    intro y hy
    have hmv := (convex_closedBall c t).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hh₁d w hw).differentiableAt)
      (fun w hw => by rw [(hh₁d w hw).deriv]; exact hLip w hw)
      (mem_closedBall_self ht0) hy
    have hc0 : h₁ c = 0 := by simp [hh₁]
    rw [hc0, sub_zero] at hmv
    exact hmv.trans (mul_le_mul_of_nonneg_left (hyt y hy) (mul_nonneg hK0 ht0))
  -- the remainder `h y = G y - D c (y - c) - D₂ c / 2 (y - c)²`
  set h : ℂ → ℂ := fun y => G y - D c * (y - c) - D₂ c / 2 * (y - c) ^ 2 with hhdef
  have hhd : ∀ y ∈ closedBall c t, HasDerivAt h (h₁ y) y := by
    intro y hy
    have hGy : HasDerivAt G (D y) y := (hGa y (hballR (hball hy))).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun y : ℂ => D c * (y - c)) (D c * 1) y :=
      ((hasDerivAt_id y).sub_const c).const_mul (D c)
    have h3 : HasDerivAt (fun y : ℂ => D₂ c / 2 * (y - c) ^ 2)
        (D₂ c / 2 * (↑2 * (y - c) ^ (2 - 1) * 1)) y :=
      (((hasDerivAt_id y).sub_const c).pow 2).const_mul (D₂ c / 2)
    have e : h₁ y = D y - D c * 1 - D₂ c / 2 * (↑2 * (y - c) ^ (2 - 1) * 1) := by
      simp only [hh₁]; ring
    rw [e]
    exact (hGy.sub h2).sub h3
  have hmv := (convex_closedBall c t).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hhd w hw).differentiableAt)
    (fun w hw => by rw [(hhd w hw).deriv]; exact hh₁b w hw)
    (mem_closedBall_self ht0) (mem_closedBall.2 (by rw [dist_eq_norm]))
  have hhc : h c = 0 := by simp [hhdef, hG0]
  rw [hhc, sub_zero] at hmv
  have hre_eq : f x - f c - (D c * (x - c)).re - (D₂ c / 2 * (x - c) ^ 2).re = (h x).re := by
    simp only [hhdef, sub_re]
    rw [hGre x (hballR hx)]
  rw [hre_eq]
  calc |(h x).re| ≤ ‖h x‖ := abs_re_le_norm _
    _ ≤ K * t * t * ‖x - c‖ := hmv
    _ = 1536 * M * ‖x - c‖ ^ 3 / R ^ 3 := by rw [hK, ht]; ring

/-- The second-order Taylor expansion of a planar harmonic function, for every bound `M ≥ 0`. -/
theorem abs_sub_taylor_two_le_of_harmonicOnNhd' {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hf : InnerProductSpace.HarmonicOnNhd f (ball c R))
    (hfM : ∀ y ∈ ball c R, |f y| ≤ M) :
    ∃ q₁ q₂ : ℂ, ∀ x ∈ ball c (R / 4),
      |f x - f c - (q₁ * (x - c)).re - (q₂ * (x - c) ^ 2).re| ≤
        1536 * M * ‖x - c‖ ^ 3 / R ^ 3 := by
  rcases hM.eq_or_lt with h0 | hpos
  · refine ⟨0, 0, fun x hx => ?_⟩
    have hx' : x ∈ ball c R := ball_subset_ball (by linarith) hx
    have h1 : f x = 0 := abs_nonpos_iff.1 (h0 ▸ hfM x hx')
    have h2 : f c = 0 := abs_nonpos_iff.1 (h0 ▸ hfM c (mem_ball_self hR))
    rw [h1, h2, ← h0]
    simp
  · exact abs_sub_taylor_two_le_of_harmonicOnNhd hR hpos hf hfM

end Rigidity.Proofs.Regularity
