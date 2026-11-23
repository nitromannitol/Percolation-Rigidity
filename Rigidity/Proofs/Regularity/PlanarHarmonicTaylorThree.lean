import Rigidity.Proofs.Regularity.PlanarHarmonicTaylor

/-!
# Third-order Taylor expansion of planar harmonic functions

A function `f : ℂ → ℝ` harmonic on the disc `B_R(c)` with `|f| ≤ M` there is the real part of a
holomorphic function `F`; as in `Rigidity.Proofs.Regularity.PlanarHarmonicTaylor`, the
Borel–Carathéodory theorem bounds `G = F - F(c)` by `4 M` on `B_{R/2}(c)`, and the Cauchy estimate
bounds the fourth derivative `G⁗` by `24576 M / R⁴` on `B_{R/4}(c)`. Three applications of the
mean value inequality give the third-order Taylor expansion
`|f(x) - f(c) - Re(q₁ (x - c)) - Re(q₂ (x - c)²) - Re(q₃ (x - c)³)| ≤ 24576 M |x - c|⁴ / R⁴`
on `B_{R/4}(c)` (`abs_sub_taylor_three_le_of_harmonicOnNhd`), used for the excess decay of order
three of harmonic functions in the plane.
-/

open Complex Metric

namespace Rigidity.Proofs.Regularity

/-- **Mean value inequality from the centre of a closed disc.** -/
theorem norm_le_of_hasDerivAt_closedBall {φ ψ : ℂ → ℂ} {c : ℂ} {t B : ℝ} (ht : 0 ≤ t)
    (hB : 0 ≤ B) (hd : ∀ y ∈ closedBall c t, HasDerivAt φ (ψ y) y)
    (hb : ∀ y ∈ closedBall c t, ‖ψ y‖ ≤ B) (h0 : φ c = 0) :
    ∀ y ∈ closedBall c t, ‖φ y‖ ≤ B * t := by
  intro y hy
  have hmv := (convex_closedBall c t).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hd w hw).differentiableAt)
    (fun w hw => by rw [(hd w hw).deriv]; exact hb w hw) (mem_closedBall_self ht) hy
  rw [h0, sub_zero] at hmv
  have hyc : ‖y - c‖ ≤ t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
  exact hmv.trans (mul_le_mul_of_nonneg_left hyc hB)

/-- **Third-order Taylor expansion of a planar harmonic function.** -/
theorem abs_sub_taylor_three_le_of_harmonicOnNhd {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 < M) (hf : InnerProductSpace.HarmonicOnNhd f (ball c R))
    (hfM : ∀ y ∈ ball c R, |f y| ≤ M) :
    ∃ q₁ q₂ q₃ : ℂ, ∀ x ∈ ball c (R / 4),
      |f x - f c - (q₁ * (x - c)).re - (q₂ * (x - c) ^ 2).re - (q₃ * (x - c) ^ 3).re| ≤
        24576 * M * ‖x - c‖ ^ 4 / R ^ 4 := by
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
  set D₃ := deriv D₂ with hD₃
  set K : ℝ := 24576 * M / R ^ 4 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hDa : AnalyticOnNhd ℂ D (ball c R) := hGa.deriv
  have hD₂a : AnalyticOnNhd ℂ D₂ (ball c R) := hDa.deriv
  have hD₃a : AnalyticOnNhd ℂ D₃ (ball c R) := hD₂a.deriv
  have hD₄ : ∀ y ∈ ball c (R / 4), ‖deriv D₃ y‖ ≤ K := by
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
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 4 (by positivity) hcl
      hbound
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at h
    calc ‖deriv D₃ y‖ ≤ (Nat.factorial 4 : ℝ) * (2 * (2 * M)) / (R / 4) ^ 4 := h
      _ = K := by rw [hK]; norm_num; field_simp; ring
  refine ⟨D c, D₂ c / 2, D₃ c / 6, fun x hx => ?_⟩
  have hxc : ‖x - c‖ < R / 4 := by rw [← dist_eq_norm]; exact mem_ball.1 hx
  set t := ‖x - c‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hball : closedBall c t ⊆ ball c (R / 4) := closedBall_subset_ball hxc
  have hballR : ball c (R / 4) ⊆ ball c R := ball_subset_ball (by linarith)
  have hyR : ∀ y ∈ closedBall c t, y ∈ ball c R := fun y hy => hballR (hball hy)
  -- `D₃` is `K`-Lipschitz on `closedBall c t`
  have hLip : ∀ y ∈ closedBall c t, ‖D₃ y - D₃ c‖ ≤ K * t := by
    intro y hy
    have := (convex_ball c (R / 4)).norm_image_sub_le_of_norm_deriv_le
      (fun w hw => (hD₃a w (hballR hw)).differentiableAt) hD₄ (mem_ball_self (by linarith))
      (hball hy)
    have hyc : ‖y - c‖ ≤ t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    exact this.trans (mul_le_mul_of_nonneg_left hyc hK0)
  have hlin : ∀ (a : ℂ) (y : ℂ), HasDerivAt (fun y : ℂ => a * (y - c)) a y := fun a y => by
    have := ((hasDerivAt_id y).sub_const c).const_mul a
    rwa [mul_one] at this
  have hsq : ∀ (a : ℂ) (y : ℂ), HasDerivAt (fun y : ℂ => a / 2 * (y - c) ^ 2) (a * (y - c)) y :=
    fun a y => ((((hasDerivAt_id' y).sub_const c).pow 2).const_mul (a / 2)).congr_deriv (by
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring)
  have hcube : ∀ (a : ℂ) (y : ℂ),
      HasDerivAt (fun y : ℂ => a / 6 * (y - c) ^ 3) (a / 2 * (y - c) ^ 2) y := fun a y =>
    ((((hasDerivAt_id' y).sub_const c).pow 3).const_mul (a / 6)).congr_deriv (by
      rw [show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring)
  -- the remainders of the expansions of `D₂`, `D` and `G`
  set h₂ : ℂ → ℂ := fun y => D₂ y - D₂ c - D₃ c * (y - c) with hh₂
  set h₁ : ℂ → ℂ := fun y => D y - D c - D₂ c * (y - c) - D₃ c / 2 * (y - c) ^ 2 with hh₁
  set h : ℂ → ℂ := fun y =>
    G y - D c * (y - c) - D₂ c / 2 * (y - c) ^ 2 - D₃ c / 6 * (y - c) ^ 3 with hhdef
  have hh₂d : ∀ y ∈ closedBall c t, HasDerivAt h₂ (D₃ y - D₃ c) y := fun y hy =>
    (((hD₂a y (hyR y hy)).differentiableAt.hasDerivAt).sub_const (D₂ c)).sub (hlin (D₃ c) y)
  have hh₁d : ∀ y ∈ closedBall c t, HasDerivAt h₁ (h₂ y) y := fun y hy =>
    ((((hDa y (hyR y hy)).differentiableAt.hasDerivAt).sub_const (D c)).sub
      (hlin (D₂ c) y)).sub (hsq (D₃ c) y)
  have hhd : ∀ y ∈ closedBall c t, HasDerivAt h (h₁ y) y := fun y hy =>
    ((((hGa y (hyR y hy)).differentiableAt.hasDerivAt).sub (hlin (D c) y)).sub
      (hsq (D₂ c) y)).sub (hcube (D₃ c) y)
  have hh₂b := norm_le_of_hasDerivAt_closedBall ht0 (mul_nonneg hK0 ht0) hh₂d hLip
    (by simp [hh₂])
  have hh₁b := norm_le_of_hasDerivAt_closedBall ht0 (by positivity) hh₁d hh₂b (by simp [hh₁])
  have hhb := norm_le_of_hasDerivAt_closedBall ht0 (by positivity) hhd hh₁b (by simp [hhdef, hG0])
  have hre_eq : f x - f c - (D c * (x - c)).re - (D₂ c / 2 * (x - c) ^ 2).re -
      (D₃ c / 6 * (x - c) ^ 3).re = (h x).re := by
    simp only [hhdef, sub_re]
    rw [hGre x (hballR hx)]
  rw [hre_eq]
  calc |(h x).re| ≤ ‖h x‖ := abs_re_le_norm _
    _ ≤ K * t * t * t * t := hhb x (mem_closedBall.2 (by rw [dist_eq_norm]))
    _ = 24576 * M * ‖x - c‖ ^ 4 / R ^ 4 := by rw [hK, ht]; ring

/-- The third-order Taylor expansion of a planar harmonic function, for every bound `M ≥ 0`. -/
theorem abs_sub_taylor_three_le_of_harmonicOnNhd' {f : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM : 0 ≤ M) (hf : InnerProductSpace.HarmonicOnNhd f (ball c R))
    (hfM : ∀ y ∈ ball c R, |f y| ≤ M) :
    ∃ q₁ q₂ q₃ : ℂ, ∀ x ∈ ball c (R / 4),
      |f x - f c - (q₁ * (x - c)).re - (q₂ * (x - c) ^ 2).re - (q₃ * (x - c) ^ 3).re| ≤
        24576 * M * ‖x - c‖ ^ 4 / R ^ 4 := by
  rcases hM.eq_or_lt with h0 | hpos
  · refine ⟨0, 0, 0, fun x hx => ?_⟩
    have hx' : x ∈ ball c R := ball_subset_ball (by linarith) hx
    have h1 : f x = 0 := abs_nonpos_iff.1 (h0 ▸ hfM x hx')
    have h2 : f c = 0 := abs_nonpos_iff.1 (h0 ▸ hfM c (mem_ball_self hR))
    rw [h1, h2, ← h0]
    simp
  · exact abs_sub_taylor_three_le_of_harmonicOnNhd hR hpos hf hfM

end Rigidity.Proofs.Regularity
