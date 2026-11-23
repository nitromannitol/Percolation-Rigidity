import Rigidity.Proofs.Regularity.PlanarHarmonicTaylorThree
import Rigidity.Proofs.Regularity.PlanarMesoscopicRegularity
import Rigidity.Proofs.Regularity.KIterationGeneral

/-!
# Excess decay of order three of harmonic functions in the plane

The harmonic cubic polynomials of the plane, `Ā_3`, are the functions
`x ↦ Re(b₀ + b₁ ζ + b₂ ζ² + b₃ ζ³)`, `ζ = planarEquiv.symm x`, `bᵢ ∈ ℂ` (`planarHarmonicCubic`);
they contain the harmonic quadratic polynomials `Ā_2 = planarHarmonicQuadratic`. Recentring at
`c = planarEquiv.symm z` writes such a function as `Re(b₀' + b₁' (ζ - c) + b₂' (ζ - c)²) +
Re(b₃ (ζ - c)³)` with the same `b₃` (`planarCubic`, `planarCubic_mem`).

* For `v` harmonic on `B_r(z)` and `w ∈ Ā_3`, the third-order Taylor expansion of the planar
  harmonic function `(v - w) ∘ planarEquiv` gives an element of `Ā_3` within
  `C (s/r)⁴ ‖v - w‖_{L̲²(B_r)}` of `v` on `B_s`: the excess decay of order three
  (`harmonicRegularity_three_planarHarmonicClass`, `CH = 786432`).
* The excess of `w ∈ Ā_3` over `Ā_2` on `B_ρ(z)` is at most `|b₃| ρ³`, and at least
  `|b₃| ρ³ / 576`: the third difference of `w - h`, `h ∈ Ā_2`, along a step `η` with
  `b₃ η³ = |b₃| |η|³` is `6 |b₃| |η|³`, and the mean value property bounds the four values by
  `2 ‖w - h‖_{L̲²(B_ρ)}` (`polynomialComparison_planarHarmonicCubic`, `CP = 576`).

With these, Lemma 7.2 of Armstrong and Dario (arXiv:1609.09431v2) for `k = 2` holds in the plane,
in the normalized `L²` norms of Lebesgue measure with `Ā(B_r)` the harmonic functions on `B_r(z)`,
with only the harmonic approximation hypothesis (`armstrongDario_lemma_7_2_two_planar`), and so
does the form of Lemma 7.3 at `k = 2`, `D_2(r) ≤ C (r/R)³ D_2(R) + 2 C r^{-α} (r/R) ‖u‖_{L̲²(B_R)}`
(`armstrongDario_lemma_7_3_two_planar`).
-/

open MeasureTheory Metric Complex

namespace Rigidity.Proofs.Regularity

/-- A continuous function on `ℝ^d` is square integrable on every ball. -/
theorem memLp_ball_of_continuous {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (c : EuclideanSpace ℝ (Fin d)) (R : ℝ) : MemLp f 2 (volume.restrict (ball c R)) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hC x (ball_subset_closedBall hx))

/-- The real part of the complex cubic `b₀ + b₁ (ζ - c) + b₂ (ζ - c)² + b₃ (ζ - c)³` in
`ζ = planarEquiv.symm x`. -/
noncomputable def planarCubicFun (c b₀ b₁ b₂ b₃ : ℂ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (b₀ + b₁ * (planarEquiv.symm x - c) + b₂ * (planarEquiv.symm x - c) ^ 2 +
    b₃ * (planarEquiv.symm x - c) ^ 3).re

theorem continuous_planarCubicFun (c b₀ b₁ b₂ b₃ : ℂ) :
    Continuous (planarCubicFun c b₀ b₁ b₂ b₃) := by
  have h : Continuous fun x : EuclideanSpace ℝ (Fin 2) => planarEquiv.symm x - c :=
    planarEquiv.symm.continuous.sub continuous_const
  exact Complex.continuous_re.comp (((continuous_const.add (continuous_const.mul h)).add
    (continuous_const.mul (h.pow 2))).add (continuous_const.mul (h.pow 3)))

/-- The cubic `planarCubicFun c b₀ b₁ b₂ b₃` as an element of `locallySqIntegrable 2`. -/
noncomputable def planarCubic (c b₀ b₁ b₂ b₃ : ℂ) : locallySqIntegrable 2 :=
  ⟨planarCubicFun c b₀ b₁ b₂ b₃, fun z R =>
    memLp_ball_of_continuous (continuous_planarCubicFun c b₀ b₁ b₂ b₃) z R⟩

@[simp] theorem planarCubic_apply (c b₀ b₁ b₂ b₃ : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    (planarCubic c b₀ b₁ b₂ b₃ : EuclideanSpace ℝ (Fin 2) → ℝ) x =
      planarCubicFun c b₀ b₁ b₂ b₃ x :=
  rfl

/-- The harmonic cubic polynomials of the plane, `Ā_3`: the functions
`x ↦ Re(b₀ + b₁ ζ + b₂ ζ² + b₃ ζ³)`, `ζ = planarEquiv.symm x`. -/
def planarHarmonicCubic : AddSubgroup (locallySqIntegrable 2) where
  carrier := {f | ∃ b₀ b₁ b₂ b₃ : ℂ,
    ∀ x, (f : EuclideanSpace ℝ (Fin 2) → ℝ) x = planarCubicFun 0 b₀ b₁ b₂ b₃ x}
  add_mem' := by
    rintro f g ⟨a₀, a₁, a₂, a₃, hf⟩ ⟨b₀, b₁, b₂, b₃, hg⟩
    refine ⟨a₀ + b₀, a₁ + b₁, a₂ + b₂, a₃ + b₃, fun x => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, hf, hg, planarCubicFun, ← add_re]
    congr 1
    ring
  zero_mem' := ⟨0, 0, 0, 0, fun _ => by simp [planarCubicFun]⟩
  neg_mem' := by
    rintro f ⟨a₀, a₁, a₂, a₃, hf⟩
    refine ⟨-a₀, -a₁, -a₂, -a₃, fun x => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, hf, planarCubicFun, ← neg_re]
    congr 1
    ring

/-- Every recentred cubic is a harmonic cubic polynomial. -/
theorem planarCubic_mem (c b₀ b₁ b₂ b₃ : ℂ) : planarCubic c b₀ b₁ b₂ b₃ ∈ planarHarmonicCubic :=
  ⟨b₀ - b₁ * c + b₂ * c ^ 2 - b₃ * c ^ 3, b₁ - 2 * b₂ * c + 3 * b₃ * c ^ 2, b₂ - 3 * b₃ * c, b₃,
    fun x => by
      simp only [planarCubic_apply, planarCubicFun]
      congr 1
      ring⟩

/-- A recentred cubic without cubic term is a harmonic quadratic polynomial. -/
theorem planarCubic_mem_planarHarmonicQuadratic (c b₀ b₁ b₂ : ℂ) :
    planarCubic c b₀ b₁ b₂ 0 ∈ planarHarmonicQuadratic :=
  ⟨(b₀ - b₁ * c + b₂ * c ^ 2).re, b₁ - 2 * b₂ * c, b₂, fun x => by
    simp only [planarCubic_apply, planarCubicFun, ← add_re]
    congr 1
    ring⟩

theorem planarHarmonicQuadratic_le_planarHarmonicCubic :
    planarHarmonicQuadratic ≤ planarHarmonicCubic := by
  rintro f ⟨a, q₁, q₂, hf⟩
  refine ⟨a, q₁, q₂, 0, fun x => ?_⟩
  rw [hf, planarCubicFun]
  simp only [sub_zero, zero_mul, add_zero, add_re, ofReal_re]

theorem harmonicOnNhd_planarHarmonicCubic {f : locallySqIntegrable 2}
    (hf : f ∈ planarHarmonicCubic) (s : Set ℂ) :
    InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => (f : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) s := by
  obtain ⟨b₀, b₁, b₂, b₃, hf⟩ := hf
  have e : (fun ζ : ℂ => (f : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) =
      fun ζ => (b₀ + b₁ * (ζ - 0) + b₂ * (ζ - 0) ^ 2 + b₃ * (ζ - 0) ^ 3).re := by
    funext ζ
    rw [hf, planarCubicFun, LinearIsometryEquiv.symm_apply_apply]
  rw [e]
  intro ζ _
  have h : AnalyticAt ℂ (fun ζ : ℂ => ζ - 0) ζ := analyticAt_id.sub analyticAt_const
  exact (((analyticAt_const.add (analyticAt_const.mul h)).add
    (analyticAt_const.mul (h.pow 2))).add (analyticAt_const.mul (h.pow 3))).harmonicAt_re

/-- **Excess decay of order three, against one harmonic cubic polynomial.** -/
theorem ballExcess_three_le_planar_mul (z : EuclideanSpace ℝ (Fin 2)) {r s : ℝ} (hs : 0 < s)
    (hsr : s ≤ r / 2) {v : locallySqIntegrable 2} (hv : v ∈ planarHarmonicClass z r)
    {w' : locallySqIntegrable 2} (hw' : w' ∈ planarHarmonicCubic) :
    ballExcess (continuumBallSeminorm z) planarHarmonicCubic s v ≤
      786432 * (s / r) ^ 4 * continuumBallSeminorm z r (v - w') := by
  have hr : 0 < r := by linarith
  set w : locallySqIntegrable 2 := v - w' with hw
  set N := continuumBallSeminorm z r w with hN
  have hN0 : 0 ≤ N := apply_nonneg _ _
  set c := planarEquiv.symm z with hc
  set g : ℂ → ℝ := fun ζ => (w : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ) with hg
  have hwh : InnerProductSpace.HarmonicOnNhd g (ball c r) :=
    InnerProductSpace.HarmonicOnNhd.sub hv
      (harmonicOnNhd_planarHarmonicCubic hw' (ball (planarEquiv.symm z) r))
  by_cases hs8 : s < r / 8
  · set M := 2 * N with hM
    have hM0 : 0 ≤ M := by positivity
    have hbound : ∀ y ∈ ball c (r / 2), |g y| ≤ M := fun y hy =>
      abs_le_of_planarHarmonic z hr w hwh hy
    obtain ⟨q₁, q₂, q₃, hq⟩ := abs_sub_taylor_three_le_of_harmonicOnNhd'
      (by positivity : (0 : ℝ) < r / 2) hM0 (hwh.mono (ball_subset_ball (by linarith))) hbound
    set Q := planarCubic c (g c : ℂ) q₁ q₂ q₃ with hQ
    have hA : w' + Q ∈ planarHarmonicCubic :=
      planarHarmonicCubic.add_mem hw' (planarCubic_mem c _ _ _ _)
    refine (ballExcess_le _ _ hA).trans ?_
    have hbd : 0 ≤ 393216 * M * s ^ 4 / r ^ 4 := by positivity
    refine (continuumBallSeminorm_le_of_abs_le z hbd (v - (w' + Q)) ?_).trans (le_of_eq ?_)
    · intro x hx
      set ζ := planarEquiv.symm x with hζ
      have hxz : dist x z < s := mem_ball.1 hx
      have hζc : ‖ζ - c‖ < s := by
        rw [← dist_eq_norm, hζ, hc, LinearIsometryEquiv.dist_map]; exact hxz
      have hζ8 : ζ ∈ ball c (r / 2 / 4) := by
        rw [mem_ball, dist_eq_norm]; linarith
      have h1 : g ζ =
          (v : EuclideanSpace ℝ (Fin 2) → ℝ) x - (w' : EuclideanSpace ℝ (Fin 2) → ℝ) x := by
        simp only [hg, hζ, LinearIsometryEquiv.apply_symm_apply, hw, AddSubgroup.coe_sub,
          Pi.sub_apply]
      have hQx : (Q : EuclideanSpace ℝ (Fin 2) → ℝ) x = g c + (q₁ * (ζ - c)).re +
          (q₂ * (ζ - c) ^ 2).re + (q₃ * (ζ - c) ^ 3).re := by
        rw [hQ, planarCubic_apply, planarCubicFun, ← hζ, add_re, add_re, add_re, ofReal_re]
      have hval : ((v - (w' + Q) : locallySqIntegrable 2) : EuclideanSpace ℝ (Fin 2) → ℝ) x =
          g ζ - g c - (q₁ * (ζ - c)).re - (q₂ * (ζ - c) ^ 2).re - (q₃ * (ζ - c) ^ 3).re := by
        simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.sub_apply, Pi.add_apply]
        rw [hQx, h1]
        ring
      rw [hval]
      have hζs : ‖ζ - c‖ ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hζc.le 4
      calc |g ζ - g c - (q₁ * (ζ - c)).re - (q₂ * (ζ - c) ^ 2).re - (q₃ * (ζ - c) ^ 3).re|
          ≤ 24576 * M * ‖ζ - c‖ ^ 4 / (r / 2) ^ 4 := hq ζ hζ8
        _ ≤ 24576 * M * s ^ 4 / (r / 2) ^ 4 := by gcongr
        _ = 393216 * M * s ^ 4 / r ^ 4 := by ring
    · rw [hM]; field_simp; ring
  · push Not at hs8
    have h1 := ballExcess_le (continuumBallSeminorm z) planarHarmonicCubic (s := s) (u := v) hw'
    have hmono := radiusMonotone_continuumBallSeminorm (d := 2) z (X := s) (R := r) hs (v - w') s
      r le_rfl (by linarith) le_rfl
    have he : (r / s) ^ (((2 : ℕ) : ℝ) / 2) = r / s := by norm_num
    rw [he, one_mul] at hmono
    have hrs : r / s ≤ 8 := by rw [div_le_iff₀ hs]; linarith
    have hsr4 : 8 ≤ 786432 * (s / r) ^ 4 := by
      have h8 : 1 / 8 ≤ s / r := by rw [le_div_iff₀ hr]; linarith
      have := pow_le_pow_left₀ (by norm_num) h8 4
      nlinarith
    calc _ ≤ continuumBallSeminorm z s (v - w') := h1
      _ ≤ r / s * N := hmono
      _ ≤ 786432 * (s / r) ^ 4 * N := mul_le_mul_of_nonneg_right (by linarith) hN0

/-- **Excess decay of order three of harmonic functions in the plane**: `HarmonicRegularity`
with `j = 3` for the harmonic cubic polynomials, with `CH = 786432`, above every radius `X > 0`. -/
theorem harmonicRegularity_three_planarHarmonicClass (z : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    {X : ℝ} (hX : 0 < X) :
    HarmonicRegularity (continuumBallSeminorm z) (planarHarmonicClass z) planarHarmonicCubic 3
      X R 786432 := by
  intro r _ v hv s hXs hsr
  have hs : 0 < s := hX.trans_le hXs
  have hK : 0 ≤ 786432 * (s / r) ^ (3 + 1) := by
    have hr : 0 < r := by linarith
    positivity
  have e : 786432 * (s / r) ^ (3 + 1) *
      ballExcess (continuumBallSeminorm z) planarHarmonicCubic r v =
      ⨅ w : planarHarmonicCubic,
        786432 * (s / r) ^ (3 + 1) * continuumBallSeminorm z r (v - w) :=
    Real.mul_iInf_of_nonneg hK _
  rw [e]
  refine le_ciInf fun w => ?_
  calc _ ≤ 786432 * (s / r) ^ 4 * continuumBallSeminorm z r (v - w) :=
        ballExcess_three_le_planar_mul z hs hsr hv w.2
    _ = _ := by norm_num

theorem norm_planarEquiv_symm_sub_lt {z x : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ}
    (hx : x ∈ ball z ρ) : ‖planarEquiv.symm x - planarEquiv.symm z‖ < ρ := by
  rw [← dist_eq_norm, LinearIsometryEquiv.dist_map]
  exact mem_ball.1 hx

/-- The excess of a harmonic cubic polynomial over `Ā_2` on `B_ρ(z)` is at most `|b₃| ρ³`. -/
theorem ballExcess_planarHarmonicCubic_le (z : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {w : locallySqIntegrable 2} {b₀ b₁ b₂ b₃ : ℂ}
    (hw : ∀ x, (w : EuclideanSpace ℝ (Fin 2) → ℝ) x = planarCubicFun 0 b₀ b₁ b₂ b₃ x) :
    ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic ρ w ≤ ‖b₃‖ * ρ ^ 3 := by
  set c := planarEquiv.symm z with hc
  set h := planarCubic c (b₀ + b₁ * c + b₂ * c ^ 2 + b₃ * c ^ 3)
    (b₁ + 2 * b₂ * c + 3 * b₃ * c ^ 2) (b₂ + 3 * b₃ * c) 0 with hh
  have hmem : h ∈ planarHarmonicQuadratic := planarCubic_mem_planarHarmonicQuadratic c _ _ _
  refine (ballExcess_le _ _ hmem).trans ?_
  apply continuumBallSeminorm_le_of_abs_le z (by positivity)
  intro x hx
  have e : ((w - h : locallySqIntegrable 2) : EuclideanSpace ℝ (Fin 2) → ℝ) x =
      (b₃ * (planarEquiv.symm x - c) ^ 3).re := by
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, hw, hh, planarCubic_apply, planarCubicFun,
      ← sub_re]
    congr 1
    ring
  rw [e]
  have hxc : ‖planarEquiv.symm x - c‖ ≤ ρ := (norm_planarEquiv_symm_sub_lt hx).le
  calc |(b₃ * (planarEquiv.symm x - c) ^ 3).re| ≤ ‖b₃ * (planarEquiv.symm x - c) ^ 3‖ :=
        abs_re_le_norm _
    _ = ‖b₃‖ * ‖planarEquiv.symm x - c‖ ^ 3 := by rw [norm_mul, norm_pow]
    _ ≤ ‖b₃‖ * ρ ^ 3 := by gcongr

/-- **Lower bound for the excess of a harmonic cubic polynomial over `Ā_2`**:
`|b₃| ρ³ / 576 ≤ inf_{h ∈ Ā_2} ‖w - h‖_{L̲²(B_ρ(z))}`. -/
theorem le_ballExcess_planarHarmonicCubic (z : EuclideanSpace ℝ (Fin 2)) {ρ : ℝ} (hρ : 0 < ρ)
    {w : locallySqIntegrable 2} {b₀ b₁ b₂ b₃ : ℂ}
    (hw : ∀ x, (w : EuclideanSpace ℝ (Fin 2) → ℝ) x = planarCubicFun 0 b₀ b₁ b₂ b₃ x) :
    ‖b₃‖ * ρ ^ 3 / 576 ≤ ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic ρ w := by
  apply le_ballExcess
  intro h hh
  have hwm : w ∈ planarHarmonicCubic := ⟨b₀, b₁, b₂, b₃, hw⟩
  obtain ⟨a, q₁, q₂, hh'⟩ := hh
  set N := continuumBallSeminorm z ρ (w - h) with hN
  have hN0 : 0 ≤ N := apply_nonneg _ _
  rcases eq_or_ne b₃ 0 with hb | hb
  · rw [hb, norm_zero, zero_mul, zero_div]; exact hN0
  set c := planarEquiv.symm z with hc
  set P : ℂ → ℂ := fun ζ => (b₀ - a) + (b₁ - q₁) * ζ + (b₂ - q₂) * ζ ^ 2 + b₃ * ζ ^ 3 with hP
  have hPw : ∀ ζ, ((w - h : locallySqIntegrable 2) : EuclideanSpace ℝ (Fin 2) → ℝ)
      (planarEquiv ζ) = (P ζ).re := by
    intro ζ
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, hw, hh', planarCubicFun,
      LinearIsometryEquiv.symm_apply_apply]
    rw [show a + (q₁ * ζ).re + (q₂ * ζ ^ 2).re = ((a : ℂ) + q₁ * ζ + q₂ * ζ ^ 2).re by
      simp only [add_re, ofReal_re], ← sub_re, hP]
    congr 1
    ring
  have hharm : InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => ((w - h : locallySqIntegrable 2) : EuclideanSpace ℝ (Fin 2) → ℝ)
        (planarEquiv ζ)) (ball c ρ) :=
    (harmonicOnNhd_planarHarmonicCubic hwm _).sub
      (harmonicOnNhd_planarHarmonicCubic
        (planarHarmonicQuadratic_le_planarHarmonicCubic ⟨a, q₁, q₂, hh'⟩) _)
  have hbd : ∀ y ∈ ball c (ρ / 2), |(P y).re| ≤ 2 * N := fun y hy => by
    rw [← hPw]; exact abs_le_of_planarHarmonic z hρ (w - h) hharm hy
  -- a step `η` with `b₃ η³ = |b₃| |η|³`
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_pow_nat_eq (starRingEnd ℂ b₃ / (‖b₃‖ : ℂ))
    (by norm_num : 0 < 3)
  have hb0 : (‖b₃‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hb
  have hω1 : ‖ω‖ = 1 := by
    have h3 : ‖ω‖ ^ 3 = 1 := by
      rw [← norm_pow, hω, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, div_self hb0]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h3
  have hbω : b₃ * ω ^ 3 = (‖b₃‖ : ℂ) := by
    rw [hω, mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : (‖b₃‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
    field_simp
    push_cast
    ring
  set t := ρ / 6 with ht
  have ht0 : 0 < t := by positivity
  set η : ℂ := (t : ℂ) * ω with hη
  have hηn : ‖η‖ = t := by rw [hη, norm_mul, Complex.norm_real, Real.norm_eq_abs, hω1,
    abs_of_pos ht0, mul_one]
  have hmem : ∀ m : ℝ, |m| ≤ 3 / 2 → c + (m : ℂ) * η ∈ ball c (ρ / 2) := by
    intro m hm
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, hηn]
    have := mul_le_mul_of_nonneg_right hm ht0.le
    rw [ht] at this ⊢
    linarith
  have hdiff : P (c + ((3 / 2 : ℝ) : ℂ) * η) - 3 * P (c + ((1 / 2 : ℝ) : ℂ) * η) +
      3 * P (c + ((-1 / 2 : ℝ) : ℂ) * η) - P (c + ((-3 / 2 : ℝ) : ℂ) * η) = 6 * b₃ * η ^ 3 := by
    simp only [hP]
    push_cast
    ring
  have hre : (6 * b₃ * η ^ 3).re = 6 * ‖b₃‖ * t ^ 3 := by
    have e : 6 * b₃ * η ^ 3 = ((6 * ‖b₃‖ * t ^ 3 : ℝ) : ℂ) := by
      rw [hη, mul_pow, show (6 : ℂ) * b₃ * ((t : ℂ) ^ 3 * ω ^ 3) =
        6 * (t : ℂ) ^ 3 * (b₃ * ω ^ 3) by ring, hbω]
      push_cast
      ring
    rw [e, ofReal_re]
  have hsum := congrArg Complex.re hdiff
  simp only [sub_re, add_re, hre] at hsum
  have e3 : ∀ y : ℂ, ((3 : ℂ) * P y).re = 3 * (P y).re := fun y => by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, re_ofReal_mul]
  rw [e3, e3] at hsum
  have h1 := hbd _ (hmem (3 / 2) (by norm_num [abs_of_pos]))
  have h2 := hbd _ (hmem (1 / 2) (by norm_num [abs_of_pos]))
  have h3 := hbd _ (hmem (-1 / 2) (by rw [abs_le]; constructor <;> norm_num))
  have h4 := hbd _ (hmem (-3 / 2) (by rw [abs_le]; constructor <;> norm_num))
  have hle : 6 * ‖b₃‖ * t ^ 3 ≤ 16 * N := by
    rw [← hsum]
    have := abs_le.1 h1
    have := abs_le.1 h2
    have := abs_le.1 h3
    have := abs_le.1 h4
    linarith
  rw [ht] at hle
  have e : ‖b₃‖ * ρ ^ 3 / 576 = 6 * ‖b₃‖ * (ρ / 6) ^ 3 / 16 := by ring
  rw [e, div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
  linarith

/-- **Polynomial comparison for harmonic cubic polynomials on discs**, with `CP = 576`. -/
theorem polynomialComparison_planarHarmonicCubic (z : EuclideanSpace ℝ (Fin 2)) {X R : ℝ}
    (hX : 0 < X) :
    PolynomialComparison (continuumBallSeminorm z) planarHarmonicQuadratic planarHarmonicCubic 3
      X R 576 := by
  rintro w ⟨b₀, b₁, b₂, b₃, hw⟩ ρ ρ' hXρ hρρ' _
  have hρ : 0 < ρ := hX.trans_le hXρ
  have hρ' : 0 < ρ' := hρ.trans_le hρρ'
  have hup := ballExcess_planarHarmonicCubic_le z hρ.le hw
  have hlow := le_ballExcess_planarHarmonicCubic z hρ' hw
  calc _ ≤ ‖b₃‖ * ρ ^ 3 := hup
    _ = 576 * (ρ / ρ') ^ 3 * (‖b₃‖ * ρ' ^ 3 / 576) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **Armstrong–Dario, Lemma 7.2 (`k = 2`), in the plane**, in the normalized `L²` norms of
Lebesgue measure with `Ā(B_r)` the harmonic functions on `B_r(z)`, `Ā_2` the harmonic quadratic
polynomials and `Ā_3` the harmonic cubic polynomials, whose excess decay of orders one and three
and polynomial comparisons are proved: only the harmonic approximation hypothesis remains. -/
theorem armstrongDario_lemma_7_2_two_planar {A α : ℝ} (hA : 2 ≤ A) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin 2)) (R X E : ℝ) (u : locallySqIntegrable 2),
      1 ≤ X → X ≤ R / A → 0 ≤ E →
      HarmonicApproximation (continuumBallSeminorm z) (planarHarmonicClass z)
        (continuumConstants 2) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic r u ≤
          C * (r / R) ^ 3 * ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic R u +
          C * r ^ (1 - α) *
            (ballExcess (continuumBallSeminorm z) (continuumConstants 2) R u / R + E / r) := by
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2.{0} 2 hA hα (γ := ((2 : ℕ) : ℝ) / 2) (CV := 1)
    (CP := 4 * 2 ^ 2 + 576) (CH := 786432) (by positivity) zero_le_one (by positivity)
    (by norm_num)
  refine ⟨C, hC, fun z R X E u hX hXR hE happ r hr hrR => ?_⟩
  have hX0 : 0 < X := by linarith
  have hpc₁ := (polynomialComparison_continuumAffine (d := 2) z (R := R) hX0).mono_const _
    hX0.le (by norm_num : (4 : ℝ) * 2 ^ 2 ≤ 4 * 2 ^ 2 + 576)
  have hpc₂ := (polynomialComparison_planarHarmonicCubic z (R := R) hX0).mono_const _ hX0.le
    (by norm_num : (576 : ℝ) ≤ 4 * 2 ^ 2 + 576)
  exact h (continuumBallSeminorm z) (continuumConstants 2) (continuumAffine 2)
    planarHarmonicQuadratic planarHarmonicCubic (planarHarmonicClass z) R X E u
    continuumConstants_le_continuumAffine planarHarmonicQuadratic_le_planarHarmonicCubic hX hXR hE
    (radiusMonotone_continuumBallSeminorm z hX0) hpc₁ hpc₂
    ((harmonicRegularity_planarHarmonicClass z R hX0).mono_const (by norm_num) hX0)
    (harmonicRegularity_three_planarHarmonicClass z R hX0)
    (fun r _ _ => ⟨0, zero_mem_planarHarmonicClass z r⟩) happ r hr hrR

/-- **Armstrong–Dario, Lemma 7.3 (`k = 2`), in the plane**, in the form
`D_2(r) ≤ C (r / R)³ D_2(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}`, under the harmonic
approximation hypothesis with `R E ≤ ‖u‖_{L̲²(B_R)}`. -/
theorem armstrongDario_lemma_7_3_two_planar {A α : ℝ} (hA : 2 ≤ A) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin 2)) (R X E : ℝ) (u : locallySqIntegrable 2),
      1 ≤ X → X ≤ R / A → 0 ≤ E → R * E ≤ continuumBallSeminorm z R u →
      HarmonicApproximation (continuumBallSeminorm z) (planarHarmonicClass z)
        (continuumConstants 2) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic r u ≤
          C * (r / R) ^ 3 * ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic R u +
          2 * C * r ^ (-α) * (r / R) * continuumBallSeminorm z R u := by
  obtain ⟨C, hC, hlem⟩ := armstrongDario_lemma_7_2_two_planar hA hα
  refine ⟨C, hC, fun z R X E u hX hXR hE hRE happ r hr hrR => ?_⟩
  have h1 := hlem z R X E u hX hXR hE happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_continuumBallSeminorm z (continuumConstants 2) R u) hRE
  linarith

end Rigidity.Proofs.Regularity
