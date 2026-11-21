import Rigidity.Proofs.Regularity.PlanarHarmonicRegularity
import Rigidity.Proofs.Regularity.ContinuumBallExcessTwo
import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# Excess decay of order two of harmonic functions in the plane

The harmonic quadratic polynomials of the plane are the functions
`x ↦ a + Re(q₁ ζ) + Re(q₂ ζ²)`, `ζ = planarEquiv.symm x` (`planarHarmonicQuadratic`); they are
quadratic functions of `x` (`planarHarmonicQuadratic_le_continuumQuadratic`, with
`Re(q ζ²) = q_M(x)` for `M = planarQuadMatrix q`) and contain the affine functions. For `v`
harmonic on `B_r(z)` and `w` a harmonic quadratic polynomial, the second-order Taylor expansion of
the planar harmonic function `(v - w) ∘ planarEquiv` gives a harmonic quadratic polynomial within
`C (s/r)³ ‖v - w‖_{L̲²(B_r)}` of `v` on `B_s`, `s < r / 8`: the excess decay of order two
(`harmonicRegularity_two_planarHarmonicClass`). With the excess decay of order one this gives
Lemma 7.2 of Armstrong and Dario for `k = 1` in the plane with only the harmonic approximation
hypothesis (`armstrongDario_lemma_7_2_one_planar`).
-/

open MeasureTheory Metric Complex

namespace Rigidity.Proofs.Regularity

theorem planarEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    planarEquiv.symm x = (x 0 : ℂ) + (x 1 : ℂ) * I :=
  Complex.orthonormalBasisOneI_repr_symm_apply x

theorem re_mul_planarEquiv_symm (q : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    (q * planarEquiv.symm x).re = inner ℝ (planarEquiv (starRingEnd ℂ q)) x := by
  conv_rhs => rw [← planarEquiv.apply_symm_apply x]
  rw [planarEquiv.inner_map_map, Complex.inner, Complex.conj_conj, mul_comm]

/-- The matrix of the quadratic form `x ↦ Re(q ζ²)`. -/
def planarQuadMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![q.re, -q.im; -q.im, -q.re]

theorem re_mul_sq_planarEquiv_symm (q : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    (q * planarEquiv.symm x ^ 2).re = quadForm (planarQuadMatrix q) x := by
  rw [planarEquiv_symm_apply]
  simp [quadForm, Fin.sum_univ_two, planarQuadMatrix, sq, Complex.mul_re, Complex.mul_im]
  ring

/-- The harmonic quadratic polynomials of the plane, `Ā_2`. -/
def planarHarmonicQuadratic : AddSubgroup (locallySqIntegrable 2) where
  carrier := {f | ∃ (a : ℝ) (q₁ q₂ : ℂ), ∀ x, (f : EuclideanSpace ℝ (Fin 2) → ℝ) x =
    a + (q₁ * planarEquiv.symm x).re + (q₂ * planarEquiv.symm x ^ 2).re}
  add_mem' := by
    rintro f g ⟨a, q₁, q₂, hf⟩ ⟨b, r₁, r₂, hg⟩
    refine ⟨a + b, q₁ + r₁, q₂ + r₂, fun x => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, hf, hg, add_mul, add_re]
    ring
  zero_mem' := ⟨0, 0, 0, fun _ => by simp⟩
  neg_mem' := by
    rintro f ⟨a, q₁, q₂, hf⟩
    refine ⟨-a, -q₁, -q₂, fun x => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, hf, neg_mul, neg_re]
    ring

theorem planarHarmonicQuadratic_le_continuumQuadratic :
    planarHarmonicQuadratic ≤ continuumQuadratic 2 := by
  rintro f ⟨a, q₁, q₂, hf⟩
  exact ⟨a, planarEquiv (starRingEnd ℂ q₁), planarQuadMatrix q₂, fun x => by
    rw [hf, re_mul_planarEquiv_symm, re_mul_sq_planarEquiv_symm]⟩

theorem continuumAffine_le_planarHarmonicQuadratic :
    continuumAffine 2 ≤ planarHarmonicQuadratic := by
  rintro f ⟨a, p, hf⟩
  refine ⟨a, starRingEnd ℂ (planarEquiv.symm p), 0, fun x => ?_⟩
  rw [hf, re_mul_planarEquiv_symm, Complex.conj_conj, LinearIsometryEquiv.apply_symm_apply]
  simp

theorem harmonicOnNhd_planarHarmonicQuadratic {f : locallySqIntegrable 2}
    (hf : f ∈ planarHarmonicQuadratic) (s : Set ℂ) :
    InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => (f : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) s := by
  obtain ⟨a, q₁, q₂, hf⟩ := hf
  have e : (fun ζ : ℂ => (f : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) =
      fun ζ => ((a : ℂ) + q₁ * ζ + q₂ * ζ ^ 2).re := by
    funext ζ
    rw [hf, LinearIsometryEquiv.symm_apply_apply]
    simp [add_re]
  rw [e]
  intro ζ _
  exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add
    (analyticAt_const.mul (analyticAt_id.pow 2))).harmonicAt_re

/-- **Excess decay of order two, against one harmonic quadratic polynomial.** -/
theorem ballExcess_two_le_planar_mul (z : EuclideanSpace ℝ (Fin 2)) {r s : ℝ} (hs : 0 < s)
    (hsr : s ≤ r / 2) {v : locallySqIntegrable 2} (hv : v ∈ planarHarmonicClass z r)
    {w' : locallySqIntegrable 2} (hw' : w' ∈ planarHarmonicQuadratic) :
    ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic s v ≤
      24576 * (s / r) ^ 3 * continuumBallSeminorm z r (v - w') := by
  have hr : 0 < r := by linarith
  set w : locallySqIntegrable 2 := v - w' with hw
  set N := continuumBallSeminorm z r w with hN
  have hN0 : 0 ≤ N := apply_nonneg _ _
  set c := planarEquiv.symm z with hc
  set g : ℂ → ℝ := fun ζ => (w : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ) with hg
  have hwh : InnerProductSpace.HarmonicOnNhd g (ball c r) :=
    InnerProductSpace.HarmonicOnNhd.sub hv
      (harmonicOnNhd_planarHarmonicQuadratic hw' (ball (planarEquiv.symm z) r))
  by_cases hs8 : s < r / 8
  · set M := 2 * N with hM
    have hM0 : 0 ≤ M := by positivity
    have hbound : ∀ y ∈ ball c (r / 2), |g y| ≤ M := fun y hy =>
      abs_le_of_planarHarmonic z hr w hwh hy
    obtain ⟨q₁, q₂, hq⟩ := abs_sub_taylor_two_le_of_harmonicOnNhd' (by positivity : (0 : ℝ) < r / 2)
      hM0 (hwh.mono (ball_subset_ball (by linarith))) hbound
    set a := g c - (q₁ * c).re + (q₂ * c ^ 2).re with ha
    set Q : locallySqIntegrable 2 := continuumQuadraticFun a
      (planarEquiv (starRingEnd ℂ (q₁ - 2 * q₂ * c))) (planarQuadMatrix q₂) with hQ
    have hQx : ∀ x, (Q : EuclideanSpace ℝ (Fin 2) → ℝ) x =
        a + ((q₁ - 2 * q₂ * c) * planarEquiv.symm x).re + (q₂ * planarEquiv.symm x ^ 2).re :=
      fun x => by
        rw [hQ, continuumQuadraticFun_apply, re_mul_planarEquiv_symm, re_mul_sq_planarEquiv_symm]
    have hQm : Q ∈ planarHarmonicQuadratic := ⟨a, q₁ - 2 * q₂ * c, q₂, hQx⟩
    have hA : w' + Q ∈ planarHarmonicQuadratic := planarHarmonicQuadratic.add_mem hw' hQm
    refine (ballExcess_le _ _ hA).trans ?_
    have hbd : 0 ≤ 12288 * M * s ^ 3 / r ^ 3 := by positivity
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
      have key : q₁ * (ζ - c) + q₂ * (ζ - c) ^ 2 =
          (q₁ - 2 * q₂ * c) * ζ - q₁ * c + q₂ * c ^ 2 + q₂ * ζ ^ 2 := by ring
      have key' := congrArg Complex.re key
      simp only [add_re, sub_re] at key'
      have hval : ((v - (w' + Q) : locallySqIntegrable 2) : EuclideanSpace ℝ (Fin 2) → ℝ) x =
          g ζ - g c - (q₁ * (ζ - c)).re - (q₂ * (ζ - c) ^ 2).re := by
        simp only [AddSubgroup.coe_sub, AddSubgroup.coe_add, Pi.sub_apply, Pi.add_apply]
        rw [hQx, h1, ha]
        linarith
      rw [hval]
      have hζs : ‖ζ - c‖ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hζc.le 3
      calc |g ζ - g c - (q₁ * (ζ - c)).re - (q₂ * (ζ - c) ^ 2).re|
          ≤ 1536 * M * ‖ζ - c‖ ^ 3 / (r / 2) ^ 3 := hq ζ hζ8
        _ ≤ 1536 * M * s ^ 3 / (r / 2) ^ 3 := by gcongr
        _ = 12288 * M * s ^ 3 / r ^ 3 := by ring
    · rw [hM]; field_simp; ring
  · push Not at hs8
    have h1 := ballExcess_le (continuumBallSeminorm z) planarHarmonicQuadratic (s := s) (u := v)
      hw'
    have hmono := radiusMonotone_continuumBallSeminorm (d := 2) z (X := s) (R := r) hs (v - w') s
      r le_rfl (by linarith) le_rfl
    have he : (r / s) ^ (((2 : ℕ) : ℝ) / 2) = r / s := by norm_num
    rw [he, one_mul] at hmono
    have hrs : r / s ≤ 8 := by rw [div_le_iff₀ hs]; linarith
    have hsr3 : 8 ≤ 24576 * (s / r) ^ 3 := by
      have h8 : 1 / 8 ≤ s / r := by rw [le_div_iff₀ hr]; linarith
      have := pow_le_pow_left₀ (by norm_num) h8 3
      nlinarith
    calc _ ≤ continuumBallSeminorm z s (v - w') := h1
      _ ≤ r / s * N := hmono
      _ ≤ 24576 * (s / r) ^ 3 * N := mul_le_mul_of_nonneg_right (by linarith) hN0

/-- **Excess decay of order two of harmonic functions in the plane**: `HarmonicRegularity` with
`j = 2` for the harmonic quadratic polynomials, with `CH = 24576`, above every radius `X > 0`. -/
theorem harmonicRegularity_two_planarHarmonicClass (z : EuclideanSpace ℝ (Fin 2)) (R : ℝ) {X : ℝ}
    (hX : 0 < X) :
    HarmonicRegularity (continuumBallSeminorm z) (planarHarmonicClass z) planarHarmonicQuadratic 2
      X R 24576 := by
  intro r _ v hv s hXs hsr
  have hs : 0 < s := hX.trans_le hXs
  have hK : 0 ≤ 24576 * (s / r) ^ (2 + 1) := by
    have hr : 0 < r := by linarith
    positivity
  have e : 24576 * (s / r) ^ (2 + 1) *
      ballExcess (continuumBallSeminorm z) planarHarmonicQuadratic r v =
      ⨅ w : planarHarmonicQuadratic,
        24576 * (s / r) ^ (2 + 1) * continuumBallSeminorm z r (v - w) :=
    Real.mul_iInf_of_nonneg hK _
  rw [e]
  refine le_ciInf fun w => ?_
  calc _ ≤ 24576 * (s / r) ^ 3 * continuumBallSeminorm z r (v - w) :=
        ballExcess_two_le_planar_mul z hs hsr hv w.2
    _ = _ := by norm_num

/-- **Armstrong–Dario, Lemma 7.2 (`k = 1`), in the plane**, in the normalized `L²` norms of
Lebesgue measure with `Ā(B_r)` the harmonic functions on `B_r(z)` and `Ā_2` the harmonic quadratic
polynomials, whose excess decay of orders one and two is proved: only the harmonic approximation
hypothesis remains. -/
theorem armstrongDario_lemma_7_2_one_planar {A α : ℝ} (hA : 2 ≤ A) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin 2)) (R X E : ℝ) (u : locallySqIntegrable 2),
      1 ≤ X → X ≤ R / A → 0 ≤ E →
      HarmonicApproximation (continuumBallSeminorm z) (planarHarmonicClass z)
        (continuumConstants 2) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (continuumBallSeminorm z) (continuumAffine 2) r u ≤
          C * (r / R) ^ 2 * ballExcess (continuumBallSeminorm z) (continuumAffine 2) R u +
          C * r ^ (1 - α) *
            (ballExcess (continuumBallSeminorm z) (continuumConstants 2) R u / R + E / r) := by
  obtain ⟨C, hC, h⟩ := armstrongDario_lemma_7_2_one_continuum 2 hA hα (CH := 24576) (by norm_num)
  refine ⟨C, hC, fun z R X E u hX hXR hE happ r hr hrR => ?_⟩
  have hX0 : 0 < X := by linarith
  exact h z planarHarmonicQuadratic (planarHarmonicClass z) R X E u
    continuumAffine_le_planarHarmonicQuadratic planarHarmonicQuadratic_le_continuumQuadratic hX hXR
    hE ((harmonicRegularity_planarHarmonicClass z R hX0).mono_const (by norm_num) hX0)
    (harmonicRegularity_two_planarHarmonicClass z R hX0)
    (fun r _ _ => ⟨0, zero_mem_planarHarmonicClass z r⟩) happ r hr hrR

end Rigidity.Proofs.Regularity
