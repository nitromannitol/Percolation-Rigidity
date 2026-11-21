import Rigidity.Proofs.Regularity.ContinuumBallExcess
import Rigidity.Proofs.Regularity.PlanarHarmonicTaylor
import Rigidity.Proofs.Regularity.PlanarHarmonicMeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Excess decay of order one of harmonic functions in the plane

The plane `ℝ²` is identified with `ℂ` by the linear isometry `planarEquiv`, which preserves Lebesgue
measure. A function `v` on `ℝ²` is in `planarHarmonicClass z r` when `v ∘ planarEquiv` is
harmonic on the disc `B_r(z)`. For such `v` and any affine `ℓ`, `g = (v - ℓ) ∘ planarEquiv` is
harmonic; the mean value property bounds `|g|` on `B_{r/2}` by `2 ‖v - ℓ‖_{L̲²(B_r)}`
(`abs_le_of_planarHarmonic`), and the first-order Taylor expansion of planar harmonic functions gives
an affine function within `C (s/r)² ‖v - ℓ‖_{L̲²(B_r)}` of `v` on `B_s` for `s < r / 8`. This is the
excess decay of order one (`harmonicRegularity_planarHarmonicClass`, `HarmonicRegularity` with
`j = 1` and `CH = 1024`) of harmonic functions in the normalized `L²` norms of Lebesgue measure, so
that Lemma 7.2 of Armstrong and Dario for `k = 0` holds in the plane with only the harmonic
approximation hypothesis (`armstrongDario_lemma_7_2_zero_planar`).
-/

open MeasureTheory Metric Complex

namespace Rigidity.Proofs.Regularity

/-- The identification of `ℝ²` with `ℂ`. -/
noncomputable def planarEquiv : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

theorem planarEquiv_preimage_ball (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    planarEquiv ⁻¹' ball z r = ball (planarEquiv.symm z) r := by
  have h := planarEquiv.isometry.preimage_ball (planarEquiv.symm z) r
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

theorem setIntegral_ball_planarEquiv (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    ∫ w in ball (planarEquiv.symm z) r, φ (planarEquiv w) = ∫ x in ball z r, φ x := by
  rw [← planarEquiv_preimage_ball]
  exact planarEquiv.measurePreserving.setIntegral_preimage_emb
    planarEquiv.toMeasurableEquiv.measurableEmbedding φ (ball z r)

theorem ballVolume_planar (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ballVolume z r = Real.pi * r ^ 2 := by
  have h := planarEquiv.measurePreserving.measure_preimage
    (measurableSet_ball (x := z) (ε := r)).nullMeasurableSet
  rw [planarEquiv_preimage_ball] at h
  rw [ballVolume, ← h, ← volume_real_ball_complex (planarEquiv.symm z) hr]
  rfl

theorem ballL2_eq_sqrt {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (f : locallySqIntegrable d) :
    ballL2 z r f = Real.sqrt (∫ x in ball z r, (f : EuclideanSpace ℝ (Fin d) → ℝ) x ^ 2) := by
  rw [ballL2, (f.2 z r).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  have e : ∀ x, ‖(f : EuclideanSpace ℝ (Fin d) → ℝ) x‖ ^ (ENNReal.toReal 2) =
      (f : EuclideanSpace ℝ (Fin d) → ℝ) x ^ 2 := fun x => by
    rw [show ENNReal.toReal 2 = (2 : ℝ) by norm_num, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  norm_num

/-- The functions on `ℝ²` harmonic on the disc `B_r(z)`, as elements of
`locallySqIntegrable 2`. -/
def planarHarmonicClass (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : Set (locallySqIntegrable 2) :=
  {v | InnerProductSpace.HarmonicOnNhd
    (fun ζ : ℂ => (v : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) (ball (planarEquiv.symm z) r)}

theorem zero_mem_planarHarmonicClass (z : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    (0 : locallySqIntegrable 2) ∈ planarHarmonicClass z r := by
  have e : (fun ζ : ℂ => ((0 : locallySqIntegrable 2) : EuclideanSpace ℝ (Fin 2) → ℝ)
      (planarEquiv ζ)) = fun _ => (0 : ℝ) := rfl
  show InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => ((0 : locallySqIntegrable 2) :
    EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) (ball (planarEquiv.symm z) r)
  rw [e]
  exact InnerProductSpace.harmonicOnNhd_const 0

theorem inner_planarEquiv (p : EuclideanSpace ℝ (Fin 2)) (ζ : ℂ) :
    inner ℝ p (planarEquiv ζ) = (ζ * starRingEnd ℂ (planarEquiv.symm p)).re := by
  rw [← Complex.inner, ← planarEquiv.inner_map_map, LinearIsometryEquiv.apply_symm_apply]

theorem harmonicOnNhd_affine_planarEquiv {ℓ : locallySqIntegrable 2}
    (hℓ : ℓ ∈ continuumAffine 2) (s : Set ℂ) :
    InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) s := by
  obtain ⟨a, p, hℓ⟩ := hℓ
  have e : (fun ζ : ℂ => (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) =
      fun ζ => ((a : ℂ) + ζ * starRingEnd ℂ (planarEquiv.symm p)).re := by
    funext ζ
    rw [hℓ, inner_planarEquiv, add_re, ofReal_re]
  rw [e]
  intro ζ _
  exact (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).harmonicAt_re

/-- **Bound by the square average.** For `w` with `w ∘ planarEquiv` harmonic on `B_r`,
`|w| ≤ 2 ‖w‖_{L̲²(B_r)}` on `B_{r/2}`. -/
theorem abs_le_of_planarHarmonic (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (w : locallySqIntegrable 2)
    (hw : InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => (w : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ))
      (ball (planarEquiv.symm z) r))
    {y : ℂ} (hy : y ∈ ball (planarEquiv.symm z) (r / 2)) :
    |(w : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv y)| ≤ 2 * continuumBallSeminorm z r w := by
  set g : ℂ → ℝ := fun ζ => (w : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ) with hgdef
  set c := planarEquiv.symm z with hc
  have hyc : dist y c < r / 2 := mem_ball.1 hy
  have hsub : closedBall y (r / 2) ⊆ ball c r := by
    intro ζ hζ
    rw [mem_closedBall] at hζ
    rw [mem_ball]
    linarith [dist_triangle ζ y c]
  have h1 := sq_mul_le_integral_sq_of_harmonicOnNhd (g := g) (y := y) (by positivity : 0 < r / 2)
    fun x hx => hw x (hsub hx)
  have h2 : ∫ x in ball y (r / 2), g x ^ 2 =
      ∫ x in ball (planarEquiv y) (r / 2), (w : EuclideanSpace ℝ (Fin 2) → ℝ) x ^ 2 := by
    have := setIntegral_ball_planarEquiv
      (fun x => (w : EuclideanSpace ℝ (Fin 2) → ℝ) x ^ 2) (planarEquiv y) (r / 2)
    rw [LinearIsometryEquiv.symm_apply_apply] at this
    exact this
  have hball : ball (planarEquiv y) (r / 2) ⊆ ball z r := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have : dist (planarEquiv y) z = dist y c := by
      rw [hc, ← planarEquiv.dist_map y (planarEquiv.symm z), LinearIsometryEquiv.apply_symm_apply]
    linarith [dist_triangle x (planarEquiv y) z]
  have h3 : ∫ x in ball (planarEquiv y) (r / 2), (w : EuclideanSpace ℝ (Fin 2) → ℝ) x ^ 2 ≤
      ∫ x in ball z r, (w : EuclideanSpace ℝ (Fin 2) → ℝ) x ^ 2 :=
    setIntegral_mono_set ((w.2 z r).integrable_sq)
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) (Filter.Eventually.of_forall hball)
  set I := ∫ x in ball z r, (w : EuclideanSpace ℝ (Fin 2) → ℝ) x ^ 2 with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
  have hgy : g y ^ 2 * (Real.pi * r ^ 2) ≤ 4 * I := by
    have := h1.trans (h2 ▸ h3)
    nlinarith
  have hN : continuumBallSeminorm z r w = Real.sqrt I / Real.sqrt (Real.pi * r ^ 2) := by
    rw [continuumBallSeminorm_apply, ballL2_eq_sqrt, ballVolume_planar z hr]
  rw [hN]
  have hpr : 0 < Real.pi * r ^ 2 := by positivity
  have hsq : 0 < Real.sqrt (Real.pi * r ^ 2) := Real.sqrt_pos.2 hpr
  rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (Real.sqrt I / Real.sqrt (Real.pi * r ^ 2)))]
  apply sq_le_sq.1
  rw [mul_pow, div_pow, Real.sq_sqrt hI0, Real.sq_sqrt hpr.le]
  rw [← mul_div_assoc, le_div_iff₀ hpr]
  show g y ^ 2 * (Real.pi * r ^ 2) ≤ 2 ^ 2 * I
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [h4]
  exact hgy

end Rigidity.Proofs.Regularity
