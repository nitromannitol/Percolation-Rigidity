import Rigidity.Proofs.Regularity.ContinuumBallExcess
import Rigidity.Proofs.Regularity.PlanarHarmonicTaylor
import Rigidity.Proofs.Regularity.PlanarHarmonicMeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

end Rigidity.Proofs.Regularity
