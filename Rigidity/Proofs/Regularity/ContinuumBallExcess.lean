import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Rigidity.Proofs.Regularity.KIteration

/-!
# Normalized `L²` norms on Euclidean balls

Armstrong and Dario (arXiv:1609.09431v2) run the iteration of Lemma 7.2 in the normalized `L²`
norms `‖f‖_{L̲²(B_s)} = |B_s|^{-1/2} ‖f‖_{L²(B_s)}` of Lebesgue measure, applied to the coarsened
function `[u]_P`, and with `Ā(B_r)` the `ā`-harmonic functions on `B_r`. This file sets up these
norms on the group `locallySqIntegrable d` of functions on `ℝ^d` square integrable on every ball
(`continuumBallSeminorm`), with their monotonicity in the radius
(`radiusMonotone_continuumBallSeminorm`, with the factor `(r / s)^{d/2}`) and the comparison of
the excess of affine functions over constants on two balls (`polynomialComparison_continuumAffine`),
so that Lemma 7.2 for `k = 0` holds in these norms with only the excess decay of `Ā` and the
harmonic approximation hypothesis as hypotheses (`armstrongDario_lemma_7_2_zero_continuum`).
-/

open MeasureTheory Metric

namespace Rigidity.Proofs.Regularity

variable {d : ℕ}

/-- The functions on `ℝ^d` square integrable on every Euclidean ball. -/
def locallySqIntegrable (d : ℕ) : AddSubgroup (EuclideanSpace ℝ (Fin d) → ℝ) where
  carrier := {f | ∀ (c : EuclideanSpace ℝ (Fin d)) (R : ℝ), MemLp f 2 (volume.restrict (ball c R))}
  add_mem' hf hg c R := (hf c R).add (hg c R)
  zero_mem' _ _ := MemLp.zero
  neg_mem' hf c R := (hf c R).neg

/-- The `L²` norm on the ball `B_s(z)`. -/
noncomputable def ballL2 (z : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  (eLpNorm f 2 (volume.restrict (ball z s))).toReal

/-- The volume of the ball `B_s(z)`. -/
noncomputable def ballVolume (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) : ℝ :=
  (volume (ball z s)).toReal

/-- The volume of the unit ball of `ℝ^d`. -/
noncomputable def unitBallVolume (d : ℕ) : ℝ := ballVolume (0 : EuclideanSpace ℝ (Fin d)) 1

theorem ballL2_nonneg (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    0 ≤ ballL2 z s f :=
  ENNReal.toReal_nonneg

/-- The normalized `L²` norm `‖f‖_{L̲²(B_s(z))}` as an additive group seminorm. -/
noncomputable def continuumBallSeminorm (z : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    AddGroupSeminorm (locallySqIntegrable d) where
  toFun f := ballL2 z s f / Real.sqrt (ballVolume z s)
  map_zero' := by simp [ballL2]
  add_le' f g := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hf := f.2 z s
    have hg := g.2 z s
    simp only [ballL2, AddSubgroup.coe_add]
    rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
      (eLpNorm_add_le hf.1 hg.1 (by norm_num))
  neg' f := by simp [ballL2, eLpNorm_neg]

theorem continuumBallSeminorm_apply (z : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (f : locallySqIntegrable d) :
    continuumBallSeminorm z s f = ballL2 z s f / Real.sqrt (ballVolume z s) :=
  rfl

theorem ballVolume_eq (z : EuclideanSpace ℝ (Fin d)) {s : ℝ} (hs : 0 < s) :
    ballVolume z s = s ^ d * unitBallVolume d := by
  rw [ballVolume, Measure.addHaar_ball_of_pos volume z hs, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem unitBallVolume_pos [NeZero d] : 0 < unitBallVolume d :=
  ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

theorem rpow_half_eq_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ ((d : ℝ) / 2) = Real.sqrt (x ^ d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

theorem ballL2_mono (z : EuclideanSpace ℝ (Fin d)) {s r : ℝ} (hsr : s ≤ r)
    (f : locallySqIntegrable d) : ballL2 z s f ≤ ballL2 z r f :=
  ENNReal.toReal_mono (f.2 z r).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball hsr) le_rfl))

/-- **Monotonicity in the radius.** `‖f‖_{L̲²(B_s)} ≤ (r / s)^{d/2} ‖f‖_{L̲²(B_r)}`. -/
theorem radiusMonotone_continuumBallSeminorm [NeZero d] (z : EuclideanSpace ℝ (Fin d))
    {X R : ℝ} (hX : 0 < X) :
    RadiusMonotone (continuumBallSeminorm z) X R 1 ((d : ℝ) / 2) := by
  intro f s r hXs hsr _
  have hs : 0 < s := hX.trans_le hXs
  have hr : 0 < r := hs.trans_le hsr
  have hV := unitBallVolume_pos (d := d)
  rw [continuumBallSeminorm_apply, continuumBallSeminorm_apply, ballVolume_eq z hs,
    ballVolume_eq z hr, one_mul, rpow_half_eq_sqrt (div_nonneg hr.le hs.le)]
  have hsd : 0 < Real.sqrt (s ^ d) := Real.sqrt_pos.2 (by positivity)
  have hrd : 0 < Real.sqrt (r ^ d) := Real.sqrt_pos.2 (by positivity)
  have hVs : 0 < Real.sqrt (unitBallVolume d) := Real.sqrt_pos.2 hV
  have e : Real.sqrt ((r / s) ^ d) * (ballL2 z r f / Real.sqrt (r ^ d * unitBallVolume d)) =
      ballL2 z r f / Real.sqrt (s ^ d * unitBallVolume d) := by
    rw [div_pow, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (ballL2_mono z hsr f) (Real.sqrt_nonneg _)

end Rigidity.Proofs.Regularity
