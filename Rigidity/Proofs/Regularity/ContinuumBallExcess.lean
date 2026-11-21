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

instance isFiniteMeasure_restrict_ball (c : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    IsFiniteMeasure (volume.restrict (ball c R)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

theorem sqrt_toReal_eq (x : ENNReal) : Real.sqrt x.toReal = (x ^ (2 : ENNReal).toReal⁻¹).toReal := by
  rw [← ENNReal.toReal_rpow, Real.sqrt_eq_rpow]
  norm_num

/-- **Upper bound by the supremum.** -/
theorem continuumBallSeminorm_le_of_abs_le (z : EuclideanSpace ℝ (Fin d)) {s M : ℝ} (hM : 0 ≤ M)
    (f : locallySqIntegrable d) (hf : ∀ x ∈ ball z s, |(f : _ → ℝ) x| ≤ M) :
    continuumBallSeminorm z s f ≤ M := by
  rcases (ENNReal.toReal_nonneg (a := volume (ball z s))).eq_or_lt with h0 | hpos
  · rw [continuumBallSeminorm_apply, ballVolume, ← h0, Real.sqrt_zero, div_zero]; exact hM
  have hae : ∀ᵐ x ∂(volume.restrict (ball z s)), ‖(f : _ → ℝ) x‖ ≤ M :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx => by
      rw [Real.norm_eq_abs]; exact hf x hx
  have h1 := eLpNorm_le_of_ae_bound (p := 2) hae
  rw [Measure.restrict_apply_univ] at h1
  have hfin : volume (ball z s) ^ (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal M ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne)
      ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hfin h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, ← sqrt_toReal_eq] at h2
  rw [continuumBallSeminorm_apply, ballVolume, div_le_iff₀ (Real.sqrt_pos.2 hpos)]
  calc ballL2 z s f ≤ Real.sqrt (volume (ball z s)).toReal * M := h2
    _ = M * Real.sqrt (volume (ball z s)).toReal := mul_comm _ _

/-- **Lower bound on a subset.** -/
theorem le_continuumBallSeminorm (z : EuclideanSpace ℝ (Fin d)) {s m : ℝ}
    {S : Set (EuclideanSpace ℝ (Fin d))} (hS : MeasurableSet S) (hSB : S ⊆ ball z s) (hm : 0 ≤ m)
    (f : locallySqIntegrable d)
    (hf : ∀ x ∈ S, m ≤ |(f : EuclideanSpace ℝ (Fin d) → ℝ) x|) :
    m * Real.sqrt ((volume S).toReal / ballVolume z s) ≤ continuumBallSeminorm z s f := by
  set g : EuclideanSpace ℝ (Fin d) → ℝ := f.val with hg
  have hae : ∀ᵐ x ∂(volume.restrict S), ‖(fun _ : EuclideanSpace ℝ (Fin d) => m) x‖ ≤ ‖g x‖ :=
    ae_restrict_of_forall_mem hS fun x hx => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm]; exact hf x hx
  have h1 : eLpNorm (fun _ : EuclideanSpace ℝ (Fin d) => m) 2 (volume.restrict S) ≤
      eLpNorm g 2 (volume.restrict S) := eLpNorm_mono_ae hae
  have h1' : eLpNorm g 2 (volume.restrict S) ≤ eLpNorm g 2 (volume.restrict (ball z s)) :=
    eLpNorm_mono_measure g (Measure.restrict_mono hSB le_rfl)
  have h3 : eLpNorm (fun _ : EuclideanSpace ℝ (Fin d) => m) 2 (volume.restrict S) =
      ‖m‖ₑ * volume S ^ (1 / (2 : ENNReal).toReal) := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num), Measure.restrict_apply_univ]
  have h2 := ENNReal.toReal_mono (f.2 z s).eLpNorm_ne_top ((h3 ▸ h1).trans h1')
  have hm' : ‖m‖ₑ.toReal = m := by simp [abs_of_nonneg hm]
  rw [ENNReal.toReal_mul, one_div, ← sqrt_toReal_eq, hm'] at h2
  have hV : 0 ≤ ballVolume z s := ENNReal.toReal_nonneg
  rw [continuumBallSeminorm_apply, Real.sqrt_div' _ hV, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h2 (Real.sqrt_nonneg _)

theorem memLp_affine (a : ℝ) (p c : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    MemLp (fun x => a + inner ℝ p x) 2 (volume.restrict (ball c R)) := by
  refine MemLp.of_bound
    (continuous_const.add (continuous_const.inner continuous_id)).aestronglyMeasurable
    (|a| + ‖p‖ * (‖c‖ + |R|)) ?_
  refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
  rw [Real.norm_eq_abs]
  have hx' : ‖x‖ ≤ ‖c‖ + |R| := by
    have h1 : ‖x - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hx
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + |R| := by linarith [le_abs_self R]
  calc |a + inner ℝ p x| ≤ |a| + |inner ℝ p x| := abs_add_le _ _
    _ ≤ |a| + ‖p‖ * ‖x‖ := by linarith [abs_real_inner_le_norm p x]
    _ ≤ |a| + ‖p‖ * (‖c‖ + |R|) := by
        have := mul_le_mul_of_nonneg_left hx' (norm_nonneg p); linarith

/-- The affine function `x ↦ a + ⟪p, x⟫` as an element of `locallySqIntegrable d`. -/
noncomputable def continuumAffineFun (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    locallySqIntegrable d :=
  ⟨fun x => a + inner ℝ p x, fun c R => memLp_affine a p c R⟩

@[simp] theorem continuumAffineFun_apply (a : ℝ) (p x : EuclideanSpace ℝ (Fin d)) :
    (continuumAffineFun a p : EuclideanSpace ℝ (Fin d) → ℝ) x = a + inner ℝ p x :=
  rfl

/-- The constant functions, `Ā_0`. -/
def continuumConstants (d : ℕ) : AddSubgroup (locallySqIntegrable d) where
  carrier := {f | ∃ a : ℝ, ∀ x, (f : EuclideanSpace ℝ (Fin d) → ℝ) x = a}
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, fun x => by simp only [AddSubgroup.coe_add, Pi.add_apply, ha, hb]⟩
  zero_mem' := ⟨0, fun _ => rfl⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, fun x => by simp only [AddSubgroup.coe_neg, Pi.neg_apply, ha]⟩

/-- The affine functions, `Ā_1`. -/
def continuumAffine (d : ℕ) : AddSubgroup (locallySqIntegrable d) where
  carrier := {f | ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin d)),
    ∀ x, (f : EuclideanSpace ℝ (Fin d) → ℝ) x = a + inner ℝ p x}
  add_mem' := by
    rintro f g ⟨a, p, ha⟩ ⟨b, q, hb⟩
    refine ⟨a + b, p + q, fun x => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, ha, hb, inner_add_left]
    ring
  zero_mem' := ⟨0, 0, fun _ => by simp⟩
  neg_mem' := by
    rintro f ⟨a, p, ha⟩
    refine ⟨-a, -p, fun x => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, ha, inner_neg_left]
    ring

theorem continuumConstants_le_continuumAffine : continuumConstants d ≤ continuumAffine d := by
  rintro f ⟨a, ha⟩
  exact ⟨a, 0, fun x => by simp [ha]⟩

/-- The excess of `x ↦ a + ⟪p, x⟫` over constants on `B_ρ(z)` is at most `‖p‖ ρ`. -/
theorem ballExcess_continuumAffine_le (z : EuclideanSpace ℝ (Fin d)) {ρ a : ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (hρ : 0 ≤ ρ) {w : locallySqIntegrable d}
    (hw : ∀ x, (w : EuclideanSpace ℝ (Fin d) → ℝ) x = a + inner ℝ p x) :
    ballExcess (continuumBallSeminorm z) (continuumConstants d) ρ w ≤ ‖p‖ * ρ := by
  have hc : continuumAffineFun (a + inner ℝ p z) 0 ∈ continuumConstants d :=
    ⟨a + inner ℝ p z, fun x => by simp⟩
  refine (ballExcess_le _ _ hc).trans ?_
  apply continuumBallSeminorm_le_of_abs_le z (by positivity)
  intro x hx
  have e : ((w - continuumAffineFun (a + inner ℝ p z) 0 : locallySqIntegrable d) :
      EuclideanSpace ℝ (Fin d) → ℝ) x = inner ℝ p (x - z) := by
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, hw, continuumAffineFun_apply, inner_zero_left,
      add_zero, inner_sub_right]
    ring
  rw [e]
  calc |inner ℝ p (x - z)| ≤ ‖p‖ * ‖x - z‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖p‖ * ρ := mul_le_mul_of_nonneg_left
        (by rw [← dist_eq_norm]; exact (mem_ball.1 hx).le) (norm_nonneg _)

theorem ballVolume_ratio [NeZero d] (z c : EuclideanSpace ℝ (Fin d)) {ρ t : ℝ} (hρ : 0 < ρ)
    (ht : 0 < t) : (volume (ball c t)).toReal / ballVolume z ρ = (t / ρ) ^ d := by
  have h1 : (volume (ball c t)).toReal = ballVolume c t := rfl
  have hV := unitBallVolume_pos (d := d)
  rw [h1, ballVolume_eq c ht, ballVolume_eq z hρ, div_pow]
  field_simp

/-- The excess of `x ↦ a + ⟪p, x⟫` over constants on `B_ρ(z)` is at least `2^{-d} ‖p‖ ρ / 4`:
on the ball `B_{ρ/4}(z ± ρ p / (2 ‖p‖))` the affine function stays `‖p‖ ρ / 4` away from any
constant on one side. -/
theorem le_ballExcess_continuumAffine [NeZero d] (z : EuclideanSpace ℝ (Fin d)) {ρ a : ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (hρ : 0 < ρ) {w : locallySqIntegrable d}
    (hw : ∀ x, (w : EuclideanSpace ℝ (Fin d) → ℝ) x = a + inner ℝ p x) :
    ‖p‖ * ρ / 4 * (1 / 2) ^ d ≤
      ballExcess (continuumBallSeminorm z) (continuumConstants d) ρ w := by
  apply le_ballExcess
  rintro c ⟨b, hb⟩
  rcases eq_or_ne p 0 with rfl | hp
  · rw [norm_zero, zero_mul, zero_div, zero_mul]; exact apply_nonneg _ _
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp
  set t := a + inner ℝ p z - b with ht
  set v : EuclideanSpace ℝ (Fin d) := (ρ / (2 * ‖p‖)) • p with hv
  have hvn : ‖v‖ = ρ / 2 := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
  have hpv : inner ℝ p v = ‖p‖ * ρ / 2 := by
    rw [hv, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  obtain ⟨σ, hσ, hσt⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 ≤ σ * t := by
    rcases le_total 0 t with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hSB : ball (z + σ • v) (ρ / 4) ⊆ ball z ρ := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have h1 : dist (z + σ • v) z = ρ / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hσabs, one_mul, hvn]
    calc dist x z ≤ dist x (z + σ • v) + dist (z + σ • v) z := dist_triangle _ _ _
      _ < ρ / 4 + ρ / 2 := by rw [h1]; linarith
      _ ≤ ρ := by linarith
  have hval : ∀ x ∈ ball (z + σ • v) (ρ / 4),
      ‖p‖ * ρ / 4 ≤ |((w - c : locallySqIntegrable d) : EuclideanSpace ℝ (Fin d) → ℝ) x| := by
    intro x hx
    set y := inner ℝ p (x - (z + σ • v)) with hy
    have e : ((w - c : locallySqIntegrable d) : EuclideanSpace ℝ (Fin d) → ℝ) x =
        t + σ * inner ℝ p v + y := by
      simp only [AddSubgroup.coe_sub, Pi.sub_apply, hw, hb, ht, hy, inner_sub_right,
        inner_add_right, real_inner_smul_right]
      ring
    rw [e]
    have hy1 : |y| ≤ ‖p‖ * (ρ / 4) := by
      refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [← dist_eq_norm]; exact (mem_ball.1 hx).le
    have h3 : |σ * y| ≤ ‖p‖ * (ρ / 4) := by rw [abs_mul, hσabs, one_mul]; exact hy1
    have h4 : -(‖p‖ * (ρ / 4)) ≤ σ * y := (abs_le.1 h3).1
    have h2 : σ * (t + σ * inner ℝ p v + y) = σ * t + inner ℝ p v + σ * y := by
      have : σ * (σ * inner ℝ p v) = (σ * σ) * inner ℝ p v := by ring
      rw [mul_add, mul_add, this, hσ2, one_mul]
    have h5 : ‖p‖ * ρ / 4 ≤ σ * (t + σ * inner ℝ p v + y) := by
      rw [h2, hpv]; linarith
    calc ‖p‖ * ρ / 4 ≤ σ * (t + σ * inner ℝ p v + y) := h5
      _ ≤ |σ * (t + σ * inner ℝ p v + y)| := le_abs_self _
      _ = |t + σ * inner ℝ p v + y| := by rw [abs_mul, hσabs, one_mul]
  have hlow := le_continuumBallSeminorm z measurableSet_ball hSB (by positivity) (w - c) hval
  rw [ballVolume_ratio z _ hρ (by positivity : (0 : ℝ) < ρ / 4)] at hlow
  have hq : Real.sqrt ((ρ / 4 / ρ) ^ d) = (1 / 2) ^ d := by
    have e1 : ρ / 4 / ρ = ((1 : ℝ) / 2) ^ 2 := by field_simp; norm_num
    rw [e1, ← pow_mul, mul_comm, pow_mul, Real.sqrt_sq (by positivity)]
  rw [hq] at hlow
  exact hlow

/-- **Polynomial comparison for affine functions on Euclidean balls**, with `CP = 4 · 2^d`. -/
theorem polynomialComparison_continuumAffine [NeZero d] (z : EuclideanSpace ℝ (Fin d)) {X R : ℝ}
    (hX : 0 < X) :
    PolynomialComparison (continuumBallSeminorm z) (continuumConstants d) (continuumAffine d) 1
      X R (4 * 2 ^ d) := by
  rintro w ⟨a, p, hw⟩ ρ ρ' hXρ hρρ' _
  have hρ : 0 < ρ := hX.trans_le hXρ
  have hρ' : 0 < ρ' := hρ.trans_le hρρ'
  have hup := ballExcess_continuumAffine_le z hρ.le hw
  have hlow := le_ballExcess_continuumAffine z hρ' hw
  rw [pow_one]
  have h2 : (2 : ℝ) ^ d * (1 / 2) ^ d = 1 := by rw [← mul_pow]; norm_num
  have e : ‖p‖ * ρ = 4 * 2 ^ d * (ρ / ρ') * (‖p‖ * ρ' / 4 * (1 / 2) ^ d) := by
    have h3 : 4 * 2 ^ d * (ρ / ρ') * (‖p‖ * ρ' / 4 * (1 / 2) ^ d) =
        (2 ^ d * (1 / 2) ^ d) * (ρ / ρ' * ρ') * ‖p‖ := by ring
    rw [h3, h2, div_mul_cancel₀ ρ hρ'.ne']; ring
  calc ballExcess (continuumBallSeminorm z) (continuumConstants d) ρ w ≤ ‖p‖ * ρ := hup
    _ = 4 * 2 ^ d * (ρ / ρ') * (‖p‖ * ρ' / 4 * (1 / 2) ^ d) := e
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

end Rigidity.Proofs.Regularity
