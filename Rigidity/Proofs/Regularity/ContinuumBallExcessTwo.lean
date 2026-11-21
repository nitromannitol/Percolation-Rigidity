import Rigidity.Proofs.Regularity.ContinuumBallExcess
import Rigidity.Proofs.Regularity.ClusterKIterationOne

/-!
# Quadratic functions on Euclidean balls

The quadratic functions `x ↦ a + ⟪p, x⟫ + q_M(x)` on `ℝ^d` (`continuumQuadratic`), the
translation invariance of the `L²` norms on balls (`eLpNorm_comp_add_ball`), and the comparison
of the excess of quadratic functions over affine functions on two balls
(`polynomialComparison_continuumQuadratic`): the excess on `B_ρ(z)` is at most `d m ρ²`, `m` the
largest entry of the symmetric part of `M`, and at least `2^{-d} m ρ² / 32`, by the second
difference `g(x + h) + g(x - h) - 2 g(x) = 2 q_M(h)` on three balls of radius `ρ / 4`. With these,
Lemma 7.2 of Armstrong and Dario for `k = 1` holds in the normalized `L²` norms of Lebesgue measure
with only the excess decay of `Ā` and the harmonic approximation hypothesis as hypotheses
(`armstrongDario_lemma_7_2_one_continuum`).
-/

open MeasureTheory Metric

namespace Rigidity.Proofs.Regularity

variable {d : ℕ}

theorem continuous_quadForm (M : Matrix (Fin d) (Fin d) ℝ) : Continuous (quadForm M) := by
  unfold quadForm
  fun_prop

theorem continuous_quadratic (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) : Continuous fun x => a + inner ℝ p x + quadForm M x :=
  (continuous_const.add (continuous_const.inner continuous_id)).add (continuous_quadForm M)

/-- The sum of the absolute values of the entries of the symmetric part of `M`. -/
noncomputable def symEntrySum (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, |symEntry M i j|

theorem abs_symEntry_le_symEntrySum (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    |symEntry M i j| ≤ symEntrySum M :=
  (Finset.single_le_sum (f := fun j => |symEntry M i j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, |symEntry M i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem symEntrySum_nonneg (M : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ symEntrySum M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem memLp_quadratic (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    MemLp (fun x => a + inner ℝ p x + quadForm M x) 2 (volume.restrict (ball c R)) := by
  set K := ‖c‖ + |R| with hK
  refine MemLp.of_bound (continuous_quadratic a p M).aestronglyMeasurable
    (|a| + ‖p‖ * K + d * symEntrySum M * K ^ 2) ?_
  refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
  rw [Real.norm_eq_abs]
  have hx' : ‖x‖ ≤ K := by
    have h1 : ‖x - c‖ < R := by rw [← dist_eq_norm]; exact mem_ball.1 hx
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ K := by rw [hK]; linarith [le_abs_self R]
  have hq := abs_quadForm_le M (symEntrySum_nonneg M) (abs_symEntry_le_symEntrySum M) x
  have hx2 : ‖x‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx' 2
  have h0 : 0 ≤ (d : ℝ) * symEntrySum M := mul_nonneg (Nat.cast_nonneg d) (symEntrySum_nonneg M)
  have hp := abs_real_inner_le_norm p x
  have hpK : ‖p‖ * ‖x‖ ≤ ‖p‖ * K := mul_le_mul_of_nonneg_left hx' (norm_nonneg p)
  have hqK : (d : ℝ) * symEntrySum M * ‖x‖ ^ 2 ≤ d * symEntrySum M * K ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 h0
  calc |a + inner ℝ p x + quadForm M x| ≤ |a| + |inner ℝ p x| + |quadForm M x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |a| + ‖p‖ * K + d * symEntrySum M * K ^ 2 := by linarith

/-- The quadratic function `x ↦ a + ⟪p, x⟫ + q_M(x)` as an element of `locallySqIntegrable d`. -/
noncomputable def continuumQuadraticFun (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) : locallySqIntegrable d :=
  ⟨fun x => a + inner ℝ p x + quadForm M x, fun c R => memLp_quadratic a p M c R⟩

@[simp] theorem continuumQuadraticFun_apply (a : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (M : Matrix (Fin d) (Fin d) ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (continuumQuadraticFun a p M : EuclideanSpace ℝ (Fin d) → ℝ) x =
      a + inner ℝ p x + quadForm M x :=
  rfl

/-- The quadratic functions on `ℝ^d`. -/
def continuumQuadratic (d : ℕ) : AddSubgroup (locallySqIntegrable d) where
  carrier := {f | ∃ (a : ℝ) (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ),
    ∀ x, (f : EuclideanSpace ℝ (Fin d) → ℝ) x = a + inner ℝ p x + quadForm M x}
  add_mem' := by
    rintro f g ⟨a, p, M, ha⟩ ⟨b, q, N, hb⟩
    refine ⟨a + b, p + q, M + N, fun x => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, ha, hb, inner_add_left, quadForm,
      Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  zero_mem' := ⟨0, 0, 0, fun _ => by simp [quadForm]⟩
  neg_mem' := by
    rintro f ⟨a, p, M, ha⟩
    refine ⟨-a, -p, -M, fun x => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, ha, inner_neg_left, quadForm,
      Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
    ring

theorem continuumAffine_le_continuumQuadratic : continuumAffine d ≤ continuumQuadratic d := by
  rintro f ⟨a, p, ha⟩
  exact ⟨a, p, 0, fun x => by simp [ha, quadForm]⟩

/-- **Translation invariance** of the `L²` norms on balls. -/
theorem eLpNorm_comp_add_ball {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (y h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    eLpNorm (fun x => g (x + h)) 2 (volume.restrict (ball y t)) =
      eLpNorm g 2 (volume.restrict (ball (y + h) t)) := by
  have hpre : (fun x => x + h) ⁻¹' ball (y + h) t = ball y t := by
    ext x
    simp only [Set.mem_preimage, mem_ball, dist_add_right]
  have hmp := (measurePreserving_add_right volume h).restrict_preimage
    (measurableSet_ball (x := y + h) (ε := t))
  rw [hpre] at hmp
  exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hmp

/-- **Second difference lower bound**: for `g(x) = c + ⟪p, x⟫ + q_M(x)` and `e` with `‖e‖ ≤ 2` and
`m ≤ |q_M(e)|`, `‖g‖_{L²(B_ρ(z))} ≥ m ρ² |B_{ρ/4}|^{1/2} / 32`. -/
theorem le_ballL2_quadratic (z : EuclideanSpace ℝ (Fin d)) {ρ m : ℝ} (hρ : 0 < ρ) (c : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (M : Matrix (Fin d) (Fin d) ℝ) {e : EuclideanSpace ℝ (Fin d)}
    (he : ‖e‖ ≤ 2) (hqe : m ≤ |quadForm M e|) :
    m * ρ ^ 2 / 32 * Real.sqrt (ballVolume z (ρ / 4)) ≤
      ballL2 z ρ (fun x => c + inner ℝ p x + quadForm M x) := by
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => c + inner ℝ p x + quadForm M x with hgdef
  have hg : Continuous g := continuous_quadratic c p M
  set h : EuclideanSpace ℝ (Fin d) := (ρ / 4) • e with hh
  have hhn : ‖h‖ ≤ ρ / 2 := by
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ ρ / 4)
    linarith
  have hsub : ∀ k : EuclideanSpace ℝ (Fin d), ‖k‖ ≤ ρ / 2 → ball (z + k) (ρ / 4) ⊆ ball z ρ := by
    intro k hk x hx
    rw [mem_ball] at hx ⊢
    calc dist x z ≤ dist x (z + k) + dist (z + k) z := dist_triangle _ _ _
      _ < ρ / 4 + ρ / 2 := by
          rw [dist_eq_norm (z + k) z, add_sub_cancel_left]; linarith
      _ ≤ ρ := by linarith
  have hsd : ∀ x, g (x + h) + g (x + -h) + (-2 : ℝ) * g x = 2 * quadForm M h := by
    intro x
    have h1 := quadForm_add_add_sub M x h
    have e1 : inner ℝ p (x + h) = inner ℝ p x + inner ℝ p h := inner_add_right _ _ _
    have e2 : inner ℝ p (x + -h) = inner ℝ p x - inner ℝ p h := by
      rw [inner_add_right, inner_neg_right]; ring
    have e3 : x + -h = x - h := (sub_eq_add_neg x h).symm
    simp only [hgdef]
    rw [e1, e2, e3]
    linarith
  set μ₀ := volume.restrict (ball z (ρ / 4)) with hμ₀
  set E := eLpNorm g 2 (volume.restrict (ball z ρ)) with hE
  have hEfin : E ≠ ⊤ := (memLp_quadratic c p M z ρ).eLpNorm_ne_top
  have hT : ∀ k : EuclideanSpace ℝ (Fin d), ‖k‖ ≤ ρ / 2 →
      eLpNorm (fun x => g (x + k)) 2 μ₀ ≤ E := by
    intro k hk
    rw [hμ₀, eLpNorm_comp_add_ball hg z k (ρ / 4)]
    exact eLpNorm_mono_measure g (Measure.restrict_mono (hsub k hk) le_rfl)
  have h1 := hT h hhn
  have h2 := hT (-h) (by rw [norm_neg]; exact hhn)
  have h3 : eLpNorm ((-2 : ℝ) • g) 2 μ₀ ≤ 2 * E := by
    rw [eLpNorm_const_smul]
    have : ‖(-2 : ℝ)‖ₑ = 2 := by
      have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [enorm_neg, ← e2, Real.enorm_natCast]
      norm_num
    rw [this]
    have h0 : ball z (ρ / 4) ⊆ ball z ρ := ball_subset_ball (by linarith)
    have h0' : eLpNorm g 2 μ₀ ≤ E :=
      eLpNorm_mono_measure g (Measure.restrict_mono h0 (le_refl (volume : Measure _)))
    gcongr
  have hsum : eLpNorm (((fun x => g (x + h)) + fun x => g (x + -h)) + (-2 : ℝ) • g) 2 μ₀ ≤
      4 * E := by
    calc _ ≤ eLpNorm ((fun x => g (x + h)) + fun x => g (x + -h)) 2 μ₀ +
          eLpNorm ((-2 : ℝ) • g) 2 μ₀ :=
          eLpNorm_add_le (((hg.comp (continuous_id.add continuous_const)).add
            (hg.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
            (hg.const_smul _).aestronglyMeasurable (by norm_num)
      _ ≤ (eLpNorm (fun x => g (x + h)) 2 μ₀ + eLpNorm (fun x => g (x + -h)) 2 μ₀) + 2 * E :=
          add_le_add (eLpNorm_add_le
            (hg.comp (continuous_id.add continuous_const)).aestronglyMeasurable
            (hg.comp (continuous_id.add continuous_const)).aestronglyMeasurable (by norm_num)) h3
      _ ≤ (E + E) + 2 * E := add_le_add (add_le_add h1 h2) le_rfl
      _ = 4 * E := by ring
  have hconst : (((fun x => g (x + h)) + fun x => g (x + -h)) + (-2 : ℝ) • g) =
      fun _ => 2 * quadForm M h := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hsd x
  rw [hconst, eLpNorm_const' _ (by norm_num) (by norm_num), Measure.restrict_apply_univ] at hsum
  have hfin : (4 : ENNReal) * E ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hEfin
  have hreal := ENNReal.toReal_mono hfin hsum
  have hn : ‖2 * quadForm M h‖ₑ.toReal = |2 * quadForm M h| := by simp
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, one_div, ← sqrt_toReal_eq, hn] at hreal
  have h4 : (4 : ENNReal).toReal = 4 := by norm_num
  rw [h4] at hreal
  have hqh : quadForm M h = (ρ / 4) ^ 2 * quadForm M e := by rw [hh, quadForm_smul]
  have hlow : m * ρ ^ 2 / 8 ≤ |2 * quadForm M h| := by
    rw [hqh, abs_mul, abs_mul, abs_two, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ρ / 4) ^ 2)]
    have := mul_le_mul_of_nonneg_left hqe (by positivity : (0 : ℝ) ≤ 2 * (ρ / 4) ^ 2)
    nlinarith
  have hsv : 0 ≤ Real.sqrt (volume (ball z (ρ / 4))).toReal := Real.sqrt_nonneg _
  have h5 : m * ρ ^ 2 / 8 * Real.sqrt (volume (ball z (ρ / 4))).toReal ≤
      |2 * quadForm M h| * Real.sqrt (volume (ball z (ρ / 4))).toReal :=
    mul_le_mul_of_nonneg_right hlow hsv
  have h6 : ballL2 z ρ g = E.toReal := rfl
  rw [h6, ballVolume]
  linarith

end Rigidity.Proofs.Regularity
