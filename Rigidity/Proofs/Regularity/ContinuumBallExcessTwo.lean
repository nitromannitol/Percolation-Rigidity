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

end Rigidity.Proofs.Regularity
