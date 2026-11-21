import Rigidity.Proofs.Regularity.PlanarHarmonicRegularityTwo
import Rigidity.Proofs.Regularity.MesoscopicRegularity
import Rigidity.Proofs.Regularity.OrderZeroOrigin

/-!
# The form of Armstrong–Dario, Lemma 7.3, in the plane

In the normalized `L²` norms of Lebesgue measure on the discs of the plane, with `Ā(B_r)` the
harmonic functions, Lemma 7.2 of Armstrong and Dario (`armstrongDario_lemma_7_2_zero_planar`,
`armstrongDario_lemma_7_2_one_planar`) and the bound `mul_rpow_one_sub_mul_le` of its error term
give the form of Lemma 7.3 (arXiv:1609.09431v2):
`D_k(r) ≤ C (r / R)^{k+1} D_k(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}` for `k = 0, 1`, under the
harmonic approximation hypothesis with `R E ≤ ‖u‖_{L̲²(B_R)}`
(`armstrongDario_lemma_7_3_zero_planar`, `armstrongDario_lemma_7_3_one_planar`). The Campanato
argument then gives one constant `φ` with `‖u - φ‖_{L̲²(B_r)} ≤ C (r / R) B` for every `B` bounding
`D_0(R) + R E` (`armstrongDario_orderZero_origin_planar`), the constants having the same normalized
norm on every disc (`polynomialGrowth_continuumConstants`).
-/

open MeasureTheory Metric

namespace Rigidity.Proofs.Regularity

theorem ballExcess_le_continuumBallSeminorm {d : ℕ} (z : EuclideanSpace ℝ (Fin d))
    (P : AddSubgroup (locallySqIntegrable d)) (R : ℝ) (u : locallySqIntegrable d) :
    ballExcess (continuumBallSeminorm z) P R u ≤ continuumBallSeminorm z R u := by
  have := ballExcess_le (continuumBallSeminorm z) P (s := R) (u := u) (zero_mem P)
  rwa [sub_zero] at this

/-- **Armstrong–Dario, Lemma 7.3 (`k = 0`), in the plane.** -/
theorem armstrongDario_lemma_7_3_zero_planar {A α : ℝ} (hA : 2 ≤ A) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin 2)) (R X E : ℝ) (u : locallySqIntegrable 2),
      1 ≤ X → X ≤ R / A → 0 ≤ E → R * E ≤ continuumBallSeminorm z R u →
      HarmonicApproximation (continuumBallSeminorm z) (planarHarmonicClass z)
        (continuumConstants 2) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (continuumBallSeminorm z) (continuumConstants 2) r u ≤
          C * (r / R) * ballExcess (continuumBallSeminorm z) (continuumConstants 2) R u +
          2 * C * r ^ (-α) * (r / R) * continuumBallSeminorm z R u := by
  obtain ⟨C, hC, hlem⟩ := armstrongDario_lemma_7_2_zero_planar hA hα
  refine ⟨C, hC, fun z R X E u hX hXR hE hRE happ r hr hrR => ?_⟩
  have h1 := hlem z R X E u hX hXR hE happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_continuumBallSeminorm z (continuumConstants 2) R u) hRE
  linarith

/-- **Armstrong–Dario, Lemma 7.3 (`k = 1`), in the plane.** -/
theorem armstrongDario_lemma_7_3_one_planar {A α : ℝ} (hA : 2 ≤ A) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin 2)) (R X E : ℝ) (u : locallySqIntegrable 2),
      1 ≤ X → X ≤ R / A → 0 ≤ E → R * E ≤ continuumBallSeminorm z R u →
      HarmonicApproximation (continuumBallSeminorm z) (planarHarmonicClass z)
        (continuumConstants 2) A α X R E u →
      ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
        ballExcess (continuumBallSeminorm z) (continuumAffine 2) r u ≤
          C * (r / R) ^ 2 * ballExcess (continuumBallSeminorm z) (continuumAffine 2) R u +
          2 * C * r ^ (-α) * (r / R) * continuumBallSeminorm z R u := by
  obtain ⟨C, hC, hlem⟩ := armstrongDario_lemma_7_2_one_planar hA hα
  refine ⟨C, hC, fun z R X E u hX hXR hE hRE happ r hr hrR => ?_⟩
  have h1 := hlem z R X E u hX hXR hE happ r hr hrR
  have hr1 : 1 ≤ r := hX.trans ((le_max_left _ _).trans hr)
  have hR : 0 < R := by linarith
  have h2 := mul_rpow_one_sub_mul_le (α := α) hC.le hr1 hR hE
    (ballExcess_le_continuumBallSeminorm z (continuumConstants 2) R u) hRE
  linarith

theorem continuumBallSeminorm_const {d : ℕ} [NeZero d] (z : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : 0 < r) {f : locallySqIntegrable d} {a : ℝ}
    (hf : ∀ x, (f : EuclideanSpace ℝ (Fin d) → ℝ) x = a) :
    continuumBallSeminorm z r f = |a| := by
  have hfun : (f : EuclideanSpace ℝ (Fin d) → ℝ) = fun _ => a := funext hf
  have hV : 0 < ballVolume z r := by
    rw [ballVolume_eq z hr]; exact mul_pos (by positivity) unitBallVolume_pos
  rw [continuumBallSeminorm_apply, ballL2, hfun, eLpNorm_const' _ (by norm_num) (by norm_num),
    Measure.restrict_apply_univ, ENNReal.toReal_mul, one_div, ← sqrt_toReal_eq]
  have hm : ‖a‖ₑ.toReal = |a| := by simp
  rw [hm, ← ballVolume, mul_div_assoc, div_self (Real.sqrt_pos.2 hV).ne', mul_one]

/-- The constants have the same normalized norm on every disc. -/
theorem polynomialGrowth_continuumConstants {d : ℕ} [NeZero d] (z : EuclideanSpace ℝ (Fin d))
    {X R : ℝ} (hX : 0 < X) :
    PolynomialGrowth (continuumBallSeminorm z) (continuumConstants d) 0 X R 1 := by
  rintro w ⟨a, ha⟩ ρ r hXρ hρr _
  have hρ : 0 < ρ := hX.trans_le hXρ
  rw [continuumBallSeminorm_const z (hρ.trans_le hρr) ha, continuumBallSeminorm_const z hρ ha]
  simp

/-- **Order-zero regularity at the origin in the plane**, in the normalized `L²` norms of
Lebesgue measure: one constant `φ` with `‖u - φ‖_{L̲²(B_r)} ≤ C (r / R) B` for `r ∈ [X ∨ C, R / 2]`,
for every `B > 0` bounding `D_0(R) + R E`, under the harmonic approximation hypothesis. -/
theorem armstrongDario_orderZero_origin_planar {A α : ℝ} (hA : 2 ≤ A) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : EuclideanSpace ℝ (Fin 2)) (R X E : ℝ) (u : locallySqIntegrable 2),
      1 ≤ X → X ≤ R / A → 0 ≤ E →
      HarmonicApproximation (continuumBallSeminorm z) (planarHarmonicClass z)
        (continuumConstants 2) A α X R E u →
      ∀ B : ℝ, 0 < B →
        ballExcess (continuumBallSeminorm z) (continuumConstants 2) R u + R * E ≤ B →
        ∃ φ ∈ continuumConstants 2, ∀ r : ℝ, max X C ≤ r → r ≤ R / 2 →
          continuumBallSeminorm z r (u - φ) ≤ C * (r / R) * B := by
  obtain ⟨C, hC, h⟩ := armstrongDario_orderZero_origin.{0} hA hα (γ := ((2 : ℕ) : ℝ) / 2)
    (CV := 1) (CP := 4 * 2 ^ 2) (CH := 1024) (CG := 1) (by positivity) zero_le_one
    (by positivity) (by norm_num) zero_le_one
  refine ⟨C, hC, fun z R X E u hX hXR hE happ B hB hBu => ?_⟩
  have hX0 : 0 < X := by linarith
  exact h (continuumBallSeminorm z) (continuumConstants 2) (continuumAffine 2)
    (planarHarmonicClass z) R X E u continuumConstants_le_continuumAffine hX hXR hE
    (radiusMonotone_continuumBallSeminorm z hX0) (polynomialComparison_continuumAffine z hX0)
    (harmonicRegularity_planarHarmonicClass z R hX0)
    (fun r _ _ => ⟨0, zero_mem_planarHarmonicClass z r⟩) happ
    (polynomialGrowth_continuumConstants z hX0) B hB hBu

end Rigidity.Proofs.Regularity
