import Rigidity.Proofs.Regularity.PlanarHarmonicRegularityTwo
import Rigidity.Proofs.Regularity.MesoscopicRegularity

/-!
# The form of Armstrong–Dario, Lemma 7.3, in the plane

In the normalized `L²` norms of Lebesgue measure on the discs of the plane, with `Ā(B_r)` the
harmonic functions, Lemma 7.2 of Armstrong and Dario (`armstrongDario_lemma_7_2_zero_planar`,
`armstrongDario_lemma_7_2_one_planar`) and the bound `mul_rpow_one_sub_mul_le` of its error term
give the form of Lemma 7.3 (arXiv:1609.09431v2):
`D_k(r) ≤ C (r / R)^{k+1} D_k(R) + 2 C r^{-α} (r / R) ‖u‖_{L̲²(B_R)}` for `k = 0, 1`, under the
harmonic approximation hypothesis with `R E ≤ ‖u‖_{L̲²(B_R)}`
(`armstrongDario_lemma_7_3_zero_planar`, `armstrongDario_lemma_7_3_one_planar`).
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

end Rigidity.Proofs.Regularity
