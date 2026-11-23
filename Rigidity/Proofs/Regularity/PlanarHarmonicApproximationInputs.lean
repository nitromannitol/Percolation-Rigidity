import Rigidity.Proofs.Regularity.PlanarHarmonicDistTwo
import Rigidity.Proofs.Regularity.PlanarCorrectorReduction

/-!
# Lemma 7.1 and the order-zero regularity on the planar cluster from Theorem 1 and Proposition 2.4

The three estimates on squares of the proof of Armstrong–Dario, Lemma 7.1 (arXiv:1609.09431v2),
in dimension two, are proved almost surely above a minimal scale:

* (7.7), the harmonic approximation of `[u]_𝒫` (`planarHarmonicDistTwo_of_homogenizationError`),
  from Theorem 1 (`PlanarHomogenizationErrorTwo p p'`) and Proposition 2.4
  (`PlanarMinimalScalesTwo p`);
* (7.8), the comparison of `u` with `[u]_𝒫` (`planarCoarseComparisonTwo_of_minimalScales`);
* the bound of Step 2 with `w = a` (`planarCoarseBoundTwo_of_minimalScales`).

`planarSquareEstimatesTwo_of_parts` combines them into `PlanarSquareEstimatesTwo p` (with
`L = 6`), and `planarHarmonicApproximationTwo_of_inputs` gives Lemma 7.1 in dimension two
(`PlanarHarmonicApproximationTwo`) from Theorem 1 and Proposition 2.4 for every supercritical
`p`; `armstrongDarioOrderZeroTwo_of_inputs` gives the order-zero regularity of Theorem 2 (iii).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Percolation

/-- **The estimates on squares of the proof of Lemma 7.1** from (7.7), (7.8) and Step 2. -/
theorem planarSquareEstimatesTwo_of_parts {p : unitInterval} (h1 : PlanarHarmonicDistTwo p)
    (h2 : PlanarCoarseComparisonTwo p) (h3 : PlanarCoarseBoundTwo p) :
    PlanarSquareEstimatesTwo p := by
  obtain ⟨s₁, θ₁, C₁, α, hs₁, hθ₁, hC₁, hα, X₁, hX₁m, hX₁0, hX₁os, hae₁⟩ := h1
  obtain ⟨s₂, θ₂, K₂, hs₂, hθ₂, hK₂, X₂, hX₂m, hX₂0, hX₂os, hae₂⟩ := h2
  obtain ⟨s₃, θ₃, K₃, hs₃, hθ₃, hK₃, X₃, hX₃m, hX₃0, hX₃os, hae₃⟩ := h3
  obtain ⟨θ₁₂, hθ₁₂, h12⟩ := exists_isOsBond_max hs₁ hs₂ hθ₁ hθ₂ hX₁m hX₂m hX₁os hX₂os
  obtain ⟨θX, hθX, hXos⟩ := exists_isOsBond_max (lt_min hs₁ hs₂) hs₃ hθ₁₂ hθ₃ (hX₁m.max hX₂m)
    hX₃m h12 hX₃os
  refine ⟨_, θX, 6, C₁, K₂, K₃, α, lt_min (lt_min hs₁ hs₂) hs₃, hθX, by norm_num, hC₁, hK₂, hK₃,
    hα, _, (hX₁m.max hX₂m).max hX₃m,
    fun ω => (hX₁0 ω).trans ((le_max_left _ _).trans (le_max_left _ _)), hXos, ?_⟩
  filter_upwards [hae₁, hae₂, hae₃] with ω hω₁ hω₂ hω₃ h R u hu j hj hjR
  have hj1 : X₁ ω ≤ 3 ^ j := ((le_max_left _ _).trans (le_max_left _ _)).trans hj
  have hj2 : X₂ ω ≤ 3 ^ j := ((le_max_right _ _).trans (le_max_left _ _)).trans hj
  have hj3 : X₃ ω ≤ 3 ^ j := (le_max_right _ _).trans hj
  have hjR2 : 2 * 3 ^ (j + 3) ≤ R := by
    have : (0 : ℝ) ≤ 3 ^ (j + 3) := by positivity
    linarith
  exact ⟨hω₁ h R u hu j hj1 hjR, hω₂ h R u hu j hj2 hjR2, hω₃ h R u hu j hj3 hjR2⟩

/-- **Armstrong–Dario, Lemma 7.1, in dimension two**, from Theorem 1 in dimension two with the
discrete homogenized solution and Proposition 2.4 for the planar partitions. -/
theorem planarHarmonicApproximationTwo_of_inputs
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hHE : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ p' : ℝ, 2 < p' → PlanarHomogenizationErrorTwo p p') :
    PlanarHarmonicApproximationTwo :=
  planarHarmonicApproximationTwo_of_squareEstimates
    (fun p hpc hp1 => planarSquareEstimatesTwo_of_parts
      (planarHarmonicDistTwo_of_homogenizationError hpc hp1 (hM5 p hpc hp1) (hHE p hpc hp1))
      (planarCoarseComparisonTwo_of_minimalScales hpc hp1 (hM5 p hpc hp1))
      (planarCoarseBoundTwo_of_minimalScales hpc hp1 (hM5 p hpc hp1)))
    (fun p hpc hp1 => planarPartitionSizeScale_of_minimalScales (hM5 p hpc hp1))

/-- **Armstrong–Dario, Theorem 2 (iii) for `k = 0`, in dimension two**, from Theorem 1 in
dimension two with the discrete homogenized solution and Proposition 2.4. -/
theorem armstrongDarioOrderZeroTwo_of_inputs
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hHE : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ p' : ℝ, 2 < p' → PlanarHomogenizationErrorTwo p p') :
    ArmstrongDarioOrderZeroTwo :=
  armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation
    (planarHarmonicApproximationTwo_of_inputs hM5 hHE)

end Rigidity.Proofs.Regularity
