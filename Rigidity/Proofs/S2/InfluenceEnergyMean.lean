import Rigidity.Proofs.S2.InfluenceMomentSummation

/-!
# Mean resampling energy for planar cluster density

The sum of squared single-bond influences is finite almost surely, and its mean is bounded at the
volume scale of the counting cube.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The unnormalized planar density resampling energy has volume-scale mean. -/
theorem planar_density_resampling_energy_mean (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      (∫⁻ q : Configuration 2 × Configuration 2,
        ∑' e : Bond 2, ENNReal.ofReal
          (|(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤
        ENNReal.ofReal (C * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2) ∧
      ∀ᵐ q ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)),
        (∑' e : Bond 2, ENNReal.ofReal
          (|(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2)) < ⊤ := by
  classical
  obtain ⟨a, A, a', A', D, ha, hA, ha', hA', hD, hmoment⟩ :=
    planar_density_influence_moments_summable p hp
  let M : ℝ := max ((4 : ℝ) ^ (2 + 1) * (((2 * 2).factorial : ℝ) / a ^ (2 * 2)) * A)
    (Real.sqrt ((4 : ℝ) ^ (2 * 2 + 1) *
      (((2 * (2 * 2)).factorial : ℝ) / a' ^ (2 * (2 * 2))) * A'))
  let C : ℝ := D * (M + 1)
  have hM : 0 ≤ M := (Real.sqrt_nonneg _).trans (le_max_right _ _)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let F (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2
  let G (q : Configuration 2 × Configuration 2) : ℝ≥0∞ := ∑' e, ENNReal.ofReal (F e q)
  obtain ⟨hInt, hSum, hBound⟩ := hmoment m k 2 (by norm_num)
  have hF0 (e : Bond 2) (q : Configuration 2 × Configuration 2) : 0 ≤ F e q := by
    dsimp [F]; positivity
  have hFm (e : Bond 2) : Measurable (F e) := (measurable_count_influence m k e).pow_const 2
  have hGm : AEMeasurable G μ := AEMeasurable.tsum fun e => (hFm e).ennreal_ofReal.aemeasurable
  have hL : (∫⁻ q, G q ∂μ) = ENNReal.ofReal (∑' e, ∫ q, F e q ∂μ) := by
    dsimp only [G]
    rw [lintegral_tsum (fun e => (hFm e).ennreal_ofReal.aemeasurable)]
    have hterm (e : Bond 2) : (∫⁻ q, ENNReal.ofReal (F e q) ∂μ) =
        ENNReal.ofReal (∫ q, F e q ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hInt e) (Filter.Eventually.of_forall (hF0 e))).symm
    simp_rw [hterm]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun e => integral_nonneg (hF0 e)) hSum).symm
  have hreal : (∑' e, ∫ q, F e q ∂μ) ≤ C * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ D * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2 * M := hBound
      _ ≤ C * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2 := by
        dsimp only [C]
        nlinarith [mul_nonneg hD.le (sq_nonneg (((3 ^ m : ℕ) : ℝ) + 1))]
  have hlin : (∫⁻ q, G q ∂μ) ≤ ENNReal.ofReal (C * (((3 ^ m : ℕ) : ℝ) + 1) ^ 2) := by
    rw [hL]
    exact ENNReal.ofReal_le_ofReal hreal
  refine ⟨hlin, ?_⟩
  exact ae_lt_top' hGm (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)

end Rigidity.Proofs.S2
