import Rigidity.Proofs.S2.InfluenceEnergyMean

/-!
# Normalized planar density resampling energy

Dividing the cluster count by the cube volume gives a resampling energy whose mean decays as the
inverse cube volume.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The normalized planar density resampling energy has inverse-volume mean. -/
theorem planar_normalized_density_resampling_energy_mean (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      (∫⁻ q : Configuration 2 × Configuration 2,
        ∑' e : Bond 2, ENNReal.ofReal
          (|(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2)
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤
        ENNReal.ofReal (C / (((3 ^ m : ℕ) : ℝ) ^ 2)) ∧
      ∀ᵐ q ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)),
        (∑' e : Bond 2, ENNReal.ofReal
          (|(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2)) < ⊤ := by
  classical
  obtain ⟨C, hC, hraw⟩ := planar_density_resampling_energy_mean p hp
  refine ⟨4 * C, by positivity, fun m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  let V : ℝ := (triadicCube 2 m k).ncard
  let c : ℝ := 1 / V ^ 2
  let F (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2
  let G (q : Configuration 2 × Configuration 2) : ℝ≥0∞ := ∑' e, ENNReal.ofReal (F e q)
  let H (q : Configuration 2 × Configuration 2) : ℝ≥0∞ := ∑' e, ENNReal.ofReal
    (|(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) / V -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) / V| ^ 2)
  have hv1 : 1 ≤ v := by
    have hvNat : 0 < (3 : ℕ) ^ m := by positivity
    have hvNat' : 1 ≤ (3 : ℕ) ^ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hvNat)
    change (1 : ℝ) ≤ ((3 ^ m : ℕ) : ℝ)
    exact_mod_cast hvNat'
  have hv : 0 < v := zero_lt_one.trans_le hv1
  have hv2 : 0 < v ^ 2 := pow_pos hv 2
  have hV : V = v ^ 2 := by
    dsimp only [V, v]
    rw [ncard_triadicCube]
    push_cast
    rw [show 2 * m = m * 2 by omega, pow_mul]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hGm : AEMeasurable G μ := AEMeasurable.tsum fun e =>
    ((measurable_count_influence m k e).pow_const 2).ennreal_ofReal.aemeasurable
  have hscale (q : Configuration 2 × Configuration 2) : H q = ENNReal.ofReal c * G q := by
    dsimp only [H, G]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro e
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    dsimp only [F, c]
    rw [← sub_div, abs_div, div_pow]
    simp only [sq_abs]
    ring
  have hrawMean := (hraw m k).1
  have hrawAE := (hraw m k).2
  have hdiv : (v + 1) ^ 2 / v ^ 2 ≤ 4 := by
    apply (div_le_iff₀ hv2).2
    nlinarith [sq_nonneg (v - 1)]
  have hreal : c * (C * (v + 1) ^ 2) ≤ (4 * C) / v ^ 2 := by
    rw [show c = 1 / (v ^ 2) ^ 2 by simp only [c, hV]]
    calc
      _ = (C / v ^ 2) * ((v + 1) ^ 2 / v ^ 2) := by field_simp
      _ ≤ (C / v ^ 2) * 4 := mul_le_mul_of_nonneg_left hdiv (div_nonneg hC.le hv2.le)
      _ = _ := by ring
  have hmean : (∫⁻ q, H q ∂μ) ≤ ENNReal.ofReal ((4 * C) / v ^ 2) := by
    simp_rw [hscale]
    rw [lintegral_const_mul'' _ hGm]
    calc
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (C * (v + 1) ^ 2) :=
        mul_le_mul_right hrawMean _
      _ = ENNReal.ofReal (c * (C * (v + 1) ^ 2)) := (ENNReal.ofReal_mul hc).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  refine ⟨hmean, ?_⟩
  filter_upwards [hrawAE] with q hq
  change H q < ⊤
  rw [hscale]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hq

end Rigidity.Proofs.S2
