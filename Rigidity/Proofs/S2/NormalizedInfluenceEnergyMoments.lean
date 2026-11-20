import Rigidity.Proofs.S2.InfluenceEnergyMoments

/-!
# Moments of normalized planar resampling energy

Normalizing by the triadic cube volume gives inverse-volume `Lʳ` bounds for the total
resampling energy.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The normalized planar density resampling energy has `Lʳ` norm at most `C r¹² 3⁻²ᵐ`. -/
theorem planar_normalized_density_energy_moments (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex 2),
      (∀ᵐ q : Configuration 2 × Configuration 2
          ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)),
        Summable (fun e : Bond 2 =>
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ) -
              (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
                ((triadicCube 2 m k).ncard : ℝ)| ^ 2)) ∧
      MemLp (fun q : Configuration 2 × Configuration 2 => ∑' e : Bond 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2)
        r ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      lpNorm (fun q : Configuration 2 × Configuration 2 => ∑' e : Bond 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) /
              ((triadicCube 2 m k).ncard : ℝ)| ^ 2)
        r ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ≤
          C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hraw⟩ := planar_density_resampling_energy_moments p hp
  refine ⟨4 * C, by positivity, fun r hr m k => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  let V : ℝ := (triadicCube 2 m k).ncard
  let c : ℝ := 1 / V ^ 2
  let f (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ 2
  let g (e : Bond 2) (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) / V -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ) / V| ^ 2
  let F (q : Configuration 2 × Configuration 2) : ℝ := ∑' e, f e q
  let G (q : Configuration 2 × Configuration 2) : ℝ := ∑' e, g e q
  have hv1 : 1 ≤ v := by
    have h : 0 < (3 : ℕ) ^ m := by positivity
    change (1 : ℝ) ≤ ((3 ^ m : ℕ) : ℝ)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt h))
  have hv : 0 < v := zero_lt_one.trans_le hv1
  have hv2 : 0 < v ^ 2 := pow_pos hv 2
  have hV : V = v ^ 2 := by
    dsimp only [V, v]
    rw [ncard_triadicCube]
    push_cast
    rw [show 2 * m = m * 2 by omega, pow_mul]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hfg (e : Bond 2) (q : Configuration 2 × Configuration 2) : g e q = c * f e q := by
    dsimp only [f, g, c]
    rw [← sub_div, abs_div, div_pow]
    simp only [sq_abs]
    ring
  have hGF : G = fun q => c * F q := by
    funext q
    dsimp only [G, F]
    simp_rw [hfg]
    exact tsum_mul_left
  obtain ⟨hSummable, hF, hFnorm⟩ := hraw r hr m k
  have hG : MemLp G r μ := by
    rw [hGF]
    exact hF.const_mul c
  have hGnorm : lpNorm G r μ = c * lpNorm F r μ := by
    rw [hGF]
    change lpNorm (c • F) r μ = _
    rw [lpNorm_const_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg hc]
  have hdiv : (v + 1) ^ 2 / v ^ 2 ≤ 4 := by
    apply (div_le_iff₀ hv2).2
    nlinarith [sq_nonneg (v - 1)]
  have hscale : c * (C * (r : ℝ) ^ 12 * (v + 1) ^ 2) ≤
      (4 * C) * (r : ℝ) ^ 12 / v ^ 2 := by
    rw [show c = 1 / (v ^ 2) ^ 2 by simp only [c, hV]]
    calc
      _ = (C * (r : ℝ) ^ 12 / v ^ 2) * ((v + 1) ^ 2 / v ^ 2) := by field_simp
      _ ≤ (C * (r : ℝ) ^ 12 / v ^ 2) * 4 :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  refine ⟨?_, hG, ?_⟩
  · filter_upwards [hSummable] with q hq
    change Summable (fun e => g e q)
    simpa only [hfg] using hq.mul_left c
  · rw [hGnorm]
    exact (mul_le_mul_of_nonneg_left hFnorm hc).trans hscale

end Rigidity.Proofs.S2
