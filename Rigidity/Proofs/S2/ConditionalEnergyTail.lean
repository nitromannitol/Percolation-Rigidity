import PercolationClusterHomogenization.Proofs.Density.ConditionalEnergyMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Rigidity.Proofs.S2.NormalizedEnergyOsMoment

/-!
# Tail estimates for conditional planar resampling energy

The conditional moment estimates yield geometric probability bounds at polynomial thresholds.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The normalized resampling energy has geometric tails at polynomially spaced thresholds. -/
theorem planar_conditional_density_energy_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ), 1 ≤ r → ∀ (m : ℕ) (k : Vertex 2)
      (𝓜 : MeasurableSpace (Configuration 2 × Configuration 2)),
      ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
        {q : Configuration 2 × Configuration 2 |
          C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2) ≤
            |MeasureTheory.condExp 𝓜 ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
              (planarDensityResamplingEnergy m k) q|} ≤ (1 / 2 : ℝ≥0∞) ^ r := by
  obtain ⟨C, hC, hmom⟩ := planar_conditional_density_energy_moments p hp
  refine ⟨2 * C, by positivity, fun r hr m k 𝓜 => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let Z := MeasureTheory.condExp 𝓜 μ (planarDensityResamplingEnergy m k)
  let Y : Configuration 2 × Configuration 2 → ℝ := fun q => |Z q|
  let N : ℝ := C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2)
  let t : ℝ := 2 * N
  have hr0 : r ≠ 0 := by omega
  have hp0 : (r : ℝ≥0∞) ≠ 0 := by exact_mod_cast hr0
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hY0 (q : Configuration 2 × Configuration 2) : 0 ≤ Y q :=
    abs_nonneg _
  obtain ⟨hZ, hnorm⟩ := hmom r hr m k 𝓜
  have hY : MemLp Y r μ := hZ.abs
  have hYnorm : lpNorm Y r μ = lpNorm Z r μ := lpNorm_abs hZ.aestronglyMeasurable r
  have hnorm' : eLpNorm Y r μ ≤ ENNReal.ofReal N := by
    rw [← ofReal_lpNorm hY]
    exact ENNReal.ofReal_le_ofReal (hYnorm.trans_le hnorm)
  have hmark := meas_ge_le_mul_pow_eLpNorm_enorm μ hp0 (ENNReal.natCast_ne_top r)
    hY.aestronglyMeasurable (ε := ENNReal.ofReal t) (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
    (by simp)
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] at hmark
  have hevent : {q | t ≤ Y q} = {q | ENNReal.ofReal t ≤ ‖Y q‖ₑ} := by
    ext q
    simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hY0 q),
      ENNReal.ofReal_le_ofReal_iff (hY0 q)]
  have htEq : t = 2 * C * (r : ℝ) ^ 12 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
    dsimp [t, N]
    ring
  rw [← htEq]
  change μ {q | t ≤ Y q} ≤ (1 / 2 : ℝ≥0∞) ^ r
  rw [hevent]
  calc
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ r * eLpNorm Y r μ ^ r := hmark
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ r * (ENNReal.ofReal N) ^ r := by gcongr
    _ = (1 / 2 : ℝ≥0∞) ^ r := by
      rw [← mul_pow, ← ENNReal.ofReal_inv_of_pos ht,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
      have hhalf : t⁻¹ * N = (1 : ℝ) / 2 := by
        dsimp [t]
        field_simp
      rw [hhalf]
      simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

end Rigidity.Proofs.S2
