import Rigidity.Proofs.S2.PlanarAllMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Moment and tail bounds for planar density

The moment recursion gives polynomial moment growth and geometric tails at seventh-power
thresholds.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Planar density has `Lⁿ` norm at most `C n⁷ 3⁻ᵐ`. -/
theorem planar_density_moment_norms (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (k : Vertex 2),
      let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      MemLp (planarDensityRealObservable p m k) n P ∧
      lpNorm (planarDensityRealObservable p m k) n P ≤
        C * (n : ℝ) ^ 7 / ((3 ^ m : ℕ) : ℝ) := by
  obtain ⟨C, hC, hmom⟩ := planar_density_moment_roots p hp
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X := planarDensityRealObservable p m k
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  let b : ℝ := Real.sqrt C * (n : ℝ) ^ 7 / v
  have hv : 0 < v := by dsimp [v]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hXm : Measurable X := (planar_density_real_observable_properties p m k).1
  have hXb : ∀ ω, |X ω| ≤ 1 := (planar_density_real_observable_properties p m k).2.1
  have hXmem : MemLp X n P := by
    refine MemLp.of_bound hXm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hXb ω
  have hsq : lpNorm X n P ^ 2 ≤ C * (n : ℝ) ^ 14 / v ^ 2 := by
    rw [← planar_density_moment_root_eq_lpNorm_sq p m k n hn]
    exact hmom n hn m k
  have hbSq : b ^ 2 = C * (n : ℝ) ^ 14 / v ^ 2 := by
    dsimp [b]
    rw [div_pow, mul_pow, Real.sq_sqrt hC.le]
    congr 1
    ring
  refine ⟨hXmem, ?_⟩
  exact (sq_le_sq₀ lpNorm_nonneg hb).mp (by rwa [hbSq])

/-- The centered planar density has geometric tails at seventh-power thresholds. -/
theorem planar_density_moment_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (k : Vertex 2),
      (Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p))
        {ω | C * (n : ℝ) ^ 7 / ((3 ^ m : ℕ) : ℝ) ≤
          |planarDensityRealObservable p m k ω|} ≤ (1 / 2 : ℝ≥0∞) ^ n := by
  obtain ⟨C, hC, hmom⟩ := planar_density_moment_norms p hp
  refine ⟨2 * C, by positivity, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X := planarDensityRealObservable p m k
  let N : ℝ := C * (n : ℝ) ^ 7 / ((3 ^ m : ℕ) : ℝ)
  let t : ℝ := 2 * N
  have hn0 : n ≠ 0 := by omega
  have hp0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn0
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨hX, hnorm⟩ := hmom n hn m k
  have hnorm' : eLpNorm X n P ≤ ENNReal.ofReal N := by
    rw [← ofReal_lpNorm hX]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hmark := meas_ge_le_mul_pow_eLpNorm_enorm P hp0 (ENNReal.natCast_ne_top n)
    hX.aestronglyMeasurable (ε := ENNReal.ofReal t) (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
    (by simp)
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] at hmark
  have hevent : {ω | t ≤ |X ω|} = {ω | ENNReal.ofReal t ≤ ‖X ω‖ₑ} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  have htEq : t = 2 * C * (n : ℝ) ^ 7 / ((3 ^ m : ℕ) : ℝ) := by dsimp [t, N]; ring
  change P {ω | 2 * C * (n : ℝ) ^ 7 / ((3 ^ m : ℕ) : ℝ) ≤ |X ω|} ≤ _
  rw [← htEq, hevent]
  calc
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ n * eLpNorm X n P ^ n := hmark
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ n * (ENNReal.ofReal N) ^ n := by gcongr
    _ = (1 / 2 : ℝ≥0∞) ^ n := by
      rw [← mul_pow, ← ENNReal.ofReal_inv_of_pos ht,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
      have hhalf : t⁻¹ * N = (1 : ℝ) / 2 := by dsimp [t]; field_simp
      rw [hhalf]
      simp only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

end Rigidity.Proofs.S2
