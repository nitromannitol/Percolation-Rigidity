import Rigidity.Proofs.S2.PlanarDyadicMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# All moment bounds for planar density

Monotonicity of moment norms extends the dyadic estimates to every positive integer order.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- A planar density moment root is the square of its `Lⁿ` norm. -/
theorem planar_density_moment_root_eq_lpNorm_sq (p : unitInterval) (m : ℕ) (k : Vertex 2)
    (n : ℕ) (hn : 1 ≤ n) :
    let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
    planarDensityMomentRoot p m k n = lpNorm (planarDensityRealObservable p m k) n P ^ 2 := by
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X := planarDensityRealObservable p m k
  let M : ℝ := ∫ ω, |X ω| ^ n ∂P
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hM : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hm : Measurable X := (planar_density_real_observable_properties p m k).1
  change M ^ (2 / (n : ℝ)) = lpNorm X n P ^ 2
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hn0)
    (ENNReal.natCast_ne_top n) hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  change M ^ (2 / (n : ℝ)) = (M ^ (n : ℝ)⁻¹) ^ 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
  congr 1
  field_simp
  norm_num

/-- All positive integer squared moment norms grow at most polynomially in the order. -/
theorem planar_density_moment_roots (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (m : ℕ) (k : Vertex 2),
      planarDensityMomentRoot p m k n ≤
        C * (n : ℝ) ^ 14 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hdyad⟩ := planar_density_dyadic_moment_roots p hp
  refine ⟨C * (2 : ℝ) ^ 14, by positivity, fun n hn m k => ?_⟩
  let j := Nat.log 2 n
  let N : ℕ := 2 ^ (j + 1)
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X := planarDensityRealObservable p m k
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  have hn0 : n ≠ 0 := by omega
  have hnN : n ≤ N := by
    dsimp [N, j]
    exact (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n).le
  have hN2 : 2 ≤ N := by
    dsimp [N]
    exact Nat.le_pow (by omega : 1 ≤ j + 1)
  have hNle : N ≤ 2 * n := by
    dsimp [N, j]
    rw [pow_succ]
    have h := Nat.pow_log_le_self 2 hn0
    omega
  have hXm : Measurable X := (planar_density_real_observable_properties p m k).1
  have hXb : ∀ ω, |X ω| ≤ 1 := (planar_density_real_observable_properties p m k).2.1
  have hXN : MemLp X N P := by
    refine MemLp.of_bound hXm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hXb ω
  have hnorm : lpNorm X n P ≤ lpNorm X N P := by
    rw [← toReal_eLpNorm hXm.aestronglyMeasurable,
      ← toReal_eLpNorm hXm.aestronglyMeasurable]
    exact ENNReal.toReal_mono hXN.2.ne
      (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hnN) hXm.aestronglyMeasurable)
  have hroot : planarDensityMomentRoot p m k n ≤ planarDensityMomentRoot p m k N := by
    rw [planar_density_moment_root_eq_lpNorm_sq p m k n hn,
      planar_density_moment_root_eq_lpNorm_sq p m k N (by omega)]
    exact pow_le_pow_left₀ lpNorm_nonneg hnorm 2
  have hpow : (N : ℝ) ^ 14 ≤ (2 * (n : ℝ)) ^ 14 := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg N)
    exact_mod_cast hNle
  have hv0 : 0 ≤ v ^ 2 := by positivity
  calc
    _ ≤ planarDensityMomentRoot p m k N := hroot
    _ ≤ C * (N : ℝ) ^ 14 / v ^ 2 := hdyad j m k
    _ ≤ C * (2 * (n : ℝ)) ^ 14 / v ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le) hv0
    _ = _ := by rw [mul_pow]; ring

end Rigidity.Proofs.S2
