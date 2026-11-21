import Rigidity.Proofs.S2.PlanarDensityStochasticBound
import Rigidity.Proofs.S2.PlanarDensityEncodingTransfer

/-!
# Concentration of planar cluster density

The planar infinite-cluster density satisfies the Dario–Gu concentration estimate at the
central-limit scale.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External

/-- The real-encoded density has the cited exponential moment at inverse-length scale. -/
theorem planar_density_real_expOs (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
      Integrable (fun ω => Real.exp ((max (|planarDensityRealObservable p m k ω| /
        (C / ((3 ^ m : ℕ) : ℝ))) 0) ^ (2 / 15 : ℝ))) P ∧
      (∫ ω, Real.exp ((max (|planarDensityRealObservable p m k ω| /
        (C / ((3 ^ m : ℕ) : ℝ))) 0) ^ (2 / 15 : ℝ)) ∂P) ≤ 2 := by
  obtain ⟨C, hC, htail⟩ := planar_density_osBound p hp
  refine ⟨C * 4 ^ (15 : ℕ), by positivity, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X (ω : Bond 2 → ℝ) := |planarDensityRealObservable p m k ω|
  let θ : ℝ := C / ((3 ^ m : ℕ) : ℝ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hXm : Measurable X := (planar_density_real_observable_properties p m k).1.abs
  have hsmall := integrable_scaled_exponential_of_osBound P X (2 / 15) θ (by norm_num) hθ hXm
    ((htail m k).of_exponent_le (by norm_num))
  have hroot : ((4 : ℝ) ^ (15 : ℕ)) ^ (1 / 15 : ℝ) = 4 := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.pow_rpow_inv_natCast (x := (4 : ℝ)) (n := 15) (by norm_num) (by norm_num)
  have hpow : ((4 : ℝ) ^ (15 : ℕ)) ^ (2 / 15 : ℝ) = 16 := by
    rw [show (2 / 15 : ℝ) = (1 / 15 : ℝ) * 2 by norm_num,
      Real.rpow_mul (by positivity), hroot, Real.rpow_two]
    norm_num
  have hEq (ω : Bond 2 → ℝ) :
      (max (X ω / ((C * 4 ^ (15 : ℕ)) / ((3 ^ m : ℕ) : ℝ))) 0) ^ (2 / 15 : ℝ) =
        (max (X ω) 0 / θ) ^ (2 / 15 : ℝ) / 16 := by
    have hscale : (C * 4 ^ (15 : ℕ)) / ((3 ^ m : ℕ) : ℝ) = θ * 4 ^ (15 : ℕ) := by
      dsimp [θ]; ring
    have hX0 : 0 ≤ X ω := abs_nonneg _
    rw [max_eq_left (div_nonneg hX0 (by positivity)), max_eq_left hX0,
      hscale, div_mul_eq_div_div, Real.div_rpow (div_nonneg hX0 hθ.le) (by positivity), hpow]
  change Integrable (fun ω => Real.exp ((max (X ω /
      ((C * 4 ^ (15 : ℕ)) / ((3 ^ m : ℕ) : ℝ))) 0) ^ (2 / 15 : ℝ))) P ∧
    (∫ ω, Real.exp ((max (X ω /
      ((C * 4 ^ (15 : ℕ)) / ((3 ^ m : ℕ) : ℝ))) 0) ^ (2 / 15 : ℝ)) ∂P) ≤ 2
  simpa only [hEq] using hsmall

/-- Planar Dario–Gu concentration of the infinite-cluster density. -/
theorem planar_cluster_density_concentration : ClusterDensityConcentrationInputTwo := by
  intro p hp hp1
  obtain ⟨C, hC, hreal⟩ := planar_density_real_expOs p hp
  refine ⟨C, hC, fun m k => ?_⟩
  have hscale : (3 : ℝ) ^ (-((2 : ℝ) * (m : ℝ)) / 2) =
      1 / ((3 ^ m : ℕ) : ℝ) := by
    rw [show -((2 : ℝ) * (m : ℝ)) / 2 = -(m : ℝ) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
    push_cast
    simp
  have h := planar_density_isOsBond_of_real_encoding p m k (2 / 15)
    (C / ((3 ^ m : ℕ) : ℝ)) (hreal m k)
  have hexp : (2 * ((2 : ℝ) - 1) / (3 * (2 : ℝ) ^ 2 + 2 * (2 : ℝ) - 1)) =
      (2 / 15 : ℝ) := by norm_num
  rw [hexp, hscale]
  simpa only [div_eq_mul_inv, one_mul] using h

end Rigidity.Proofs.S2
