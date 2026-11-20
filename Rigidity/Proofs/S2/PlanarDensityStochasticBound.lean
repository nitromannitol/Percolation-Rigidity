import Rigidity.Proofs.S2.GeometricSeventhTail

/-!
# Stretched-exponential concentration of planar density

The centered density has a stretched-exponential tail at the central-limit scale.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The centered planar density has an inverse-length `O₁/₇` tail. -/
theorem planar_density_osBound (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (k : Vertex 2),
      LatticeProb.OsBound
        (Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)) (1 / 7 : ℝ)
        (C / ((3 ^ m : ℕ) : ℝ))
        (fun ω => |planarDensityRealObservable p m k ω|) := by
  obtain ⟨C, hC, htail⟩ := planar_density_moment_tail p hp
  refine ⟨C * 4 ^ (7 : ℕ), by positivity, fun m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X (ω : Bond 2 → ℝ) := |planarDensityRealObservable p m k ω|
  let v : ℝ := ((3 ^ m : ℕ) : ℝ)
  have hv : 0 < v := by dsimp [v]; positivity
  have hgrid (n : ℕ) (hn : 1 ≤ n) : P {ω | (C / v) * (n : ℝ) ^ 7 ≤ X ω} ≤
      (1 / 2 : ℝ≥0∞) ^ n := by
    have heq : (C / v) * (n : ℝ) ^ 7 = C * (n : ℝ) ^ 7 / v := by ring
    simpa only [heq] using htail n hn m k
  have h := osBound_one_seventh_of_geometric_tails P X (C / v) (by positivity)
    (fun ω => abs_nonneg _) hgrid
  have hscale : C / v * 4 ^ (7 : ℕ) = (C * 4 ^ (7 : ℕ)) / v := by ring
  simpa only [hscale] using h

end Rigidity.Proofs.S2
