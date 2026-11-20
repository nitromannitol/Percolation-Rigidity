import Rigidity.Proofs.S2.NormalizedInfluenceEnergy
import LatticeProb.Prob.EfronSteinCountable

/-!
# Real encoding of Bernoulli bond configurations

The Boolean Bernoulli product law is the image of the real-valued Bernoulli product law under
coordinatewise decoding, and decoding commutes with resampling a coordinate.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation

/-- Decode the two points supporting a real Bernoulli measure. -/
noncomputable def bernoulliRealBit (x : ℝ) : Bool := if x = 1 then true else false

/-- Decode each coordinate of a real-valued bond configuration. -/
noncomputable def bernoulliRealConfiguration {d : ℕ} (ω : Bond d → ℝ) : Configuration d :=
  fun e => bernoulliRealBit (ω e)

/-- The Bernoulli bit decoder is measurable. -/
theorem measurable_bernoulliRealBit : Measurable bernoulliRealBit := by
  classical
  exact Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const

/-- The real Bernoulli law pushes forward to the Boolean Bernoulli law. -/
theorem map_bernoulliRealBit (p : unitInterval) :
    (bernoulliMeasure (1 : ℝ) 0 p).map bernoulliRealBit = bernoulliMeasure true false p := by
  rw [map_bernoulliMeasure' _ _ measurable_bernoulliRealBit]
  simp [bernoulliRealBit]

/-- Coordinatewise decoding preserves the Bernoulli product law. -/
theorem measurePreserving_bernoulliRealConfiguration (d : ℕ) (p : unitInterval) :
    MeasurePreserving (bernoulliRealConfiguration (d := d))
      (Measure.infinitePi fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p)
      (latticeBondLaw d p) := by
  refine ⟨measurable_pi_lambda _ fun e => measurable_bernoulliRealBit.comp (measurable_pi_apply e), ?_⟩
  change Measure.map (fun (ω : Bond d → ℝ) (e : Bond d) => bernoulliRealBit (ω e))
    (Measure.infinitePi fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p) = latticeBondLaw d p
  rw [latticeBondLaw, Measure.infinitePi_map_pi
    (fun _ : Bond d => bernoulliMeasure (1 : ℝ) 0 p) (fun _ => measurable_bernoulliRealBit)]
  simp only [map_bernoulliRealBit]

/-- Updating a real coordinate then decoding is the same as updating its decoded bit. -/
theorem bernoulliRealConfiguration_update {d : ℕ} (ω : Bond d → ℝ) (e : Bond d) (x : ℝ) :
    bernoulliRealConfiguration (Function.update ω e x) =
      Function.update (bernoulliRealConfiguration ω) e (bernoulliRealBit x) := by
  classical
  funext f
  by_cases h : f = e
  · subst f
    simp [bernoulliRealConfiguration]
  · simp [bernoulliRealConfiguration, Function.update_of_ne h]

end Rigidity.Proofs.S2
