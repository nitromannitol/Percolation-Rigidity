import Rigidity.Proofs.Percolation.PlanarProbability
import Rigidity.Proofs.Percolation.DimensionMonotonicity

/-!
# The planar critical probability is below one

A Peierls estimate for the outgoing-bond site field gives positive probability of an infinite
open bond cluster at a parameter strictly below one. This is the standard high-density argument
for G. Grimmett, *Percolation*, 2nd ed. (1999), Theorem (1.10).
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation
open scoped ENNReal

noncomputable section

namespace Rigidity.Percolation

open Rigidity.Steps.Section5 Rigidity.Proofs.Section5

/-- A concrete high-density parameter for planar bond percolation. -/
def highDensityParameter : unitInterval :=
  ⟨1 - 1 / (4 * (64 : ℝ) ^ 9), by constructor <;> norm_num⟩

/-- The high-density parameter is strictly below one. -/
theorem highDensityParameter_lt_one : (highDensityParameter : ℝ) < 1 := by
  norm_num [highDensityParameter]

/-- The origin percolates with positive probability at the high-density parameter. -/
theorem theta_highDensityParameter_pos :
    0 < LatticeProb.Percolation.theta 2 highDensityParameter := by
  let p := highDensityParameter
  let ν := (latticeBondLaw 2 p).map outgoingField
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map measurable_outgoingField.aemeasurable
  have hε : 0 ≤ 2 * (1 - (p : ℝ)) := by
    have := p.property.2
    positivity
  have hbad := measure_not_inInfiniteSiteCluster_le (outgoingField_oneDependent p) hε
    (outgoingField_closed_le p) (0, 0)
  have hnum : (64 : ℝ) ^ 9 * (2 * (1 - (p : ℝ))) = 1 / 2 := by
    norm_num [p, highDensityParameter]
  have hbadlt : ν {η | ¬ InInfiniteSiteCluster η (0, 0)} < 1 := by
    apply lt_of_le_of_lt hbad
    rw [hnum, ENNReal.ofReal_lt_one]
    norm_num
  let A : Set (PlanarCarrier → Bool) := {η | InInfiniteSiteCluster η (0, 0)}
  have hA : MeasurableSet A := infiniteClusterMeasurableStep (0, 0)
  have hApos : 0 < ν A := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hb : ν Aᶜ = 1 := (prob_compl_eq_one_iff hA).mpr hz
    exact (ne_of_lt hbadlt) hb
  have hmap : ν A = latticeBondLaw 2 p (outgoingField ⁻¹' A) :=
    Measure.map_apply measurable_outgoingField hA
  have hsub : outgoingField ⁻¹' A ⊆ infiniteComponentEvent (0 : Vertex 2) := by
    intro ω hω
    have h := infiniteComponent_of_outgoingSite ω (0, 0) hω
    have h0 : toSite2 (0, 0) = (0 : Vertex 2) := by
      funext i
      fin_cases i <;> rfl
    rw [h0] at h
    exact h
  have hpos : 0 < latticeBondLaw 2 p (infiniteComponentEvent (0 : Vertex 2)) := by
    rw [hmap] at hApos
    exact hApos.trans_le (measure_mono hsub)
  change 0 < (latticeBondLaw 2 p).real (infiniteComponentEvent 0)
  rw [measureReal_def]
  exact ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)

/-- The critical probability in dimension two is strictly less than one. -/
theorem criticalProbability_two_lt_one : criticalProbability 2 < 1 :=
  (criticalProbability_le highDensityParameter theta_highDensityParameter_pos).trans_lt
    highDensityParameter_lt_one

/-- The critical probability is strictly below one in every dimension at least two. -/
theorem criticalProbability_lt_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    criticalProbability d < 1 :=
  (criticalProbability_antitone hd).trans_lt criticalProbability_two_lt_one

end Rigidity.Percolation
