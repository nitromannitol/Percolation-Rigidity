import Rigidity.Proofs.Percolation.PlanarSitePaths

/-!
# The density of planar good sites

The probability that a site has a closed outgoing bond is at most twice the closed-bond
probability.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation
open scoped ENNReal

noncomputable section

namespace Rigidity.Percolation

/-- The probability that a bond is closed is `1 - p`. -/
theorem latticeBondLaw_closed (p : unitInterval) (e : Bond 2) :
    latticeBondLaw 2 p {ω | ω e = false} = ENNReal.ofReal (1 - (p : ℝ)) := by
  have he : {ω : Configuration 2 | ω e = false} = {ω | ω e = true}ᶜ := by
    ext ω
    cases h : ω e <;> simp [h]
  have hm : MeasurableSet {ω : Configuration 2 | ω e = true} := by
    have h := (measurable_pi_apply e : Measurable fun ω : Configuration 2 => ω e)
      (measurableSet_singleton (true : Bool))
    simpa only [Set.preimage, Set.mem_singleton_iff] using h
  rw [he, prob_compl_eq_one_sub hm, latticeBondLaw_open,
    ENNReal.ofReal_sub _ p.property.1, ENNReal.ofReal_one]

/-- A site with a closed outgoing bond has probability at most `2(1 - p)`. -/
theorem outgoingField_closed_le (p : unitInterval) (z : PlanarCarrier) :
    (latticeBondLaw 2 p).map outgoingField {η | η z = false} ≤
      ENNReal.ofReal (2 * (1 - (p : ℝ))) := by
  have hmeas : MeasurableSet {η : PlanarCarrier → Bool | η z = false} := by
    have h := (measurable_pi_apply z : Measurable fun η : PlanarCarrier → Bool => η z)
      (measurableSet_singleton (false : Bool))
    simpa only [Set.preimage, Set.mem_singleton_iff] using h
  rw [Measure.map_apply measurable_outgoingField hmeas]
  calc
    _ ≤ latticeBondLaw 2 p (⋃ i : Fin 2, {ω | ω (outgoingBond z i) = false}) := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_setOf_eq] at hω
      have hn : ¬ ∀ i : Fin 2, ω (outgoingBond z i) = true := by
        simpa only [outgoingField, decide_eq_false_iff_not] using hω
      push Not at hn
      obtain ⟨i, hi⟩ := hn
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      cases h : ω (outgoingBond z i) <;> simp_all
    _ ≤ ∑ i : Fin 2, latticeBondLaw 2 p {ω | ω (outgoingBond z i) = false} :=
      measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal (2 * (1 - (p : ℝ))) := by
      simp only [latticeBondLaw_closed, Fin.sum_univ_two]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [two_mul]

end Rigidity.Percolation
