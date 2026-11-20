import Rigidity.Percolation.LatticeBoundaryBonds

/-!
# Probabilities of extinction between successive regions

For decreasing survival events, the successive extinction events are
disjoint. On a finite measure space their probabilities tend to zero.
-/

namespace Rigidity.Percolation

open MeasureTheory Filter
open scoped Topology ENNReal

/-- Successive extinction events for decreasing survival events are disjoint. -/
theorem pairwise_disjoint_extinction_events {Ω : Type*} (E : ℕ → Set Ω)
    (hE : Antitone E) : Pairwise (fun n m => Disjoint (E n \ E (n + 1))
      (E m \ E (m + 1))) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro ω hωn hωm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hωn.2 (hE (Nat.succ_le_iff.mpr hlt) hωm.1)
  · exact hωm.2 (hE (Nat.succ_le_iff.mpr hgt) hωn.1)

/-- In a finite measure space, the probability of extinction between two
successive decreasing survival events tends to zero. -/
theorem tendsto_measure_extinction_events {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet (E n)) (hE : Antitone E) :
    Tendsto (fun n => μ (E n \ E (n + 1))) atTop (𝓝 0) := by
  let D : ℕ → Set Ω := fun n => E n \ E (n + 1)
  have htail := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (μ := μ) (Es := D) (fun n => ((hmeas n).diff (hmeas (n + 1))).nullMeasurableSet)
    (pairwise_disjoint_extinction_events E hE)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  exact Set.subset_iUnion_of_subset n (Set.subset_iUnion_of_subset le_rfl (Set.Subset.rfl))

/-- Events whose probabilities have a uniform positive finite-energy cost
relative to successive extinctions have probabilities tending to zero. -/
theorem tendsto_measure_of_extinction_cost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E A : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet (E n)) (hE : Antitone E)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hcost : ∀ n, c * μ (A n) ≤ μ (E n \ E (n + 1))) :
    Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
  have hlim := tendsto_measure_extinction_events μ E hmeas hE
  have hlim' : Tendsto (fun n => c⁻¹ * μ (E n \ E (n + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := c⁻¹) hlim (Or.inr (ENNReal.inv_ne_top.mpr hc0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun _ => zero_le) ?_
  intro n
  exact (ENNReal.mul_le_iff_le_inv hc0 hct).mp (hcost n)

end Rigidity.Percolation
