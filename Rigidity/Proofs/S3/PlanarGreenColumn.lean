import Rigidity.External.PlanarInputs
import LatticeProb.Prob.Percolation.GreenColumnEvent

/-!
# Planar Green columns at every pole

Countability combines the fixed-pole Green-column statement with uniqueness of the infinite
cluster.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation

/-- Almost surely every pole of the infinite cluster has a unique planar Green column. -/
theorem ae_unique_green_column_for_all_poles_two
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hU : LatticeProb.External.SupercriticalBondUniqueness) (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∃ _h : HasUniqueInfiniteOpenComponent ω,
        ∀ h' : HasUniqueInfiniteOpenComponent ω, ∀ y : uniqueInfiniteComponent h',
          ∃! g : uniqueInfiniteComponent h' → ℝ,
            IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h') y g := by
  have huniq : ∀ᵐ ω ∂latticeBondLaw 2 p, HasUniqueInfiniteOpenComponent ω := by
    apply (ae_mem_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent 2).nullMeasurableSet).2
    simpa using hU.2 2 le_rfl p hp hp1
  have hcols := ae_all_iff.mpr (hE p hp hp1)
  filter_upwards [huniq, hcols] with ω hω hcolsω
  refine ⟨hω, ?_⟩
  intro h' y
  simpa only using hcolsω y.val h' y.property

end Rigidity.Proofs.S3
