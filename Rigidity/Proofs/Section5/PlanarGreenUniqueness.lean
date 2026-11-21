import Rigidity.Proofs.Section5.PlanarLiteratureAdapters
import Rigidity.Proofs.Section5.TrichotomyMeasurable

/-!
# Uniqueness of planar Green columns

The planar order-zero regularity estimate gives the uniqueness part of the Green-column input.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.External

/-- Existence of planar Green columns at each fixed pole. -/
def SupercriticalBondGreenColumnExistsTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃ g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g

end Rigidity.External

namespace Rigidity.Proofs.Section5

/-- The order-zero estimate and existence imply planar Green-column uniqueness. -/
theorem greenColumnExistenceTwo_of_exists
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistsTwo) :
    Rigidity.External.SupercriticalBondGreenColumnExistenceTwo := by
  intro p hpc hp1 y
  filter_upwards [hE p hpc hp1 y, sublinearLiouville_two p hpc hp1 hAD] with ω hEω hLω
  intro h hy
  obtain ⟨g, hg⟩ := hEω h hy
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact eq_of_isGreenColumn (hLω h) hg' hg

end Rigidity.Proofs.Section5
