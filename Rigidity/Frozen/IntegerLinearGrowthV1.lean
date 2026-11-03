import Rigidity.Support.IntegerLinearGrowthResult

open MeasureTheory LatticeProb.Percolation

namespace Rigidity

/-- Almost surely, every harmonic, integer-valued function of at most linear growth on the unique
infinite open component of supercritical bond percolation on the integer lattice is a constant
integer. -/
theorem integer_valued_linear_growth (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (p : unitInterval)
    (_hpc : criticalProbability d < (p : ℝ)) (_hp1 : (p : ℝ) < 1)
    (_hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (_hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ) := by
  exact Rigidity.Support.integer_valued_linear_growth d _hd p _hpc _hp1 _hclassical _hcorrector

end Rigidity
