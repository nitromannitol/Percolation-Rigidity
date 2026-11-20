import Rigidity.Proofs.Section5.PotentialLocalBound
import Rigidity.Proofs.Section5.PlanarPotentialCompactness

/-!
# Green columns from logarithmic potential bounds

Local boundedness follows from voltages, leaving only the global growth estimate.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Section5

namespace Rigidity.Proofs.Section5

/-- A uniform logarithmic bound on truncated potentials gives a planar Green column. -/
theorem exists_greenColumn_of_truncatedPotential_log_bound {ω : Configuration 2}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C) (K R₀ : ℝ)
    (hK : 0 ≤ K) (hbound : ∀ n (x : C), R₀ ≤ eucl x.val →
      |truncatedComponentPotential C n y x| ≤ K * Real.log (eucl x.val)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g :=
  exists_greenColumn_of_bounded_truncatedPotential C hC y K R₀
    (exists_bound_truncatedComponentPotential C hC y) hK hbound

/-- A uniform logarithmic bound for the cluster potential kernels gives Green-column existence. -/
theorem greenColumnExistsTwo_of_truncatedPotential_log_bound
    (hbound : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
        ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
            ∃ K R₀ : ℝ, 0 ≤ K ∧ ∀ n (x : uniqueInfiniteComponent h),
              R₀ ≤ eucl x.val →
              |truncatedComponentPotential (uniqueInfiniteComponent h) n ⟨y, hy⟩ x| ≤
                K * Real.log (eucl x.val)) :
    Rigidity.External.SupercriticalBondGreenColumnExistsTwo := by
  intro p hp hp1 y
  filter_upwards [hbound p hp hp1 y] with ω hω h hy
  obtain ⟨K, R₀, hK, hbound⟩ := hω h hy
  exact exists_greenColumn_of_truncatedPotential_log_bound _ (uniqueInfiniteComponent_infinite h)
    ⟨y, hy⟩ K R₀ hK hbound

end Rigidity.Proofs.Section5
