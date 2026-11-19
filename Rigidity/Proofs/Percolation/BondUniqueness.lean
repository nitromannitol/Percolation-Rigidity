import Rigidity.Proofs.Percolation.PlanarCriticalBound
import Rigidity.Proofs.Percolation.PositiveCriticalProbability
import Rigidity.Proofs.Percolation.SupercriticalUniqueness
import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# Supercritical bond uniqueness

The bounded-degree and planar Peierls bounds give `0 < p_c(d) < 1` for `d ≥ 2`. Above
criticality the zero–one law and the Burton–Keane theorem give a unique infinite component.
See G. Grimmett, *Percolation*, 2nd ed. (1999), Theorems (1.10) and (8.1), and
R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121
(1989), 501–505, Theorem 2.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The classical critical bounds and uniqueness for supercritical lattice bond percolation. -/
theorem supercriticalBondUniqueness : LatticeProb.External.SupercriticalBondUniqueness := by
  constructor
  · intro d _ hd
    exact ⟨criticalProbability_pos d, criticalProbability_lt_one d hd⟩
  · intro d _ _ p hp _
    exact uniqueInfiniteComponentEvent_eq_one_of_criticalProbability_lt d p hp

end Rigidity.Percolation
