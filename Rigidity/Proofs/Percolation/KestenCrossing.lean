import Rigidity.Proofs.Percolation.Kesten.RigidityCrossingAdapter
import Rigidity.Proofs.Percolation.ClusterComparison
import Rigidity.External.KestenCrossing

/-!
# Supercritical planar rectangle crossings

Kesten's square-lattice critical value and exponential decay for the dual subcritical model
bound the probability that a supercritical rectangle lacks an open crossing. The rectangle
estimate is the form of H. Kesten, *Percolation Theory for Mathematicians* (1982), Theorem 11.1,
(11.4), used in the paper.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation _root_.Percolation.Literature

/-- The pinned planar critical probability equals one half. -/
theorem critical_probability_two_eq_half : criticalProbability 2 = 1 / 2 := by
  rw [criticalProbability_eq]
  exact kesten_criticalProb_Z2_holds

/-- The supercritical rectangle crossing estimate of Kesten. -/
theorem kesten_rectangle_crossing : Rigidity.External.KestenRectangleCrossing := by
  intro p hp
  have hp' : (1 : ℝ) / 2 < (p : ℝ) := by
    simpa only [← critical_probability_two_eq_half] using hp
  exact RigidityCrossingAdapter.consumer_at_half p hp'

end Rigidity.Percolation
