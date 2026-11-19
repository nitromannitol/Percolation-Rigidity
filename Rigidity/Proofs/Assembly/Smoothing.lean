import Rigidity.Proofs.Assembly.Section6
import Rigidity.Proofs.Smoothing.MicciancioRegev

/-!
# Sandpile mixing with the lattice smoothing bound

Theorem 6.5 follows from supercritical bond uniqueness and the well-connectedness estimate, using
the lattice smoothing bound of Micciancio and Regev.
-/

namespace Rigidity.Assembly.WithSmoothing

open MeasureTheory LatticeProb.Percolation

/-- Theorem 6.5, with the lattice smoothing bound supplied by Micciancio and Regev. -/
theorem slow_mixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section6.SlowMixingStmt d p :=
  Rigidity.Assembly.slowMixing hd p hpc hp1 hUq hW
    Rigidity.Smoothing.micciancio_regev_smoothing

end Rigidity.Assembly.WithSmoothing
