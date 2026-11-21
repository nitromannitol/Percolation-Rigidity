import Rigidity.Proofs.Assembly.ProvedInputs
import Rigidity.Proofs.Percolation.WellConnected

/-!
# Main theorems with every literature input proved

Theorem 6.5 uses three literature inputs: the existence and uniqueness of the infinite cluster,
the smoothing bound of Micciancio and Regev, and Proposition 2.3. All three are proved, so the
theorem holds with the regime `2 ≤ d`, `p_c(d) < p < 1` as its only hypotheses.
-/

namespace Rigidity.Assembly.Unconditional

open LatticeProb.Percolation

/-- **Theorem 6.5**, with supercritical bond uniqueness, lattice smoothing and Proposition 2.3
supplied by their proofs. -/
theorem slow_mixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section6.SlowMixingStmt d p :=
  Rigidity.Assembly.WithProvedInputs.slow_mixing d hd p hpc hp1
    Rigidity.Percolation.wellConnected_input

end Rigidity.Assembly.Unconditional
