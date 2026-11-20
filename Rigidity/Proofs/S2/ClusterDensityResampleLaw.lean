import Rigidity.Proofs.S2.ClusterDensityInfluenceBound
import LatticeProb.Prob.Splice

/-!
# The law of a resampled bond configuration

Replacing one bond by its value in an independent configuration preserves the Bernoulli bond law.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation ProbabilityTheory

/-- Single-bond resampling from an independent configuration preserves the bond law. -/
theorem measurePreserving_resampleBond (d : ℕ) (p : unitInterval) (e : Bond d) :
    MeasurePreserving (fun q : Configuration d × Configuration d => resampleBond q.1 q.2 e)
      ((latticeBondLaw d p).prod (latticeBondLaw d p)) (latticeBondLaw d p) := by
  classical
  have heq : (fun q : Configuration d × Configuration d => resampleBond q.1 q.2 e) =
      (fun q => LatticeProb.comb ({e}ᶜ : Set (Bond d)) q.1 q.2) := by
    funext q f
    by_cases h : f = e
    · subst f
      simp [resampleBond, LatticeProb.comb]
    · simp [resampleBond, LatticeProb.comb, h]
  rw [heq]
  exact LatticeProb.measurePreserving_comb (fun _ : Bond d => bernoulliMeasure true false p) _

end Rigidity.Proofs.S2
