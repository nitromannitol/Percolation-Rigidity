import Rigidity.Proofs.S6.Calculus
import Rigidity.Proofs.S6.GadgetCharacter
import Rigidity.Proofs.S6.GadgetCount
import Rigidity.Proofs.S6.LargestClusterExists
import Rigidity.Proofs.S6.LatticeCorrespondence
import Rigidity.Proofs.S6.PhaseBound
import Rigidity.Proofs.S6.WiredLaplacian

/-!
# Section 6: the composed result

Theorem 6.5 of the corrected draft (`Rigidity.Section6.SlowMixingStmt`), obtained by composing the
reduction `Rigidity.Steps.S6.slowMixing_of_steps` with the proved steps (`Rigidity.Proofs.S6`), the
upper bound step being itself composed by `Rigidity.Steps.S6.upperBound_of_steps`. The hypotheses
are the regime `2 ≤ d`, `p_c(d) < p < 1` and the cited literature inputs used by the steps:

* `LatticeProb.External.SupercriticalBondUniqueness`: uniqueness of the infinite cluster;
* `Rigidity.External.WellConnectedInput`: the well-connected cubes of Antal-Pisztora/Penrose-Pisztora
  (a largest cluster of `Q_n` inside `𝒞_∞` for large `n`, single exit of the largest cluster of a
  box, density of the gadgets);
* `Rigidity.External.MicciancioRegevSmoothing`: the smoothing parameter bound of Micciancio-Regev
  (Lemma 3.3), used for the upper bound as in Jerison-Levine-Pike.
-/

namespace Rigidity.Assembly

open LatticeProb.Percolation

/-- **Theorem 6.5**: there are `c, C > 0` such that almost surely, for every `ε > 0` and every
large `n`, some largest cluster `V` of the box of side `n` lies in `𝒞_∞`, and the sandpile chain on
every such `V` satisfies `‖P^t - U‖₂² ≤ ε` for `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for
`t ≤ c n^d log n`. -/
theorem slowMixing {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hwc : Rigidity.External.WellConnectedInput)
    (hMR : Rigidity.External.MicciancioRegevSmoothing) :
    Section6.SlowMixingStmt d p :=
  Steps.S6.slowMixing_of_steps hd p hpc hp1
    (Proofs.S6.uniqueClusterStep hd p hpc hclassical)
    ((Proofs.S6.largestClusterExists hd p hpc hp1 hwc hclassical).mono
      fun _ ⟨_, hω⟩ _ => hω)
    Proofs.S6.finiteGroupStep Proofs.S6.fourierStep
    (Steps.S6.upperBound_of_steps hMR Proofs.S6.latticeCorrespondenceStep
      Proofs.S6.phaseBoundStep Proofs.S6.wiredLaplacianStep)
    (Proofs.S6.singleExitStep hd p hpc hp1 hwc) Proofs.S6.upperTimeStep
    Proofs.S6.gadgetCharacterStep (Proofs.S6.gadgetCountStep hd p hpc hp1 hwc)
    (Proofs.S6.lowerBoundStep (by omega))

end Rigidity.Assembly
