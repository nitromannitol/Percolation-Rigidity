import Rigidity.Proofs.S3.FiniteEnergy

/-!
# Proposition 3.2: uniqueness of the infinite cluster after closing finitely many bonds

Step `ClosedBondsUniqueStep` of Proposition 3.2 (preamble of the proof, corrected draft L952; used
in `step:3.2-bridge-flux`). The event that the infinite cluster exists and is unique is measurable
(`measurableSet_uniqueInfiniteComponentEvent`); if it has full measure, Lemma 2.1 in its closing
form (`ae_forall_closeBonds`) shows that almost surely it still holds after closing the bonds of
any finite set.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- `ClosedBondsUniqueStep` (preamble of the proof of Proposition 3.2, L952): if the infinite
cluster exists and is unique almost surely, then almost surely the same holds for every
environment in which the bonds of a finite set are closed. -/
theorem closedBondsUniqueStep [NeZero d] (p : unitInterval) : ClosedBondsUniqueStep d p := by
  intro hp1 h1
  have hU : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ uniqueInfiniteComponentEvent d :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent d).nullMeasurableSet).2
      (h1.trans measure_univ.symm)
  exact ae_forall_closeBonds p hp1 hU

end Rigidity.Proofs.S3
