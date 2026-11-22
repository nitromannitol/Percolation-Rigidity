import Rigidity.Proofs.Cluster.PlanarRestrictQuadCoarsen
import Rigidity.Proofs.Cluster.PlanarReachConcentrationHolds
import Rigidity.Proofs.Percolation.PlanarOmegaDecay

/-!
# Lemma 5.5 and Proposition 5.2 of Armstrong and Dario from the Gehring partition

With the concentration of the averages of the reach proved (`planarReachConcentration_holds`),
Lemma 5.5 of Armstrong and Dario in dimension two, for `μ` and for `ν`, in the input forms
`PlanarRestrictQuadCoarsenMu` and `PlanarRestrictQuadCoarsenNu`, follows from the single statement
`PlanarGehringPartition` (a Gehring partition in the form used by the planar Meyers estimate,
with its minimal scales), and the
qualitative part of Proposition 5.2 in dimension two follows from it and Lemma 5.7
(`PlanarWeakConvergence`).
-/

namespace Rigidity.Proofs.Cluster

open Rigidity.Percolation LatticeProb.Percolation
open scoped Matrix

/-- **Lemma 5.5 of Armstrong and Dario for `μ`** (display (5.12), in dimension two), from the
Gehring partition `PlanarGehringPartition`. -/
theorem planarRestrictQuadCoarsenMu_of_gehring {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    PlanarRestrictQuadCoarsenMu p :=
  planarRestrictQuadCoarsenMu_of_inputs hpc hG (planarReachConcentration_holds hpc)

/-- **Lemma 5.5 of Armstrong and Dario for `ν`** (display (5.12), in dimension two), from the
Gehring partition `PlanarGehringPartition`. -/
theorem planarRestrictQuadCoarsenNu_of_gehring {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hG : PlanarGehringPartition p) :
    PlanarRestrictQuadCoarsenNu p :=
  planarRestrictQuadCoarsenNu_of_inputs hpc hG (planarReachConcentration_holds hpc)

/-- **Proposition 5.2 of Armstrong and Dario, qualitative part** (dimension two), from Lemma 5.7
and the Gehring partition `PlanarGehringPartition`:
`lim E[-μ(□_n, q)] = (1/2) q · ā⁻¹ q`. -/
theorem planarMuLimit_eq_of_gehring {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (h57 : PlanarWeakConvergence p) (hG : PlanarGehringPartition p) (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i :=
  planarMuLimit_eq_of_inputs hpc h57 (planarRestrictQuadCoarsenMu_of_gehring hpc hG)
    (planarRestrictQuadCoarsenNu_of_gehring hpc hG) q

end Rigidity.Proofs.Cluster
