import Rigidity.Proofs.Section5.MengerRays
import Rigidity.Proofs.Section5.KestenChannelCut
import Rigidity.Proofs.Section5.RenormWalk
import Rigidity.Proofs.Section5.RenormField
import Rigidity.Proofs.Section5.VeryGoodProbability

/-! # Section 5: composed Proposition 5.24 (d = 2), route without Liggett-Schonmann-Stacey

`longPathRenormalized` concludes the draft `Rigidity.Section5.LongPathRenormalizedStmt p`
(Proposition 5.24, `prop:longpathsupercritrenormlatt`, corrected draft L2280-2290) by the Peierls
route `Rigidity.Steps.Section5.longPathRenormalized_of_peierls`, from its proved steps:
* the deterministic half `RenormalizedClusterPathsStep` (eq. `implication-renormalized-cluster`),
  from `mengerRaysStep` and `kestenChannelCutStep` (`renormalizedClusterPaths_of_cut`);
* the probabilistic half, from `veryGoodProbabilityStep`, `renormFieldMeasurableStep`,
  `renormFieldOneDependentStep` (steps of Lemma 5.23) and `oneDependentWalkStep` (the Peierls
  bound for `1`-dependent fields).

Hypotheses: the regime `p_c(2) < p` (the upper bound `p < 1` is not used) and the literature
inputs
* `Rigidity.External.WellConnectedInput` (Proposition 2.3),
* `Rigidity.External.KestenRectangleCrossing` (Kesten's crossing estimate, bond form),

both consumed by `VeryGoodProbabilityStep`. Neither Lemma 5.23 (`RenormalizedDominationStmt`,
Liggett-Schonmann-Stacey) nor any local proposed input is used.

Proposition 5.20 (`BoundarySizeStmt`) is composed in `Section5d.lean` (`boundarySize`, with the
proved `ThreeExitsStep`). -/

namespace Rigidity.Assembly

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- **Proposition 5.24** (long paths through the good sites): for `p_c(2) < p` and every `C_f`,
beyond a scale `R₁`, some `c₁ > 0` bounds by `C exp(-c K)` the probability that a path of `𝒞_∞`
from the origin reaching `|γ(end)|₁ ≥ K` has at most `c₁ |γ(end)|₁` of its sites in `E_R`.
Inputs: Proposition 2.3 (`WellConnectedInput`) and Kesten's crossing estimate
(`KestenRectangleCrossing`). -/
theorem longPathRenormalized (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) : LongPathRenormalizedStmt p :=
  longPathRenormalized_of_peierls hW hK hpc Proofs.Section5.veryGoodProbabilityStep
    Proofs.Section5.renormFieldMeasurableStep Proofs.Section5.renormFieldOneDependentStep
    (renormalizedClusterPaths_of_cut Proofs.Section5.mengerRaysStep
      Proofs.Section5.kestenChannelCutStep)
    Proofs.Section5.oneDependentWalkStep

end Rigidity.Assembly
