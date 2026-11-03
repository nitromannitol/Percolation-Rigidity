import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Section5.LSSDomination
import Rigidity.Proofs.Section5.RenormField
import Rigidity.Proofs.Section5.VeryGoodProbability

/-! # Section 5: Lemma 5.23 (d = 2)

Draft statement concluded verbatim:
* Lemma 5.23 (`renormalizedDomination : RenormalizedDominationStmt p`), from
  `renormalizedDomination_of_steps'` (`renormalizedDomination_of_steps` with the proved
  Liggett-Schonmann-Stacey step `oneDependentDominationStep`, `C₀ = 4`, `a = 1/16`; no literature
  input for the domination) and the three proved steps `veryGoodProbabilityStep`,
  `renormFieldMeasurableStep`, `renormFieldOneDependentStep`. Hypotheses: `p_c(2) < p`, and the
  cited inputs `WellConnectedInput` (Proposition 2.3) and `KestenRectangleCrossing`, consumed by
  `veryGoodProbabilityStep`.

Proposition 5.11 in draft form ([C29]) is `Rigidity.Assembly.levelSetDensity`
(`Section5GeneralSlope.lean`). No locally stated input is used. -/

namespace Rigidity.Assembly

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-! ### Lemma 5.23 -/

/-- **Lemma 5.23** (`RenormalizedDominationStmt`): for `p_c(2) < p`, there are `C, c, s > 0` such
that for every `R ≥ 1` the renormalized percolation process of size `R` stochastically dominates
Bernoulli site percolation of parameter `1 - C exp(-c R^s)` on measurable increasing events.
Composed from `renormalizedDomination_of_steps'` (the Liggett-Schonmann-Stacey step is proved,
`oneDependentDominationStep`) and the proved steps `veryGoodProbabilityStep`,
`renormFieldMeasurableStep`, `renormFieldOneDependentStep`.
Inputs: `WellConnectedInput` (Proposition 2.3), `KestenRectangleCrossing`. -/
theorem renormalizedDomination (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) : RenormalizedDominationStmt p :=
  Proofs.Section5.renormalizedDomination_of_steps' hW hK hp
    Proofs.Section5.veryGoodProbabilityStep Proofs.Section5.renormFieldMeasurableStep
    Proofs.Section5.renormFieldOneDependentStep

end Rigidity.Assembly
