import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section5
import Rigidity.Proofs.Assembly.Section5b
import Rigidity.Proofs.Assembly.Section5c
import Rigidity.Proofs.Section5.ThreeExits
import Rigidity.Proofs.Section5.GoodEventMeasurable
import Rigidity.Proofs.Section5.GoodEventBasics
import Rigidity.Proofs.Section5.SecondGoodEvent
import Rigidity.Proofs.Section5.TwoScaleSteps
import Rigidity.Proofs.Section5.GreenTaylor
import Rigidity.Steps.Section5.TwoScaleExpansion
import Rigidity.Steps.Section5.GradientTrichotomy
import Rigidity.Steps.Section5.LevelSetDensityEventual
import Rigidity.Proofs.Section5.FlipSteps
import Rigidity.Proofs.Section5.FlipInfluence
import Rigidity.Proofs.Section5.DensityConclusion
import Rigidity.Proofs.Section5.TrichotomyMeasurable
import Rigidity.Proofs.Section5.PotentialLimit
import Rigidity.Proofs.Section5.GreenSymmetry
import Rigidity.Proofs.Section5.SublinearLiouville
import Rigidity.Proofs.Section5.TriangleDensity

/-! # Section 5: composed results (d = 2)

This file composes results of Section 5 whose step proofs are finished but which were not composed
in `Section5.lean` or `Section5b.lean`. Each concludes its draft statement verbatim:
* Proposition 5.20 (`boundarySize : BoundarySizeStmt p f`), from `boundarySize_of_inputs`
  (`ThreeExitsStep` is proved), Lemma 5.16 and Proposition 5.12;
* Proposition 5.8 (`twoScaleExpansion : TwoScaleExpansionStmt p f`), from
  `twoScaleExpansion_of_steps`, Proposition 2.6 and the proved steps;
* Lemma 5.26 (`goodEventDensity : GoodEventDensityStmt p`, null-measurable form, all parameters),
  from the null-measurability of the good event and the ergodic theorem on triangles;
* Lemma 5.25 (`goodEventLowerBound : GoodEventLowerBoundStmt p`, universal `G_1` [C31],
  direction-free `G_3` [C32]), from Theorem 2.5, Proposition 3.2 and the proved steps.

Literature inputs (explicit hypotheses whose `Prop` lives in `Rigidity.External` or
`LatticeProb.External`): `SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`,
`SupercriticalBondGreenQuantitative`, `SupercriticalBondGreenColumnExistence`,
`ArmstrongDarioOrderZero`, `CorrectorQuantitativeInput`, `WellConnectedInput`,
`KestenRectangleCrossing`, `JordanCurveTheoremSphere`; each theorem takes only those it uses.
**Derived inputs**, hypotheses here (propositions of `Rigidity/Proofs`, derived from cited inputs
in `Rigidity/Proofs/Assembly/Main.lean`):
* `Rigidity.Proofs.S2.ArmstrongDarioOrderOneProposed` and
  `Rigidity.Proofs.S2.ClusterDensityInputProposed` (through Proposition 2.6, in Proposition 5.8;
  `armstrongDarioOrderOneProposed_of_origin`, `clusterDensityInputProposed_of_concentration`);
* `Rigidity.Proofs.S3.HomogenizedCoefficientProposed` (through Proposition 3.2, in Lemma 5.25;
  `Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed`).

Propositions 5.11 and 5.7 are composed in `Section5Decay.lean` and `Section5GeneralSlope.lean`. -/

namespace Rigidity.Assembly

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section5
  Rigidity.Steps.Section5

/-! ### Proposition 5.20 -/

/-- **Proposition 5.20** (`BoundarySizeStmt`, corrected draft L2142-2149): for `p_c(2) < p < 1` and
finitely supported `f`, there is `C_f ∈ ℕ`, depending only on `f`, with `supp f ⊆ Q_{C_f/2}` and
such that for every `a` and every biconnected `S ⊆ L_a` whose complement in `ℤ²` has no finite
connected component meeting `supp f`, at most `C_f` disjoint paths connect `S` to infinity.
Composed from `boundarySize_of_inputs` (with the proved `ThreeExitsStep`), Lemma 5.16 and
Proposition 5.12. Inputs: uniqueness of the infinite cluster, Kesten's crossing estimate (through
Proposition 5.12) and the Jordan curve theorem on the sphere. -/
theorem boundarySize (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    BoundarySizeStmt p f :=
  Proofs.Section5.boundarySize_of_inputs hJ (strongMaxPrinciple hUq hp hp1)
    (infiniteDisjointPaths hUq hK hJ hp hp1 f)

/-! ### Proposition 5.8 -/

/-- **Proposition 5.8** (`TwoScaleExpansionStmt`, two-scale expansion of the potential): for
`p_c(2) < p < 1` and finitely supported `f`, there are `C, s` and a minimal scale `M_f ≤ O_s(C)`
such that on `Σ f = 0`, `u_f` has a limit `L` at infinity and, for `|x| ≥ M_f`,
`|u_f(x) - L + Σᵢ (Σ_y f(y) ℓ_{eᵢ}(y)) ∂ᵢḠ(x)| ≤ C |x|^{-5/4}` [C18]. Composed from
`twoScaleExpansion_of_steps`, Proposition 2.6 (`greenGradientHomogenization`), the steps of
Lemma 5.6 and the steps proved in `TwoScaleSteps.lean` and `GreenTaylor.lean`.
Inputs: `SupercriticalBondUniqueness`, `WellConnectedInput` (Proposition 2.3),
`SupercriticalBondGreenQuantitative`, `CorrectorQuantitativeInput` (Theorem 2.5),
`SupercriticalBondCorrectorInput`, and, through Proposition 2.6, the **derived inputs**
`Rigidity.Proofs.S2.ArmstrongDarioOrderOneProposed` (Theorem 2.4 at order one, [C34]) and
`Rigidity.Proofs.S2.ClusterDensityInputProposed` (density of the cluster, Dario-Gu Proposition A.1,
[C35]). -/
theorem twoScaleExpansion (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hW : Rigidity.External.WellConnectedInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : Proofs.S2.ArmstrongDarioOrderOneProposed) (hD : Proofs.S2.ClusterDensityInputProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : TwoScaleExpansionStmt p f :=
  twoScaleExpansion_of_steps hp hp1 hW hGQ hCQ (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    (greenGradientHomogenization le_rfl hp hp1 hGQ hCQ hU hAD hD)
    Proofs.Section5.connectingSetStep Proofs.Section5.flowOnConnectedSet
    Proofs.Section5.summationByParts Proofs.Section5.connectedSetRadiusStep
    Proofs.Section5.normalizedGreenSymmetryStep Proofs.Section5.correctedPlaneGradientStep
    Proofs.Section5.forwardDiffEdgeStep Proofs.Section5.greenTaylorStep
    (Proofs.S2.tailOfOsStep 2 p) (Proofs.S2.minimalScaleStep 2 p) f

/-! ### Lemma 5.26 -/

/-- **Lemma 5.26** (`GoodEventDensityStmt`, null-measurable form, all parameters): for
`p_c(2) < p < 1` and all parameters, the good event `G(0, C_χ, K)` is null-measurable and almost
surely `liminf_L L⁻² |{y ∈ T_L : G(y, C_χ, K)}| = P[G(0, C_χ, K)]`.
Input: `SupercriticalBondCorrectorInput`. -/
theorem goodEventDensity (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GoodEventDensityStmt p :=
  Proofs.Section5.goodEventDensity hU hp hp1

/-! ### Lemma 5.25 -/

/-- **Lemma 5.25** (`GoodEventLowerBoundStmt`, universal `G_1` [C31], direction-free `G_3` [C32]):
for `p_c(2) < p < 1` and every `C_χ ≥ 1` there is `c > 0` such that, for parameters `R, c₁`
satisfying the bound of Proposition 5.24, `P[G(x, C_χ, K)] ≥ c` (with a measurable witness) for all
`x` and all large `K`. Composed from `goodEventLowerBound_of_steps`, the proved steps
(`goodEventTranslationStep`, `firstGoodEventStep`, `secondGoodEventStep`, `thirdGoodEventStep`)
and Proposition 3.2 (`notLipschitz`). Inputs: `CorrectorQuantitativeInput` (Theorem 2.5),
`SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`, and, through Proposition 3.2,
`ArmstrongDarioOrderZero`, `SupercriticalBondGreenColumnExistence`,
`SupercriticalBondGreenQuantitative`, `WellConnectedInput` and the **derived input**
`Rigidity.Proofs.S3.HomogenizedCoefficientProposed` (positivity of `ā`). -/
theorem goodEventLowerBound (hQ : Rigidity.External.CorrectorQuantitativeInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hgreen : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hhom : Proofs.S3.HomogenizedCoefficientProposed) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GoodEventLowerBoundStmt p :=
  Proofs.Section5.goodEventLowerBound_of_second_third hQ hUq hU hp hp1
    (notLipschitz le_rfl p hp hp1 hUq hU hQ hreg hgreen hGQ hW hhom)
    Proofs.Section5.secondGoodEventStep Proofs.Section5.thirdGoodEventStep

end Rigidity.Assembly
