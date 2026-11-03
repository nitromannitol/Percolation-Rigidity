import Rigidity.Steps.Section5.DirectionFree
import Rigidity.Proofs.Section5.ThreeExits
import Rigidity.Proofs.Section5.GoodEventBasics
import Rigidity.Proofs.Section5.SecondGoodEvent
import Rigidity.Proofs.Section5.TriangleDensity
import Rigidity.Proofs.Section5.TwoScaleSteps
import Rigidity.Proofs.Section5.GreenTaylor
import Rigidity.Proofs.Section5.GreenSymmetry
import Rigidity.Proofs.Section5.PotentialLimit
import Rigidity.Proofs.Section5.TrichotomyMeasurable
import Rigidity.Proofs.Section5.FlipInfluence
import Rigidity.Proofs.Section5.FlipSteps
import Rigidity.Proofs.Section5.DensityConclusion
import Rigidity.Steps.Section5.LevelSetDensityEventual
import Rigidity.Steps.Section5.FastDecayPotential
import Rigidity.Steps.Section5.TwoScaleExpansion
/-! # Section 5: the decay chain, Theorem 1.3 and Theorem 5.1 (d = 2)

End-to-end composition of the fast-decay theorem from the reductions `…_of_steps` of
`Rigidity/Steps/Section5` and the proved steps of `Rigidity/Proofs`, with **no open step**:

* Theorem 1.3 (`FastDecayStmt`) ← Theorem 5.1 (`fastDecay_of_steps`, `annulusStep`);
* Theorem 5.1 (`FastDecayDichotomyStmt`) ← Propositions 5.3 and 5.5 (`fastDecayDichotomy_of_steps`);
* Proposition 5.3 (`FastDecayPotentialStmt`) ← Proposition 5.7 at the slope `e₁`, Proposition 5.8
  and the existence of corrected planes (`fastDecayPotential_of_e1` below);
* Proposition 5.7 at `e₁` (`GradientTrichotomyAt p f e₁`) ← its proved steps and Proposition 5.11
  at `e₁` in `lim inf` form (`gradientTrichotomyAt_of_steps`);
* Proposition 5.11 at `e₁` (`LevelSetDensityEventuallyAt p f e₁`, the draft form at `q = e₁`,
  [C29]) ← Lemma 5.27 and the ergodic theorem on triangles
  (`levelSetDensityEventuallyAt_e1_of_steps`, `triangleDensityStep`);
* Lemma 5.27 (`LargeGradientSensitiveStmt`, universal `G_1` [C31], direction-free `G_3` [C32]) ←
  Proposition 5.20, Lemma 5.24, Lemma 5.25, Lemma 5.28 (`finiteBranches`, `Section5.lean`) and the
  proved steps (`largeGradientSensitive_of_steps`);
* Proposition 5.20 (`BoundarySizeStmt`) and Proposition 5.8 (`TwoScaleExpansionStmt`): composed
  in `Section5d.lean` (`boundarySize`, `twoScaleExpansion`);
* Lemma 5.25 (`GoodEventLowerBoundStmt`): composed in `Section5d.lean` (`goodEventLowerBound`)
  from Proposition 3.2 (`notLipschitz`).

**Forms used.** The composed theorems conclude the draft `FastDecayStmt`,
`FastDecayDichotomyStmt`, `LargeGradientSensitiveStmt` verbatim, and:
1. Proposition 5.7 at the slope `e₁` only (`GradientTrichotomyAt p f e₁`): the reduction
   `fastDecayPotential_of_steps` consumes the draft `GradientTrichotomyStmt` (every `q ≠ 0`) but
   uses `q = e₁` only; `fastDecayPotential_of_e1` is that reduction. The draft
   `GradientTrichotomyStmt` and `LevelSetDensityStmt` (every `q ≠ 0`) are concluded in
   `Section5GeneralSlope.lean`.
2. Lemma 5.26 is not consumed: Proposition 5.11 uses the ergodic theorem on triangles
   (`TriangleDensityStep`) directly.

**Inputs.** Regime `p_c(2) < p < 1`; cited inputs (`Prop`s of `LatticeProb.External` and
`Rigidity.External`): `SupercriticalBondUniqueness`, `SupercriticalBondGreenQuantitative`,
`SupercriticalBondGreenColumnExistence`, `ArmstrongDarioOrderZero`,
`SupercriticalBondCorrectorInput`, `CorrectorQuantitativeInput`, `WellConnectedInput`,
`KestenRectangleCrossing`, `JordanCurveTheoremSphere`; **derived inputs**, hypotheses here
(propositions of `Rigidity/Proofs`, derived from cited inputs in
`Rigidity.Assembly.Main.fastDecay`):
* `Rigidity.Proofs.S3.HomogenizedCoefficientProposed` (positivity of `ā`, through Proposition 3.2,
  consumed by Lemma 5.25; `Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed`);
* `Rigidity.Proofs.S2.ArmstrongDarioOrderOneProposed` and
  `Rigidity.Proofs.S2.ClusterDensityInputProposed` (through Proposition 2.6, consumed by
  Proposition 5.8; `armstrongDarioOrderOneProposed_of_origin`,
  `clusterDensityInputProposed_of_concentration`). -/

namespace Rigidity.Assembly

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-! ### Proposition 5.3 from Proposition 5.7 at the slope `e₁` -/

/-- Proposition 5.3 from Proposition 5.7 at the slope `e₁` only, Proposition 5.8 and the existence
of corrected planes: the reduction `fastDecayPotential_of_steps`, which uses Proposition 5.7 at
`q = e₁` only. -/
theorem fastDecayPotential_of_e1 {p : unitInterval} {f : Vertex 2 → ℤ}
    (h57 : (Function.support f).Finite → GradientTrichotomyAt p f (Pi.single 0 1))
    (h58 : TwoScaleExpansionStmt p f) (hplanes : CorrectedPlanesExist p) :
    FastDecayPotentialStmt p f := by
  intro hf
  have hU : UniqueClusterAe p := (h57 hf).mono fun _ h => h.1
  obtain ⟨K, s, -, -, κ, M, -, -, h58ae⟩ := h58 hf
  filter_upwards [h57 hf, h58ae, hplanes, clusterMeetsAxis_of_uniqueClusterAe hU] with
    ω H57 H58 HP HA
  obtain ⟨h, H57⟩ := H57
  obtain ⟨h', H58⟩ := H58
  refine ⟨h, fun G hG => ?_⟩
  by_cases hm : mass (uniqueInfiniteComponent h) f = 0
  swap
  · exact Or.inl hm
  right
  choose ℓ hℓ using HP h
  rcases H57 hm G hG (ℓ 0) (hℓ 0) with hpair | ⟨L, hL, hsupp⟩
  · obtain ⟨L, hL⟩ := H58 hm G hG ℓ hℓ
    exact ⟨L, tendsto_of_twoScaleExpansion κ _ hL,
      Or.inl (linearDecay_of_twoScaleExpansion κ _ hpair hL (HA h))⟩
  · exact ⟨L, hL, Or.inr (eventuallyZero_of_support_finite hsupp)⟩

/-! ### Lemma 5.27 with the direction-free third good event -/

/-- **Lemma 5.27** (`LargeGradientSensitiveStmt`, universal `G_1` [C31], direction-free `G_3`
[C32]), composed from Proposition 5.20, Lemma 5.24, Lemma 5.25, Lemma 5.28 and the proved steps. -/
theorem largeGradientSensitive
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : LargeGradientSensitiveStmt p f :=
  largeGradientSensitive_of_steps hCQ hp hp1 (boundarySize hUq hK hJ hp hp1 f)
    (longPathRenormalized hW hK hp)
    (goodEventLowerBound hCQ hUq hCorr hAD hE hGQ hW hHom hp hp1)
    (finiteBranches hUq hK hJ hp hp1 f)
    Proofs.Section5.correctedPlaneMinimalScaleStep Proofs.Section5.explorationBlockStep
    Proofs.Section5.explorationHolesStep Proofs.Section5.rootBlockStep
    Proofs.Section5.leafSensitiveStep Proofs.Section5.fluxBalanceStep
    Proofs.Section5.fluxGrowthStep Proofs.Section5.greedyExplorationStep
    Proofs.Section5.explorationAssemblyStep Proofs.Section5.terminationWindowStep

/-! ### Propositions 5.11 and 5.7 at the slope `e₁` -/

/-- **Proposition 5.11** at the slope `e₁` (`LevelSetDensityEventuallyAt p f e₁`, the draft form at
`q = e₁`, [C29]), from Lemma 5.27 and the ergodic theorem on triangles. -/
theorem levelSetDensityEventuallyAtE1
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite) :
    LevelSetDensityEventuallyAt p f (Pi.single 0 1) :=
  levelSetDensityEventuallyAt_e1_of_steps hf (Proofs.Section5.triangleDensityStep p)
    (largeGradientSensitive hUq hGQ hE hAD hCorr hCQ hW hK hJ hHom hp hp1 f)

/-- **Proposition 5.7** at the slope `e₁` (`GradientTrichotomyAt p f e₁`): its steps are proved,
Proposition 5.11 enters in `lim inf` form. -/
theorem gradientTrichotomyAtE1
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite) :
    GradientTrichotomyAt p f (Pi.single 0 1) :=
  gradientTrichotomyAt_of_steps ((criticalProbability_nonneg 2).trans_lt hp) hp1 hf
    (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    (Proofs.Section5.potentialLimit_of_asymptotic (Proofs.Section5.potentialAsymptotic hGQ hp hp1))
    (Proofs.Section5.sublinearLiouville p hp hp1 hAD) (Proofs.Section5.greenSymmetry hGQ hp hp1)
    (Proofs.Section5.trichotomyEventMeasurable _ (Proofs.Section5.sublinearLiouville p hp hp1 hAD)
      hf)
    (Proofs.Section5.flipInfluenceStep p) (Proofs.Section5.flipShrinkStep f)
    (Proofs.Section5.flipIdentityStep f _) (Proofs.Section5.flipGradientStep _)
    Proofs.Section5.densityConclusionStep
    (levelSetDensityEventuallyAtE1 hUq hGQ hE hAD hCorr hCQ hW hK hJ hHom hp hp1 hf)

/-! ### Proposition 5.3, Theorem 5.1, Theorem 1.3 -/

/-- **Proposition 5.3** (`FastDecayPotentialStmt`): for `p_c(2) < p < 1` and finitely supported
`f`, almost surely, for every Green family, either `Σ f ≠ 0`, or the potential `u_f` converges at
infinity to some `L` and `u_f - L` decays like `1/|x|` or is eventually zero. -/
theorem fastDecayPotential (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    (hAD1 : Proofs.S2.ArmstrongDarioOrderOneProposed)
    (hD : Proofs.S2.ClusterDensityInputProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : FastDecayPotentialStmt p f :=
  fastDecayPotential_of_e1
    (fun hf => gradientTrichotomyAtE1 hUq hGQ hE hAD hCorr hCQ hW hK hJ hHom hp hp1 hf)
    (twoScaleExpansion hUq hW hGQ hCQ hCorr hAD1 hD hp hp1 f)
    (correctedPlanesExist_of_input hCorr hp hp1)

/-- **Theorem 5.1** (`FastDecayDichotomyStmt`): for `p_c(2) < p < 1`, almost surely a function on
the infinite cluster tending to `0` at infinity with integer-valued Laplacian either decays like
`1/|x|` or is eventually zero. -/
theorem fastDecayDichotomy (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    (hAD1 : Proofs.S2.ArmstrongDarioOrderOneProposed)
    (hD : Proofs.S2.ClusterDensityInputProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    FastDecayDichotomyStmt p :=
  fastDecayDichotomy_of_steps
    (fastDecayPotential hUq hGQ hE hAD hCorr hCQ hW hK hJ hHom hAD1 hD hp hp1)
    (logGrowth hUq hGQ hp hp1) (Proofs.Section5.greenFamilyExists hE hp hp1)
    (Proofs.Section5.sublinearLiouville p hp hp1 hAD) Proofs.Section5.potentialLaplacian

/-- **Theorem 1.3** (`FastDecayStmt`): for `p_c(2) < p < 1`, almost surely, for every finitely
supported `f : ℤ² → ℤ`, every `u : 𝒞_∞ → ℝ` with `-Δu = f` and
`lim sup_R R sup_{B_R \ B_{R/2}} |u| = 0` has finite support. No open step. Inputs: the cited
inputs of `Rigidity.External` and `LatticeProb.External` listed as hypotheses, and the local
proposed `HomogenizedCoefficientProposed` (Proposition 3.2), `ArmstrongDarioOrderOneProposed` and
`ClusterDensityInputProposed` (Proposition 2.6). -/
theorem fastDecay (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    (hAD1 : Proofs.S2.ArmstrongDarioOrderOneProposed)
    (hD : Proofs.S2.ClusterDensityInputProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    FastDecayStmt p :=
  fastDecay_of_steps
    (fastDecayDichotomy hUq hGQ hE hAD hCorr hCQ hW hK hJ hHom hAD1 hD hp hp1)
    Proofs.Section5.annulusStep

end Rigidity.Assembly
