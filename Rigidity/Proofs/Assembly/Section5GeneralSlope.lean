import Rigidity.Steps.Section5.GeneralSlope
import Rigidity.Steps.S3.NotLipschitzAt
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section5Decay
/-! # Section 5 at every slope: Propositions 5.7 and 5.11 (d = 2)

End-to-end composition of the draft statements `GradientTrichotomyStmt p f` (Proposition 5.7,
`prop:gradient-trichotomy`) and `LevelSetDensityStmt p f` (Proposition 5.11,
`prop:level-set-of-harmonic-function`), for every slope `q ≠ 0`, with **no open step**:

* Proposition 3.2 at slope `q` (`NotLipschitzAtStep p q`) ← Proposition 3.2 at `e₁`
  (`Rigidity.Assembly.notLipschitz`) and the reduction to `e₁` through the reflection half of
  Lemma 3.1 (`Rigidity.Steps.S3.notLipschitzAt`); `notLipschitzAtSlope` below;
* Lemma 5.27 at slope `q` (`LargeGradientSensitiveAtStmt p f q`) ← Proposition 3.2 at slope `q`,
  Lemma 5.25 at slope `q` with a free direction of `G_3` (`goodEventPositiveAt_of_steps`,
  `exists_eventG3At_of_notLipschitzAt`), eq. PG2goesto1 at slope `q` (`secondGoodEventAtStep`,
  Theorem 2.5 at slope `q`), Proposition 5.20, Lemma 5.24, Lemma 5.28 in harmonic form
  (`finiteBranchesHarmonic_of_steps`, from Lemma 5.16 and Proposition 5.12) and the proved steps of
  `Rigidity/Steps/Section5/GeneralSlope.lean` (`largeGradientSensitiveAt_of_steps`);
  `largeGradientSensitiveAt` below;
* Proposition 5.11 at slope `q`, `lim inf` form (`LevelSetDensityEventuallyAt p f q`) ← Lemma 5.27
  at every slope (`levelSetDensityEventuallyAt_of_largeGradientSensitiveAt`, the ergodic theorem
  on anchored rectangles); `levelSetDensityEventuallyAt` below;
* Proposition 5.11, draft form (`LevelSetDensityStmt p f`, [C29]) ← the `lim inf` form at every
  slope; `levelSetDensity` below;
* Proposition 5.7, draft form (`GradientTrichotomyStmt p f`) ← its proved Steps 1-3 (slope-free or
  stated for every `q`) and Proposition 5.11 in `lim inf` form at every slope
  (`gradientTrichotomy_of_steps`); `gradientTrichotomy` below.

**`lim inf` versus `lim sup` ([C29]).** The printed Proposition 5.11 asserts the density bound
for infinitely many `k` (a `lim sup`, L1732-1738); Step 3 of the proof of Proposition 5.7 consumes
the bound for all large `k` (`∀ᶠ k`, a `lim inf`), and the draft `LevelSetDensityStmt` states that
form. The proof of Proposition 5.11 gives it (the ergodic theorem is a limit).

**Inputs.** Regime `p_c(2) < p < 1`; cited inputs (`Prop`s of `LatticeProb.External` and
`Rigidity.External`): `SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`,
`CorrectorQuantitativeInput`, `ArmstrongDarioOrderZero`, `SupercriticalBondGreenColumnExistence`,
`SupercriticalBondGreenQuantitative`, `WellConnectedInput`, `KestenRectangleCrossing`,
`JordanCurveTheoremSphere`; **derived input**, a hypothesis here:
`Rigidity.Proofs.S3.HomogenizedCoefficientProposed` (positivity of the homogenized coefficient
`ā`, through Proposition 3.2; proved by
`Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed`). Proposition 5.8 is
not used, hence neither `ArmstrongDarioOrderOneProposed` nor `ClusterDensityInputProposed`. -/

namespace Rigidity.Assembly

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- **Proposition 3.2 at every slope** (`d = 2`): for `p_c(2) < p < 1`, every `q ≠ 0` and every
`L ≥ 1`, with positive probability the origin lies in the infinite cluster and some corrected
plane `ℓ_q` has `|∇ℓ_q(0)| > L`. -/
theorem notLipschitzAtSlope (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed) {q : Fin 2 → ℝ} (hq : q ≠ 0) :
    NotLipschitzAtStep p q :=
  Steps.S3.notLipschitzAt le_rfl p hpc hp1 hUq hCorr
    (notLipschitz le_rfl p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW hHom) hq

/-- **Lemma 5.27 at every slope** (`LargeGradientSensitiveAtStmt p f q`, direction of `G_3` free,
cone `κ |x₀|₁ ≤ q · x₀`): composed from Proposition 3.2 at slope `q`, Lemma 5.25 and eq.
PG2goesto1 at slope `q`, Proposition 5.20, Lemma 5.24, Lemma 5.28 in harmonic form and the proved
steps. -/
theorem largeGradientSensitiveAt (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed) {q : Fin 2 → ℝ} (hq : q ≠ 0) :
    LargeGradientSensitiveAtStmt p f q := by
  obtain ⟨Λ, hΛ, h2q⟩ := secondGoodEventAtStep hUq hCQ p hpc hp1 q
  exact largeGradientSensitiveAt_of_steps hq hΛ hCQ hpc hp1 (boundarySize hUq hK hJ hpc hp1 f)
    (longPathRenormalized hW hK hpc)
    (goodEventPositiveAt_of_steps (exists_eventG3At_of_notLipschitzAt hCorr hpc hp1
      (notLipschitzAtSlope p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW hHom hq)) h2q)
    (finiteBranchesHarmonic_of_steps hJ (strongMaxPrinciple hUq hpc hp1)
      (infiniteDisjointPaths hUq hK hJ hpc hp1 f) Proofs.Section5.infiniteBranchesStep
      leafExitHarmonicStep Proofs.Section5.exitsDistinctStep Proofs.Section5.leafSeparatorStep
      Proofs.Section5.noK33MinorStep)
    correctedPlaneMinimalScaleAtStep Proofs.Section5.explorationBlockStep
    explorationHolesRayStep rootBlockHarmonicStep leafSensitiveHarmonicStep
    fluxBalanceHarmonicStep Proofs.Section5.fluxGrowthStep Proofs.Section5.greedyExplorationStep
    Proofs.Section5.explorationAssemblyStep Proofs.Section5.terminationWindowStep

/-- **Proposition 5.11 at every slope, `lim inf` form** (`LevelSetDensityEventuallyAt p f q`):
for `p_c(2) < p < 1`, finitely supported `f` and `q ≠ 0`, almost surely on `Σ f = 0` with
`u_f - lim u_f` of infinite support, for some `c > 0` and every large `k`,
`|B_{2^k}|⁻¹ |{e ∈ E(B_{2^k}) : ∇u_f(e) ≠ 0, ∇ℓ_q(e) ≠ 0}| ≥ c`. This is the form consumed by
Step 3 of Proposition 5.7. -/
theorem levelSetDensityEventuallyAt (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {f : Vertex 2 → ℤ}
    (hf : (Function.support f).Finite)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed) {q : Fin 2 → ℝ} (hq : q ≠ 0) :
    LevelSetDensityEventuallyAt p f q :=
  levelSetDensityEventuallyAt_of_largeGradientSensitiveAt hf
    (fun _ hq' => largeGradientSensitiveAt p hpc hp1 f hUq hCorr hCQ hAD hE hGQ hW hK hJ hHom hq')
    hq

/-- **Proposition 5.11** (`LevelSetDensityStmt`, the draft statement): for `p_c(2) < p < 1` and
finitely supported `f`, for every slope `q ≠ 0`, almost surely on `Σ f = 0` with `u_f - lim u_f`
of infinite support,
`liminf_k |B_{2^k}|⁻¹ |{e ∈ E(B_{2^k}) : ∇u_f(e) ≠ 0, ∇ℓ_q(e) ≠ 0}| > 0` ([C29], [C30]): it is
`levelSetDensityEventuallyAt` at every slope. -/
theorem levelSetDensity (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed) :
    LevelSetDensityStmt p f :=
  levelSetDensityStmt_iff.2 fun hf _ hq =>
    levelSetDensityEventuallyAt p hpc hp1 hf hUq hCorr hCQ hAD hE hGQ hW hK hJ hHom hq

/-- **Proposition 5.7** (`GradientTrichotomyStmt`, the draft statement): for `p_c(2) < p < 1`,
finitely supported `f` and every slope `q ≠ 0`, almost surely on `Σ f = 0`, for every Green
family and every corrected plane `ℓ_q`, either `Σ f ℓ_q ≠ 0`, or `u_f` converges at infinity to
some `L` and `u_f - L` has finite support. Proposition 5.11 enters in `lim inf` form. -/
theorem gradientTrichotomy (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed) :
    GradientTrichotomyStmt p f := fun hf =>
  gradientTrichotomy_of_steps ((criticalProbability_nonneg 2).trans_lt hpc) hp1
    (Proofs.Section5.uniqueClusterAe hUq hpc hp1)
    (Proofs.Section5.potentialLimit_of_asymptotic (Proofs.Section5.potentialAsymptotic hGQ hpc hp1))
    (Proofs.Section5.sublinearLiouville p hpc hp1 hAD) (Proofs.Section5.greenSymmetry hGQ hpc hp1)
    (fun q _ => Proofs.Section5.trichotomyEventMeasurable q
      (Proofs.Section5.sublinearLiouville p hpc hp1 hAD) hf)
    (Proofs.Section5.flipInfluenceStep p) (Proofs.Section5.flipShrinkStep f)
    (Proofs.Section5.flipIdentityStep f) Proofs.Section5.flipGradientStep
    Proofs.Section5.densityConclusionStep
    (fun _ hq => levelSetDensityEventuallyAt p hpc hp1 hf hUq hCorr hCQ hAD hE hGQ hW hK hJ hHom hq)
    hf

end Rigidity.Assembly
