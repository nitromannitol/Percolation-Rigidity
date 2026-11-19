import Rigidity.Proofs.Assembly.Section5Decay
import Rigidity.Proofs.S3.PlanarNotLipschitz

/-!
# Large-gradient estimates from planar well-connectedness

The non-Lipschitz and long-path inputs in the planar large-gradient argument use only the
well-connectedness estimate in dimension two.
-/

namespace Rigidity.Assembly.WithPlanarWellConnected

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- The lower bound for the good event from planar well-connectedness. -/
theorem goodEventLowerBound (hQ : Rigidity.External.CorrectorQuantitativeInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hgreen : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInputTwo)
    (hhom : Proofs.S3.HomogenizedCoefficientProposed) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GoodEventLowerBoundStmt p :=
  Proofs.Section5.goodEventLowerBound_of_second_third hQ hUq hU hp hp1
    (Proofs.S3.notLipschitz_two p hp hp1 hUq hU hQ hreg hgreen hGQ hW hhom)
    Proofs.Section5.secondGoodEventStep Proofs.Section5.thirdGoodEventStep

/-- The large-gradient estimate from planar well-connectedness. -/
theorem largeGradientSensitive
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInputTwo)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : LargeGradientSensitiveStmt p f :=
  largeGradientSensitive_of_steps hCQ hp hp1 (Rigidity.Assembly.boundarySize hUq hK hJ hp hp1 f)
    (Rigidity.Assembly.longPathRenormalized_two hW hK hp)
    (goodEventLowerBound hCQ hUq hCorr hAD hE hGQ hW hHom hp hp1)
    (Rigidity.Assembly.finiteBranches hUq hK hJ hp hp1 f)
    Proofs.Section5.correctedPlaneMinimalScaleStep Proofs.Section5.explorationBlockStep
    Proofs.Section5.explorationHolesStep Proofs.Section5.rootBlockStep
    Proofs.Section5.leafSensitiveStep Proofs.Section5.fluxBalanceStep
    Proofs.Section5.fluxGrowthStep Proofs.Section5.greedyExplorationStep
    Proofs.Section5.explorationAssemblyStep Proofs.Section5.terminationWindowStep

/-- The gradient trichotomy at the first coordinate from planar well-connectedness. -/
theorem gradientTrichotomyAtE1
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hW : Rigidity.External.WellConnectedInputTwo)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite) :
    GradientTrichotomyAt p f (Pi.single 0 1) := by
  have hlevel : LevelSetDensityEventuallyAt p f (Pi.single 0 1) :=
    levelSetDensityEventuallyAt_e1_of_steps hf (Proofs.Section5.triangleDensityStep p)
      (largeGradientSensitive hUq hGQ hE hAD hCorr hCQ hW hK hJ hHom hp hp1 f)
  exact gradientTrichotomyAt_of_steps ((criticalProbability_nonneg 2).trans_lt hp) hp1 hf
    (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    (Proofs.Section5.potentialLimit_of_asymptotic (Proofs.Section5.potentialAsymptotic hGQ hp hp1))
    (Proofs.Section5.sublinearLiouville p hp hp1 hAD) (Proofs.Section5.greenSymmetry hGQ hp hp1)
    (Proofs.Section5.trichotomyEventMeasurable _ (Proofs.Section5.sublinearLiouville p hp hp1 hAD)
      hf)
    (Proofs.Section5.flipInfluenceStep p) (Proofs.Section5.flipShrinkStep f)
    (Proofs.Section5.flipIdentityStep f _) (Proofs.Section5.flipGradientStep _)
    Proofs.Section5.densityConclusionStep hlevel

end Rigidity.Assembly.WithPlanarWellConnected
