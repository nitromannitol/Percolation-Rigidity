import Rigidity.Proofs.Assembly.PlanarProvedDensity
import Rigidity.Proofs.Section5.PlanarGoodEvent
import Rigidity.Proofs.Section5.PlanarGreenUniqueness
import Rigidity.Proofs.Section5.PlanarMinimalScale
import Rigidity.Proofs.Section5.PlanarGreenAsymptotics
import Rigidity.Steps.Section5.PlanarLargeGradient
import Rigidity.Steps.Section5.PlanarTwoScaleExpansion
import Rigidity.Proofs.S2.PlanarGreenGradient

/-!
# Fast decay from planar literature inputs

This module proves Theorem 1.3 and its supporting estimates from the literature inputs stated in
dimension two (the planar corrector, regularity, Green-column and quantitative Green estimates),
taken as hypotheses. Each of these inputs is proved, and Theorem 1.3 without them is
`fast_decay_holds` (`Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean`).
-/

namespace Rigidity.Assembly.WithPlanarInputs

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- The planar good-event lower bound. -/
theorem goodEventLowerBound
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hW : Rigidity.External.WellConnectedInputTwo)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    GoodEventLowerBoundStmt p :=
  Proofs.Section5.goodEventLowerBound_of_planar_inputs hCQ hUq hCorr hp hp1
    (Proofs.S3.notLipschitz_of_planar_inputs p hp hp1 hUq hCorr hCQ hAD hE hGQ hW)

/-- The planar large-gradient estimate. -/
theorem largeGradientSensitive
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hW : Rigidity.External.WellConnectedInputTwo)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : LargeGradientSensitiveStmt p f :=
  largeGradientSensitive_of_planar_scale (Rigidity.Assembly.boundarySize hUq hK hJ hp hp1 f)
    (Rigidity.Assembly.longPathRenormalized_two hW hK hp)
    (goodEventLowerBound hUq hGQ hE hAD hCorr hCQ hW hp hp1)
    (Rigidity.Assembly.finiteBranches hUq hK hJ hp hp1 f)
    (Proofs.Section5.correctedPlaneMinimalScale_two hCQ p hp hp1)
    Proofs.Section5.explorationBlockStep Proofs.Section5.explorationHolesStep
    Proofs.Section5.rootBlockStep Proofs.Section5.leafSensitiveStep
    Proofs.Section5.fluxBalanceStep Proofs.Section5.fluxGrowthStep
    Proofs.Section5.greedyExplorationStep Proofs.Section5.explorationAssemblyStep
    Proofs.Section5.terminationWindowStep

/-- The gradient trichotomy at the first coordinate from planar inputs. -/
theorem gradientTrichotomyAtE1
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hW : Rigidity.External.WellConnectedInputTwo)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite) :
    GradientTrichotomyAt p f (Pi.single 0 1) := by
  have hlevel : LevelSetDensityEventuallyAt p f (Pi.single 0 1) :=
    levelSetDensityEventuallyAt_e1_of_steps hf (Proofs.Section5.triangleDensityStep p)
      (largeGradientSensitive hUq hGQ hE hAD hCorr hCQ hW hK hJ hp hp1 f)
  exact gradientTrichotomyAt_of_steps ((criticalProbability_nonneg 2).trans_lt hp) hp1 hf
    (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    (Proofs.Section5.potentialLimit_of_asymptotic
      (Proofs.Section5.potentialAsymptotic_two hGQ hp hp1))
    (Proofs.Section5.sublinearLiouville_two p hp hp1 hAD)
    (Proofs.Section5.greenSymmetry_two hGQ hp hp1)
    (Proofs.Section5.trichotomyEventMeasurable _
      (Proofs.Section5.sublinearLiouville_two p hp hp1 hAD) hf)
    (Proofs.Section5.flipInfluenceStep p) (Proofs.Section5.flipShrinkStep f)
    (Proofs.Section5.flipIdentityStep f _) (Proofs.Section5.flipGradientStep _)
    Proofs.Section5.densityConclusionStep hlevel

/-- Theorem 1.3 from its dimension-two literature estimates. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOriginTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) : FastDecayStmt p := by
  have hUq := Rigidity.Percolation.supercritical_bond_uniqueness
  have hK := Rigidity.Percolation.kesten_rectangle_crossing
  have hW := Rigidity.Percolation.wellConnected_input_two
  have hJ := Rigidity.Topology.jordan_curve_theorem_sphere
  have hGrad : Section2.GreenGradientHomogenizationStmt 2 le_rfl p :=
    Proofs.S2.greenGradientHomogenization_two p hpc hp1 hGQ hCQ
      (Proofs.S2.regularityScaleStep_two_of_origin p hAD1 hCorr)
      (Proofs.S2.densityScaleStep_two_of_concentration p
        Proofs.S2.planar_cluster_density_concentration)
  have hExpansion (f : Vertex 2 → ℤ) : TwoScaleExpansionStmt p f :=
    twoScaleExpansion_of_planar_inputs hpc hp1 hGQ hCQ
      (Proofs.Section5.uniqueClusterAe hUq hpc hp1) hGrad
      (Proofs.Section5.connectingSetStep_two hW p hpc hp1) Proofs.Section5.flowOnConnectedSet
      Proofs.Section5.summationByParts Proofs.Section5.connectedSetRadiusStep
      Proofs.Section5.forwardDiffEdgeStep Proofs.Section5.greenTaylorStep
      (Proofs.S2.tailOfOsStep 2 p) (Proofs.S2.minimalScaleStep 2 p) f
  have hPotential (f : Vertex 2 → ℤ) : FastDecayPotentialStmt p f :=
    Rigidity.Assembly.fastDecayPotential_of_e1
      (fun hf => gradientTrichotomyAtE1 hUq hGQ hE hAD hCorr hCQ hW hK hJ hpc hp1 hf)
      (hExpansion f) (Proofs.Section5.correctedPlanesExist_of_input_two hCorr hpc hp1)
  exact fastDecay_of_steps
    (fastDecayDichotomy_of_steps hPotential (Proofs.Section5.logGrowth_two hUq hGQ hpc hp1)
      (Proofs.Section5.greenFamilyExists_two hE hpc hp1)
      (Proofs.Section5.sublinearLiouville_two p hpc hp1 hAD) Proofs.Section5.potentialLaplacian)
    Proofs.Section5.annulusStep


/-- Theorem 1.3 from planar inputs and Green-column existence. -/
theorem fast_decay_of_green_exists (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOriginTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistsTwo)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) : FastDecayStmt p :=
  fast_decay p hpc hp1 hCorr hCQ hAD hAD1
    (Proofs.Section5.greenColumnExistenceTwo_of_exists hAD hE) hGQ

end Rigidity.Assembly.WithPlanarInputs
