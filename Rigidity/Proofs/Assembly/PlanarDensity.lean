import Rigidity.Proofs.Assembly.Crossing
import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.S2.PlanarRegularity

/-!
# Fast decay from planar density concentration

The density and order-one regularity inputs to the two-scale expansion are needed only in
dimension two.
-/

namespace Rigidity.Assembly.WithPlanarDensity

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- Theorem 1.3 with planar density concentration and order-one regularity. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOriginTwo)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInputTwo)
    (hW : Rigidity.External.WellConnectedInput)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) : FastDecayStmt p := by
  have hUq := Rigidity.Percolation.supercritical_bond_uniqueness
  have hK := Rigidity.Percolation.kesten_rectangle_crossing
  have hHom := Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ
  have hGrad : Section2.GreenGradientHomogenizationStmt 2 le_rfl p :=
    Proofs.S2.greenGradientHomogenization_of_regularity_density le_rfl p hpc hp1 hGQ hCQ
      (Proofs.S2.regularityScaleStep_two_of_origin p hAD1
        (Rigidity.External.supercriticalBondCorrectorInputTwo_of_input hCorr))
      (Proofs.S2.densityScaleStep_two_of_concentration p hDG)
  have hExpansion (f : Vertex 2 → ℤ) : TwoScaleExpansionStmt p f :=
    twoScaleExpansion_of_steps hpc hp1 hW hGQ hCQ (Proofs.Section5.uniqueClusterAe hUq hpc hp1)
      hGrad Proofs.Section5.connectingSetStep Proofs.Section5.flowOnConnectedSet
      Proofs.Section5.summationByParts Proofs.Section5.connectedSetRadiusStep
      Proofs.Section5.normalizedGreenSymmetryStep Proofs.Section5.correctedPlaneGradientStep
      Proofs.Section5.forwardDiffEdgeStep Proofs.Section5.greenTaylorStep
      (Proofs.S2.tailOfOsStep 2 p) (Proofs.S2.minimalScaleStep 2 p) f
  have hPotential (f : Vertex 2 → ℤ) : FastDecayPotentialStmt p f :=
    Rigidity.Assembly.fastDecayPotential_of_e1
      (fun hf => Rigidity.Assembly.gradientTrichotomyAtE1 hUq hGQ hE hAD hCorr hCQ hW hK hJ
        hHom hpc hp1 hf)
      (hExpansion f) (correctedPlanesExist_of_input hCorr hpc hp1)
  exact fastDecay_of_steps
    (fastDecayDichotomy_of_steps hPotential (Rigidity.Assembly.logGrowth hUq hGQ hpc hp1)
      (Proofs.Section5.greenFamilyExists hE hpc hp1)
      (Proofs.Section5.sublinearLiouville p hpc hp1 hAD) Proofs.Section5.potentialLaplacian)
    Proofs.Section5.annulusStep

end Rigidity.Assembly.WithPlanarDensity
