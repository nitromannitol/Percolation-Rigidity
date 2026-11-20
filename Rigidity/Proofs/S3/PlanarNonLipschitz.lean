import Rigidity.Proofs.S3.PlanarNotLipschitz
import Rigidity.Proofs.S3.PlanarCompare
import Rigidity.Steps.S3.PlanarOriginGradient
import Rigidity.Steps.S3.PlanarNotLipschitzInner
import Rigidity.Proofs.S3.PlanarFluxEvent

/-!
# Planar non-Lipschitz correctors

The non-Lipschitz argument uses only the planar forms of its literature inputs.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Steps.S3

/-- Proposition 3.2 from planar corrector, Green, regularity, and connectivity estimates. -/
theorem notLipschitz_of_planar_inputs (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hquant : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hreg : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hgreen : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hginput : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (hwc : Rigidity.External.WellConnectedInputTwo) : Rigidity.Section3.NotLipschitzStmt 2 p :=
  notLipschitzStmt_of_originGradient_two hclassical hcorrector hpc hp1 fun L hL =>
    originGradient_of_wellConnected_event_two p hpc hp1 hginput hreg hclassical
      (compareDifferentPlanes_two p hpc hp1 hclassical hcorrector hgreen hreg)
      (edgeGradientStep p) (finiteEnergyStep p) (closedBondsUniqueStep p)
      (wellConnectedEvent_two p hwc hpc hp1) (greenScaleEventStep 2 p)
      (fluxEventStep_two hclassical hcorrector hquant
        (homogenizedCoefficient_two hclassical hcorrector hquant) p) removalStep
      (shortPathsStep 2) divergenceStep bridgeFluxStep (greenKernelSumStep 2) L (by linarith)

end Rigidity.Proofs.S3
