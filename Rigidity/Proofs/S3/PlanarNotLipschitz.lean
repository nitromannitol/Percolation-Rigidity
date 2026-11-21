import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.S3.PlanarGreenColumn

/-!
# Non-Lipschitz correctors from planar well-connectedness

The non-Lipschitz argument at dimension two needs only the planar well-connectedness estimate.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Steps.S3

/-- Planar well-connectedness implies that the failure probability tends to zero. -/
theorem wellConnectedEvent_two (p : unitInterval) (hW : Rigidity.External.WellConnectedInputTwo)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Tendsto (fun N : ℕ =>
      latticeBondLaw 2 p {ω | ¬ Rigidity.External.IsWellConnected ω 0 N}) atTop (𝓝 0) := by
  obtain ⟨c, C, s, hc, -, hs, hbound⟩ := hW p hpc hp1
  have hpow : Tendsto (fun N : ℕ => c * (N : ℝ) ^ s) atTop atTop :=
    ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hexp : Tendsto (fun N : ℕ => C * Real.exp (-(c * (N : ℝ) ^ s))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hpow).const_mul C
  have hlim := ENNReal.tendsto_ofReal hexp
  rw [ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun N => hbound 0 N

/-- Proposition 3.2 in dimension two from planar well-connectedness. -/
theorem notLipschitz_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hquant : Rigidity.External.CorrectorQuantitativeInput)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hgreen : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hginput : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hwc : Rigidity.External.WellConnectedInputTwo)
    (hhom : HomogenizedCoefficientProposed) : Rigidity.Section3.NotLipschitzStmt 2 p :=
  notLipschitzStmt_of_originGradient hclassical hcorrector le_rfl hpc hp1 fun L hL =>
    originGradient_of_wellConnected_event le_rfl p hpc hp1 hginput hreg hclassical
      (compareDifferentPlanes_of_green_event le_rfl p hpc hp1 hcorrector
        (ae_unique_green_column_for_all_poles_two hgreen hclassical p hpc hp1)
        flipClusterStep (flipCorrectorStep le_rfl p hpc hp1 hcorrector)
        (greenLaplacianStep le_rfl) (greenColumnSublinearStep le_rfl)
        (sublinearLiouvilleStep le_rfl p hpc hp1 hreg))
      (edgeGradientStep p) (finiteEnergyStep p) (closedBondsUniqueStep p)
      (wellConnectedEvent_two p hwc hpc hp1) (greenScaleEventStep 2 p)
      (fluxEventStep hclassical hcorrector hquant hhom p) removalStep
      (shortPathsStep 2) divergenceStep bridgeFluxStep (greenKernelSumStep 2) L (by linarith)

end Rigidity.Proofs.S3
