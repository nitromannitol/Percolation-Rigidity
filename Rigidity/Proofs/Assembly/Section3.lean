import Rigidity.Steps.S3.Lipschitz
import Rigidity.Steps.S3.NotLipschitz
import Rigidity.Steps.S3.CompareDifferentPlanes
import Rigidity.Proofs.S3.SlopeZeroOne
import Rigidity.Proofs.S3.LipschitzMemA1
import Rigidity.Proofs.S3.ClosedSlopes
import Rigidity.Proofs.S3.Reflection
import Rigidity.Proofs.S3.FlipCluster
import Rigidity.Proofs.S3.FlipCorrector
import Rigidity.Proofs.S3.GreenLaplacian
import Rigidity.Proofs.S3.GreenColumnSublinear
import Rigidity.Proofs.S3.SublinearLiouville
import Rigidity.Proofs.S3.EdgeGradient
import Rigidity.Proofs.S3.FiniteEnergy
import Rigidity.Proofs.S3.ClosedBondsUnique
import Rigidity.Proofs.S3.WellConnectedEvent
import Rigidity.Proofs.S3.GreenScaleEvent
import Rigidity.Proofs.S3.FluxEvent
import Rigidity.Proofs.S3.Removal
import Rigidity.Proofs.S3.ShortPaths
import Rigidity.Proofs.S3.Divergence
import Rigidity.Proofs.S3.BridgeFlux
import Rigidity.Proofs.S3.GreenKernelSum

/-!
# Section 3: the composed results

The numbered results of Section 3 of the corrected draft and Theorem 1.1, each obtained by
composing the reduction of its carving (`Rigidity.Steps.S3`) with the proved steps
(`Rigidity.Proofs.S3`). The hypotheses are the regime `2 ≤ d`, `p_c(d) < p < 1` and the cited
literature inputs used by the steps:

* `LatticeProb.External.SupercriticalBondUniqueness`: existence and uniqueness of the infinite
  cluster;
* `LatticeProb.External.SupercriticalBondCorrectorInput`: the first-order correctors of the
  infinite cluster (Armstrong-Dario, qualitative part of Theorem 2.5);
* `Rigidity.External.CorrectorQuantitativeInput`: the quantitative sublinearity of the correctors
  (Theorem 2.5);
* `LatticeProb.External.ArmstrongDarioOrderZero`: the Liouville theorem for sublinear harmonic
  functions on the infinite cluster (Armstrong-Dario, order zero);
* `LatticeProb.External.SupercriticalBondGreenColumnExistence` and
  `LatticeProb.External.SupercriticalBondGreenQuantitative`: the Green function of the infinite
  cluster (Dario-Gu), the cited inputs of Proposition 2.8;
* `Rigidity.External.WellConnectedInput`: the well-connected cubes (Proposition 2.3,
  Antal-Pisztora/Penrose-Pisztora).

Proposition 3.2 and Theorem 1.1 also use the positivity of the homogenized coefficient `ā` as the
mean of the gradient of the corrected plane `ℓ_{e₁}` along the bond `(0, e₁)`. No proposition of
`Rigidity/External` or `LatticeProb/External` states it; it enters as the hypothesis
`Rigidity.Proofs.S3.HomogenizedCoefficientProposed`, the local proposed input of
`Rigidity/Proofs/S3/FluxEvent.lean`, which
`Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed` proves from the cited
inputs (as in `Rigidity/Proofs/Assembly/Main.lean`).
-/

namespace Rigidity.Assembly

open LatticeProb.Percolation

variable {d : ℕ} [NeZero d]

/-- **Lemma 3.1**: if, with positive probability, the infinite cluster carries a non-constant
Lipschitz harmonic function, then for a deterministic `L > 0` the corrected plane `ℓ_{e₁}` is
almost surely `L`-Lipschitz. -/
theorem reductionToSlopeE1 (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hwc : External.WellConnectedInput) :
    Section3.ReductionToSlopeE1Stmt d p :=
  have hA1 := Proofs.S3.lipschitzMemA1Step hd hpc hp1 hwc hcorrector
  Steps.S3.reductionToSlopeE1_of_steps
    (Proofs.S3.zeroOneStep hclassical hcorrector hd p hpc hp1 hA1) hA1
    (Proofs.S3.closedSlopesStep hclassical hcorrector hd p hpc hp1)
    (Proofs.S3.deterministicSlopeStep hclassical hcorrector hd p hpc hp1)
    (Proofs.S3.reflectionStep p)

/-- **Lemma 3.3**: almost surely, for every finite set `B` of edges of the infinite cluster whose
removal does not disconnect it, the corrected planes of every slope on the cluster and on the
cluster without `B` exist and are unique up to an additive constant, and their gradients differ
by the sum over `B` of the mixed gradient of the Green function of the cluster. -/
theorem compareDifferentPlanes (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hgreen : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero) :
    Section3.CompareDifferentPlanesStmt d hd p :=
  Steps.S3.compareDifferentPlanes_of_steps hd p hpc hp1 hclassical hcorrector hgreen
    Proofs.S3.flipClusterStep (Proofs.S3.flipCorrectorStep hd p hpc hp1 hcorrector)
    (Proofs.S3.greenLaplacianStep hd) (Proofs.S3.greenColumnSublinearStep hd)
    (Proofs.S3.sublinearLiouvilleStep hd p hpc hp1 hreg)

/-- **Proposition 3.2**: for every `L ≥ 1`, with positive probability the origin lies in the
infinite cluster and `|∇ℓ_{e₁}(0)| > L`; consequently `ℓ_{e₁}` is not `L`-Lipschitz with
positive probability. Besides the cited inputs, it uses the positivity of the homogenized
coefficient through the local proposed hypothesis
`Rigidity.Proofs.S3.HomogenizedCoefficientProposed` of `Rigidity/Proofs/S3/FluxEvent.lean`. -/
theorem notLipschitz (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hquant : External.CorrectorQuantitativeInput)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hgreen : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hginput : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hwc : External.WellConnectedInput)
    (hhom : Proofs.S3.HomogenizedCoefficientProposed) :
    Section3.NotLipschitzStmt d p :=
  Steps.S3.notLipschitz_of_steps hd p hpc hp1 hwc hginput hreg hclassical hcorrector
    (compareDifferentPlanes hd p hpc hp1 hclassical hcorrector hgreen hreg)
    (Proofs.S3.edgeGradientStep p) (Proofs.S3.finiteEnergyStep p)
    (Proofs.S3.closedBondsUniqueStep p) (Proofs.S3.wellConnectedEventStep d p)
    (Proofs.S3.greenScaleEventStep d p)
    (Proofs.S3.fluxEventStep hclassical hcorrector hquant hhom p) Proofs.S3.removalStep
    (Proofs.S3.shortPathsStep d) Proofs.S3.divergenceStep Proofs.S3.bridgeFluxStep
    (Proofs.S3.greenKernelSumStep d)

/-- **Theorem 1.1**: for `d ≥ 2` and `p_c(d) < p < 1`, almost surely every Lipschitz harmonic
function on the infinite cluster is constant. Composed from Lemma 3.1 and Proposition 3.2; besides
the cited inputs, it uses the positivity of the homogenized coefficient through the local proposed
hypothesis `Rigidity.Proofs.S3.HomogenizedCoefficientProposed` of
`Rigidity/Proofs/S3/FluxEvent.lean`. -/
theorem lipschitz (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hquant : External.CorrectorQuantitativeInput)
    (hreg : LatticeProb.External.ArmstrongDarioOrderZero)
    (hgreen : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hginput : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hwc : External.WellConnectedInput)
    (hhom : Proofs.S3.HomogenizedCoefficientProposed) :
    Section3.LipschitzStmt d p :=
  Steps.S3.lipschitz_of_steps hd p hpc hp1 hclassical
    (reductionToSlopeE1 hd p hpc hp1 hclassical hcorrector hwc)
    (notLipschitz hd p hpc hp1 hclassical hcorrector hquant hreg hgreen hginput hwc hhom)

end Rigidity.Assembly
