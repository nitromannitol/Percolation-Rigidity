import Rigidity.Proofs.Assembly.ProvedGreenColumn
import PercolationClusterHomogenization.Proofs.Regularity.CorrectorSublinearFromRegularity

/-!
# The main theorems with the regularity of order one of Armstrong and Dario proved

The input `Rigidity.External.ArmstrongDarioOrderOneOrigin` (Armstrong and Dario, Theorem 2 (iii) at
`k = 1` at the origin, in every dimension `d ≥ 2`) is proved in Percolation-Cluster-Homogenization from
the existence of the corrected planes alone
(`Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput`): the
mesoscopic estimate (7.18) at `k = 2` is proved in every dimension, and with the density of the infinite
cluster it makes the sublinearity of the corrected planes quantitative, (1.18) with a minimal scale of
class `O_s`. The existence of the corrected planes is the first part of
`LatticeProb.External.SupercriticalBondCorrectorInput`, which the theorems taking the order-one input
already assume. The three theorems of `Rigidity.Assembly.WithProvedGreenColumn` that take
`ArmstrongDarioOrderOneOrigin` are restated here without it.
-/

namespace Rigidity.Assembly.WithProvedOrderOne

open MeasureTheory LatticeProb.Percolation

/-- **Theorem 1.3**, with every proved literature input supplied, the regularity of order one
included. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedGreenColumn.fast_decay p hpc hp1 hCorr hCQ
    (Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput hCorr)
    hGQ

/-- `Rigidity.Assembly.Main.fastDecayDichotomy` with every proved literature input supplied, the
regularity of order one included. -/
theorem fastDecayDichotomy (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayDichotomyStmt p :=
  Rigidity.Assembly.WithProvedGreenColumn.fastDecayDichotomy p hpc hp1 hCorr hCQ
    (Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput hCorr)
    hGQ

/-- `Rigidity.Assembly.Main.fastDecayPotential` with every proved literature input supplied, the
regularity of order one included. -/
theorem fastDecayPotential (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayPotentialStmt p f :=
  Rigidity.Assembly.WithProvedGreenColumn.fastDecayPotential p f hpc hp1 hCorr hCQ
    (Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_supercriticalBondCorrectorInput hCorr)
    hGQ

end Rigidity.Assembly.WithProvedOrderOne
