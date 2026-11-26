import Rigidity.Proofs.Assembly.ProvedOrderOne
import Rigidity.Proofs.Corrector.CorrectorQuantitative
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderOneHolds

/-!
# The main theorems with the qualitative corrector input proved

The input `LatticeProb.External.SupercriticalBondCorrectorInput` (Armstrong and Dario, Theorem 2 (i)
and (ii) at `k = 1`; Dario and Gu, Proposition 2.12, qualitative part) is proved in every dimension
`d ≥ 2` in Percolation-Cluster-Homogenization
(`Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds`). The three theorems of
`Rigidity.Assembly.WithProvedOrderOne` are restated here without it: they take
`CorrectorQuantitativeInput` and `SupercriticalBondGreenQuantitative`. By the reduction of
`CorrectorQuantitativeInput` to Theorem 1 of Dario in `d ≥ 3`
(`Rigidity.Corrector.GeneralDim.correctorQuantitativeInput_of_dario`), the quantitative corrector
input follows from `DarioOptimalCorrectorThree` alone (`correctorQuantitativeInput_of_darioThree`).
-/

namespace Rigidity.Assembly.WithProvedCorrector

open MeasureTheory LatticeProb.Percolation

/-- The quantitative corrector input from Theorem 1 of Dario in `d ≥ 3`, the qualitative corrector
input being proved. -/
theorem correctorQuantitativeInput_of_darioThree
    (hD : Rigidity.Corrector.GeneralDim.DarioOptimalCorrectorThree) :
    Rigidity.External.CorrectorQuantitativeInput :=
  Rigidity.Corrector.GeneralDim.correctorQuantitativeInput_of_dario hD
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Theorem 1.3**, with every proved literature input supplied, the qualitative corrector input
and the regularity of order one included. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedOrderOne.fast_decay p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds hCQ hGQ

/-- `Rigidity.Assembly.Main.fastDecayDichotomy` with every proved literature input supplied, the
qualitative corrector input and the regularity of order one included. -/
theorem fastDecayDichotomy (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayDichotomyStmt p :=
  Rigidity.Assembly.WithProvedOrderOne.fastDecayDichotomy p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds hCQ hGQ

/-- `Rigidity.Assembly.Main.fastDecayPotential` with every proved literature input supplied, the
qualitative corrector input and the regularity of order one included. -/
theorem fastDecayPotential (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayPotentialStmt p f :=
  Rigidity.Assembly.WithProvedOrderOne.fastDecayPotential p f hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds hCQ hGQ

end Rigidity.Assembly.WithProvedCorrector
