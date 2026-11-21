import Rigidity.Proofs.Assembly.ProvedInputs
import Rigidity.Proofs.Percolation.WellConnected
import Rigidity.Proofs.S2.ClusterDensityConcentration

/-!
# Main theorems with the density concentration proved

The concentration of the density of the infinite cluster (Dario–Gu, Proposition A.1,
`Rigidity.External.ClusterDensityConcentrationInput`) is proved in every dimension
(`Rigidity.Proofs.S2.cluster_density_concentration`). Proposition 2.6 therefore no longer takes it
as a hypothesis, and neither does Theorem 1.3, which also uses the proved Proposition 2.3.
-/

namespace Rigidity.Assembly.WithProvedDensity

open LatticeProb.Percolation

/-- **Proposition 2.6**, with the density concentration supplied by its proof. -/
theorem green_gradient_homogenization (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section2.GreenGradientHomogenizationStmt d hd p :=
  Rigidity.Assembly.Main.greenGradientHomogenization d hd p hpc hp1 hCorr hCQ hAD1 hGQ
    Rigidity.Proofs.S2.cluster_density_concentration

/-- **Theorem 1.3**, with supercritical uniqueness, rectangle crossings, the sphere Jordan
theorem, Proposition 2.3 and the density concentration supplied by their proofs. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedInputs.fast_decay p hpc hp1 hCorr hCQ hAD hAD1 hE hGQ
    Rigidity.Proofs.S2.cluster_density_concentration Rigidity.Percolation.wellConnected_input

end Rigidity.Assembly.WithProvedDensity
