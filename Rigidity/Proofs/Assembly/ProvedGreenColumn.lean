import Rigidity.Proofs.Assembly.ProvedOrderZero
import Rigidity.Proofs.Green.GreenColumnHolds

/-!
# The main theorems with the Green-column input proved

The existence and uniqueness of the Green columns of the infinite cluster
(`LatticeProb.External.SupercriticalBondGreenColumnExistence`, which Dario and Gu state without
proof) is proved in every dimension `d ≥ 2`
(`Rigidity.Green.supercriticalBondGreenColumnExistence_holds`). The theorems of
`Rigidity.Assembly.WithProvedOrderZero` that take it are restated here without it, and without
the other proved inputs: supercritical uniqueness, Proposition 2.3, the density concentration,
the rectangle crossings and the Jordan curve theorem on the sphere. Eleven theorems there take it
and ten are restated: `fastDecay` and `fastDecayWithProvedDensity` give the same statement,
`fast_decay`. What remains are the corrector inputs (Theorem 2.5), the regularity of order one
(Theorem 2.4 (iii) at `k = 1`) and the quantitative Green estimate of Dario and Gu, for the results
that use them.
-/

namespace Rigidity.Assembly.WithProvedGreenColumn

open MeasureTheory LatticeProb.Percolation

/-- **Theorem 1.1**, with every proved literature input supplied. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section3.LipschitzStmt d p :=
  Rigidity.Assembly.WithProvedOrderZero.lipschitz d hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input

/-- **Theorem 1.3**, with every proved literature input supplied. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedOrderZero.fastDecayWithProvedDensity p hpc hp1 hCorr hCQ hAD1
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ

/-- `Rigidity.Assembly.Main.notLipschitz` with every proved literature input supplied. -/
theorem notLipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section3.NotLipschitzStmt d p :=
  Rigidity.Assembly.WithProvedOrderZero.notLipschitz d hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input

/-- `Rigidity.Assembly.Main.fastDecayDichotomy` with every proved literature input supplied. -/
theorem fastDecayDichotomy (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayDichotomyStmt p :=
  Rigidity.Assembly.WithProvedOrderZero.fastDecayDichotomy p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ hAD1
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Proofs.S2.cluster_density_concentration Rigidity.Percolation.wellConnected_input
    Rigidity.Percolation.kesten_rectangle_crossing Rigidity.Topology.jordan_curve_theorem_sphere

/-- `Rigidity.Assembly.Main.fastDecayPotential` with every proved literature input supplied. -/
theorem fastDecayPotential (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayPotentialStmt p f :=
  Rigidity.Assembly.WithProvedOrderZero.fastDecayPotential p f hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ hAD1
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Proofs.S2.cluster_density_concentration Rigidity.Percolation.wellConnected_input
    Rigidity.Percolation.kesten_rectangle_crossing Rigidity.Topology.jordan_curve_theorem_sphere

/-- `Rigidity.Assembly.Main.gradientTrichotomy` with every proved literature input supplied. -/
theorem gradientTrichotomy (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.GradientTrichotomyStmt p f :=
  Rigidity.Assembly.WithProvedOrderZero.gradientTrichotomy p f hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere

/-- `Rigidity.Assembly.Main.levelSetDensity` with every proved literature input supplied. -/
theorem levelSetDensity (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.LevelSetDensityStmt p f :=
  Rigidity.Assembly.WithProvedOrderZero.levelSetDensity p f hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere

/-- `Rigidity.Assembly.Main.goodEventLowerBound` with every proved literature input supplied. -/
theorem goodEventLowerBound (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.GoodEventLowerBoundStmt p :=
  Rigidity.Assembly.WithProvedOrderZero.goodEventLowerBound p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input

/-- `Rigidity.Assembly.Main.largeGradientSensitive` with every proved literature input
supplied. -/
theorem largeGradientSensitive (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.LargeGradientSensitiveStmt p f :=
  Rigidity.Assembly.WithProvedOrderZero.largeGradientSensitive p f hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere

/-- `Rigidity.Assembly.Main.goodEventLowerBoundDirectional` with every proved literature input
supplied. -/
theorem goodEventLowerBoundDirectional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Steps.Section5.GoodEventLowerBoundDirectionalStmt p :=
  Rigidity.Assembly.WithProvedOrderZero.goodEventLowerBoundDirectional p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr hCQ
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds hGQ
    Rigidity.Percolation.wellConnected_input

end Rigidity.Assembly.WithProvedGreenColumn
