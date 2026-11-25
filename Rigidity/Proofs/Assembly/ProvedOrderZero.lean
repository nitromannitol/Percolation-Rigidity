import Rigidity.Proofs.Assembly.Main
import Rigidity.Proofs.Assembly.ProvedDensity
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderZeroHolds

/-!
# The main theorems with the order-zero regularity of Armstrong and Dario proved

The input `LatticeProb.External.ArmstrongDarioOrderZero` (Armstrong and Dario, Theorem 2 (iii) at
`k = 0`, in every dimension `d ≥ 2`: uniqueness of the infinite cluster, `dim 𝒜₀ = 1` and the
order-zero decay above a minimal scale) is proved in Percolation-Cluster-Homogenization
(`Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`, from Lemma 7.1 for the partition into
good cubes, Theorem 1 of Armstrong and Dario in every dimension and Lemmas 7.2 and 7.3). The
theorems of `Rigidity.Assembly.Main` that take it as a hypothesis, and Theorem 1.3 of
`Rigidity.Assembly.WithProvedDensity`, are restated here without it.
-/

namespace Rigidity.Assembly.WithProvedOrderZero

open MeasureTheory LatticeProb.Percolation

/-- `Rigidity.Assembly.Main.lipschitz` with the order-zero regularity input proved. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section3.LipschitzStmt d p :=
  Rigidity.Assembly.Main.lipschitz d hd p hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW

/-- `Rigidity.Assembly.Main.fastDecay` with the order-zero regularity input proved. -/
theorem fastDecay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.Main.fastDecay p hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hAD1 hE hGQ hDG hW hK hJ

/-- `Rigidity.Assembly.Main.notLipschitz` with the order-zero regularity input proved. -/
theorem notLipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section3.NotLipschitzStmt d p :=
  Rigidity.Assembly.Main.notLipschitz d hd p hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW

/-- `Rigidity.Assembly.Main.nonConstantOnGadget` with the order-zero regularity input proved. -/
theorem nonConstantOnGadget (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Rigidity.Section4.NonConstantOnGadgetStmt d hd p :=
  Rigidity.Assembly.Main.nonConstantOnGadget d hd p hpc hp1 hCorr
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds

/-- `Rigidity.Assembly.Main.fastDecayDichotomy` with the order-zero regularity input proved. -/
theorem fastDecayDichotomy (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.FastDecayDichotomyStmt p :=
  Rigidity.Assembly.Main.fastDecayDichotomy p hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hAD1 hE hGQ hDG hW hK hJ

/-- `Rigidity.Assembly.Main.fastDecayPotential` with the order-zero regularity input proved. -/
theorem fastDecayPotential (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.FastDecayPotentialStmt p f :=
  Rigidity.Assembly.Main.fastDecayPotential p f hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hAD1 hE hGQ hDG hW hK hJ

/-- `Rigidity.Assembly.Main.gradientTrichotomy` with the order-zero regularity input proved. -/
theorem gradientTrichotomy (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.GradientTrichotomyStmt p f :=
  Rigidity.Assembly.Main.gradientTrichotomy p f hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW hK hJ

/-- `Rigidity.Assembly.Main.levelSetDensity` with the order-zero regularity input proved. -/
theorem levelSetDensity (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.LevelSetDensityStmt p f :=
  Rigidity.Assembly.Main.levelSetDensity p f hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW hK hJ

/-- `Rigidity.Assembly.Main.goodEventLowerBound` with the order-zero regularity input proved. -/
theorem goodEventLowerBound (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section5.GoodEventLowerBoundStmt p :=
  Rigidity.Assembly.Main.goodEventLowerBound p hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW

/-- `Rigidity.Assembly.Main.largeGradientSensitive` with the order-zero regularity input proved. -/
theorem largeGradientSensitive (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.LargeGradientSensitiveStmt p f :=
  Rigidity.Assembly.Main.largeGradientSensitive p f hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW hK hJ

/-- `Rigidity.Assembly.Main.goodEventLowerBoundDirectional` with the order-zero regularity input
proved. -/
theorem goodEventLowerBoundDirectional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Steps.Section5.GoodEventLowerBoundDirectionalStmt p :=
  Rigidity.Assembly.Main.goodEventLowerBoundDirectional p hpc hp1 hUq hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hE hGQ hW

/-- **Theorem 1.3** in the form `Rigidity.Assembly.WithProvedDensity.fast_decay`, with the
order-zero regularity input proved as well. -/
theorem fastDecayWithProvedDensity (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.WithProvedDensity.fast_decay p hpc hp1 hCorr hCQ
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds hAD1 hE hGQ

end Rigidity.Assembly.WithProvedOrderZero
