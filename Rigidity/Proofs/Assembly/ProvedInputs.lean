import Rigidity.Proofs.Assembly.Main
import Rigidity.Proofs.Assembly.Smoothing
import PercolationClusterHomogenization.Proofs.Percolation.BondUniqueness
import PercolationClusterHomogenization.Proofs.Percolation.KestenCrossing
import Rigidity.Proofs.Topology.JordanCurveSphere

/-!
# Main theorems with proved literature inputs

The uniqueness and rectangle-crossing theorems and the sphere Jordan curve theorem are supplied
by their proofs. The smoothing bound is supplied in the sandpile mixing theorem.
-/

namespace Rigidity.Assembly.WithProvedInputs

open MeasureTheory LatticeProb.Percolation

/-- Theorem 1.1, with supercritical bond uniqueness supplied. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section3.LipschitzStmt d p :=
  Rigidity.Assembly.Main.lipschitz d hd p hpc hp1 Rigidity.Percolation.supercritical_bond_uniqueness
    hCorr hCQ hAD hE hGQ hW

/-- Theorem 1.2, with supercritical bond uniqueness supplied. -/
theorem integer_valued_linear_growth (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ) :=
  Rigidity.Assembly.Main.integerValuedLinearGrowth d hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hCorr

/-- Theorem 1.3, with uniqueness, rectangle crossings, and the sphere Jordan theorem supplied. -/
theorem fast_decay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.Main.fastDecay p hpc hp1 Rigidity.Percolation.supercritical_bond_uniqueness
    hCorr hCQ hAD hAD1 hE hGQ hDG hW Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere

/-- Theorem 6.5, with supercritical bond uniqueness and lattice smoothing supplied. -/
theorem slow_mixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.External.WellConnectedInput) : Rigidity.Section6.SlowMixingStmt d p :=
  Rigidity.Assembly.WithSmoothing.slow_mixing d hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness hW

end Rigidity.Assembly.WithProvedInputs
