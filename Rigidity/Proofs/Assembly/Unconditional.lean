import Rigidity.Proofs.Assembly.ProvedInputs
import Rigidity.Proofs.Assembly.ProvedFluxWeakNorm
import Rigidity.Proofs.Assembly.ProvedCorrectorQuantitative
import Rigidity.Proofs.Percolation.WellConnected
import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorInput

/-!
# Main theorems with every literature input proved

Theorem 6.5 uses three literature inputs: the existence and uniqueness of the infinite cluster,
the smoothing bound of Micciancio and Regev, and Proposition 2.3. All three are proved, so the
theorem holds with the regime `2 ≤ d`, `p_c(d) < p < 1` as its only hypotheses.

Theorem 1.2 uses two literature inputs: the existence and uniqueness of the infinite cluster, and
the qualitative part of Theorem 2.5 (a unique normalized corrected plane for each slope, and a
unique slope for each harmonic function of linear growth). Both are proved, so the theorem holds
with the regime `2 ≤ d`, `p_c(d) < p < 1` as its only hypotheses.

Every literature input of Theorem 1.3 is proved in dimension two, so the theorem holds with the
regime `p_c(2) < p < 1` as its only hypotheses.

Theorem 1.1 and Proposition 3.2 use seven literature inputs: the existence and uniqueness of the
infinite cluster, the qualitative and the quantitative parts of Theorem 2.5, the regularity of
order zero (Theorem 2.4), the existence and uniqueness of the Green columns, the quantitative
estimate of the Green function of Dario and Gu, and Proposition 2.3. All seven are proved, so both
hold with the regime `2 ≤ d`, `p_c(d) < p < 1` as their only hypotheses.
-/

namespace Rigidity.Assembly.Unconditional

open MeasureTheory LatticeProb.Percolation

/-- **Theorem 6.5**, with supercritical bond uniqueness, lattice smoothing and Proposition 2.3
supplied by their proofs. -/
theorem slow_mixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section6.SlowMixingStmt d p :=
  Rigidity.Assembly.WithProvedInputs.slow_mixing d hd p hpc hp1
    Rigidity.Percolation.wellConnected_input

/-- **Theorem 1.2**, with supercritical bond uniqueness and the qualitative corrector input supplied
by their proofs: the regime `2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem integer_valued_linear_growth (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ) :=
  Rigidity.Assembly.WithProvedInputs.integer_valued_linear_growth d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Theorem 1.3**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem fast_decay (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.ProvedFluxWeakNorm.fast_decay_holds p hpc hp1

/-- **Theorem 1.1** (`theorem:lipschitz`), with every literature input supplied by its proof: the
regime `2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section3.LipschitzStmt d p :=
  Rigidity.Assembly.WithProvedGreenColumn.lipschitz d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Proposition 3.2** (`prop:not-lipschitz`), with every literature input supplied by its proof:
the regime `2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem notLipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section3.NotLipschitzStmt d p :=
  Rigidity.Assembly.WithProvedGreenColumn.notLipschitz d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

end Rigidity.Assembly.Unconditional
