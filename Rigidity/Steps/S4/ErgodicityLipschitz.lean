import Rigidity.Draft.Section4Statements
import Rigidity.Frozen.IntegerLinearGrowthV1

/-!
# Lemma 4.9 from Theorem 1.2

Lemma 4.9 (paper L1405-1430 of the corrected draft) is proved in the paper by ergodicity, and the
paper then derives Theorem 1.2 from Lemmas 4.7-4.9. Theorem 1.2 is available independently
(`Rigidity.integer_valued_linear_growth`): almost surely every integer-valued harmonic function of
linear growth on the infinite cluster is constant. Hence the antecedent of Lemma 4.9, a nonconstant
such function with positive probability, is contained in a null set, and Lemma 4.9 holds
vacuously.
-/

namespace Rigidity.Steps.S4

open MeasureTheory LatticeProb.Percolation Rigidity.Section4

/-- Lemma 4.9 from Theorem 1.2: the event that the infinite cluster carries a nonconstant
integer-valued harmonic function of linear growth is null, so the implication holds. -/
theorem ergodicityLipschitz_of_integerValuedLinearGrowth {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (p : unitInterval) (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ErgodicityLipschitzStmt d p := by
  intro hpos
  exfalso
  apply hpos
  have hae := Rigidity.integer_valued_linear_growth d hd p hpc hp1 hclassical hcorrector
  rw [ae_iff] at hae
  refine measure_mono_null ?_ hae
  intro ω hω hgood
  obtain ⟨h, u, hharm, hint, hgrowth, x, y, hxy⟩ := hω
  obtain ⟨_, hconst⟩ := hgood
  obtain ⟨a, ha⟩ := hconst u hharm hint hgrowth
  exact hxy ((ha x).trans (ha y).symm)

end Rigidity.Steps.S4
