import Rigidity.Steps.S4.DetSlope

/-!
# Corrected planes of nonzero slope are not constant

Proof of `Rigidity.Steps.S4.CorrectedPlaneNonconstantStep`, and with it Lemma 4.7 (paper
L1330-1376 of the corrected draft). A constant function is a corrected plane of slope `0`
(`isCorrectedPlane_const`). The cited corrector input
(`LatticeProb.External.SupercriticalBondCorrectorInput`, Armstrong-Dario) gives, almost surely,
uniqueness of the slope of every element of `A₁(C_∞)`; hence a constant corrected plane has slope
`0`.
-/

namespace Rigidity.Proofs.S4

open MeasureTheory LatticeProb.Percolation Rigidity.Section4 Rigidity.Steps.S4

/-- Almost surely, a corrected plane of nonzero slope on the infinite cluster is not constant:
the slope of an element of `A₁(C_∞)` is unique, and constants have slope `0`. -/
theorem correctedPlaneNonconstantStep {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    CorrectedPlaneNonconstantStep d p := by
  filter_upwards [hcorrector d hd p hpc hp1] with ω hω h q hq u hu
  by_contra hconstant
  push Not at hconstant
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent h).nonempty_supp
  have heq : u = fun _ => u ⟨o, ho⟩ := funext fun x => hconstant x _
  have hzero : IsCorrectedPlane (uniqueInfiniteComponent h) 0 u := by
    rw [heq]
    exact isCorrectedPlane_const _ _
  obtain ⟨_, _, hunique⟩ := (hω h).2 u hu.1
  exact hq ((hunique q hu).trans (hunique 0 hzero).symm)

/-- Lemma 4.7: for a deterministic nonzero slope `q`, almost surely some edge of the infinite
cluster carries a non-integer gradient of the corrected plane `ℓ_q`. -/
theorem detSlope {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    DetSlopeStmt d p :=
  detSlope_of_steps hd p hpc hp1 hclassical hcorrector
    (correctedPlaneNonconstantStep hd p hpc hp1 hcorrector)

end Rigidity.Proofs.S4
