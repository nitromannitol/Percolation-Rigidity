import Rigidity.Draft.Section4Statements
import Rigidity.Support.IntegerLinearGrowthResult

/-!
# Lemma 4.7 from Theorem 1.2

Lemma 4.7 (paper L1330-1376 of the corrected draft) is proved in the paper from Lemma 4.8 and the
corrector oscillation bound, and the paper then derives Theorem 1.2 from Lemmas 4.7-4.9. Here the
order is reversed: the rigidity statement behind Theorem 1.2
(`Rigidity.Support.integer_gradient_corrected_planes_constant`) says that almost surely every
corrected plane with integer gradients on the infinite cluster is constant. Lemma 4.7 follows from
it and the step `CorrectedPlaneNonconstantStep`: a corrected plane of nonzero slope is not constant.
-/

namespace Rigidity.Steps.S4

open MeasureTheory LatticeProb.Percolation Rigidity.Section4

/-- Step for Lemma 4.7: almost surely, for every nonzero slope `q`, no corrected plane `ℓ_q` of
slope `q` on the infinite cluster is constant. -/
def CorrectedPlaneNonconstantStep (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
    ∀ q : Fin d → ℝ, q ≠ 0 → ∀ u : uniqueInfiniteComponent h → ℝ,
      IsCorrectedPlane (uniqueInfiniteComponent h) q u →
        ∃ x y : uniqueInfiniteComponent h, u x ≠ u y

/-- Lemma 4.7 from the rigidity of corrected planes with integer gradients and
`CorrectedPlaneNonconstantStep`. -/
theorem detSlope_of_steps {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput)
    (h : CorrectedPlaneNonconstantStep d p) : DetSlopeStmt d p := by
  intro q hq
  filter_upwards [Rigidity.Support.integer_gradient_corrected_planes_constant d hd p hpc hp1
    hclassical hcorrector, h] with ω hconst hnonconst
  obtain ⟨hω, hconst⟩ := hconst
  refine ⟨hω, fun u hu => ?_⟩
  by_contra hall
  push Not at hall
  obtain ⟨x, y, hxy⟩ := hnonconst hω q hq u hu
  refine hxy (hconst q u hu (fun a b hab => ?_) x y)
  obtain ⟨n, hn⟩ := hall b a hab.symm
  exact ⟨n, hn.symm⟩

end Rigidity.Steps.S4
