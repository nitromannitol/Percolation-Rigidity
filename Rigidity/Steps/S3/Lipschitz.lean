import Rigidity.Steps.S3.ReductionToSlopeE1
import Rigidity.Steps.S3.NotLipschitzInner
import LatticeProb.External.SupercriticalBondUniquenessInput

/-!
# Theorem 1.1 from Lemma 3.1 and Proposition 3.2

Theorem 1.1 (paper L95-98 of the corrected draft, proof at L863): almost surely, every Lipschitz
harmonic function on the infinite cluster is constant. If nonconstant Lipschitz harmonic functions
existed with positive probability, Lemma 3.1 would give a deterministic `L > 0` with `ℓ_{e₁}` almost
surely `L`-Lipschitz, contradicting the second conclusion of Proposition 3.2 at `max L 1`.
-/

namespace Rigidity.Steps.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3

variable {d : ℕ}

/-- Lipschitz with some nonnegative constant is the same as `L`-Lipschitz for some real `L`. -/
theorem componentLipschitz_iff_exists_isLipschitzWith {ω : Configuration d}
    (C : OpenComponent ω) (u : C → ℝ) :
    ComponentLipschitz C u ↔ ∃ L : ℝ, IsLipschitzWith C L u := by
  constructor
  · rintro ⟨K, -, hK⟩
    exact ⟨K, hK⟩
  · rintro ⟨L, hL⟩
    exact ⟨max L 0, le_max_right _ _, isLipschitzWith_mono hL (le_max_left _ _)⟩

/-- Theorem 1.1 follows from Lemma 3.1 and Proposition 3.2, with the classical existence and
uniqueness of the infinite cluster. -/
theorem lipschitz_of_steps [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (h31 : Section3.ReductionToSlopeE1Stmt d p) (h32 : Section3.NotLipschitzStmt d p) :
    Section3.LipschitzStmt d p := by
  have hN : latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
        ComponentLipschitz (uniqueInfiniteComponent h) u ∧ ∃ x y, u x ≠ u y} = 0 := by
    by_contra hN
    obtain ⟨L, -, hL⟩ := h31 hN
    refine (h32.notLipschitzWith_ne_zero (le_max_right L 1)) (measure_mono_null ?_ (ae_iff.1 hL))
    rintro ω ⟨h, u, hu, hnot⟩ ⟨h', hh'⟩
    exact hnot (isLipschitzWith_mono (hh' u hu) (le_max_left _ _))
  have hU : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ uniqueInfiniteComponentEvent d :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent d)).2
      (hclassical.2 d hd p hpc hp1)
  filter_upwards [hU, measure_eq_zero_iff_ae_notMem.1 hN] with ω hω hωN
  refine ⟨hω, fun u hharm hlip => ?_⟩
  by_cases hc : ∃ x y, u x ≠ u y
  · exact (hωN ⟨hω, u, hharm, hlip, hc⟩).elim
  · push Not at hc
    by_cases hne : Nonempty (uniqueInfiniteComponent hω)
    · obtain ⟨x₀⟩ := hne
      exact ⟨u x₀, fun x => hc x x₀⟩
    · exact ⟨0, fun x => (hne ⟨x⟩).elim⟩

end Rigidity.Steps.S3
