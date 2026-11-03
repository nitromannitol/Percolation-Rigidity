import Rigidity.Proofs.S3.SlopeSetMeasurable

/-!
# Lemma 3.1: the set of Lipschitz slopes is closed and stable under linear combinations

Step `step:3.1-closed-slopes` of Lemma 3.1 (paper L825-827 of the corrected draft). On a
measurable corrector-valid set of full measure, the corrected plane `ℓ_q` has the gradient
`∑ⱼ qⱼ g(ω, e)ⱼ` along every open edge `e` of the cluster, for a coefficient field `g` which does
not depend on `q` (the map `q ↦ ℓ_q(x) - ℓ_q(y)` is linear, by uniqueness of corrected planes up
to constants). The set of `L`-Lipschitz slopes is then the slab set
`{q | ∀ e, |∑ⱼ qⱼ g(ω, e)ⱼ| ≤ L}`: it is closed, and the triangle inequality bounds the gradients
of `ℓ_{a q + b q'}` by `|a| L + |b| L'`.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation LatticeProb.External Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- The gradient bounds of slab sets add under linear combinations of slopes. -/
theorem smul_add_smul_mem_slabSlopeSet (c : (Vertex d × Vertex d) → Fin d → ℝ)
    {L L' a b : ℝ} {q q' : Fin d → ℝ} (hq : q ∈ slabSlopeSet c L)
    (hq' : q' ∈ slabSlopeSet c L') : a • q + b • q' ∈ slabSlopeSet c (|a| * L + |b| * L') := by
  intro e
  have hsum : ∑ j, (a • q + b • q') j * c e j =
      a * ∑ j, q j * c e j + b * ∑ j, q' j * c e j := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  rw [hsum]
  calc
    |a * ∑ j, q j * c e j + b * ∑ j, q' j * c e j| ≤
        |a * ∑ j, q j * c e j| + |b * ∑ j, q' j * c e j| := abs_add_le _ _
    _ = |a| * |∑ j, q j * c e j| + |b| * |∑ j, q' j * c e j| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * L + |b| * L' := add_le_add (mul_le_mul_of_nonneg_left (hq e) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hq' e) (abs_nonneg b))

/-- Step `step:3.1-closed-slopes`: almost surely, the set of `L`-Lipschitz slopes is closed for
every `L`, and `ℓ_{a q + b q'}` is `(|a| L + |b| L')`-Lipschitz when `ℓ_q` is `L`-Lipschitz and
`ℓ_{q'}` is `L'`-Lipschitz. -/
theorem closedSlopesStep (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) : ClosedSlopesStep d p := by
  obtain ⟨G, hG, hmass, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  obtain ⟨g, -, hzero, hgradient, -⟩ :=
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid
  have hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G := (mem_ae_iff_prob_eq_one hG).mpr hmass
  filter_upwards [hGae] with ω hω L
  have hS : ∀ L, lipschitzSlopeSet ω L = slabSlopeSet (g ⟨ω, hω⟩) L := fun L =>
    lipschitzSlopeSet_eq_of_gradients G hvalid g hzero hgradient ⟨ω, hω⟩ L
  refine ⟨hS L ▸ isClosed_slabSlopeSet _ L, fun L' a b q q' hq hq' => ?_⟩
  rw [hS] at hq hq' ⊢
  exact smul_add_smul_mem_slabSlopeSet _ hq hq'

end Rigidity.Proofs.S3
