import Rigidity.Percolation.VertexCutSymmetry

/-!
# Symmetries of fully open seeds

Lattice symmetries transport fully open regions and preserve their
conditional probabilities under the uniform-mark coupling.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

/-- A lattice symmetry transports full openness of a vertex region. -/
theorem fullyOpenRegion_latticeEquiv_iff {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (S : Set (Vertex d)) (ω : Configuration d) :
    latticeConfigurationEquiv f hf ω ∈ fullyOpenRegion (f '' S) ↔ ω ∈ fullyOpenRegion S := by
  constructor
  · intro h e he
    have he' := (latticeBondEquiv_mem_localBonds_iff f hf S e).mpr he
    have hopen := h (latticeBondEquiv f hf e) he'
    rwa [latticeConfigurationEquiv_apply_bond] at hopen
  · intro h e he
    obtain ⟨a, rfl⟩ := (latticeBondEquiv f hf).surjective e
    rw [latticeConfigurationEquiv_apply_bond]
    exact h a ((latticeBondEquiv_mem_localBonds_iff f hf S a).mp he)

/-- Applying the same lattice symmetry to two measurable mark events
preserves their conditional probability. -/
theorem bondMarkLaw_real_preimage_conditional {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (A B : Set (BondMarks d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (bondMarkLaw d).real ((latticeBondMarkEquiv f hf) ⁻¹' A ∩
        (latticeBondMarkEquiv f hf) ⁻¹' B) /
      (bondMarkLaw d).real ((latticeBondMarkEquiv f hf) ⁻¹' A) =
    (bondMarkLaw d).real (A ∩ B) / (bondMarkLaw d).real A := by
  have hmap := bondMarkLaw_map_latticeBondMarkEquiv f hf
  have h₁ : (bondMarkLaw d).real ((latticeBondMarkEquiv f hf) ⁻¹' (A ∩ B)) =
      (bondMarkLaw d).real (A ∩ B) := by
    rw [measureReal_def, ← Measure.map_apply (latticeBondMarkEquiv f hf).measurable (hA.inter hB), hmap]
    rfl
  have h₂ : (bondMarkLaw d).real ((latticeBondMarkEquiv f hf) ⁻¹' A) =
      (bondMarkLaw d).real A := by
    rw [measureReal_def, ← Measure.map_apply (latticeBondMarkEquiv f hf).measurable hA, hmap]
    rfl
  rw [← Set.preimage_inter, h₁, h₂]

end Rigidity.Percolation
