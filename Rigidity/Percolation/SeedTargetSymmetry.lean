import Rigidity.Percolation.SeedSymmetry

/-!
# Symmetries of seed target families

The event that a face vertex is joined to a fully open seed transforms
covariantly when the face, seed family, pad, and outward step are moved by a
lattice symmetry.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- Face vertices joined by an open edge to a fully open member of a seed
family contained in the prescribed pad. -/
noncomputable def seedFamilyTargets {d : ℕ} {ι : Type*} (face : Finset (Vertex d))
    (seeds : ι → Set (Vertex d)) (pad : Set (Vertex d)) (step : Vertex d → Vertex d)
    (ω : Configuration d) : Finset (Vertex d) := by
  classical
  exact face.filter fun x => ∃ a, seeds a ⊆ pad ∧ ω ∈ fullyOpenRegion (seeds a) ∧
    step x ∈ seeds a ∧ (openGraph ω).Adj x (step x)

/-- Seed-family targets transform with their face and seed regions. -/
theorem seedFamilyTargets_latticeEquiv {d : ℕ} {ι : Type*} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (face : Finset (Vertex d)) (seeds : ι → Set (Vertex d)) (pad : Set (Vertex d))
    (step : Vertex d → Vertex d) (ω : Configuration d) :
    seedFamilyTargets (face.image f) (fun a => f '' seeds a) (f '' pad)
      (fun x => f (step (f.symm x))) (latticeConfigurationEquiv f hf ω) =
      (seedFamilyTargets face seeds pad step ω).image f := by
  classical
  ext x
  obtain ⟨x, rfl⟩ := f.surjective x
  simp only [seedFamilyTargets, Finset.mem_filter, Finset.mem_image,
    f.injective.eq_iff, exists_eq_right, Equiv.symm_apply_apply,
    Set.image_subset_image_iff f.injective, fullyOpenRegion_latticeEquiv_iff,
    f.injective.mem_set_image, openGraph_adj_latticeConfigurationEquiv_iff]

/-- Moving boundary bonds and thresholds together transports the event that
all boundary marks exceed their thresholds. -/
theorem bondMarksAbove_latticeEquiv_iff {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (F : Finset (Bond d)) (β : Bond d → unitInterval) (ω : BondMarks d) :
    latticeBondMarkEquiv f hf ω ∈ bondMarksAbove (F.image (latticeBondEquiv f hf))
      (fun e => β ((latticeBondEquiv f hf).symm e)) ↔ ω ∈ bondMarksAbove F β := by
  classical
  change (∀ e ∈ F.image (latticeBondEquiv f hf),
    β ((latticeBondEquiv f hf).symm e) < latticeBondMarkEquiv f hf ω e) ↔ _
  constructor
  · intro h e he
    have h' := h (latticeBondEquiv f hf e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    simpa only [Equiv.symm_apply_apply, latticeBondMarkEquiv_apply_bond] using h'
  · intro h e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    simpa only [Equiv.symm_apply_apply, latticeBondMarkEquiv_apply_bond] using h a ha

end Rigidity.Percolation
