import Rigidity.Percolation.BondSymmetry
import Rigidity.Percolation.BondContactHarris

/-!
# Symmetries of reached boundary contacts

Lattice symmetries transport open paths and preserve the number of vertices
of a finite face reached from a finite seed.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- A vertex symmetry acts on configurations by permuting their bond coordinates. -/
def latticeConfigurationEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) :
    Configuration d ≃ᵐ Configuration d :=
  MeasurableEquiv.piCongrLeft (fun _ : Bond d => Bool) (latticeBondEquiv f hf)

/-- Moving a bond together with the configuration preserves its state. -/
theorem latticeConfigurationEquiv_apply_bond {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (ω : Configuration d) (e : Bond d) :
    latticeConfigurationEquiv f hf ω (latticeBondEquiv f hf e) = ω e :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Bond d => Bool)
    (latticeBondEquiv f hf) ω e

/-- Open adjacency is preserved by a lattice symmetry. -/
theorem openGraph_adj_latticeConfigurationEquiv_iff {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (ω : Configuration d) (x y : Vertex d) :
    (openGraph (latticeConfigurationEquiv f hf ω)).Adj (f x) (f y) ↔
      (openGraph ω).Adj x y := by
  constructor
  · rintro ⟨h, hopen⟩
    have hxy : (nearestNeighborGraph d).Adj x y := lattice_adj_iff_l1Dist.mpr
      ((hf x y).symm.trans (lattice_adj_iff_l1Dist.mp h))
    refine ⟨hxy, ?_⟩
    rw [← latticeBondEquiv_bondOfAdjacent f hf hxy,
      latticeConfigurationEquiv_apply_bond] at hopen
    exact hopen
  · rintro ⟨h, hopen⟩
    refine ⟨lattice_adj_iff_l1Dist.mpr ((hf x y).trans (lattice_adj_iff_l1Dist.mp h)), ?_⟩
    rw [← latticeBondEquiv_bondOfAdjacent f hf h, latticeConfigurationEquiv_apply_bond]
    exact hopen

/-- A lattice symmetry is an isomorphism of the open graphs restricted to
corresponding vertex regions. -/
def openInLatticeEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (ω : Configuration d) (B : Set (Vertex d)) :
    openIn ω B ≃g openIn (latticeConfigurationEquiv f hf ω) (f '' B) where
  toEquiv := f
  map_rel_iff' := by
    intro x y
    change ((openGraph (latticeConfigurationEquiv f hf ω)).Adj (f x) (f y) ∧
      f x ∈ f '' B ∧ f y ∈ f '' B) ↔
        ((openGraph ω).Adj x y ∧ x ∈ B ∧ y ∈ B)
    rw [openGraph_adj_latticeConfigurationEquiv_iff]
    simp only [Equiv.injective f |>.mem_set_image]

/-- The contact set transforms by applying the symmetry to its vertices. -/
theorem seedReachableContacts_latticeEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (ω : Configuration d) (B : Set (Vertex d)) (roots face : Finset (Vertex d)) :
    seedReachableContacts (f '' B) (roots.image f) (face.image f)
        (latticeConfigurationEquiv f hf ω) =
      (seedReachableContacts B roots face ω).image f := by
  classical
  ext x
  obtain ⟨x, rfl⟩ := f.surjective x
  rw [mem_seedReachableContacts, Finset.mem_image]
  simp only [f.injective.eq_iff, exists_eq_right, Finset.mem_image]
  constructor
  · rintro ⟨hface, y, ⟨w, hw, hwy⟩, hyx⟩
    subst y
    apply (mem_seedReachableContacts B roots face ω x).mpr
    exact ⟨hface, w, hw, (openInLatticeEquiv f hf ω B).reachable_iff.mp hyx⟩
  · intro hx
    obtain ⟨hface, y, hy, hyx⟩ := (mem_seedReachableContacts B roots face ω x).mp hx
    exact ⟨hface, f y, ⟨y, hy, rfl⟩,
      (openInLatticeEquiv f hf ω B).reachable_iff.mpr hyx⟩

/-- A symmetry preserves the probability of a small reached-contact set when
it moves the region, seed and face together. -/
theorem measureReal_fewSeedContacts_latticeEquiv {d : ℕ} (p : unitInterval)
    (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (B : Set (Vertex d)) (roots face : Finset (Vertex d)) (m : ℕ) :
    (latticeBondLaw d p).real (fewSeedContacts (f '' B) (roots.image f) (face.image f) m) =
      (latticeBondLaw d p).real (fewSeedContacts B roots face m) := by
  classical
  have hevent : (latticeConfigurationEquiv f hf) ⁻¹'
      fewSeedContacts (f '' B) (roots.image f) (face.image f) m =
        fewSeedContacts B roots face m := by
    ext ω
    change (seedReachableContacts (f '' B) (roots.image f) (face.image f)
      (latticeConfigurationEquiv f hf ω)).card < m ↔
        (seedReachableContacts B roots face ω).card < m
    rw [seedReachableContacts_latticeEquiv, Finset.card_image_of_injective _ f.injective]
  have hmap := latticeBondLaw_map_piCongrLeft p (latticeBondEquiv f hf)
  change (latticeBondLaw d p).map (latticeConfigurationEquiv f hf) = _ at hmap
  have h := congrArg (fun μ : Measure (Configuration d) =>
    μ (fewSeedContacts (f '' B) (roots.image f) (face.image f) m)) hmap
  rw [Measure.map_apply (latticeConfigurationEquiv f hf).measurable
    (measurableSet_fewSeedContacts _ _ _ _), hevent] at h
  exact congrArg ENNReal.toReal h.symm

end Rigidity.Percolation
