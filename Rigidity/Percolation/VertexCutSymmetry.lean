import Rigidity.Percolation.BondMarkSymmetry
import Rigidity.Percolation.ConditionalFaceSeedInside

/-!
# Symmetry of lattice boundary cuts

A distance-preserving vertex equivalence carries the boundary bonds of a
finite set exactly onto the boundary bonds of its image.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- A cut bond joins a vertex of the finite set to a neighbor outside it. -/
theorem mem_vertexCutBonds_iff {d : ℕ} (R : Finset (Vertex d)) (e : Bond d) :
    e ∈ vertexCutBonds R ↔ ∃ x ∈ R, ∃ y ∉ R,
      ∃ hxy : (nearestNeighborGraph d).Adj x y, e = bondOfAdjacent hxy := by
  classical
  constructor
  · intro he
    obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp he
    unfold regionOutgoingBonds at he
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp he
    simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hy
    have hynot : y.val ∉ R := hy
    exact ⟨x, hx, y.val, hynot, (SimpleGraph.mem_neighborFinset _ _ _).mp y.property, heq.symm⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact bondOfAdjacent_mem_vertexCutBonds R hx hy hxy

/-- A lattice symmetry preserves and reflects nearest-neighbor adjacency. -/
theorem nearestNeighborGraph_adj_latticeEquiv_iff {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (x y : Vertex d) :
    (nearestNeighborGraph d).Adj (f x) (f y) ↔ (nearestNeighborGraph d).Adj x y := by
  rw [lattice_adj_iff_l1Dist, lattice_adj_iff_l1Dist, hf]

/-- The inverse induced bond equivalence is induced by the inverse vertex map. -/
theorem latticeBondEquiv_symm {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) :
    (latticeBondEquiv f hf).symm = latticeBondEquiv f.symm (latticeL1Dist_symm f hf) := by
  apply Equiv.ext
  intro e
  rfl

/-- Mapping the endpoints of a cut bond gives a cut bond of the image set. -/
theorem latticeBondEquiv_mem_vertexCutBonds {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (R : Finset (Vertex d)) {e : Bond d} (he : e ∈ vertexCutBonds R) :
    latticeBondEquiv f hf e ∈ vertexCutBonds (R.image f) := by
  classical
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := (mem_vertexCutBonds_iff R e).mp he
  have hynot : f y ∉ R.image f := by
    intro h
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp h
    exact hy (f.injective hzy ▸ hz)
  apply (mem_vertexCutBonds_iff (R.image f) _).mpr
  refine ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, f y, hynot,
    (nearestNeighborGraph_adj_latticeEquiv_iff f hf x y).mpr hxy, ?_⟩
  exact latticeBondEquiv_bondOfAdjacent f hf hxy

/-- A lattice symmetry maps the complete vertex cut onto the image cut. -/
theorem image_vertexCutBonds_latticeEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (R : Finset (Vertex d)) :
    (vertexCutBonds R).image (latticeBondEquiv f hf) = vertexCutBonds (R.image f) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact latticeBondEquiv_mem_vertexCutBonds f hf R ha
  · intro he
    let a := (latticeBondEquiv f hf).symm e
    have ha := latticeBondEquiv_mem_vertexCutBonds f.symm (latticeL1Dist_symm f hf)
      (R.image f) he
    rw [← latticeBondEquiv_symm f hf] at ha
    have hR : (R.image f).image f.symm = R := by
      rw [Finset.image_image]
      simp only [Function.comp_def, Equiv.symm_apply_apply, Finset.image_id']
    rw [hR] at ha
    exact Finset.mem_image.mpr ⟨a, ha, (latticeBondEquiv f hf).apply_symm_apply e⟩

/-- A bond is internal to a region exactly when its image is internal to the
image region. -/
theorem latticeBondEquiv_mem_localBonds_iff {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (D : Set (Vertex d)) (e : Bond d) :
    latticeBondEquiv f hf e ∈ localBonds (f '' D) ↔ e ∈ localBonds D := by
  change (∀ y ∈ Sym2.map f e.val, y ∈ f '' D) ↔ ∀ x ∈ e.val, x ∈ D
  constructor
  · intro h x hx
    have hfx := h (f x) (Sym2.mem_map.mpr ⟨x, hx, rfl⟩)
    obtain ⟨z, hz, heq⟩ := hfx
    exact f.injective heq ▸ hz
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hy
    exact ⟨x, h x hx, rfl⟩

/-- A lattice symmetry also maps the cut restricted to an ambient region. -/
theorem image_vertexCutBondsIn_latticeEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (R : Finset (Vertex d)) (D : Set (Vertex d)) :
    (vertexCutBondsIn R D).image (latticeBondEquiv f hf) =
      vertexCutBondsIn (R.image f) (f '' D) := by
  classical
  ext e
  obtain ⟨a, rfl⟩ := (latticeBondEquiv f hf).surjective e
  have hcut : latticeBondEquiv f hf a ∈ vertexCutBonds (R.image f) ↔
      a ∈ vertexCutBonds R := by
    have h := congrArg (fun s : Finset (Bond d) => latticeBondEquiv f hf a ∈ s)
      (image_vertexCutBonds_latticeEquiv f hf R)
    apply Iff.of_eq
    simpa only [Finset.mem_image, (latticeBondEquiv f hf).injective.eq_iff,
      exists_eq_right] using h.symm
  simp only [vertexCutBondsIn, Finset.mem_image, (latticeBondEquiv f hf).injective.eq_iff,
    exists_eq_right, Finset.mem_filter, hcut, latticeBondEquiv_mem_localBonds_iff]

end Rigidity.Percolation
