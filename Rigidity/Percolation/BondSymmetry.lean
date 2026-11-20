import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Lattice symmetries of Bernoulli bonds

A distance-preserving equivalence of lattice vertices permutes the genuine
unordered bonds. Its induced coordinate permutation preserves the Bernoulli
bond law.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory

/-- A distance-preserving vertex equivalence carries bonds to bonds. -/
def mapLatticeBond {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    (e : Bond d) : Bond d :=
  ⟨e.val.map f, by
    obtain ⟨x, y, hxy, hdist⟩ := e.property
    exact ⟨f x, f y, by rw [hxy, Sym2.map_mk], (hf x y).trans hdist⟩⟩

/-- The inverse of a distance-preserving equivalence also preserves distance. -/
theorem latticeL1Dist_symm {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) (x y : Vertex d) :
    latticeL1Dist (f.symm x) (f.symm y) = latticeL1Dist x y := by
  simpa only [Equiv.apply_symm_apply] using (hf (f.symm x) (f.symm y)).symm

/-- A distance-preserving vertex equivalence induces an equivalence on bonds. -/
def latticeBondEquiv {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y) : Bond d ≃ Bond d where
  toFun := mapLatticeBond f hf
  invFun := mapLatticeBond f.symm (latticeL1Dist_symm f hf)
  left_inv e := by
    apply Subtype.ext
    obtain ⟨x, y, hxy, _⟩ := e.property
    simp only [mapLatticeBond, hxy, Sym2.map_mk, Equiv.symm_apply_apply]
  right_inv e := by
    apply Subtype.ext
    obtain ⟨x, y, hxy, _⟩ := e.property
    simp only [mapLatticeBond, hxy, Sym2.map_mk, Equiv.apply_symm_apply]

/-- Under the induced bond equivalence, the bond joining adjacent vertices
has the transformed endpoints. -/
theorem latticeBondEquiv_bondOfAdjacent {d : ℕ} (f : Vertex d ≃ Vertex d)
    (hf : ∀ x y, latticeL1Dist (f x) (f y) = latticeL1Dist x y)
    {x y : Vertex d} (hxy : (nearestNeighborGraph d).Adj x y) :
    latticeBondEquiv f hf (bondOfAdjacent hxy) =
      bondOfAdjacent (lattice_adj_iff_l1Dist.mpr ((hf x y).trans
        (lattice_adj_iff_l1Dist.mp hxy))) := by
  apply Subtype.ext
  change Sym2.map f s(x, y) = s(f x, f y)
  exact Sym2.map_mk f x y

/-- The bond law is invariant under every coordinate permutation of its bonds. -/
theorem latticeBondLaw_map_piCongrLeft {d : ℕ} (p : unitInterval) (e : Bond d ≃ Bond d) :
    (latticeBondLaw d p).map (MeasurableEquiv.piCongrLeft (fun _ : Bond d => Bool) e) =
      latticeBondLaw d p := by
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Bond d => bernoulliMeasure true false p) e

end Rigidity.Percolation
