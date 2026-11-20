import Rigidity.Percolation.SlabCrossings
import Rigidity.Percolation.IntegerCube

/-!
# Disjoint slabs in a lattice cube

Slicing a lattice cube into disjoint strips transverse to a crossing direction
turns a uniform lower bound on strip crossings into a geometric upper bound
for failure of a cube crossing.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The portion of a cube in a half-open slab of the given width. -/
def IntegerCube.slab {d : ℕ} (Q : IntegerCube d) (j : Fin d) (width k : ℕ) :
    Set (Vertex d) :=
  {x | x ∈ Q.vertices ∧ Q.corner j + ((k * width : ℕ) : ℤ) ≤ x j ∧
    x j < Q.corner j + (((k + 1) * width : ℕ) : ℤ)}

/-- Every slab of a finite cube is finite. -/
theorem IntegerCube.finite_slab {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width k : ℕ) : (Q.slab j width k).Finite :=
  Q.vertices.finite_toSet.subset fun _ hx => hx.1

/-- Slabs at distinct indices are disjoint. -/
theorem IntegerCube.disjoint_slab {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (Q.slab j width k) (Q.slab j width l) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases lt_or_gt_of_ne hkl with h | h
  · have hh : (k + 1) * width ≤ l * width := Nat.mul_le_mul_right width h
    have hh' : (((k + 1) * width : ℕ) : ℤ) ≤ ((l * width : ℕ) : ℤ) := by exact_mod_cast hh
    have hc : Q.corner j + (((k + 1) * width : ℕ) : ℤ) ≤ x j :=
      le_trans (add_le_add_right hh' (Q.corner j)) hy.2.1
    exact (not_lt_of_ge hc) hx.2.2
  · have hh : (l + 1) * width ≤ k * width := Nat.mul_le_mul_right width h
    have hh' : (((l + 1) * width : ℕ) : ℤ) ≤ ((k * width : ℕ) : ℤ) := by exact_mod_cast hh
    have hc : Q.corner j + (((l + 1) * width : ℕ) : ℤ) ≤ x j :=
      le_trans (add_le_add_right hh' (Q.corner j)) hx.2.1
    exact (not_lt_of_ge hc) hy.2.2

/-- A connection within a subregion persists inside any larger region. -/
theorem ConnectsRegions.mono {d : ℕ} {ω : Configuration d} {B C L R : Set (Vertex d)}
    (h : ConnectsRegions ω B L R) (hBC : B ⊆ C) : ConnectsRegions ω C L R := by
  obtain ⟨x, hxB, hxL, y, hyB, hyR, hxy⟩ := h
  refine ⟨x, hBC hxB, hxL, y, hBC hyB, hyR, ?_⟩
  apply hxy.mono
  intro a b hab
  exact ⟨hab.1, hBC hab.2.1, hBC hab.2.2⟩

/-- If every full slab has a uniform chance to connect two cube faces, failure
of the cube connection has geometric probability in the number of slabs. -/
theorem IntegerCube.measureReal_no_face_connection_le {d : ℕ} (Q : IntegerCube d)
    (j i : Fin d) (width : ℕ) (p : unitInterval) (δ : ℝ)
    (hprob : ∀ k : Fin (Q.size / width), δ ≤ (latticeBondLaw d p).real
      {ω | ConnectsRegions ω (Q.slab j width k) (Q.lowerFace i) (Q.upperFace i)}) :
    (latticeBondLaw d p).real {ω | ¬ ConnectsRegions ω Q.vertices
      (Q.lowerFace i) (Q.upperFace i)} ≤ (1 - δ) ^ (Q.size / width) := by
  let B : Fin (Q.size / width) → Set (Vertex d) := fun k => Q.slab j width k
  have hb := measureReal_failure_le_of_disjoint_region_connections p B
    (fun _ => (Q.lowerFace i : Set (Vertex d)))
    (fun _ => (Q.upperFace i : Set (Vertex d)))
    {ω | ConnectsRegions ω Q.vertices (Q.lowerFace i) (Q.upperFace i)}
    (fun k => Q.finite_slab j width k)
    (fun k l hkl => Q.disjoint_slab j width (fun h => hkl (Fin.ext h)))
    (fun _ _ h => h.mono fun _ hx => hx.1) δ hprob Finset.univ
  simpa only [Set.compl_setOf, Finset.card_univ, Fintype.card_fin] using hb

end Rigidity.Percolation
