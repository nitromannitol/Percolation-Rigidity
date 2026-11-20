import Rigidity.Percolation.SlabBoundaryCandidates
import Rigidity.Percolation.SlabCube

/-!
# Prefixes of lattice-cube slabs

A coordinate prefix of a cube is disjoint from the next half-open slab.
A point on its upper coordinate face has a nearest neighbor in that slab.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- The part of a cube preceding the slab with index `k`. -/
def IntegerCube.slabPrefix {d : ℕ} (Q : IntegerCube d) (j : Fin d) (width k : ℕ) :
    Set (Vertex d) :=
  {x | x ∈ Q.vertices ∧ x j < Q.corner j + ((k * width : ℕ) : ℤ)}

/-- A slab prefix is finite. -/
theorem IntegerCube.finite_slabPrefix {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width k : ℕ) : (Q.slabPrefix j width k).Finite :=
  Q.vertices.finite_toSet.subset fun _ hx => hx.1

/-- A slab prefix is disjoint from the next slab. -/
theorem IntegerCube.disjoint_slabPrefix_slab {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width k : ℕ) : Disjoint (Q.slabPrefix j width k) (Q.slab j width k) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact (not_lt_of_ge hy.2.1) hx.2

/-- A point immediately before a nonempty interior slab has a neighbor in it. -/
theorem IntegerCube.add_unit_mem_slab {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size)
    {x : Vertex d} (hx : x ∈ Q.vertices)
    (hface : x j + 1 = Q.corner j + ((k * width : ℕ) : ℤ)) :
    x + LatticeProb.unit j ∈ Q.slab j width k := by
  classical
  have hlt : ((k * width : ℕ) : ℤ) < (Q.size : ℤ) := by exact_mod_cast hsize
  have hwidth' : (0 : ℤ) < (width : ℤ) := by exact_mod_cast hwidth
  have hyj : (x + LatticeProb.unit j) j = Q.corner j + ((k * width : ℕ) : ℤ) := by
    simpa [LatticeProb.unit] using hface
  have hy : x + LatticeProb.unit j ∈ Q.vertices := by
    rw [Q.mem_vertices]
    intro i
    have hi := (Q.mem_vertices x).mp hx i
    by_cases hij : i = j
    · subst i
      rw [hyj]
      constructor <;> omega
    · simpa [LatticeProb.unit, hij] using hi
  refine ⟨hy, by rw [hyj], ?_⟩
  rw [hyj]
  push_cast
  nlinarith

/-- A past component reaching the upper prefix face has a candidate bond into
the next slab, without exposing that bond. -/
theorem IntegerCube.slabBoundaryReachable_of_reachable_prefix_face {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) {width k : ℕ}
    (hwidth : 0 < width) (hsize : k * width < Q.size)
    {ω : Configuration d} {z x : Vertex d} (hx : x ∈ Q.slabPrefix j width k)
    (hface : x j + 1 = Q.corner j + ((k * width : ℕ) : ℤ))
    (hzx : (openIn ω (Q.slabPrefix j width k)).Reachable z x) :
    slabBoundaryReachable (Q.slabPrefix j width k) (Q.slab j width k) z ω := by
  refine ⟨x, hx, x + LatticeProb.unit j, Q.add_unit_mem_slab j hwidth hsize hx.1 hface,
    ⟨j, Or.inl rfl⟩, hzx⟩

end Rigidity.Percolation
