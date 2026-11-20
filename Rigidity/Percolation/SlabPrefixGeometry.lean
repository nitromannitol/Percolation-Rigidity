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

namespace Rigidity.Percolation

open LatticeProb.Percolation Rigidity.External

/-- A nearest-neighbor step changes any coordinate by at most one. -/
theorem coordinate_sub_le_one_of_adj {d : ℕ} {x y : Vertex d}
    (hxy : (nearestNeighborGraph d).Adj x y) (j : Fin d) : x j - y j ≤ 1 := by
  have hsum := (lattice_adj_iff_l1Dist.mp hxy)
  have hle : |x j - y j| ≤ latticeL1Dist x y := by
    exact Finset.single_le_sum (fun i _ => abs_nonneg (x i - y i)) (Finset.mem_univ j)
  rw [hsum] at hle
  exact (le_abs_self _).trans hle

/-- A path in the cube from a prefix to its complement reaches the last
prefix face using only bonds internal to the prefix. -/
theorem IntegerCube.exists_reachable_prefix_face {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (width k : ℕ) {ω : Configuration d} {z w : Vertex d}
    (hz : z ∈ Q.slabPrefix j width k) (hw : w ∉ Q.slabPrefix j width k)
    (hzw : (openIn ω Q.vertices).Reachable z w) :
    ∃ x ∈ Q.slabPrefix j width k,
      x j + 1 = Q.corner j + ((k * width : ℕ) : ℤ) ∧
        (openIn ω (Q.slabPrefix j width k)).Reachable z x := by
  let P := Q.slabPrefix j width k
  let C : Set (Vertex d) := {x | x ∈ P ∧ (openIn ω P).Reachable z x}
  have hzC : z ∈ C := ⟨hz, SimpleGraph.Reachable.refl z⟩
  have hwC : w ∉ C := fun h => hw h.1
  obtain ⟨walk⟩ := hzw
  obtain ⟨edge, _, hxC, hyC⟩ := walk.exists_boundary_dart C hzC hwC
  have hadj := edge.adj
  have hyP : edge.snd ∉ P := by
    intro hyP
    apply hyC
    exact ⟨hyP, hxC.2.trans (SimpleGraph.Adj.reachable ⟨hadj.1, hxC.1, hyP⟩)⟩
  have hyQ : edge.snd ∈ Q.vertices := hadj.2.2
  have hybound : Q.corner j + ((k * width : ℕ) : ℤ) ≤ edge.snd j := by
    by_contra h
    exact hyP ⟨hyQ, lt_of_not_ge h⟩
  have hstep := coordinate_sub_le_one_of_adj (openGraph_adj_iff ω _ _ |>.mp hadj.1).1.symm j
  refine ⟨edge.fst, hxC.1, ?_, hxC.2⟩
  exact by have hxbound := hxC.1.2; omega

/-- A path that leaves a prefix produces a candidate for the next slab. -/
theorem IntegerCube.slabBoundaryReachable_of_reachable_outside_prefix {d : ℕ}
    (Q : IntegerCube d) (j : Fin d) {width k : ℕ}
    (hwidth : 0 < width) (hsize : k * width < Q.size)
    {ω : Configuration d} {z w : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (hw : w ∉ Q.slabPrefix j width k)
    (hzw : (openIn ω Q.vertices).Reachable z w) :
    slabBoundaryReachable (Q.slabPrefix j width k) (Q.slab j width k) z ω := by
  obtain ⟨x, hx, hface, hzx⟩ := Q.exists_reachable_prefix_face j width k hz hw hzw
  exact Q.slabBoundaryReachable_of_reachable_prefix_face j hwidth hsize hx hface hzx

/-- An earlier prefix is contained in every later prefix. -/
theorem IntegerCube.slabPrefix_mono {d : ℕ} (Q : IntegerCube d) (j : Fin d)
    (width : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    Q.slabPrefix j width k ⊆ Q.slabPrefix j width l := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have h : ((k * width : ℕ) : ℤ) ≤ ((l * width : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_le_mul_right width hkl
  exact lt_of_lt_of_le hx.2 (add_le_add le_rfl h)

/-- A component reaching the next slab also has a candidate at the previous
slab, provided its root already belongs to the earlier prefix. -/
theorem IntegerCube.slabBoundaryReachable_of_next {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) {width k : ℕ} (hwidth : 0 < width) (hsize : k * width < Q.size)
    {ω : Configuration d} {z : Vertex d} (hz : z ∈ Q.slabPrefix j width k)
    (h : slabBoundaryReachable (Q.slabPrefix j width (k + 1))
      (Q.slab j width (k + 1)) z ω) :
    slabBoundaryReachable (Q.slabPrefix j width k) (Q.slab j width k) z ω := by
  obtain ⟨x, hx, y, hy, hxy, hzx⟩ := h
  have hxout : x ∉ Q.slabPrefix j width k := by
    intro hxold
    have hstep := coordinate_sub_le_one_of_adj hxy.symm j
    have hwidth' : (0 : ℤ) < (width : ℤ) := by exact_mod_cast hwidth
    have hnext := hy.2.1
    have hold := hxold.2
    push_cast at hnext hold ⊢
    nlinarith
  apply Q.slabBoundaryReachable_of_reachable_outside_prefix j hwidth hsize hz hxout
  exact reachable_openIn_mono (fun _ hx' => hx'.1) hzx

end Rigidity.Percolation
