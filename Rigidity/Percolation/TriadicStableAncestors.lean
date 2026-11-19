import Rigidity.Percolation.TriadicInfluence

/-!
# Stable ancestors of triadic cubes

A stable cube forces every child of each ancestor at least two scales above it
to be stable. This is the deterministic finiteness property used in the
construction of partitions into stable good cubes.
-/

namespace Rigidity.Percolation

/-- The ancestor obtained by repeatedly taking the parent. -/
def TriadicCube.ancestor {d : ℕ} (Q : TriadicCube d) (n : ℕ) : TriadicCube d :=
  (TriadicCube.parent^[n]) Q

/-- The zeroth ancestor is the cube itself. -/
@[simp] theorem TriadicCube.ancestor_zero {d : ℕ} (Q : TriadicCube d) :
    Q.ancestor 0 = Q := rfl

/-- The next ancestor is the parent of the preceding ancestor. -/
@[simp] theorem TriadicCube.ancestor_succ {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    Q.ancestor (n + 1) = (Q.ancestor n).parent := by
  simp only [ancestor, Function.iterate_succ_apply']

/-- Each ancestor has the expected scale. -/
theorem TriadicCube.scale_ancestor {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    (Q.ancestor n).scale = Q.scale + n := by
  induction n with
  | zero => simp only [ancestor_zero, Nat.add_zero]
  | succ n ih => simp only [ancestor_succ, parent, ih, Nat.add_succ]

/-- Every cube is contained in each of its ancestors. -/
theorem TriadicCube.vertices_subset_ancestor {d : ℕ} (Q : TriadicCube d) (n : ℕ) :
    Q.vertices ⊆ (Q.ancestor n).vertices := by
  induction n with
  | zero => simp only [ancestor_zero, Set.Subset.rfl]
  | succ n ih =>
    rw [ancestor_succ]
    exact ih.trans (vertices_subset_parent _)

/-- An intersecting cube of larger scale is an ancestor. -/
theorem TriadicCube.eq_ancestor_of_mem {d : ℕ} {Q R : TriadicCube d}
    {x : LatticeProb.Percolation.Vertex d} (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices)
    (hscale : Q.scale ≤ R.scale) : R = Q.ancestor (R.scale - Q.scale) := by
  apply eq_of_mem_of_scale_eq _ hxR (Q.vertices_subset_ancestor _ hxQ)
  rw [scale_ancestor]
  omega

/-- A stable cube has stable ancestors. -/
theorem TriadicCube.ancestor_mem_stableGood {d : ℕ} {G : Set (TriadicCube d)}
    {Q : TriadicCube d} (hQ : Q ∈ stableGood G) (n : ℕ) :
    Q.ancestor n ∈ stableGood G := by
  induction n with
  | zero => simpa only [ancestor_zero] using hQ
  | succ n ih => simpa only [ancestor_succ] using parent_mem_stableGood ih

/-- Every child of the grandparent of a stable cube is stable. -/
theorem TriadicCube.child_grandparent_mem_stableGood {d : ℕ} {G : Set (TriadicCube d)}
    {Q : TriadicCube d} (hQ : Q ∈ stableGood G) (digits : Fin d → Fin 3) :
    Q.parent.parent.child digits ∈ stableGood G := by
  apply influence_subset_stableGood hQ
  apply Relation.ReflTransGen.single
  constructor
  · simp only [child, parent]
    omega
  · refine ⟨(fun i => Q.side * Q.index i), Q.center_mem,
      (fun i => Q.side * Q.index i), ?_, ?_⟩
    · rw [child_parent _ _ (by simp [parent])]
      exact Q.parent.vertices_subset_parent (Q.vertices_subset_parent Q.center_mem)
    · intro i
      simp only [sub_self, abs_zero]
      norm_num

/-- A stable cube forces the children of all its ancestors at least two scales up to be stable. -/
theorem TriadicCube.child_ancestor_mem_stableGood {d : ℕ} {G : Set (TriadicCube d)}
    {Q : TriadicCube d} (hQ : Q ∈ stableGood G) (n : ℕ) (digits : Fin d → Fin 3) :
    (Q.ancestor (n + 2)).child digits ∈ stableGood G := by
  have h := child_grandparent_mem_stableGood (ancestor_mem_stableGood hQ n) digits
  simpa only [ancestor_succ, Nat.add_assoc] using h

/-- Cubes with a nonstable child which intersect a stable cube have bounded scale. -/
theorem TriadicCube.scale_le_of_not_child_mem_stableGood {d : ℕ}
    {G : Set (TriadicCube d)} {Q R : TriadicCube d}
    {x : LatticeProb.Percolation.Vertex d} (hQ : Q ∈ stableGood G)
    (hxQ : x ∈ Q.vertices) (hxR : x ∈ R.vertices) (digits : Fin d → Fin 3)
    (hbad : R.child digits ∉ stableGood G) : R.scale ≤ Q.scale + 1 := by
  by_contra h
  have hscale : Q.scale ≤ R.scale := by omega
  have heq := eq_ancestor_of_mem hxQ hxR hscale
  have hn : R.scale - Q.scale = (R.scale - Q.scale - 2) + 2 := by omega
  rw [hn] at heq
  apply hbad
  rw [heq]
  exact child_ancestor_mem_stableGood hQ _ digits

end Rigidity.Percolation
