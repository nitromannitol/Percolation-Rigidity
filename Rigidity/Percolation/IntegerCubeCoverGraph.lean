import Rigidity.Percolation.IntegerCubeOverlap

/-!
# Connectivity of lattice cube covers

The lattice points of a cube form a connected graph when points at coordinate
distance at most one are adjacent.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The graph joining distinct points at coordinate distance at most one. -/
def IntegerCube.neighborGraph {d : ℕ} (Q : IntegerCube d) :
    SimpleGraph {x : Vertex d // x ∈ Q.vertices} where
  Adj x y := x ≠ y ∧ ∀ i, |x.val i - y.val i| ≤ 1
  symm := by
    constructor
    intro x y h
    refine ⟨Ne.symm h.1, ?_⟩
    intro i
    simpa only [abs_sub_comm] using h.2 i
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- Every point of a nonempty-side cube is joined to its lower corner. -/
theorem IntegerCube.neighborGraph_reachable_corner {d : ℕ} (Q : IntegerCube d)
    (hsize : 0 < Q.size) (x : {x : Vertex d // x ∈ Q.vertices}) :
    Q.neighborGraph.Reachable x ⟨Q.corner, by
      rw [IntegerCube.mem_vertices]
      intro i
      constructor
      · exact le_rfl
      · have hs : (0 : ℤ) < Q.size := by exact_mod_cast hsize
        exact lt_add_of_pos_right _ hs⟩ := by
  classical
  let corner : {x : Vertex d // x ∈ Q.vertices} := ⟨Q.corner, by
    rw [IntegerCube.mem_vertices]
    intro i
    constructor
    · exact le_rfl
    · have hs : (0 : ℤ) < Q.size := by exact_mod_cast hsize
      exact lt_add_of_pos_right _ hs⟩
  change Q.neighborGraph.Reachable x corner
  suffices H : ∀ m : ℕ, ∀ x : {x : Vertex d // x ∈ Q.vertices},
      (∑ i, (x.val i - Q.corner i).toNat) = m →
      Q.neighborGraph.Reachable x corner from H _ x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hm
    by_cases hzero : x.val = Q.corner
    · have : x = corner := Subtype.ext hzero
      subst x
      exact SimpleGraph.Reachable.refl corner
    · obtain ⟨i, hi⟩ : ∃ i, Q.corner i < x.val i := by
        by_contra h
        push Not at h
        apply hzero
        funext i
        have hx := (Q.mem_vertices x.val).mp x.property i
        exact le_antisymm (h i) hx.1
      let y : Vertex d := Function.update x.val i (x.val i - 1)
      have hyi : y i = x.val i - 1 := by simp [y]
      have hyj : ∀ j, j ≠ i → y j = x.val j := by
        intro j hj
        simp [y, hj]
      have hy : y ∈ Q.vertices := by
        rw [IntegerCube.mem_vertices]
        intro j
        have hx := (Q.mem_vertices x.val).mp x.property j
        by_cases hj : j = i
        · subst j
          rw [hyi]
          omega
        · rw [hyj j hj]
          exact hx
      let y' : {x : Vertex d // x ∈ Q.vertices} := ⟨y, hy⟩
      have hne : x ≠ y' := by
        intro h
        have h' := congrArg (fun z : {x : Vertex d // x ∈ Q.vertices} => z.val i) h
        change x.val i = y i at h'
        rw [hyi] at h'
        omega
      have hadj : Q.neighborGraph.Adj x y' := by
        refine ⟨hne, ?_⟩
        intro j
        change |x.val j - y j| ≤ 1
        by_cases hj : j = i
        · subst j
          rw [hyi]
          simp only [sub_sub_cancel]
          norm_num
        · rw [hyj j hj, sub_self, abs_zero]
          norm_num
      have hlt : ∑ j, (y'.val j - Q.corner j).toNat < m := by
        rw [← hm]
        apply Finset.sum_lt_sum
        · intro j _
          change (y j - Q.corner j).toNat ≤ (x.val j - Q.corner j).toNat
          by_cases hj : j = i
          · subst j
            rw [hyi]
            apply Int.toNat_le_toNat
            omega
          · rw [hyj j hj]
        · refine ⟨i, Finset.mem_univ _, ?_⟩
          change (y i - Q.corner i).toNat < (x.val i - Q.corner i).toNat
          rw [hyi]
          omega
      exact hadj.reachable.trans (ih _ hlt y' rfl)

/-- Any two points in a nonempty-side cube are connected in its neighbor graph. -/
theorem IntegerCube.neighborGraph_reachable {d : ℕ} (Q : IntegerCube d)
    (hsize : 0 < Q.size) (x y : {x : Vertex d // x ∈ Q.vertices}) :
    Q.neighborGraph.Reachable x y :=
  (Q.neighborGraph_reachable_corner hsize x).trans
    (Q.neighborGraph_reachable_corner hsize y).symm

end Rigidity.Percolation
