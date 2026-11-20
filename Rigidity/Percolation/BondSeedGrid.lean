import Rigidity.Percolation.BondSeedRectangles

/-!
# Grid cells for bond seed trials

A regular partition of the lattice provides disjoint finite regions for seed
trials. The number of cells met by a finite vertex set is bounded below by its
size divided by the maximal cell size.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The index of the half-open grid cell containing a vertex. -/
def seedGridIndex {d : ℕ} (k : ℕ) (x : Vertex d) : Vertex d :=
  fun i => x i / (k : ℤ)

/-- The vertices of a grid cell of side length `k`. -/
def seedGridCell {d : ℕ} (k : ℕ) (a : Vertex d) : Set (Vertex d) :=
  {x | seedGridIndex k x = a}

/-- A grid cell is contained in the corresponding integer rectangle. -/
theorem seedGridCell_subset_rectangle {d k : ℕ} (hk : 0 < k) (a : Vertex d) :
    seedGridCell k a ⊆ latticeRectangle (fun i => (k : ℤ) * a i)
      (fun i => (k : ℤ) * a i + k) := by
  intro x hx i
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have heq : ∀ i, x i / (k : ℤ) = a i := congrFun hx
  constructor
  · simpa only [heq i] using (Int.mul_ediv_self_le (x := x i) (ne_of_gt hk'))
  · simpa only [heq i] using (Int.lt_mul_ediv_self_add (x := x i) hk')

/-- Every positive-width grid cell is finite. -/
theorem finite_seedGridCell {d k : ℕ} (hk : 0 < k) (a : Vertex d) :
    (seedGridCell k a).Finite :=
  (finite_latticeRectangle _ _).subset (seedGridCell_subset_rectangle hk a)

/-- A positive-width grid cell contains at most `k ^ d` vertices. -/
theorem card_seedGridCell_le {d k : ℕ} (hk : 0 < k) (a : Vertex d) :
    (finite_seedGridCell hk a).toFinset.card ≤ k ^ d := by
  have hcard := card_latticeRectangle_le (fun i => (k : ℤ) * a i)
    (fun i => (k : ℤ) * a i + k) k (by
      intro i
      simp only [add_sub_cancel_left, Int.toNat_natCast, le_refl])
  apply le_trans (Finset.card_le_card ?_) hcard
  intro x hx
  simpa only [Set.Finite.mem_toFinset] using
    (seedGridCell_subset_rectangle hk a (by simpa only [Set.Finite.mem_toFinset] using hx))

/-- Distinct cells of the grid have no vertex in common. -/
theorem disjoint_seedGridCell {d k : ℕ} {a b : Vertex d} (hab : a ≠ b) :
    Disjoint (seedGridCell k a) (seedGridCell k b) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hab (hx.symm.trans hy)

/-- A finite set meeting a grid cell meets it in at most `k ^ d` vertices. -/
theorem card_seedGrid_fiber_le {d k : ℕ} (hk : 0 < k) (s : Finset (Vertex d))
    (a : Vertex d) : (s.filter (fun x => seedGridIndex k x = a)).card ≤ k ^ d := by
  classical
  apply le_trans (Finset.card_le_card ?_) (card_seedGridCell_le hk a)
  intro x hx
  simpa only [Set.Finite.mem_toFinset, seedGridCell, Set.mem_setOf_eq] using
    (Finset.mem_filter.mp hx).2

/-- A set of boundary contacts meets at least its cardinality divided by the
maximum cell size many disjoint grid cells. -/
theorem card_le_card_seedGridIndex_mul {d k : ℕ} (hk : 0 < k)
    (s : Finset (Vertex d)) :
    s.card ≤ (s.image (seedGridIndex k)).card * k ^ d := by
  classical
  rw [Finset.card_eq_sum_card_image (seedGridIndex k) s]
  calc
    (∑ a ∈ s.image (seedGridIndex k),
      (s.filter (fun x => seedGridIndex k x = a)).card) ≤
        ∑ _a ∈ s.image (seedGridIndex k), k ^ d :=
      Finset.sum_le_sum (fun a _ => card_seedGrid_fiber_le hk s a)
    _ = (s.image (seedGridIndex k)).card * k ^ d := by simp

end Rigidity.Percolation
