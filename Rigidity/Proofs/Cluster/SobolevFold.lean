import Rigidity.Proofs.Cluster.SobolevMeanZero

/-!
# Reflection of an integer cube into its triple and a cutoff

For an integer cube `B` with corner `c` and side `n`, the cube `B'` with corner `c - n` and side
`3n` is folded onto `B` by reflecting each coordinate across the two faces of `B`: relative to the
corner, `r ↦ -1 - r` for `r < 0`, `r ↦ r` on `[0, n)` and `r ↦ 2n - 1 - r` for `r ≥ n`. The fold
fixes `B`, maps each lattice edge of `B'` to a lattice edge of `B` or to a single vertex, and its
fibres have at most `3^d` points. The product cutoff `η(x) = ∏_i η₁(x_i - c_i)`, with `η₁` linear
from `0` at `-n` to `1` on `[0, n)` and back to `0` at `2n - 1`, equals one on `B`, lies in
`[0, 1]` on `B'`, vanishes at the vertices of `B'` having a lattice neighbour outside `B'`, and
changes by at most `1/n` along each lattice edge of `B'`.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The reflection of `[-n, 2n)` onto `[0, n)` across the two ends of `[0, n)`. -/
def foldCoord (n : ℕ) (r : ℤ) : ℤ :=
  if r < 0 then -1 - r else if r < n then r else 2 * n - 1 - r

/-- The cube with corner `c - n` and side `3n`, made of `3^d` translates of `B`. -/
def IntegerCube.triple (B : IntegerCube d) : IntegerCube d where
  corner i := B.corner i - B.size
  size := 3 * B.size

/-- The fold of a vertex of the triple cube onto the cube. -/
def IntegerCube.fold (B : IntegerCube d) (x : Vertex d) : Vertex d :=
  fun i => B.corner i + foldCoord B.size (x i - B.corner i)

theorem add_unit_apply (x : Vertex d) (j k : Fin d) :
    (x + LatticeProb.unit j) k = x k + if k = j then 1 else 0 := by
  simp [LatticeProb.unit, Pi.single_apply]

theorem IntegerCube.mem_triple_vertices (B : IntegerCube d) (x : Vertex d) :
    x ∈ B.triple.vertices ↔
      ∀ i, B.corner i - B.size ≤ x i ∧ x i < B.corner i + 2 * B.size := by
  rw [IntegerCube.mem_vertices]
  refine forall_congr' fun i => ?_
  simp only [IntegerCube.triple]
  omega

theorem IntegerCube.vertices_subset_triple (B : IntegerCube d) :
    B.vertices ⊆ B.triple.vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hx
  rw [IntegerCube.mem_triple_vertices]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  constructor <;> omega

theorem IntegerCube.fold_mem (B : IntegerCube d) {x : Vertex d} (hx : x ∈ B.triple.vertices) :
    B.fold x ∈ B.vertices := by
  rw [IntegerCube.mem_triple_vertices] at hx
  rw [IntegerCube.mem_vertices]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  simp only [IntegerCube.fold, foldCoord]
  split_ifs <;> omega

theorem IntegerCube.fold_of_mem (B : IntegerCube d) {x : Vertex d} (hx : x ∈ B.vertices) :
    B.fold x = x := by
  rw [IntegerCube.mem_vertices] at hx
  funext i
  obtain ⟨h1, h2⟩ := hx i
  simp only [IntegerCube.fold, foldCoord]
  split_ifs <;> omega

/-- The fold of the endpoint `x + e_j` of an edge of the triple cube is the fold of `x`, or a
lattice neighbour of it in direction `j`. -/
theorem IntegerCube.fold_add_unit (B : IntegerCube d) {x : Vertex d} (j : Fin d)
    (hx : x ∈ B.triple.vertices) (hxj : x + LatticeProb.unit j ∈ B.triple.vertices) :
    B.fold (x + LatticeProb.unit j) = B.fold x ∨
      B.fold (x + LatticeProb.unit j) = B.fold x + LatticeProb.unit j ∨
      B.fold x = B.fold (x + LatticeProb.unit j) + LatticeProb.unit j := by
  rw [IntegerCube.mem_triple_vertices] at hx hxj
  obtain ⟨h1, h2⟩ := hx j
  obtain ⟨h3, h4⟩ := hxj j
  rw [add_unit_apply, if_pos rfl] at h3 h4
  have hk : ∀ k, k ≠ j → B.fold (x + LatticeProb.unit j) k = B.fold x k := by
    intro k hk
    simp only [IntegerCube.fold, add_unit_apply, if_neg hk, add_zero]
  have hj : B.fold (x + LatticeProb.unit j) j = B.fold x j ∨
      B.fold (x + LatticeProb.unit j) j = B.fold x j + 1 ∨
      B.fold x j = B.fold (x + LatticeProb.unit j) j + 1 := by
    simp only [IntegerCube.fold, add_unit_apply, foldCoord]
    split_ifs <;> omega
  rcases hj with h | h | h
  · left
    funext k
    by_cases hkj : k = j
    · subst hkj
      exact h
    · exact hk k hkj
  · right
    left
    funext k
    by_cases hkj : k = j
    · subst hkj
      rw [h, add_unit_apply, if_pos rfl]
    · rw [hk k hkj, add_unit_apply, if_neg hkj, add_zero]
  · right
    right
    funext k
    by_cases hkj : k = j
    · subst hkj
      rw [h, add_unit_apply, if_pos rfl]
    · rw [add_unit_apply, if_neg hkj, add_zero, hk k hkj]

/-- The fold maps each lattice edge of the triple cube to a lattice edge of the cube or to a
single vertex. -/
theorem IntegerCube.fold_adj (B : IntegerCube d) {x y : Vertex d} (hx : x ∈ B.triple.vertices)
    (hy : y ∈ B.triple.vertices) (hxy : (nearestNeighborGraph d).Adj x y) :
    B.fold y = B.fold x ∨ (nearestNeighborGraph d).Adj (B.fold x) (B.fold y) := by
  obtain ⟨j, h | h⟩ := hxy
  · subst h
    rcases B.fold_add_unit j hx hy with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨j, Or.inl h1⟩
    · exact Or.inr ⟨j, Or.inr h1⟩
  · subst h
    rcases B.fold_add_unit j hy hx with h1 | h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr ⟨j, Or.inr h1⟩
    · exact Or.inr ⟨j, Or.inl h1⟩

/-- The fibres of the fold have at most `3^d` points. -/
theorem IntegerCube.card_fold_fiber_le (B : IntegerCube d) (w : Vertex d) :
    (B.triple.vertices.filter fun x => B.fold x = w).card ≤ 3 ^ d := by
  have hsub : (B.triple.vertices.filter fun x => B.fold x = w) ⊆
      Fintype.piFinset fun i => ({w i, 2 * B.corner i - 1 - w i,
        2 * B.corner i + 2 * B.size - 1 - w i} : Finset ℤ) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Fintype.mem_piFinset]
    intro i
    have hi := congrFun hx.2 i
    simp only [IntegerCube.fold, foldCoord] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    split_ifs at hi <;> omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ i, ({w i, 2 * B.corner i - 1 - w i, 2 * B.corner i + 2 * B.size - 1 - w i} :
        Finset ℤ).card
      ≤ 3 ^ (Finset.univ : Finset (Fin d)).card :=
        Finset.prod_le_pow_card _ _ _ fun i _ => Finset.card_le_three
    _ = 3 ^ d := by rw [Finset.card_univ, Fintype.card_fin]

/-- Summing a nonnegative function of the fold over the triple cube gives at most `3^d` times
its sum over the cube. -/
theorem IntegerCube.sum_fold_le (B : IntegerCube d) (F : Vertex d → ℝ) (hF : ∀ w, 0 ≤ F w) :
    ∑ x ∈ B.triple.vertices, F (B.fold x) ≤ 3 ^ d * ∑ w ∈ B.vertices, F w := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := B.triple.vertices) (t := B.vertices)
    (g := B.fold) (fun x hx => B.fold_mem hx), Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => ?_
  calc ∑ x ∈ B.triple.vertices with B.fold x = w, F (B.fold x)
      = ∑ x ∈ B.triple.vertices with B.fold x = w, F w :=
        Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2]
    _ = ((B.triple.vertices.filter fun x => B.fold x = w).card : ℝ) * F w := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 ^ d * F w := by
        refine mul_le_mul_of_nonneg_right ?_ (hF w)
        exact_mod_cast B.card_fold_fiber_le w

/-- The numerator of the one-dimensional cutoff: `r + n` below `0`, `n` on `[0, n)` and
`2n - 1 - r` above. -/
def cutoffNum (n : ℕ) (r : ℤ) : ℤ :=
  if r < 0 then r + n else if r < n then n else 2 * n - 1 - r

/-- The one-dimensional cutoff `cutoffNum n r / n`. -/
noncomputable def cutoffCoord (n : ℕ) (r : ℤ) : ℝ := (cutoffNum n r : ℝ) / n

/-- The product cutoff of the triple cube. -/
noncomputable def IntegerCube.cutoff (B : IntegerCube d) (x : Vertex d) : ℝ :=
  ∏ i, cutoffCoord B.size (x i - B.corner i)

theorem cutoffCoord_nonneg {n : ℕ} {r : ℤ} (h1 : -(n : ℤ) ≤ r) (h2 : r < 2 * n) :
    0 ≤ cutoffCoord n r := by
  have : 0 ≤ cutoffNum n r := by
    simp only [cutoffNum]
    split_ifs <;> omega
  exact div_nonneg (by exact_mod_cast this) (Nat.cast_nonneg n)

theorem cutoffCoord_le_one {n : ℕ} (hn : 0 < n) (r : ℤ) : cutoffCoord n r ≤ 1 := by
  have : cutoffNum n r ≤ n := by
    simp only [cutoffNum]
    split_ifs <;> omega
  rw [cutoffCoord, div_le_one (by exact_mod_cast hn)]
  exact_mod_cast this

theorem cutoffCoord_eq_one {n : ℕ} (hn : 0 < n) {r : ℤ} (h1 : 0 ≤ r) (h2 : r < n) :
    cutoffCoord n r = 1 := by
  have : cutoffNum n r = n := by
    simp only [cutoffNum]
    split_ifs <;> omega
  rw [cutoffCoord, this, Int.cast_natCast, div_self (by exact_mod_cast hn.ne')]

theorem abs_cutoffCoord_succ_sub_le (n : ℕ) (r : ℤ) :
    |cutoffCoord n (r + 1) - cutoffCoord n r| ≤ 1 / n := by
  have h : |cutoffNum n (r + 1) - cutoffNum n r| ≤ 1 := by
    simp only [cutoffNum]
    rw [abs_le]
    split_ifs <;> omega
  rw [cutoffCoord, cutoffCoord, ← sub_div, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  rw [← Int.cast_sub, ← Int.cast_abs]
  exact_mod_cast h

theorem IntegerCube.cutoff_of_mem (B : IntegerCube d) (hB : 0 < B.size) {x : Vertex d}
    (hx : x ∈ B.vertices) : B.cutoff x = 1 := by
  rw [IntegerCube.mem_vertices] at hx
  refine Finset.prod_eq_one fun i _ => cutoffCoord_eq_one hB ?_ ?_ <;>
  · have := hx i
    omega

theorem IntegerCube.cutoff_nonneg (B : IntegerCube d) {x : Vertex d}
    (hx : x ∈ B.triple.vertices) : 0 ≤ B.cutoff x := by
  rw [IntegerCube.mem_triple_vertices] at hx
  refine Finset.prod_nonneg fun i _ => cutoffCoord_nonneg ?_ ?_ <;>
  · have := hx i
    omega

theorem IntegerCube.cutoff_le_one (B : IntegerCube d) (hB : 0 < B.size) {x : Vertex d}
    (hx : x ∈ B.triple.vertices) : B.cutoff x ≤ 1 := by
  rw [IntegerCube.mem_triple_vertices] at hx
  refine Finset.prod_le_one (fun i _ => cutoffCoord_nonneg ?_ ?_) fun i _ =>
    cutoffCoord_le_one hB _ <;>
  · have := hx i
    omega

/-- The cutoff vanishes at the vertices of the triple cube having a lattice neighbour outside
it. -/
theorem IntegerCube.cutoff_eq_zero (B : IntegerCube d) {x y : Vertex d}
    (hx : x ∈ B.triple.vertices) (hy : y ∉ B.triple.vertices)
    (hxy : (nearestNeighborGraph d).Adj x y) : B.cutoff x = 0 := by
  rw [IntegerCube.mem_triple_vertices] at hx hy
  obtain ⟨k, hk⟩ := not_forall.1 hy
  obtain ⟨h1, h2⟩ := hx k
  have hk' : x k - B.corner k = -(B.size : ℤ) ∨ x k - B.corner k = 2 * B.size - 1 := by
    obtain ⟨j, h | h⟩ := hxy
    · subst h
      rw [add_unit_apply] at hk
      split_ifs at hk <;> omega
    · subst h
      rw [add_unit_apply] at h1 h2 ⊢
      split_ifs at h1 h2 ⊢ <;> omega
  refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
  rw [cutoffCoord]
  have : cutoffNum B.size (x k - B.corner k) = 0 := by
    simp only [cutoffNum]
    split_ifs <;> omega
  rw [this, Int.cast_zero, zero_div]

/-- Along the edge from `x` to `x + e_j` the cutoff changes by at most `1/n`. -/
theorem IntegerCube.abs_cutoff_add_unit_sub_le (B : IntegerCube d) (hB : 0 < B.size)
    {x : Vertex d} (j : Fin d) (hx : x ∈ B.triple.vertices) :
    |B.cutoff (x + LatticeProb.unit j) - B.cutoff x| ≤ 1 / B.size := by
  rw [IntegerCube.mem_triple_vertices] at hx
  have hP : ∏ i ∈ Finset.univ.erase j,
      cutoffCoord B.size ((x + LatticeProb.unit j) i - B.corner i) =
      ∏ i ∈ Finset.univ.erase j, cutoffCoord B.size (x i - B.corner i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [add_unit_apply, if_neg (Finset.ne_of_mem_erase hi), add_zero]
  have hP0 : 0 ≤ ∏ i ∈ Finset.univ.erase j, cutoffCoord B.size (x i - B.corner i) :=
    Finset.prod_nonneg fun i _ => cutoffCoord_nonneg (by have := hx i; omega)
      (by have := hx i; omega)
  have hP1 : ∏ i ∈ Finset.univ.erase j, cutoffCoord B.size (x i - B.corner i) ≤ 1 :=
    Finset.prod_le_one (fun i _ => cutoffCoord_nonneg (by have := hx i; omega)
      (by have := hx i; omega)) fun i _ => cutoffCoord_le_one hB _
  rw [IntegerCube.cutoff, IntegerCube.cutoff,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), hP, ← sub_mul, abs_mul,
    abs_of_nonneg hP0, add_unit_apply, if_pos rfl,
    show x j + 1 - B.corner j = (x j - B.corner j) + 1 by ring]
  calc |cutoffCoord B.size ((x j - B.corner j) + 1) - cutoffCoord B.size (x j - B.corner j)| *
        ∏ i ∈ Finset.univ.erase j, cutoffCoord B.size (x i - B.corner i)
      ≤ (1 / B.size) * 1 :=
        mul_le_mul (abs_cutoffCoord_succ_sub_le _ _) hP1 hP0 (by positivity)
    _ = 1 / B.size := mul_one _

/-- Along every lattice edge of the triple cube the cutoff changes by at most `1/n`. -/
theorem IntegerCube.abs_cutoff_sub_le (B : IntegerCube d) (hB : 0 < B.size) {x y : Vertex d}
    (hx : x ∈ B.triple.vertices) (hy : y ∈ B.triple.vertices)
    (hxy : (nearestNeighborGraph d).Adj x y) : |B.cutoff x - B.cutoff y| ≤ 1 / B.size := by
  obtain ⟨j, h | h⟩ := hxy
  · subst h
    rw [abs_sub_comm]
    exact B.abs_cutoff_add_unit_sub_le hB j hx
  · subst h
    exact B.abs_cutoff_add_unit_sub_le hB j hy

end Rigidity.Percolation
