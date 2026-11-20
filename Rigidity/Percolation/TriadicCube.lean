import LatticeProb.Prob.Percolation.LatticeBondModel

/-!
# Triadic cubes of the integer lattice

The lattice cubes have side length `3 ^ n`, with centers in `3 ^ n` times the
integer lattice. Their integer points lie strictly within half a side length
of the center in each coordinate.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- A triadic cube is specified by its scale and its center index. -/
@[ext] structure TriadicCube (d : ℕ) where
  scale : ℕ
  index : Fin d → ℤ
  deriving DecidableEq

/-- The integer side length of a triadic cube. -/
def TriadicCube.side {d : ℕ} (Q : TriadicCube d) : ℤ := (3 : ℤ) ^ Q.scale

/-- The lattice points in the open Euclidean cube represented by `Q`. -/
def TriadicCube.vertices {d : ℕ} (Q : TriadicCube d) : Set (Vertex d) :=
  {x | ∀ i, |2 * (x i - Q.side * Q.index i)| < Q.side}

/-- The unique triadic cube of the next larger scale containing a cube. -/
def TriadicCube.parent {d : ℕ} (Q : TriadicCube d) : TriadicCube d where
  scale := Q.scale + 1
  index i := (Q.index i + 1) / 3

/-- A cube obtained by choosing one of the three child positions in each coordinate. -/
def TriadicCube.child {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) : TriadicCube d where
  scale := Q.scale - 1
  index i := 3 * Q.index i + (digits i : ℤ) - 1

/-- The side length is positive at every scale. -/
theorem TriadicCube.side_pos {d : ℕ} (Q : TriadicCube d) : 0 < Q.side := by
  exact pow_pos (by norm_num) _

/-- Raising the scale by one triples the side length. -/
theorem TriadicCube.side_parent {d : ℕ} (Q : TriadicCube d) : Q.parent.side = 3 * Q.side := by
  simp only [side, parent, pow_succ]
  ring

/-- Each of the three positions has the stated parent index. -/
theorem TriadicCube.child_parent {d : ℕ} (Q : TriadicCube d) (digits : Fin d → Fin 3) (hQ : 0 < Q.scale) :
    (Q.child digits).parent = Q := by
  apply TriadicCube.ext
  · simp only [parent, child]
    omega
  · funext i
    simp only [parent, child]
    have hd0 : (0 : ℤ) ≤ digits i := by exact_mod_cast (Nat.zero_le (digits i).val)
    have hd3 : (digits i : ℤ) < 3 := by exact_mod_cast (digits i).isLt
    omega

/-- The position of a cube among the children of its parent. -/
def TriadicCube.digit {d : ℕ} (Q : TriadicCube d) (i : Fin d) : Fin 3 :=
  ⟨((Q.index i + 1) % 3).toNat, by
    have h0 : 0 ≤ (Q.index i + 1) % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : (Q.index i + 1) % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega⟩

/-- Every cube is a child of its parent. -/
theorem TriadicCube.parent_child {d : ℕ} (Q : TriadicCube d) :
    Q.parent.child Q.digit = Q := by
  apply TriadicCube.ext
  · simp only [parent, child]
    omega
  · funext i
    simp only [child, parent, digit]
    have h0 : 0 ≤ (Q.index i + 1) % 3 := Int.emod_nonneg _ (by norm_num)
    have hmod := Int.emod_add_mul_ediv (Q.index i + 1) 3
    rw [Int.toNat_of_nonneg h0]
    omega

/-- Distinct child positions give distinct cubes. -/
theorem TriadicCube.child_injective {d : ℕ} (Q : TriadicCube d) :
    Function.Injective Q.child := by
  intro a b hab
  funext i
  have hi := congrArg (fun R : TriadicCube d => R.index i) hab
  simp only [child] at hi
  apply Fin.ext
  omega

/-- Every child cube is contained in its parent. -/
theorem TriadicCube.vertices_child_subset {d : ℕ} (Q : TriadicCube d)
    (digits : Fin d → Fin 3) (hQ : 0 < Q.scale) :
    (Q.child digits).vertices ⊆ Q.vertices := by
  intro x hx i
  have hs : 0 < (Q.child digits).side := side_pos _
  have hside : 3 * (Q.child digits).side = Q.side := by
    rw [← side_parent, child_parent _ _ hQ]
  have hbound := abs_lt.mp (hx i)
  have hd0 : (0 : ℤ) ≤ digits i := by exact_mod_cast (Nat.zero_le (digits i).val)
  have hd2 : (digits i : ℤ) ≤ 2 := by exact_mod_cast (Nat.le_of_lt_succ (digits i).isLt)
  have hp0 := mul_nonneg (le_of_lt hs) hd0
  have hp2 := mul_le_mul_of_nonneg_left hd2 (le_of_lt hs)
  apply abs_lt.mpr
  rw [← hside]
  change -(Q.child digits).side < 2 * (x i - (Q.child digits).side *
    (3 * Q.index i + (digits i : ℤ) - 1)) ∧
    2 * (x i - (Q.child digits).side * (3 * Q.index i + (digits i : ℤ) - 1)) <
      (Q.child digits).side at hbound
  rcases hbound with ⟨hlo, hhi⟩
  constructor <;> nlinarith

/-- A cube is contained in its parent. -/
theorem TriadicCube.vertices_subset_parent {d : ℕ} (Q : TriadicCube d) :
    Q.vertices ⊆ Q.parent.vertices := by
  have h := vertices_child_subset Q.parent Q.digit (by simp [parent])
  simpa only [Q.parent_child] using h

/-- Two cubes at the same scale which share a lattice point coincide. -/
theorem TriadicCube.eq_of_mem_of_scale_eq {d : ℕ} {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) {x : Vertex d} (hx : x ∈ Q.vertices)
    (hy : x ∈ R.vertices) : Q = R := by
  have hs : Q.side = R.side := by simp only [side, hscale]
  have hpos := Q.side_pos
  apply TriadicCube.ext hscale
  funext i
  have hq := abs_lt.mp (hx i)
  have hr := abs_lt.mp (hy i)
  rw [← hs] at hr
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmul := mul_le_mul_of_nonneg_left (show Q.index i + 1 ≤ R.index i by omega)
      (le_of_lt hpos)
    rcases hq with ⟨_, hq⟩
    rcases hr with ⟨hr, _⟩
    nlinarith
  · have hmul := mul_le_mul_of_nonneg_left (show R.index i + 1 ≤ Q.index i by omega)
      (le_of_lt hpos)
    rcases hq with ⟨hq, _⟩
    rcases hr with ⟨_, hr⟩
    nlinarith

/-- At each scale, the triadic cubes form a partition of the integer lattice. -/
theorem TriadicCube.existsUnique_mem (d n : ℕ) (x : Vertex d) :
    ∃! Q : TriadicCube d, Q.scale = n ∧ x ∈ Q.vertices := by
  have hex : ∀ n : ℕ, ∃ Q : TriadicCube d, Q.scale = n ∧ x ∈ Q.vertices := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨0, x⟩, rfl, ?_⟩
      intro i
      simp [side]
    | succ n ih =>
      obtain ⟨Q, hscale, hx⟩ := ih
      refine ⟨Q.parent, ?_, Q.vertices_subset_parent hx⟩
      simp only [parent, hscale]
  obtain ⟨Q, hQ⟩ := hex n
  refine ⟨Q, hQ, ?_⟩
  intro R hR
  exact eq_of_mem_of_scale_eq (hR.1.trans hQ.1.symm) hR.2 hQ.2

/-- The children of a positive-scale cube cover all its lattice points. -/
theorem TriadicCube.mem_child_of_mem {d : ℕ} (Q : TriadicCube d) (hQ : 0 < Q.scale)
    {x : Vertex d} (hx : x ∈ Q.vertices) :
    ∃ digits : Fin d → Fin 3, x ∈ (Q.child digits).vertices := by
  obtain ⟨R, hR, -⟩ := existsUnique_mem d (Q.scale - 1) x
  have hparent : R.parent = Q := by
    apply eq_of_mem_of_scale_eq _ (R.vertices_subset_parent hR.2) hx
    simp only [parent, hR.1]
    omega
  refine ⟨R.digit, ?_⟩
  rw [← hparent, R.parent_child]
  exact hR.2

/-- Every lattice point in a positive-scale cube belongs to exactly one child. -/
theorem TriadicCube.existsUnique_mem_child {d : ℕ} (Q : TriadicCube d) (hQ : 0 < Q.scale)
    {x : Vertex d} (hx : x ∈ Q.vertices) :
    ∃! digits : Fin d → Fin 3, x ∈ (Q.child digits).vertices := by
  obtain ⟨digits, hdigits⟩ := Q.mem_child_of_mem hQ hx
  refine ⟨digits, hdigits, ?_⟩
  intro digits' hdigits'
  apply Q.child_injective
  apply eq_of_mem_of_scale_eq _ hdigits' hdigits
  rfl

end Rigidity.Percolation
