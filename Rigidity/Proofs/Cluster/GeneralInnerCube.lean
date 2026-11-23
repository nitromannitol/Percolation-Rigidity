import Rigidity.Proofs.Cluster.GeneralCoarseMeyers
import Rigidity.Proofs.Cluster.PlanarInnerSquare
import Rigidity.Proofs.Percolation.GeneralDim.CubeNablaAffine

/-!
# A triadic cube without its boundary layer, in every dimension

For a triadic cube `V` of scale `n` and `j < n`, `innerCube V j` is the cube obtained from `V` by
removing the boundary layer of width `3^j`: the union of the triadic cubes of scale `j` inside `V`
which do not touch its boundary (the complement of the set `K_z` of Armstrong and Dario, proof of
Lemma 5.5, Step 2). The layer has at most `2d · 3^{(d-1)n + j}` vertices
(`card_sdiff_innerCube_le`, from `aᵈ - bᵈ ≤ d (a - b) a^{d-1}`), and the inner cube is resolved by
the partition into good cubes (it contains the parents of the partition cubes of its vertices) as
soon as the partition cubes of the vertices of `V` have scale less than `j`
(`partitionBoxResolved_innerCube`): the corners of triadic cubes of scale `j` differ from the
corner of `V` by multiples of `3^j`. The two-dimensional version is
`Rigidity.Proofs.Cluster.innerSquare`, for the planar partition whose cells resolve integer squares
already when they lie inside.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The cube obtained from a triadic cube by removing the boundary layer of width `3^j`. -/
def innerCube (V : TriadicCube d) (j : ℕ) : IntegerCube d :=
  ⟨fun i => V.toIntegerCube.corner i + 3 ^ j, 3 ^ V.scale - 2 * 3 ^ j⟩

theorem cast_innerCube_size {V : TriadicCube d} {j : ℕ} (hj : j < V.scale) :
    (((innerCube V j).size : ℕ) : ℤ) = 3 ^ V.scale - 2 * 3 ^ j := by
  change ((3 ^ V.scale - 2 * 3 ^ j : ℕ) : ℤ) = _
  rw [Nat.cast_sub (two_mul_three_pow_le hj)]
  push_cast
  ring

theorem TriadicCube.toIntegerCube_corner_eq_mul_sub (Q : TriadicCube d) (i : Fin d) :
    Q.toIntegerCube.corner i = 3 ^ Q.scale * Q.index i - halfSide Q.scale := by
  have h := two_mul_halfSide_add_one Q.scale
  change (3 : ℤ) ^ Q.scale * Q.index i - (3 : ℤ) ^ Q.scale / 2 = _
  rw [← h]
  omega

/-- The corners of a triadic cube and of a triadic cube of larger scale differ by a multiple
of the smaller side. -/
theorem TriadicCube.exists_corner_sub_eq_mul {T V : TriadicCube d} (h : T.scale ≤ V.scale)
    (i : Fin d) : ∃ m : ℤ,
      T.toIntegerCube.corner i - V.toIntegerCube.corner i = 3 ^ T.scale * m := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  refine ⟨T.index i - 3 ^ k * V.index i + halfSide k, ?_⟩
  rw [TriadicCube.toIntegerCube_corner_eq_mul_sub, TriadicCube.toIntegerCube_corner_eq_mul_sub, hk,
    halfSide_add, pow_add]
  ring

theorem innerCube_subset {V : TriadicCube d} {j : ℕ} (hj : j < V.scale) :
    (innerCube V j).vertices ⊆ V.toIntegerCube.vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro i
  have hxi := hx i
  rw [cast_innerCube_size hj] at hxi
  change V.toIntegerCube.corner i + 3 ^ j ≤ x i ∧
    x i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hxi
  have hs : (((V.toIntegerCube.size : ℕ) : ℤ)) = 3 ^ V.scale := by
    change ((3 ^ V.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  rw [hs]
  have hpos : (0 : ℤ) ≤ 3 ^ j := by positivity
  constructor <;> omega

/-- `aᵈ - bᵈ ≤ d (a - b) a^{d-1}` for `0 ≤ b ≤ a`. -/
theorem pow_sub_pow_le_card_mul {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * (a - b) * a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : 0 ≤ a := hb.trans hba
    have h1 : b ^ (n + 1) ≤ a ^ (n + 1) := pow_le_pow_left₀ hb hba _
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
        a * (a ^ (n + 1) - b ^ (n + 1)) + (a - b) * b ^ (n + 1) := by ring
    rw [e]
    have h2 : a * (a ^ (n + 1) - b ^ (n + 1)) ≤ a * ((n + 1) * (a - b) * a ^ n) :=
      mul_le_mul_of_nonneg_left ih ha
    have h3 : (a - b) * b ^ (n + 1) ≤ (a - b) * a ^ (n + 1) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have e2 : a * ((n + 1) * (a - b) * a ^ n) + (a - b) * a ^ (n + 1) =
        ((n + 1 : ℕ) + 1 : ℝ) * (a - b) * a ^ (n + 1) := by
      push_cast
      ring
    push_cast at e2 ⊢
    linarith

/-- The boundary layer of width `3^j` of a triadic cube of scale `n` has at most
`2d · 3^{(d-1)n + j}` vertices. -/
theorem card_sdiff_innerCube_le {V : TriadicCube d} {j : ℕ} (hj : j < V.scale) :
    ((V.toIntegerCube.vertices \ (innerCube V j).vertices).card : ℝ) ≤
      2 * d * ((3 : ℝ) ^ V.scale) ^ (d - 1) * 3 ^ j := by
  have hsub := innerCube_subset hj
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hV : (V.toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ V.scale) ^ d := by
    rw [IntegerCube.card_vertices_eq]
    change ((((3 ^ V.scale : ℕ) ^ d : ℕ)) : ℝ) = _
    push_cast
    ring
  have hB : ((innerCube V j).vertices.card : ℝ) = ((3 : ℝ) ^ V.scale - 2 * 3 ^ j) ^ d := by
    rw [IntegerCube.card_vertices_eq]
    change (((3 ^ V.scale - 2 * 3 ^ j : ℕ) ^ d : ℕ) : ℝ) = _
    rw [Nat.cast_pow, Nat.cast_sub (two_mul_three_pow_le hj)]
    push_cast
    ring
  have hcardR : ((V.toIntegerCube.vertices \ (innerCube V j).vertices).card : ℝ) +
      ((innerCube V j).vertices.card : ℝ) = (V.toIntegerCube.vertices.card : ℝ) := by
    exact_mod_cast hcard
  rw [hV, hB] at hcardR
  have h2 : (2 : ℝ) * 3 ^ j ≤ 3 ^ V.scale := by exact_mod_cast two_mul_three_pow_le hj
  have hb0 : (0 : ℝ) ≤ 3 ^ V.scale - 2 * 3 ^ j := by linarith
  have h3j : (0 : ℝ) ≤ 3 ^ j := by positivity
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [pow_zero] at hcardR
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul]
    linarith
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hd
    simp only [zero_add] at hcardR ⊢
    have h := pow_sub_pow_le_card_mul hb0 (by linarith : (3 : ℝ) ^ V.scale - 2 * 3 ^ j ≤ 3 ^ V.scale) n
    have e : (n + 1 - 1 : ℕ) = n := by omega
    rw [e]
    push_cast
    nlinarith

/-- **The inner cube is resolved.** If the partition cubes of the vertices of a triadic cube `V`
of scale `n` have scale less than `j < n`, the cube without its boundary layer of width `3^j`
contains the parents of the partition cubes of its vertices. -/
theorem partitionBoxResolved_innerCube {ω : Configuration d} (hP : PartitionEvent ω)
    {V : TriadicCube d} {j : ℕ} (hj : j < V.scale)
    (h : ∀ x ∈ V.vertices, (partitionCube ω x).scale < j) :
    PartitionBoxResolved ω (innerCube V j) := by
  intro z hz y hy
  have hzV : z ∈ V.vertices :=
    (V.mem_toIntegerCube_vertices z).1 (innerCube_subset hj hz)
  set Q := partitionCube ω z with hQ
  have hQs : Q.scale < j := h z hzV
  set T := Q.parent.ancestor (j - (Q.scale + 1)) with hT
  have hTs : T.scale = j := by
    rw [hT, TriadicCube.scale_ancestor]
    change Q.scale + 1 + (j - (Q.scale + 1)) = j
    omega
  have hzT : z ∈ T.vertices := Q.parent.vertices_subset_ancestor _
    (Q.vertices_subset_parent (mem_partitionCube hP z))
  have hyT : y ∈ T.vertices := Q.parent.vertices_subset_ancestor _ hy
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  have hzB := (IntegerCube.mem_vertices _ z).1 hz i
  rw [cast_innerCube_size hj] at hzB
  change V.toIntegerCube.corner i + 3 ^ j ≤ z i ∧
    z i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hzB
  rw [cast_innerCube_size hj]
  change V.toIntegerCube.corner i + 3 ^ j ≤ y i ∧
    y i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j)
  have hzT' := TriadicCube.coord_bounds_of_mem hzT i
  have hyT' := TriadicCube.coord_bounds_of_mem hyT i
  rw [hTs] at hzT' hyT'
  obtain ⟨m, hm⟩ := TriadicCube.exists_corner_sub_eq_mul (T := T) (V := V) (by omega) i
  rw [hTs] at hm
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hj
  have hn : (3 : ℤ) ^ V.scale = 3 ^ j * (3 * 3 ^ k) := by rw [hk]; ring
  rw [hn] at hzB ⊢
  set P : ℤ := 3 ^ j with hP'
  have hPpos : 0 < P := by positivity
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have : P * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hPpos.le (by omega)
    linarith
  have hm2 : m ≤ 3 * 3 ^ k - 2 := by
    by_contra hcon
    have h3 : P * (3 * 3 ^ k - 1) ≤ P * m := mul_le_mul_of_nonneg_left (by omega) hPpos.le
    nlinarith
  have h4 : P * m ≤ P * (3 * 3 ^ k - 2) := mul_le_mul_of_nonneg_left hm2 hPpos.le
  have h5 : P * 1 ≤ P * m := mul_le_mul_of_nonneg_left hm1 hPpos.le
  constructor <;> nlinarith

end Rigidity.Percolation
