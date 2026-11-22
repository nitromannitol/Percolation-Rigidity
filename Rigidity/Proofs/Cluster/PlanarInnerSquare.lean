import Rigidity.Proofs.Cluster.PlanarRestrictCoarse

/-!
# A triadic cube without its boundary layer

For a triadic square `V` of scale `n` and `j < n`, `innerSquare V j` is the square obtained from `V`
by removing the boundary layer of width `3^j`: the union of the triadic squares of scale `j` inside
`V` which do not touch its boundary (the complement of the set `K_z` of Armstrong and Dario, proof
of Lemma 5.5, Step 2, for `j = ⌈n/2⌉`). The layer has at most `4 · 3^{n+j}` vertices, and the inner
square is resolved by the planar partition as soon as the partition cubes of the vertices of `V`
have scale at most `j`: the corners of triadic squares of scale `j` differ from the corner of `V` by
multiples of `3^j`.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical

/-- The square obtained from a triadic square by removing the boundary layer of width `3^j`. -/
def innerSquare (V : TriadicCube 2) (j : ℕ) : IntegerCube 2 :=
  ⟨fun i => V.toIntegerCube.corner i + 3 ^ j, 3 ^ V.scale - 2 * 3 ^ j⟩

theorem two_mul_three_pow_le {j n : ℕ} (hj : j < n) : 2 * 3 ^ j ≤ 3 ^ n :=
  calc 2 * 3 ^ j ≤ 3 * 3 ^ j := by omega
    _ = 3 ^ (j + 1) := by ring
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hj

theorem cast_innerSquare_size {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale) :
    (((innerSquare V j).size : ℕ) : ℤ) = 3 ^ V.scale - 2 * 3 ^ j := by
  change ((3 ^ V.scale - 2 * 3 ^ j : ℕ) : ℤ) = _
  rw [Nat.cast_sub (two_mul_three_pow_le hj)]
  push_cast
  ring

theorem TriadicCube.toIntegerCube_corner_eq (Q : TriadicCube 2) (i : Fin 2) :
    Q.toIntegerCube.corner i = 3 ^ Q.scale * Q.index i - halfSide Q.scale := by
  have h := two_mul_halfSide_add_one Q.scale
  change (3 : ℤ) ^ Q.scale * Q.index i - (3 : ℤ) ^ Q.scale / 2 = _
  rw [← h]
  omega

/-- The corners of a triadic square and of a triadic square of larger scale differ by a multiple
of the smaller side. -/
theorem TriadicCube.exists_corner_sub_eq {T V : TriadicCube 2} (h : T.scale ≤ V.scale)
    (i : Fin 2) : ∃ m : ℤ,
      T.toIntegerCube.corner i - V.toIntegerCube.corner i = 3 ^ T.scale * m := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  refine ⟨T.index i - 3 ^ k * V.index i + halfSide k, ?_⟩
  rw [TriadicCube.toIntegerCube_corner_eq, TriadicCube.toIntegerCube_corner_eq, hk,
    halfSide_add, pow_add]
  ring

theorem innerSquare_subset {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale) :
    (innerSquare V j).vertices ⊆ V.toIntegerCube.vertices := by
  intro x hx
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro i
  have hxi := hx i
  rw [cast_innerSquare_size hj] at hxi
  change V.toIntegerCube.corner i + 3 ^ j ≤ x i ∧
    x i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hxi
  have hs : (((V.toIntegerCube.size : ℕ) : ℤ)) = 3 ^ V.scale := V.cast_toIntegerCube_size
  rw [hs]
  have hpos : (0 : ℤ) ≤ 3 ^ j := by positivity
  constructor <;> omega

/-- The boundary layer of width `3^j` of a triadic square of scale `n` has at most `4 · 3^{n+j}`
vertices. -/
theorem card_sdiff_innerSquare_le {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale) :
    ((V.toIntegerCube.vertices \ (innerSquare V j).vertices).card : ℝ) ≤
      4 * 3 ^ (V.scale + j) := by
  have hsub := innerSquare_subset hj
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hV : (V.toIntegerCube.vertices.card : ℝ) = ((3 : ℝ) ^ V.scale) ^ 2 := by
    rw [IntegerCube.card_vertices_eq]
    change ((((3 ^ V.scale : ℕ) ^ 2 : ℕ)) : ℝ) = _
    push_cast
    ring
  have hB : ((innerSquare V j).vertices.card : ℝ) = ((3 : ℝ) ^ V.scale - 2 * 3 ^ j) ^ 2 := by
    rw [IntegerCube.card_vertices_eq]
    change (((3 ^ V.scale - 2 * 3 ^ j : ℕ) ^ 2 : ℕ) : ℝ) = _
    rw [Nat.cast_pow, Nat.cast_sub (two_mul_three_pow_le hj)]
    push_cast
    ring
  have hcardR : ((V.toIntegerCube.vertices \ (innerSquare V j).vertices).card : ℝ) +
      ((innerSquare V j).vertices.card : ℝ) = (V.toIntegerCube.vertices.card : ℝ) := by
    exact_mod_cast hcard
  rw [hV, hB] at hcardR
  have hj0 : (0 : ℝ) ≤ (3 : ℝ) ^ j := by positivity
  rw [pow_add]
  nlinarith [sq_nonneg ((3 : ℝ) ^ j)]

/-- **The inner square is resolved.** If the planar partition cubes of the vertices of a triadic
square `V` of scale `n` have scale at most `j < n`, the square without its boundary layer of
width `3^j` is resolved by the planar partition. -/
theorem planarBoxResolved_innerSquare {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale)
    (h : ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j) :
    PlanarBoxResolved ω (innerSquare V j) := by
  intro z hz y hy
  have hzV : z ∈ V.vertices :=
    (V.mem_toIntegerCube_vertices z).1 (innerSquare_subset hj hz)
  set Q := planarPartCube ω z with hQ
  have hQs : Q.scale ≤ j := h z hzV
  set T := Q.ancestor (j - Q.scale) with hT
  have hTs : T.scale = j := by
    rw [hT, TriadicCube.scale_ancestor]
    omega
  have hzT : z ∈ T.vertices := Q.vertices_subset_ancestor _ (planarPartCube_spec hP z).1
  have hyT : y ∈ T.vertices := Q.vertices_subset_ancestor _ hy
  rw [Finset.mem_coe, IntegerCube.mem_vertices]
  intro i
  have hzB := (IntegerCube.mem_vertices _ z).1 hz i
  rw [cast_innerSquare_size hj] at hzB
  change V.toIntegerCube.corner i + 3 ^ j ≤ z i ∧
    z i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hzB
  rw [cast_innerSquare_size hj]
  change V.toIntegerCube.corner i + 3 ^ j ≤ y i ∧
    y i < V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j)
  have hzT' := TriadicCube.corner_le_of_mem hzT i
  have hyT' := TriadicCube.corner_le_of_mem hyT i
  rw [hTs] at hzT' hyT'
  obtain ⟨m, hm⟩ := TriadicCube.exists_corner_sub_eq (T := T) (V := V) (by omega) i
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

end Rigidity.Proofs.Cluster
