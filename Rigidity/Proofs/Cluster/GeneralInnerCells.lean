import Rigidity.Proofs.Cluster.GeneralInnerCube

/-!
# The cells of the inner cube, in every dimension

For a triadic cube `V` of scale `n` and `j < n`, the triadic cubes of scale `j` meeting the inner
cube `innerCube V j` lie in it (`TriadicCube.subset_innerCube`: their corners differ from that of
`V` by multiples of `3^j`); their triples lie in `V` (`innerCubeCells_enl_subset`), and every
vertex lies in at most `3^d` of the triples (`card_innerCubeCells_filter_le`). These are the cells
on which the Meyers estimate is used in Step 3 of the proof of Lemma 5.5 of Armstrong and Dario, in
the form of the two-dimensional version `Rigidity.Proofs.Cluster.innerCells` (cells of scale
`⌈n/2⌉` away from the boundary of `z + □_n`, Hölder's inequality in each cell).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- A triadic cube of scale `j` meeting the inner cube of `V` lies in it. -/
theorem TriadicCube.subset_innerCube {V : TriadicCube d} {j : ℕ} (hj : j < V.scale)
    {T : TriadicCube d} (hTs : T.scale = j) {z : Vertex d} (hzT : z ∈ T.vertices)
    (hz : z ∈ (innerCube V j).vertices) : T.vertices ⊆ ↑(innerCube V j).vertices := by
  intro y hyT
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

/-- The cube of scale `j` of a vertex of the inner cube lies in the inner cube. -/
theorem cube_subset_innerCube {V : TriadicCube d} {j : ℕ} (hj : j < V.scale) {x : Vertex d}
    (hx : x ∈ (innerCube V j).vertices) : cube j x ⊆ (innerCube V j).vertices := by
  intro y hy
  exact TriadicCube.subset_innerCube hj (T := ⟨j, idx j x⟩) rfl
    (mem_triadicCube_idx_iff.2 (mem_cube_self j x)) hx (mem_triadicCube_idx_iff.2 hy)

/-- The triple of the cube of scale `j` of a vertex of the inner cube lies in `V`. -/
theorem enl_subset_of_mem_innerCube {V : TriadicCube d} {j : ℕ} (hj : j < V.scale)
    {x : Vertex d} (hx : x ∈ (innerCube V j).vertices) :
    enl 1 j x ⊆ V.toIntegerCube.vertices := by
  have hsub := cube_subset_innerCube hj hx
  have h1 := two_mul_halfSide_add_one j
  have h2 : halfSide (j + 1) = 3 * halfSide j + 1 := rfl
  have hh := halfSide_nonneg j
  intro y hy
  rw [enl, mem_box] at hy
  rw [IntegerCube.mem_vertices]
  intro i
  have hlo : (fun l => center j x l - halfSide j) ∈ (innerCube V j).vertices :=
    hsub (by rw [cube, mem_box]; intro l; simp [abs_neg, abs_of_nonneg hh])
  have hhi : (fun l => center j x l + halfSide j) ∈ (innerCube V j).vertices :=
    hsub (by rw [cube, mem_box]; intro l; simp [abs_of_nonneg hh])
  have hlo' := (IntegerCube.mem_vertices _ _).1 hlo i
  have hhi' := (IntegerCube.mem_vertices _ _).1 hhi i
  rw [cast_innerCube_size hj] at hlo' hhi'
  change V.toIntegerCube.corner i + 3 ^ j ≤ center j x i - halfSide j ∧ _ at hlo'
  change _ ∧ center j x i + halfSide j <
    V.toIntegerCube.corner i + 3 ^ j + (3 ^ V.scale - 2 * 3 ^ j) at hhi'
  have hs : ((V.toIntegerCube.size : ℕ) : ℤ) = 3 ^ V.scale := by
    change ((3 ^ V.scale : ℕ) : ℤ) = _
    push_cast
    rfl
  rw [hs]
  have hyi := abs_le.1 (hy i)
  constructor <;> omega

/-- The cells of scale `j` of the inner cube of `V`, indexed by their scale and center. -/
noncomputable def innerCubeCells (V : TriadicCube d) (j : ℕ) : Finset (ℕ × Vertex d) :=
  (innerCube V j).vertices.image fun x => (j, center j x)

theorem center_mem_cube_self (k : ℕ) (x : Vertex d) : center k x ∈ cube k x := by
  rw [cube, mem_box]
  intro i
  simp [halfSide_nonneg]

/-- The cells cover the inner cube. -/
theorem innerCubeCells_cover (V : TriadicCube d) (j : ℕ) {z : Vertex d}
    (hz : z ∈ (innerCube V j).vertices) : ∃ c ∈ innerCubeCells V j, z ∈ cube c.1 c.2 := by
  refine ⟨(j, center j z), Finset.mem_image_of_mem _ hz, ?_⟩
  change z ∈ cube j (center j z)
  rw [cube_eq_of_mem (center_mem_cube_self j z)]
  exact mem_cube_self j z

/-- The triples of the cells lie in `V`. -/
theorem innerCubeCells_enl_subset {V : TriadicCube d} {j : ℕ} (hj : j < V.scale)
    {c : ℕ × Vertex d} (hc : c ∈ innerCubeCells V j) :
    enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  change enl 1 j (center j x) ⊆ _
  rw [enl_eq_of_mem (center_mem_cube_self j x)]
  exact enl_subset_of_mem_innerCube hj hx

/-- Every vertex lies in at most `3^d` of the triples of the cells. -/
theorem card_innerCubeCells_filter_le (V : TriadicCube d) (j : ℕ) (x : Vertex d) :
    ((innerCubeCells V j).filter fun c => x ∈ enl 1 c.1 c.2).card ≤ 3 ^ d := by
  set E : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ) with hE
  have hEcard : E.card = 3 ^ d := by
    rw [hE, Fintype.card_piFinset]
    simp
  have h1 := two_mul_halfSide_add_one j
  have h2 : halfSide (j + 1) = 3 * halfSide j + 1 := rfl
  have hh := halfSide_nonneg j
  have hsub : ((innerCubeCells V j).filter fun c => x ∈ enl 1 c.1 c.2) ⊆
      E.image fun e => (j, fun i => center j x i + 3 ^ j * e i) := by
    intro c hc
    obtain ⟨hcI, hxc⟩ := Finset.mem_filter.1 hc
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hcI
    rw [Finset.mem_image]
    refine ⟨fun i => idx j x' i - idx j x i, ?_, ?_⟩
    · rw [hE, Fintype.mem_piFinset]
      intro i
      change x ∈ enl 1 j (center j x') at hxc
      rw [enl, mem_box] at hxc
      have hxi := hxc i
      have hxx := (mem_box.1 (show x ∈ cube j x from mem_cube_self j x)) i
      have hc1 : center j (center j x') = center j x' := by
        rw [center_eq_of_mem (center_mem_cube_self j x')]
      rw [hc1] at hxi
      have e1 : center j x' i = 3 ^ j * idx j x' i := rfl
      have e2 : center j x i = 3 ^ j * idx j x i := rfl
      rw [e1] at hxi
      rw [e2] at hxx
      set P : ℤ := 3 ^ j with hP
      have hPpos : 0 < P := by positivity
      have hlt : |P * (idx j x' i - idx j x i)| < 2 * P := by
        rw [mul_sub]
        rw [abs_le] at hxi hxx
        rw [abs_lt]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos hPpos] at hlt
      have hlt' : |idx j x' i - idx j x i| < 2 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at hlt'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · ext
      · rfl
      · dsimp only
        simp only [center]
        ring
  calc ((innerCubeCells V j).filter fun c => x ∈ enl 1 c.1 c.2).card
      ≤ (E.image fun e => (j, fun i => center j x i + 3 ^ j * e i)).card :=
        Finset.card_le_card hsub
    _ ≤ E.card := Finset.card_image_le
    _ = 3 ^ d := hEcard

end Rigidity.Percolation
