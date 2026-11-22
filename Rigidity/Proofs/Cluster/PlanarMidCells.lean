import Rigidity.Proofs.Cluster.PlanarInnerCells

/-!
# The cells of scale `j - 1` of the inner square

For a triadic square `V` of scale `n` and `1 ≤ j < n`, the triadic squares of scale `j - 1`
meeting the inner square `innerSquare V j` (the square `V` without its boundary layer of width
`3^j`) lie in it, and their triples lie at distance at least `2 · 3^{j-1}` from the complement of
`V`: every vertex of the triples, with its lattice neighbourhood, lies in `V`. These are the cells
`midCells V j` on which the Meyers estimate is applied in the proof of Lemma 5.5 of Armstrong and
Dario (in the repaired Step 3): the Meyers estimate for the functions of `A_*(V)` needs the lattice
neighbourhood of the triple of each cell inside `V`. They cover the inner square, and every vertex
lies in at most `9` of their triples.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical

/-- A triadic square of scale at most `j` meeting the inner square of `V` lies in it. -/
theorem TriadicCube.subset_innerSquare_of_le {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale)
    {T : TriadicCube 2} (hTs : T.scale ≤ j) {z : Vertex 2} (hzT : z ∈ T.vertices)
    (hz : z ∈ (innerSquare V j).vertices) : T.vertices ⊆ ↑(innerSquare V j).vertices := by
  intro y hyT
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
  obtain ⟨m, hm⟩ := TriadicCube.exists_corner_sub_eq (T := T) (V := V) (by omega) i
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hTs
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hj
  set P : ℤ := 3 ^ T.scale with hP
  set A : ℤ := 3 ^ a with hA
  have hPpos : 0 < P := by positivity
  have hApos : 0 < A := by positivity
  have hj' : (3 : ℤ) ^ j = P * A := by rw [ha, pow_add]
  have hn' : (3 : ℤ) ^ V.scale = P * (A * (3 * 3 ^ k)) := by
    rw [hk, ha]
    ring
  rw [hj', hn'] at hzB ⊢
  set B : ℤ := A * (3 * 3 ^ k) with hB
  have hm1 : A ≤ m := by
    by_contra hcon
    have h1 : P * m + P ≤ P * A := by nlinarith
    linarith
  have hm2 : m + 1 ≤ B - A := by
    by_contra hcon
    have h1 : P * (B - A) ≤ P * m := mul_le_mul_of_nonneg_left (by omega) hPpos.le
    nlinarith
  have h4 : P * (m + 1) ≤ P * (B - A) := mul_le_mul_of_nonneg_left hm2 hPpos.le
  have h5 : P * A ≤ P * m := mul_le_mul_of_nonneg_left hm1 hPpos.le
  constructor <;> nlinarith

/-- The cube of scale `j - 1` of a vertex of the inner square lies in the inner square. -/
theorem cube_pred_subset_innerSquare {V : TriadicCube 2} {j : ℕ} (hj : j < V.scale)
    {x : Vertex 2} (hx : x ∈ (innerSquare V j).vertices) :
    cube (j - 1) x ⊆ (innerSquare V j).vertices := by
  intro y hy
  exact TriadicCube.subset_innerSquare_of_le hj (T := ⟨j - 1, idx (j - 1) x⟩) (Nat.sub_le j 1)
    (mem_triadicCube_idx_iff.2 (mem_cube_self (j - 1) x)) hx (mem_triadicCube_idx_iff.2 hy)

/-- The lattice neighbourhood of the triple of the cube of scale `j - 1` of a vertex of the inner
square lies in `V`. -/
theorem isInterior_of_mem_enl_pred {V : TriadicCube 2} {j : ℕ} (hj1 : 1 ≤ j) (hj : j < V.scale)
    {x : Vertex 2} (hx : x ∈ (innerSquare V j).vertices) {y : Vertex 2}
    (hy : y ∈ enl 1 (j - 1) x) : V.IsInterior y := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk] at hy
  have hsub := cube_pred_subset_innerSquare hj hx
  rw [hk] at hsub
  have h1 := two_mul_halfSide_add_one k
  have h2 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have hh := halfSide_nonneg k
  intro y' hy'
  rw [enl, mem_box] at hy
  rw [← V.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
  intro i
  have hlo : (fun l => center k x l - halfSide k) ∈ (innerSquare V (k + 1)).vertices :=
    hsub (by rw [cube, mem_box]; intro l; simp [abs_neg, abs_of_nonneg hh])
  have hhi : (fun l => center k x l + halfSide k) ∈ (innerSquare V (k + 1)).vertices :=
    hsub (by rw [cube, mem_box]; intro l; simp [abs_of_nonneg hh])
  have hlo' := (IntegerCube.mem_vertices _ _).1 hlo i
  have hhi' := (IntegerCube.mem_vertices _ _).1 hhi i
  rw [cast_innerSquare_size hj] at hlo' hhi'
  change V.toIntegerCube.corner i + 3 ^ (k + 1) ≤ center k x i - halfSide k ∧ _ at hlo'
  change _ ∧ center k x i + halfSide k <
    V.toIntegerCube.corner i + 3 ^ (k + 1) + (3 ^ V.scale - 2 * 3 ^ (k + 1)) at hhi'
  have hs : ((V.toIntegerCube.size : ℕ) : ℤ) = 3 ^ V.scale := V.cast_toIntegerCube_size
  rw [hs]
  have hyi := abs_le.1 (hy i)
  have hy'i := abs_le.1 (hy' i)
  have h3 : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
  rw [h3] at hlo' hhi'
  constructor <;> omega

/-- The cells of scale `j - 1` of the inner square of `V`, indexed by their scale and center. -/
noncomputable def midCells (V : TriadicCube 2) (j : ℕ) : Finset (ℕ × Vertex 2) :=
  (innerSquare V j).vertices.image fun x => (j - 1, center (j - 1) x)

/-- The cells cover the inner square. -/
theorem midCells_cover (V : TriadicCube 2) (j : ℕ) {z : Vertex 2}
    (hz : z ∈ (innerSquare V j).vertices) : ∃ c ∈ midCells V j, z ∈ cube c.1 c.2 := by
  refine ⟨(j - 1, center (j - 1) z), Finset.mem_image_of_mem _ hz, ?_⟩
  change z ∈ cube (j - 1) (center (j - 1) z)
  rw [cube_eq_of_mem (center_mem_cube (j - 1) z)]
  exact mem_cube_self (j - 1) z

/-- The lattice neighbourhoods of the triples of the cells lie in `V`. -/
theorem midCells_isInterior {V : TriadicCube 2} {j : ℕ} (hj1 : 1 ≤ j) (hj : j < V.scale)
    {c : ℕ × Vertex 2} (hc : c ∈ midCells V j) {y : Vertex 2} (hy : y ∈ enl 1 c.1 c.2) :
    V.IsInterior y := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  change y ∈ enl 1 (j - 1) (center (j - 1) x) at hy
  rw [enl_eq_of_mem (center_mem_cube (j - 1) x)] at hy
  exact isInterior_of_mem_enl_pred hj1 hj hx hy

/-- The triples of the cells lie in `V`. -/
theorem midCells_enl_subset {V : TriadicCube 2} {j : ℕ} (hj1 : 1 ≤ j) (hj : j < V.scale)
    {c : ℕ × Vertex 2} (hc : c ∈ midCells V j) : enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices :=
  fun y hy => (V.mem_toIntegerCube_vertices y).2
    (midCells_isInterior hj1 hj hc hy y fun i => by simp)

/-- The cells have scale `j - 1`. -/
theorem fst_of_mem_midCells {V : TriadicCube 2} {j : ℕ} {c : ℕ × Vertex 2}
    (hc : c ∈ midCells V j) : c.1 = j - 1 := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hc
  rfl

/-- Every vertex lies in at most `9` of the triples of the cells. -/
theorem card_midCells_filter_le (V : TriadicCube 2) (j : ℕ) (x : Vertex 2) :
    ((midCells V j).filter fun c => x ∈ enl 1 c.1 c.2).card ≤ 9 := by
  set k := j - 1 with hkdef
  set E : Finset (Fin 2 → ℤ) := Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ) with hE
  have hEcard : E.card = 9 := by
    rw [hE, Fintype.card_piFinset]
    simp
  have h1 := two_mul_halfSide_add_one k
  have h2 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have hh := halfSide_nonneg k
  have hsub : ((midCells V j).filter fun c => x ∈ enl 1 c.1 c.2) ⊆
      E.image fun e => (k, fun i => center k x i + 3 ^ k * e i) := by
    intro c hc
    obtain ⟨hcI, hxc⟩ := Finset.mem_filter.1 hc
    obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hcI
    rw [Finset.mem_image]
    refine ⟨fun i => idx k x' i - idx k x i, ?_, ?_⟩
    · rw [hE, Fintype.mem_piFinset]
      intro i
      change x ∈ enl 1 k (center k x') at hxc
      rw [enl, mem_box] at hxc
      have hxi := hxc i
      have hxx := (mem_box.1 (show x ∈ cube k x from mem_cube_self k x)) i
      have hc1 : center k (center k x') = center k x' := by
        rw [center_eq_of_mem (center_mem_cube k x')]
      rw [hc1] at hxi
      have e1 : center k x' i = 3 ^ k * idx k x' i := rfl
      have e2 : center k x i = 3 ^ k * idx k x i := rfl
      rw [e1] at hxi
      rw [e2] at hxx
      set P : ℤ := 3 ^ k with hP
      have hPpos : 0 < P := by positivity
      have hlt : |P * (idx k x' i - idx k x i)| < 2 * P := by
        rw [mul_sub]
        rw [abs_le] at hxi hxx
        rw [abs_lt]
        constructor <;> linarith
      rw [abs_mul, abs_of_pos hPpos] at hlt
      have hlt' : |idx k x' i - idx k x i| < 2 := by
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
  calc ((midCells V j).filter fun c => x ∈ enl 1 c.1 c.2).card
      ≤ (E.image fun e => (k, fun i => center k x i + 3 ^ k * e i)).card :=
        Finset.card_le_card hsub
    _ ≤ E.card := Finset.card_image_le
    _ = 9 := hEcard

end Rigidity.Proofs.Cluster
