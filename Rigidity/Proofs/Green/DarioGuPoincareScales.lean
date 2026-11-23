import Rigidity.Proofs.Green.DarioGuPoincareBall

/-!
# The triple of a triadic cube and its nine subcubes

Ingredients of the probabilistic part of the weak Poincaré inequality on balls of the planar
infinite cluster (`ClusterPoincareTwo`): the triple `enl 1 m y` of the triadic cube of scale `m`
containing `y` is covered by the nine triadic cubes of scale `m` whose index is within `1` of that
of `y` (`idx_sub_le_of_mem_enl`), so a sum of a nonnegative function over the triple is at most the
sum of its sums over these nine cubes (`sum_enl_le_sum_cubes`).
-/

open Finset LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster

namespace Rigidity.Green

/-- The vertices of the triple `enl 1 m y` lie in the triadic cubes of scale `m` whose index is
within `1` of that of `y`. -/
theorem idx_sub_le_of_mem_enl {m : ℕ} {y z : Vertex 2} (hz : z ∈ enl 1 m y) (i : Fin 2) :
    |idx m z i - idx m y i| ≤ 1 := by
  rw [enl, mem_box] at hz
  have h1 := hz i
  have hh := two_mul_halfSide_add_one m
  have hs : halfSide (m + 1) = 3 * halfSide m + 1 := rfl
  have hP : (0 : ℤ) < 3 ^ m := by positivity
  have hc : center m y i = 3 ^ m * idx m y i := rfl
  rw [abs_le] at h1 ⊢
  set a := idx m y i
  have hlo : (a - 1) * 3 ^ m ≤ z i + halfSide m := by
    have e : (a - 1) * 3 ^ m = 3 ^ m * a - 3 ^ m := by ring
    linarith [h1.1]
  have hhi : z i + halfSide m < (a + 2) * 3 ^ m := by
    have e : (a + 2) * 3 ^ m = 3 ^ m * a + 2 * 3 ^ m := by ring
    linarith [h1.2]
  have g1 : a - 1 ≤ idx m z i := (Int.le_ediv_iff_mul_le hP).2 hlo
  have g2 : idx m z i < a + 2 := (Int.ediv_lt_iff_lt_mul hP).2 hhi
  constructor <;> linarith

/-- The sum of a nonnegative function over a union is at most the sum of its sums. -/
theorem sum_biUnion_le_sum_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (T : ι → Finset (Vertex 2)) {f : Vertex 2 → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ s.biUnion T, f z ≤ ∑ i ∈ s, ∑ z ∈ T i, f z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := T a) (s₂ := s.biUnion T) (f := f)
    have h0 : 0 ≤ ∑ z ∈ T a ∩ s.biUnion T, f z := Finset.sum_nonneg fun z _ => hf z
    linarith

/-- A vertex lies in the triadic cube of scale `m` of its own index. -/
theorem mem_triadicCube_idx_self (m : ℕ) (z : Vertex 2) :
    z ∈ (⟨m, idx m z⟩ : TriadicCube 2).toIntegerCube.vertices := by
  rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
  exact mem_cube_self m z

/-- **The nine subcubes of the triple.** For `f ≥ 0`,
`Σ_{z ∈ enl 1 m y} f(z) ≤ Σ_{|e - idx_m(y)| ≤ 1} Σ_{z ∈ □_m(e)} f(z)`. -/
theorem sum_enl_le_sum_cubes (m : ℕ) (y : Vertex 2) {f : Vertex 2 → ℝ} (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ enl 1 m y, f z ≤
      ∑ e ∈ indexBox (idx m y) 1, ∑ z ∈ (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices, f z := by
  classical
  have hsub : enl 1 m y ⊆ (indexBox (idx m y) 1).biUnion
      (fun e => (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices) := by
    intro z hz
    rw [Finset.mem_biUnion]
    exact ⟨idx m z, mem_indexBox.2 fun i => idx_sub_le_of_mem_enl hz i,
      mem_triadicCube_idx_self m z⟩
  calc ∑ z ∈ enl 1 m y, f z
      ≤ ∑ z ∈ (indexBox (idx m y) 1).biUnion
          (fun e => (⟨m, e⟩ : TriadicCube 2).toIntegerCube.vertices), f z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => hf z
    _ ≤ _ := sum_biUnion_le_sum_sum _ _ hf

theorem card_indexBox_one (c : Vertex 2) : (indexBox c 1).card = 9 := by
  have := card_indexBox c (R := 1)
  simpa using this

end Rigidity.Green
