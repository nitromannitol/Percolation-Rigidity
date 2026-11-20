import Rigidity.Proofs.Percolation.PlanarMuUpperBound

/-!
# The discrete Stokes formula on integer squares

For an integer square `R` and a direction `i`, the sum of the increments `f(x + e_i) - f(x)` over
the lattice edges of `R` in direction `i` telescopes to the difference of the sums of `f` over the
upper and lower faces of `R` in direction `i`. For an affine function `x ↦ p · x` the increments
are all equal to `p_i`, and there are `L (L - 1)` such edges, `L` being the side of `R`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

theorem unitVertex_apply_self (i : Fin 2) : unitVertex i i = 1 := by
  simp [unitVertex]

theorem unitVertex_apply_ne {i j : Fin 2} (h : j ≠ i) : unitVertex i j = 0 := by
  simp [unitVertex, h]

/-- The lattice edges of an integer square in direction `i`, by their lower endpoint. -/
noncomputable def IntegerCube.edgeStarts (R : IntegerCube 2) (i : Fin 2) : Finset (Vertex 2) :=
  R.vertices.filter fun x => x + unitVertex i ∈ R.vertices

theorem IntegerCube.mem_edgeStarts {R : IntegerCube 2} {i : Fin 2} {x : Vertex 2} :
    x ∈ R.edgeStarts i ↔ x ∈ R.vertices ∧ x i + 1 < R.corner i + (R.size : ℤ) := by
  unfold IntegerCube.edgeStarts
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have := ((IntegerCube.mem_vertices _ _).1 hx' i).2
    simpa [unitVertex_apply_self] using this
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rw [IntegerCube.mem_vertices] at hx ⊢
    intro j
    by_cases hj : j = i
    · subst hj
      have := hx j
      simp only [Pi.add_apply, unitVertex_apply_self]
      constructor <;> omega
    · simp only [Pi.add_apply, unitVertex_apply_ne hj, add_zero]
      exact hx j

/-- **Discrete Stokes formula.** -/
theorem IntegerCube.sum_edgeStarts_sub (R : IntegerCube 2) (i : Fin 2) (f : Vertex 2 → ℝ) :
    ∑ x ∈ R.edgeStarts i, (f (x + unitVertex i) - f x) =
      ∑ x ∈ R.upperFace i, f x - ∑ x ∈ R.lowerFace i, f x := by
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ x ∈ R.edgeStarts i, f x = ∑ x ∈ R.vertices, f x - ∑ x ∈ R.upperFace i, f x := by
    rw [eq_sub_iff_add_eq, IntegerCube.upperFace, IntegerCube.edgeStarts]
    rw [← Finset.sum_filter_add_sum_filter_not R.vertices
      (fun x => x + unitVertex i ∈ R.vertices)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hx'⟩
      refine ⟨hx, fun h' => ?_⟩
      have := (IntegerCube.mem_edgeStarts (R := R) (i := i)).1 (Finset.mem_filter.2 ⟨hx, h'⟩)
      omega
    · rintro ⟨hx, hx'⟩
      refine ⟨hx, ?_⟩
      have h := ((IntegerCube.mem_vertices _ _).1 hx i).2
      by_contra hne
      exact hx' (Finset.mem_filter.1
        ((IntegerCube.mem_edgeStarts (R := R) (i := i)).2 ⟨hx, by omega⟩)).2
  have h2 : ∑ x ∈ R.edgeStarts i, f (x + unitVertex i) =
      ∑ x ∈ R.vertices, f x - ∑ x ∈ R.lowerFace i, f x := by
    rw [eq_sub_iff_add_eq, IntegerCube.lowerFace]
    rw [← Finset.sum_filter_add_sum_filter_not R.vertices (fun x => x i = R.corner i)]
    rw [add_comm]
    congr 1
    refine Finset.sum_nbij' (fun x => x + unitVertex i) (fun y => y - unitVertex i) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxR, hxi⟩ := (IntegerCube.mem_edgeStarts (R := R) (i := i)).1 hx
      simp only [Finset.mem_filter]
      refine ⟨(Finset.mem_filter.1 hx).2, ?_⟩
      have := ((IntegerCube.mem_vertices _ _).1 hxR i).1
      simp only [Pi.add_apply, unitVertex_apply_self]
      omega
    · intro y hy
      obtain ⟨hyR, hyi⟩ := Finset.mem_filter.1 hy
      rw [IntegerCube.mem_edgeStarts]
      have hy' := (IntegerCube.mem_vertices _ _).1 hyR
      refine ⟨?_, ?_⟩
      · rw [IntegerCube.mem_vertices]
        intro j
        by_cases hj : j = i
        · subst hj
          have := hy' j
          simp only [Pi.sub_apply, unitVertex_apply_self]
          constructor <;> omega
        · simp only [Pi.sub_apply, unitVertex_apply_ne hj, sub_zero]
          exact hy' j
      · have := hy' i
        simp only [Pi.sub_apply, unitVertex_apply_self]
        omega
    · intro x _
      simp
    · intro y _
      simp
    · intro x _
      rfl
  rw [h1, h2]
  ring

/-- The number of lattice edges of an integer square in a given direction. -/
theorem IntegerCube.card_edgeStarts (R : IntegerCube 2) (i : Fin 2) :
    ((R.edgeStarts i).card : ℝ) = (R.size : ℝ) * ((R.size : ℝ) - 1) := by
  have h : R.edgeStarts i = Fintype.piFinset fun j =>
      if j = i then Finset.Ico (R.corner j) (R.corner j + R.size - 1)
      else Finset.Ico (R.corner j) (R.corner j + R.size) := by
    ext x
    rw [IntegerCube.mem_edgeStarts, IntegerCube.mem_vertices, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hx, hxi⟩ j
      by_cases hj : j = i
      · subst hj
        simp only [if_true, Finset.mem_Ico]
        have := hx j
        constructor <;> omega
      · simp only [hj, if_false, Finset.mem_Ico]
        exact hx j
    · intro h
      have hi := h i
      simp only [if_true, Finset.mem_Ico] at hi
      refine ⟨fun j => ?_, by omega⟩
      by_cases hj : j = i
      · subst hj
        constructor <;> omega
      · have := h j
        simp only [hj, if_false, Finset.mem_Ico] at this
        exact this
  rw [h, Fintype.card_piFinset, Fin.prod_univ_two]
  rcases Nat.eq_zero_or_pos R.size with hs | hs
  · fin_cases i <;> simp [hs]
  · fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, if_true, one_ne_zero,
      zero_ne_one, if_false, Int.card_Ico] <;> push_cast <;>
      rw [show R.corner _ + (R.size : ℤ) - 1 - R.corner _ = (R.size : ℤ) - 1 by ring,
        show R.corner _ + (R.size : ℤ) - R.corner _ = (R.size : ℤ) by ring] <;>
      rw [Int.toNat_natCast] <;>
      rw [show ((R.size : ℤ) - 1).toNat = R.size - 1 by omega] <;>
      push_cast [Nat.cast_sub (show 1 ≤ R.size by omega)] <;> ring

/-- **Stokes formula for affine functions.** -/
theorem IntegerCube.sum_face_affine (R : IntegerCube 2) (i : Fin 2) (p : Fin 2 → ℝ) (c : ℝ) :
    ∑ x ∈ R.upperFace i, (∑ j, p j * (x j : ℝ) + c) -
        ∑ x ∈ R.lowerFace i, (∑ j, p j * (x j : ℝ) + c) =
      p i * ((R.size : ℝ) * ((R.size : ℝ) - 1)) := by
  rw [← R.sum_edgeStarts_sub i, ← R.card_edgeStarts i]
  have : ∀ x : Vertex 2, (∑ j, p j * ((x + unitVertex i) j : ℝ) + c) -
      (∑ j, p j * (x j : ℝ) + c) = p i := by
    intro x
    simp only [Fin.sum_univ_two, Pi.add_apply, Int.cast_add]
    fin_cases i <;> simp [unitVertex] <;> ring
  simp only [this, Finset.sum_const, nsmul_eq_mul]
  ring

end Rigidity.Percolation
