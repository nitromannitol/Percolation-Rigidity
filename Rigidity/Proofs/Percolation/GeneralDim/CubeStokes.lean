import Rigidity.Proofs.Percolation.GeneralDim.CubeSubcubes

/-!
# The discrete Stokes formula on integer cubes of `ℤ^d`

For an integer cube `R` of side `L` and a direction `i`, the sum of the increments
`f(x + e_i) - f(x)` over the lattice edges of `R` in direction `i` telescopes to the difference of
the sums of `f` over the upper and lower faces of `R` in direction `i`. For an affine function
`x ↦ p · x + c` the increments are all equal to `p_i`, and there are `L^{d-1} (L - 1)` such edges.
Consequently the coarse pairing `ℓ_q u` of a function on the cluster of a triadic cube is a sum of
the coarsened values over the faces of the cube.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

theorem unit_apply_self (i : Fin d) : LatticeProb.unit i i = (1 : ℤ) := by
  simp [LatticeProb.unit]

theorem unit_apply_ne {i j : Fin d} (h : j ≠ i) : LatticeProb.unit i j = (0 : ℤ) := by
  simp [LatticeProb.unit, h]

/-- The lattice edges of an integer cube in direction `i`, by their lower endpoint. -/
noncomputable def IntegerCube.edgeStartsIn (R : IntegerCube d) (i : Fin d) : Finset (Vertex d) :=
  R.vertices.filter fun x => x + LatticeProb.unit i ∈ R.vertices

theorem IntegerCube.mem_edgeStartsIn {R : IntegerCube d} {i : Fin d} {x : Vertex d} :
    x ∈ R.edgeStartsIn i ↔ x ∈ R.vertices ∧ x i + 1 < R.corner i + (R.size : ℤ) := by
  unfold IntegerCube.edgeStartsIn
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have := ((IntegerCube.mem_vertices _ _).1 hx' i).2
    simpa [unit_apply_self] using this
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    rw [IntegerCube.mem_vertices] at hx ⊢
    intro j
    by_cases hj : j = i
    · subst hj
      have := hx j
      simp only [Pi.add_apply, unit_apply_self]
      constructor <;> omega
    · simp only [Pi.add_apply, unit_apply_ne hj, add_zero]
      exact hx j

/-- **Discrete Stokes formula.** -/
theorem IntegerCube.sum_edgeStartsIn_sub (R : IntegerCube d) (i : Fin d) (f : Vertex d → ℝ) :
    ∑ x ∈ R.edgeStartsIn i, (f (x + LatticeProb.unit i) - f x) =
      ∑ x ∈ R.upperFace i, f x - ∑ x ∈ R.lowerFace i, f x := by
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ x ∈ R.edgeStartsIn i, f x =
      ∑ x ∈ R.vertices, f x - ∑ x ∈ R.upperFace i, f x := by
    rw [eq_sub_iff_add_eq, IntegerCube.upperFace, IntegerCube.edgeStartsIn]
    rw [← Finset.sum_filter_add_sum_filter_not R.vertices
      (fun x => x + LatticeProb.unit i ∈ R.vertices)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hx'⟩
      refine ⟨hx, fun h' => ?_⟩
      have := (IntegerCube.mem_edgeStartsIn (R := R) (i := i)).1 (Finset.mem_filter.2 ⟨hx, h'⟩)
      omega
    · rintro ⟨hx, hx'⟩
      refine ⟨hx, ?_⟩
      have h := ((IntegerCube.mem_vertices _ _).1 hx i).2
      by_contra hne
      exact hx' (Finset.mem_filter.1
        ((IntegerCube.mem_edgeStartsIn (R := R) (i := i)).2 ⟨hx, by omega⟩)).2
  have h2 : ∑ x ∈ R.edgeStartsIn i, f (x + LatticeProb.unit i) =
      ∑ x ∈ R.vertices, f x - ∑ x ∈ R.lowerFace i, f x := by
    rw [eq_sub_iff_add_eq, IntegerCube.lowerFace]
    rw [← Finset.sum_filter_add_sum_filter_not R.vertices (fun x => x i = R.corner i)]
    rw [add_comm]
    congr 1
    refine Finset.sum_nbij' (fun x => x + LatticeProb.unit i) (fun y => y - LatticeProb.unit i)
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxR, hxi⟩ := (IntegerCube.mem_edgeStartsIn (R := R) (i := i)).1 hx
      simp only [Finset.mem_filter]
      refine ⟨(Finset.mem_filter.1 hx).2, ?_⟩
      have := ((IntegerCube.mem_vertices _ _).1 hxR i).1
      simp only [Pi.add_apply, unit_apply_self]
      omega
    · intro y hy
      obtain ⟨hyR, hyi⟩ := Finset.mem_filter.1 hy
      rw [IntegerCube.mem_edgeStartsIn]
      have hy' := (IntegerCube.mem_vertices _ _).1 hyR
      refine ⟨?_, ?_⟩
      · rw [IntegerCube.mem_vertices]
        intro j
        by_cases hj : j = i
        · subst hj
          have := hy' j
          simp only [Pi.sub_apply, unit_apply_self]
          constructor <;> omega
        · simp only [Pi.sub_apply, unit_apply_ne hj, sub_zero]
          exact hy' j
      · have := hy' i
        simp only [Pi.sub_apply, unit_apply_self]
        omega
    · intro x _
      simp
    · intro y _
      simp
    · intro x _
      rfl
  rw [h1, h2]
  ring

/-- The number of lattice edges of an integer cube in a given direction. -/
theorem IntegerCube.card_edgeStartsIn (R : IntegerCube d) (i : Fin d) :
    (R.edgeStartsIn i).card = R.size ^ (d - 1) * (R.size - 1) := by
  have h : R.edgeStartsIn i = Fintype.piFinset fun j =>
      if j = i then Finset.Ico (R.corner j) (R.corner j + R.size - 1)
      else Finset.Ico (R.corner j) (R.corner j + R.size) := by
    ext x
    rw [IntegerCube.mem_edgeStartsIn, IntegerCube.mem_vertices, Fintype.mem_piFinset]
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
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    if_pos rfl, Int.card_Ico]
  have hrest : ∏ j ∈ Finset.univ.erase i, (if j = i then Finset.Ico (R.corner j)
      (R.corner j + R.size - 1) else Finset.Ico (R.corner j) (R.corner j + R.size)).card =
      ∏ _j ∈ Finset.univ.erase i, R.size := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj), Int.card_Ico]
    omega
  rw [hrest, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, mul_comm]
  congr 1
  omega

theorem IntegerCube.cast_card_edgeStartsIn (R : IntegerCube d) (hR : 0 < R.size) (i : Fin d) :
    ((R.edgeStartsIn i).card : ℝ) = (R.size : ℝ) ^ (d - 1) * ((R.size : ℝ) - 1) := by
  rw [R.card_edgeStartsIn i]
  push_cast [Nat.cast_sub (show 1 ≤ R.size by omega)]
  ring

/-- The affine function `x ↦ p · x + c` increases by `p_i` along a lattice edge in direction `i`. -/
theorem sum_mul_add_unit_sub (p : Fin d → ℝ) (c : ℝ) (x : Vertex d) (i : Fin d) :
    (∑ j, p j * ((x + LatticeProb.unit i) j : ℝ) + c) - (∑ j, p j * (x j : ℝ) + c) = p i := by
  have e : ∀ j, p j * ((x + LatticeProb.unit i) j : ℝ) =
      p j * (x j : ℝ) + if j = i then p j else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, unit_apply_self, Int.cast_add, Int.cast_one, if_true]
      ring
    · simp only [Pi.add_apply, unit_apply_ne hj, add_zero, hj, if_false]
  simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- **Stokes formula for affine functions.** -/
theorem IntegerCube.sum_face_affine_eq_mul_card (R : IntegerCube d) (i : Fin d) (p : Fin d → ℝ) (c : ℝ) :
    ∑ x ∈ R.upperFace i, (∑ j, p j * (x j : ℝ) + c) -
        ∑ x ∈ R.lowerFace i, (∑ j, p j * (x j : ℝ) + c) =
      p i * ((R.edgeStartsIn i).card : ℝ) := by
  rw [← R.sum_edgeStartsIn_sub i]
  simp only [sum_mul_add_unit_sub, Finset.sum_const, nsmul_eq_mul]
  ring

variable {ω : Configuration d}

/-- The coarse pairing as a sum over the faces of `U`. -/
theorem cubeCoarsePairing_eq_faces {U : TriadicCube d} (q : Fin d → ℝ) (u : CubeFun ω U) :
    cubeCoarsePairing ω U q u = ∑ i, q i *
      (∑ x ∈ U.toIntegerCube.upperFace i, cubeCoarsen ω U u x -
        ∑ x ∈ U.toIntegerCube.lowerFace i, cubeCoarsen ω U u x) := by
  rw [cubeCoarsePairing_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← IntegerCube.sum_edgeStartsIn_sub, Finset.mul_sum, IntegerCube.edgeStartsIn,
    Finset.sum_filter]
  rfl

end Rigidity.Percolation
