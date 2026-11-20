import Rigidity.Percolation.SignedCoordinateSymmetry

/-!
# Orthant faces of centered cubes

The boundary of a centered lattice cube is covered by faces indexed by a
coordinate and a choice of signs. This cover is adapted to signed coordinate
symmetries and to finite positive-association estimates.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- The portion of a centered cube face in a specified closed orthant. -/
noncomputable def centeredCubeOrthantFace {d : ℕ} (n : ℕ)
    (i : Fin d) (s : Fin d → Bool) : Finset (Vertex d) := by
  classical
  exact (centeredBondCubeBoundary n).filter fun x =>
    x i = (if s i then (n : ℤ) else -(n : ℤ)) ∧
      ∀ j, if s j then 0 ≤ x j else x j ≤ 0

/-- Membership in an orthant face specifies a boundary vertex, its extremal
coordinate and its coordinate signs. -/
theorem mem_centeredCubeOrthantFace {d : ℕ} (n : ℕ)
    (i : Fin d) (s : Fin d → Bool) (x : Vertex d) :
    x ∈ centeredCubeOrthantFace n i s ↔
      x ∈ centeredBondCubeBoundary n ∧
        x i = (if s i then (n : ℤ) else -(n : ℤ)) ∧
          ∀ j, if s j then 0 ≤ x j else x j ≤ 0 := by
  classical
  simp only [centeredCubeOrthantFace, Finset.mem_filter]

/-- Every boundary vertex belongs to an orthant face. -/
theorem centeredBondCubeBoundary_subset_biUnion_orthantFace {d : ℕ} (n : ℕ) :
    centeredBondCubeBoundary (d := d) n ⊆
      Finset.univ.biUnion (fun a : Fin d × (Fin d → Bool) =>
        centeredCubeOrthantFace n a.1 a.2) := by
  classical
  intro x hx
  obtain ⟨_, i, hi⟩ := (mem_centeredBondCubeBoundary n x).mp hx
  let s : Fin d → Bool := fun j => decide (0 ≤ x j)
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨i, s⟩, Finset.mem_univ _, (mem_centeredCubeOrthantFace n i s x).mpr ⟨hx, ?_, ?_⟩⟩
  · dsimp only [s]
    by_cases h : 0 ≤ x i
    · simp only [h, decide_true, ↓reduceIte]
      rw [abs_of_nonneg h] at hi
      exact hi
    · have hle : x i ≤ 0 := le_of_not_ge h
      simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [abs_of_nonpos hle] at hi
      omega
  · intro j
    dsimp only [s]
    by_cases h : 0 ≤ x j
    · simp only [h, decide_true, ↓reduceIte]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact le_of_not_ge h

/-- Signed permutations preserve membership in the boundary of a centered cube. -/
theorem mem_centeredBondCubeBoundary_signedCoordinateEquiv_iff {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (n : ℕ) (x : Vertex d) :
    signedCoordinateEquiv σ s x ∈ centeredBondCubeBoundary n ↔
      x ∈ centeredBondCubeBoundary n := by
  rw [mem_centeredBondCubeBoundary, mem_centeredBondCubeBoundary]
  have hc : signedCoordinateEquiv σ s x ∈ centeredBondCube n ↔ x ∈ centeredBondCube n := by
    rw [mem_centeredBondCube, mem_centeredBondCube]
    simp only [abs_signedCoordinateEquiv_apply]
    constructor
    · intro h i
      simpa only [Equiv.apply_symm_apply] using h (σ.symm i)
    · intro h i
      exact h (σ i)
  rw [hc]
  simp only [abs_signedCoordinateEquiv_apply]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨h, σ i, hi⟩
  · rintro ⟨h, i, hi⟩
    exact ⟨h, σ.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

/-- A signed permutation carries a positive-orthant face to a prescribed
orthant face, with the coordinate normal transformed by the permutation. -/
theorem mem_centeredCubeOrthantFace_signedCoordinateEquiv_iff {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (n : ℕ) (i : Fin d)
    (x : Vertex d) :
    signedCoordinateEquiv σ (fun j => !s j) x ∈ centeredCubeOrthantFace n i s ↔
      x ∈ centeredCubeOrthantFace n (σ i) (fun _ => true) := by
  rw [mem_centeredCubeOrthantFace, mem_centeredCubeOrthantFace,
    mem_centeredBondCubeBoundary_signedCoordinateEquiv_iff]
  have hext : signedCoordinateEquiv σ (fun j => !s j) x i =
      (if s i then (n : ℤ) else -(n : ℤ)) ↔ x (σ i) = (n : ℤ) := by
    change (if !s i then -(x (σ i)) else x (σ i)) = _ ↔ _
    cases h : s i <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    omega
  have hsign : (∀ j, if s j then 0 ≤ signedCoordinateEquiv σ (fun j => !s j) x j
      else signedCoordinateEquiv σ (fun j => !s j) x j ≤ 0) ↔ ∀ j, 0 ≤ x j := by
    have hp (j : Fin d) : (if s j then 0 ≤ signedCoordinateEquiv σ (fun k => !s k) x j
        else signedCoordinateEquiv σ (fun k => !s k) x j ≤ 0) ↔ 0 ≤ x (σ j) := by
      change (if s j then 0 ≤ (if !s j then -(x (σ j)) else x (σ j))
        else (if !s j then -(x (σ j)) else x (σ j)) ≤ 0) ↔ _
      cases h : s j <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      omega
    simp only [hp]
    constructor
    · intro h j
      simpa only [Equiv.apply_symm_apply] using h (σ.symm j)
    · intro h j
      exact h (σ j)
  simp only [hext, hsign, ↓reduceIte]

/-- A signed permutation maps the positive-orthant face onto the chosen
orthant face. -/
theorem image_centeredCubeOrthantFace_signedCoordinateEquiv {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (s : Fin d → Bool) (n : ℕ) (i : Fin d) :
    (centeredCubeOrthantFace n (σ i) (fun _ => true)).image
        (signedCoordinateEquiv σ (fun j => !s j)) = centeredCubeOrthantFace n i s := by
  classical
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_centeredCubeOrthantFace_signedCoordinateEquiv_iff σ s n i y).mpr hy
  · intro hx
    let f := signedCoordinateEquiv σ (fun j => !s j)
    refine Finset.mem_image.mpr ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    apply (mem_centeredCubeOrthantFace_signedCoordinateEquiv_iff σ s n i (f.symm x)).mp
    simpa only [f, Equiv.apply_symm_apply] using hx

end Rigidity.Percolation
