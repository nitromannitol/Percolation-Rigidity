import Rigidity.Percolation.BondContactSymmetry

/-!
# Signed coordinate symmetries

Permuting coordinates and changing their signs preserves lattice distance and
centered cubes. These symmetries act on the Bernoulli bond model.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External

/-- Independently reverse the signs of the indicated coordinates. -/
def coordinateSignFlip {d : ℕ} (s : Fin d → Bool) : Vertex d ≃ Vertex d where
  toFun x i := if s i then -(x i) else x i
  invFun x i := if s i then -(x i) else x i
  left_inv x := by
    funext i
    cases h : s i <;> simp only [h, Bool.false_eq_true, ↓reduceIte, neg_neg]
  right_inv x := by
    funext i
    cases h : s i <;> simp only [h, Bool.false_eq_true, ↓reduceIte, neg_neg]

/-- Changing coordinate signs preserves the lattice distance. -/
theorem latticeL1Dist_coordinateSignFlip {d : ℕ} (s : Fin d → Bool) (x y : Vertex d) :
    latticeL1Dist (coordinateSignFlip s x) (coordinateSignFlip s y) = latticeL1Dist x y := by
  unfold latticeL1Dist
  apply Finset.sum_congr rfl
  intro i _
  change |(if s i then -(x i) else x i) - (if s i then -(y i) else y i)| = _
  cases h : s i
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    rw [show -(x i) - -(y i) = -(x i - y i) by ring, abs_neg]

/-- Permute the coordinate positions of a lattice vertex. -/
def coordinatePermutation {d : ℕ} (σ : Equiv.Perm (Fin d)) : Vertex d ≃ Vertex d where
  toFun x i := x (σ i)
  invFun x i := x (σ.symm i)
  left_inv x := by funext i; simp only [Equiv.apply_symm_apply]
  right_inv x := by funext i; simp only [Equiv.symm_apply_apply]

/-- Coordinate permutations preserve the lattice distance. -/
theorem latticeL1Dist_coordinatePermutation {d : ℕ} (σ : Equiv.Perm (Fin d))
    (x y : Vertex d) :
    latticeL1Dist (coordinatePermutation σ x) (coordinatePermutation σ y) = latticeL1Dist x y := by
  change (∑ i, |x (σ i) - y (σ i)|) = ∑ i, |x i - y i|
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- A signed permutation of the lattice coordinates. -/
def signedCoordinateEquiv {d : ℕ} (σ : Equiv.Perm (Fin d)) (s : Fin d → Bool) :
    Vertex d ≃ Vertex d :=
  (coordinatePermutation σ).trans (coordinateSignFlip s)

/-- Signed coordinate permutations preserve the lattice distance. -/
theorem latticeL1Dist_signedCoordinateEquiv {d : ℕ} (σ : Equiv.Perm (Fin d))
    (s : Fin d → Bool) (x y : Vertex d) :
    latticeL1Dist (signedCoordinateEquiv σ s x) (signedCoordinateEquiv σ s y) =
      latticeL1Dist x y := by
  exact (latticeL1Dist_coordinateSignFlip s _ _).trans
    (latticeL1Dist_coordinatePermutation σ x y)

/-- Each coordinate absolute value is preserved up to permutation. -/
theorem abs_signedCoordinateEquiv_apply {d : ℕ} (σ : Equiv.Perm (Fin d))
    (s : Fin d → Bool) (x : Vertex d) (i : Fin d) :
    |signedCoordinateEquiv σ s x i| = |x (σ i)| := by
  change |if s i then -(x (σ i)) else x (σ i)| = _
  cases h : s i <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_neg]

/-- A signed coordinate permutation preserves a centered cube. -/
theorem signedCoordinateEquiv_image_centeredBondCube {d : ℕ} (σ : Equiv.Perm (Fin d))
    (s : Fin d → Bool) (n : ℕ) :
    signedCoordinateEquiv σ s '' centeredBondCube n = centeredBondCube n := by
  have hmem (x : Vertex d) : signedCoordinateEquiv σ s x ∈ centeredBondCube n ↔
      x ∈ centeredBondCube n := by
    simp only [mem_centeredBondCube, abs_signedCoordinateEquiv_apply]
    constructor
    · intro h i
      simpa only [Equiv.apply_symm_apply] using h (σ.symm i)
    · intro h i
      exact h (σ i)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hmem y).mpr hy
  · intro hx
    refine ⟨(signedCoordinateEquiv σ s).symm x, ?_, Equiv.apply_symm_apply _ _⟩
    apply (hmem _).mp
    rwa [Equiv.apply_symm_apply]

end Rigidity.Percolation
