import Rigidity.Proofs.Smoothing.GaussianSlice

/-!
# Fibers of an integer lattice coordinate

When a lattice contains a vector pairing to one with `b`, every integer fiber of the pairing is a
translate of the zero fiber. This identifies the slices in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- The sublattice pairing to zero with a fixed vector. -/
noncomputable def orthogonalLattice {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (b : E) : Submodule ℤ E :=
  L ⊓ (LinearMap.ker ((innerₗ E).flip b)).restrictScalars ℤ

/-- Membership in the orthogonal sublattice is lattice membership and zero pairing. -/
theorem mem_orthogonalLattice {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (b y : E) :
    y ∈ orthogonalLattice L b ↔ y ∈ L ∧ inner ℝ y b = 0 := by
  change y ∈ L ∧ ((innerₗ E).flip b) y = 0 ↔ y ∈ L ∧ inner ℝ y b = 0
  rfl

/-- Every integer pairing fiber is a translate of the orthogonal sublattice. -/
def latticeFiberEquiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (b : E) (v : L) (hv : inner ℝ (v : E) b = 1) (n : ℤ) :
    orthogonalLattice L b ≃ {y : L // inner ℝ (y : E) b = (n : ℝ)} where
  toFun k := ⟨⟨n • (v : E) + (k : E), L.add_mem (L.smul_mem n v.2)
      ((mem_orthogonalLattice L b _).mp k.2).1⟩, by
    rw [inner_add_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hv,
      ((mem_orthogonalLattice L b _).mp k.2).2]
    simp only [mul_one, add_zero]⟩
  invFun y := ⟨(y.1 : E) - n • (v : E), (mem_orthogonalLattice L b _).mpr
    ⟨L.sub_mem y.1.2 (L.smul_mem n v.2), by
      rw [inner_sub_left, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hv, y.2]
      simp only [mul_one, sub_self]⟩⟩
  left_inv k := by
    apply Subtype.ext
    simp only
    abel
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simp only
    abel

/-- The orthogonal sublattice of a discrete lattice is discrete. -/
theorem discreteTopology_orthogonalLattice {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] (b : E) :
    DiscreteTopology (orthogonalLattice L b) := by
  let f : orthogonalLattice L b → L := fun k =>
    ⟨k, ((mem_orthogonalLattice L b _).mp k.2).1⟩
  have hf : Continuous f := by fun_prop
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : L => (z : E)) h

end Rigidity.Smoothing
