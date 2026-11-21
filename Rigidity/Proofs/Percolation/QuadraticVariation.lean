import Mathlib

/-!
# Minimizers of quadratic functionals

Let `B` be a symmetric positive semidefinite bilinear form on a finite-dimensional real vector
space and `ℓ` a linear functional vanishing on the null space of `B`. Then the quadratic functional
`w ↦ B w w / 2 - ℓ w` attains its minimum, at every `u` solving the first-variation equation
`B w u = ℓ w` for all `w`, and the excess over the minimum is `B (w - u) (w - u) / 2`.

These are the first and second variations used for the subadditive energy quantities of
Armstrong and Dario (Lemma 4.2).
-/

namespace LinearMap.BilinForm

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- **Solvability of the first-variation equation.** -/
theorem exists_apply_eq_of_symm [FiniteDimensional ℝ A] (B : LinearMap.BilinForm ℝ A)
    (hB : ∀ u w, B u w = B w u) (ℓ : Module.Dual ℝ A)
    (hℓ : ∀ u, (∀ w, B w u = 0) → ℓ u = 0) :
    ∃ u, ∀ w, B w u = ℓ w := by
  set T : A →ₗ[ℝ] Module.Dual ℝ A := B.flip with hT
  have hTapply : ∀ u w, T u w = B w u := fun u w => rfl
  have hrange : LinearMap.range T = LinearMap.range T.dualMap := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      refine ⟨Module.Dual.eval ℝ A u, ?_⟩
      ext w
      simp only [LinearMap.dualMap_apply, Module.Dual.eval_apply, hTapply]
      exact hB u w
    · rintro _ ⟨φ, rfl⟩
      obtain ⟨u, rfl⟩ := (Module.evalEquiv ℝ A).surjective φ
      refine ⟨u, ?_⟩
      ext w
      simp only [LinearMap.dualMap_apply, Module.evalEquiv_apply, Module.Dual.eval_apply,
        hTapply]
      exact hB w u
  have hmem : ℓ ∈ (LinearMap.ker T).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro u hu
    apply hℓ u
    intro w
    have h := LinearMap.congr_fun (LinearMap.mem_ker.1 hu) w
    rw [hTapply] at h
    simpa using h
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← hrange] at hmem
  obtain ⟨u, hu⟩ := hmem
  exact ⟨u, fun w => by rw [← hu, hTapply]⟩

/-- **Second variation.** If `u` solves the first-variation equation, the quadratic functional
exceeds its value at `u` by half the form evaluated on the difference. -/
theorem quadratic_eq_of_apply_eq (B : LinearMap.BilinForm ℝ A) (hB : ∀ u w, B u w = B w u)
    (ℓ : Module.Dual ℝ A) {u : A} (hu : ∀ w, B w u = ℓ w) (w : A) :
    B w w / 2 - ℓ w = (B u u / 2 - ℓ u) + B (w - u) (w - u) / 2 := by
  rw [← hu w, ← hu u]
  simp only [map_sub, LinearMap.sub_apply]
  rw [hB u w]
  ring

/-- **Minimality.** If `B` is positive semidefinite, a solution of the first-variation equation
minimizes the quadratic functional. -/
theorem quadratic_le_of_apply_eq (B : LinearMap.BilinForm ℝ A) (hB : ∀ u w, B u w = B w u)
    (hpos : ∀ v, 0 ≤ B v v) (ℓ : Module.Dual ℝ A) {u : A} (hu : ∀ w, B w u = ℓ w) (w : A) :
    B u u / 2 - ℓ u ≤ B w w / 2 - ℓ w := by
  rw [quadratic_eq_of_apply_eq B hB ℓ hu w]
  linarith [hpos (w - u)]

/-- The minimum value is minus half the energy of the minimizer. -/
theorem quadratic_self_of_apply_eq (B : LinearMap.BilinForm ℝ A) (ℓ : Module.Dual ℝ A) {u : A}
    (hu : ∀ w, B w u = ℓ w) : B u u / 2 - ℓ u = -(B u u / 2) := by
  rw [← hu u]
  ring

end LinearMap.BilinForm
