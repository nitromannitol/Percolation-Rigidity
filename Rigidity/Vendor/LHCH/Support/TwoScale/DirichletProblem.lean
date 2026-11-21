/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/TwoScale/DirichletProblem.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Conductance
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# The discrete Dirichlet problem

For `d ≥ 1`, positive conductances and a finite set `U`, the matrix `L_{c,U}` is positive definite,
`g_U g` is the unique function vanishing off `U` with `L_c u = g` on `U`, and summation by parts
gives `Σ_{x∈U} u(x) L_c u(x) = Σ_e c_e |∇u(e)|²`.
In particular the solution `u_L` of `t:general` exists and is unique.
-/

open LatticeProb Matrix

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- Every site `x` with `x ∈ U` or `x + e_j ∈ U` for some `j` lies in a finite set `S`. -/
theorem exists_finset_covering_edges (U : Finset (Site d)) :
    ∃ S : Finset (Site d), ∀ x (j : Fin d), (x ∈ U ∨ x + unit j ∈ U) → x ∈ S := by
  classical
  refine ⟨U ∪ Finset.univ.biUnion (fun j : Fin d => U.image (fun y => y - unit j)), ?_⟩
  intro x j hx
  rcases hx with hx | hx
  · exact Finset.mem_union_left _ hx
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩)
    exact Finset.mem_image.mpr ⟨x + unit j, hx, by simp⟩

/-- **Summation by parts for a flow**: for `u` vanishing off `U` and a finite `S` containing
every `x` with `x ∈ U` or `x + e_j ∈ U`,
`Σ_{x∈U} u(x) ∇*J(x) = Σ_{x∈S} Σ_j J(x,j) (u(x+e_j) − u(x))`. -/
theorem sum_mul_divergence_eq_sum_gradient (J : Edge d → ℝ) (U S : Finset (Site d))
    (u : Site d → ℝ) (hu : ∀ x, x ∉ U → u x = 0)
    (hS : ∀ x (j : Fin d), (x ∈ U ∨ x + unit j ∈ U) → x ∈ S) :
    ∑ x ∈ U, u x * ∑ j : Fin d, (J (x - unit j, j) - J (x, j)) =
      ∑ x ∈ S, ∑ j : Fin d, J (x, j) * (u (x + unit j) - u x) := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := S)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hUS : U ⊆ S := fun x hx => hS x j (Or.inl hx)
  set G : Site d → ℝ := fun x => u x * J (x - unit j, j) with hG
  set F : Site d → ℝ := fun x => u x * (-J (x, j)) with hF
  have hsplit : ∀ x, u x * (J (x - unit j, j) - J (x, j)) = F x + G x := fun x => by
    simp only [hF, hG]; ring
  simp only [hsplit]
  rw [Finset.sum_add_distrib]
  have hF0 : ∑ x ∈ U, F x = ∑ x ∈ S, F x :=
    Finset.sum_subset hUS fun x _ hx => by simp [hF, hu x hx]
  have hG0 : ∑ x ∈ U, G x = ∑ x ∈ S, G (x + unit j) := by
    have hmap : ∑ x ∈ S, G (x + unit j) = ∑ x ∈ S.map (addRightEmbedding (unit j)), G x := by
      rw [Finset.sum_map]; rfl
    rw [hmap]
    refine Finset.sum_subset (fun x hx => ?_) (fun x _ hx => by simp [hG, hu x hx])
    · refine Finset.mem_map.mpr ⟨x - unit j, hS _ j (Or.inr (by simpa using hx)), by simp⟩
  rw [hF0, hG0, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [hF, hG, add_sub_cancel_right]
  ring

/-- **Bilinear summation by parts**: for `u` vanishing off `U`, `w` arbitrary and a finite `S`
containing every `x` with `x ∈ U` or `x + e_j ∈ U`,
`Σ_{x∈U} u(x) L_c w(x) = Σ_{x∈S} Σ_j c(x,j) (u(x+e_j) − u(x)) (w(x+e_j) − w(x))`. It is
`sum_mul_divergence_eq_sum_gradient` for the flow `J(x,j) = c(x,j) (w(x+e_j) − w(x))`. -/
theorem sum_mul_condLaplacian_eq_sum_gradient_mul (c : Edge d → ℝ) (U S : Finset (Site d))
    (u w : Site d → ℝ) (hu : ∀ x, x ∉ U → u x = 0)
    (hS : ∀ x (j : Fin d), (x ∈ U ∨ x + unit j ∈ U) → x ∈ S) :
    ∑ x ∈ U, u x * condLaplacian c w x =
      ∑ x ∈ S, ∑ j : Fin d, c (x, j) * ((u (x + unit j) - u x) * (w (x + unit j) - w x)) := by
  have h := sum_mul_divergence_eq_sum_gradient
    (fun e : Edge d => c e * (w (e.1 + unit e.2) - w e.1)) U S u hu hS
  simp only [sub_add_cancel] at h
  have hL : ∀ x, condLaplacian c w x = ∑ j : Fin d,
      (c (x - unit j, j) * (w x - w (x - unit j)) - c (x, j) * (w (x + unit j) - w x)) :=
    fun x => Finset.sum_congr rfl fun j _ => by ring
  simp only [hL]
  rw [h]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The extension by zero off `U` of a function on `U`. -/
def zeroExtension (U : Finset (Site d)) (v : U → ℝ) (y : Site d) : ℝ :=
  if h : y ∈ U then v ⟨y, h⟩ else 0

/-- The zero extension of `v : U → ℝ` agrees with `v` on `U`. -/
theorem zeroExtension_apply_of_mem (U : Finset (Site d)) (v : U → ℝ) (z : U) :
    zeroExtension U v z.1 = v z := by
  simp [zeroExtension]

/-- The zero extension of `v : U → ℝ` vanishes off `U`. -/
theorem zeroExtension_apply_of_not_mem (U : Finset (Site d)) (v : U → ℝ) {y : Site d}
    (hy : y ∉ U) : zeroExtension U v y = 0 := by
  simp [zeroExtension, hy]

/-- `L_c u(x) = Σ_{z∈U} u(z) L_c 1_z(x)` for `u` vanishing off `U`, by linearity of `L_c`. -/
theorem condLaplacian_eq_sum_indicator (c : Edge d → ℝ) (U : Finset (Site d)) (u : Site d → ℝ)
    (hu : ∀ x, x ∉ U → u x = 0) (x : Site d) :
    condLaplacian c u x =
      ∑ z ∈ U, u z * condLaplacian c (fun y => if y = z then 1 else 0) x := by
  have hexp : u = fun y => ∑ z ∈ U, u z * (if y = z then 1 else 0) := by
    funext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, hu y hy]
  conv_lhs => rw [hexp]
  simp only [condLaplacian, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The matrix `L_{c,U}` acts on `v : U → ℝ` as `L_c` on the zero extension of `v`. -/
theorem condLaplacianU_mulVec (c : Edge d → ℝ) (U : Finset (Site d)) (v : U → ℝ) (x : U) :
    (condLaplacianU c U *ᵥ v) x = condLaplacian c (zeroExtension U v) x.1 := by
  rw [condLaplacian_eq_sum_indicator c U (zeroExtension U v)
    (fun y hy => zeroExtension_apply_of_not_mem U v hy) x.1]
  simp only [mulVec, dotProduct, condLaplacianU]
  rw [← Finset.sum_coe_sort U]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [zeroExtension_apply_of_mem, mul_comm]

/-- The Dirichlet matrix is symmetric. -/
theorem condLaplacianU_isHermitian (c : Edge d → ℝ) (U : Finset (Site d)) :
    (condLaplacianU c U).IsHermitian := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_covering_edges U
  rw [isHermitian_iff_isSymm]
  refine Matrix.IsSymm.ext fun x z => ?_
  have key : ∀ x z : U, condLaplacianU c U x z = ∑ y ∈ S, ∑ j : Fin d, c (y, j) *
      (((if y + unit j = x.1 then 1 else 0) - (if y = x.1 then 1 else 0)) *
        ((if y + unit j = z.1 then 1 else 0) - (if y = z.1 then 1 else 0))) := by
    intro x z
    have := sum_mul_condLaplacian_eq_sum_gradient_mul c U S (fun y => if y = x.1 then 1 else 0)
      (fun y => if y = z.1 then 1 else 0)
      (fun y hy => by simp [show y ≠ x.1 from fun h => hy (h ▸ x.2)]) hS
    simpa [condLaplacianU, Finset.sum_ite_eq, x.2] using this
  rw [key, key]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A function vanishing off a finite set `U` that is invariant under translation by `e_j` at every
site of a finite set `S ⊇ U` vanishes identically. -/
theorem eq_zero_of_translation_invariant (U S : Finset (Site d)) (j : Fin d) (w : Site d → ℝ)
    (hw : ∀ x, x ∉ U → w x = 0) (hUS : U ⊆ S) (hinv : ∀ x ∈ S, w (x + unit j) = w x) :
    ∀ x, w x = 0 := by
  by_contra hne
  obtain ⟨x₀, hx₀⟩ := not_forall.mp hne
  have hmem : ∀ x, w x ≠ 0 → x ∈ U := fun x hx => by_contra fun h => hx (hw x h)
  have hconst : ∀ n : ℕ, w (x₀ + (n : ℤ) • unit j) = w x₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hmemS : x₀ + (n : ℤ) • unit j ∈ S :=
        hUS (hmem _ (by rw [ih]; exact hx₀))
      have : x₀ + ((n + 1 : ℕ) : ℤ) • unit j = (x₀ + (n : ℤ) • unit j) + unit j := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [this, hinv _ hmemS, ih]
  have hinj : Function.Injective (fun n : ℕ => x₀ + (n : ℤ) • unit j) := by
    intro m n hmn
    have := congrFun hmn j
    simpa [unit] using this
  have hinfinite : (U : Set (Site d)).Infinite :=
    Set.infinite_of_injective_forall_mem hinj fun n => by
      refine hmem _ ?_
      simp only [hconst n]
      exact hx₀
  exact hinfinite U.finite_toSet

/-- **The Dirichlet matrix is positive definite**: for `d ≥ 1`, positive conductances and a finite
`U`, `x · L_{c,U} x = Σ_e c_e |∇x̃(e)|²` for the zero extension `x̃`, which vanishes only if `x̃` is
constant, hence zero. -/
theorem condLaplacianU_posDef (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) : (condLaplacianU c U).PosDef := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_covering_edges U
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨condLaplacianU_isHermitian c U, fun v hv => ?_⟩
  set w := zeroExtension U v with hwdef
  have hw : ∀ x, x ∉ U → w x = 0 := fun x hx => zeroExtension_apply_of_not_mem U v hx
  have hQ : star v ⬝ᵥ (condLaplacianU c U *ᵥ v) =
      ∑ x ∈ S, ∑ j : Fin d, c (x, j) * ((w (x + unit j) - w x) * (w (x + unit j) - w x)) := by
    rw [← sum_mul_condLaplacian_eq_sum_gradient_mul c U S w w hw hS, ← Finset.sum_coe_sort U]
    simp only [dotProduct, condLaplacianU_mulVec, star_trivial]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hwdef, zeroExtension_apply_of_mem]
  rw [hQ]
  have hterm : ∀ (x : Site d) (j : Fin d),
      0 ≤ c (x, j) * ((w (x + unit j) - w x) * (w (x + unit j) - w x)) :=
    fun x j => mul_nonneg (hc _).le (mul_self_nonneg _)
  have hnn : ∀ x ∈ S, 0 ≤ ∑ j : Fin d, c (x, j) * ((w (x + unit j) - w x) *
      (w (x + unit j) - w x)) := fun x _ => Finset.sum_nonneg fun j _ => hterm x j
  refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => hv ?_
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0.symm
  have hinv : ∀ x ∈ S, w (x + unit ⟨0, hd⟩) = w x := by
    intro x hx
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm x j)).mp (h1 x hx)
      ⟨0, hd⟩ (Finset.mem_univ _)
    have h3 := (mul_eq_zero.mp h2).resolve_left (hc _).ne'
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  have hall := eq_zero_of_translation_invariant U S ⟨0, hd⟩ w hw
    (fun x hx => hS x ⟨0, hd⟩ (Or.inl hx)) hinv
  funext z
  have := hall z.1
  rw [hwdef, zeroExtension_apply_of_mem] at this
  simpa using this

/-- The Dirichlet Green function applied to `g` is the zero extension of `L_{c,U}⁻¹ g|_U`. -/
theorem sum_dirichletGreen_mul_eq_zeroExtension (c : Edge d → ℝ) (U : Finset (Site d))
    (g : Site d → ℝ) :
    (fun y => ∑ z ∈ U, dirichletGreen c U y z * g z) =
      zeroExtension U ((condLaplacianU c U)⁻¹ *ᵥ fun z : U => g z.1) := by
  funext y
  by_cases hy : y ∈ U
  · simp only [zeroExtension, hy, dif_pos, mulVec, dotProduct]
    rw [← Finset.sum_coe_sort U]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp [dirichletGreen, hy]
  · simp [zeroExtension, hy, dirichletGreen]

/-- **The Dirichlet Green function solves the Dirichlet problem**: `u = g_U g` vanishes off `U`
and `L_c u = g` on `U`. -/
theorem condLaplacian_dirichletGreen (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (g : Site d → ℝ) :
    ∀ x ∈ U, condLaplacian c (fun y => ∑ z ∈ U, dirichletGreen c U y z * g z) x = g x := by
  intro x hx
  classical
  have hdet : IsUnit (condLaplacianU c U).det :=
    (isUnit_iff_isUnit_det _).mp (condLaplacianU_posDef hd c hc U).isUnit
  rw [sum_dirichletGreen_mul_eq_zeroExtension,
    ← condLaplacianU_mulVec c U ((condLaplacianU c U)⁻¹ *ᵥ fun z : U => g z.1) ⟨x, hx⟩,
    mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

/-- **Uniqueness**: a function vanishing off `U` with `L_c u = g` on `U` is `g_U g`. -/
theorem eq_dirichletGreen_of_condLaplacian (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (u g : Site d → ℝ) (hu : ∀ x, x ∉ U → u x = 0)
    (h : ∀ x ∈ U, condLaplacian c u x = g x) :
    ∀ x, u x = ∑ z ∈ U, dirichletGreen c U x z * g z := by
  classical
  have hdet : IsUnit (condLaplacianU c U).det :=
    (isUnit_iff_isUnit_det _).mp (condLaplacianU_posDef hd c hc U).isUnit
  set v : U → ℝ := fun z => u z.1 with hv
  have hext : zeroExtension U v = u := by
    funext y
    by_cases hy : y ∈ U
    · simp [zeroExtension, hy, hv]
    · simp [zeroExtension_apply_of_not_mem U v hy, hu y hy]
  have hLv : condLaplacianU c U *ᵥ v = fun z : U => g z.1 :=
    funext fun z => by rw [condLaplacianU_mulVec, hext]; exact h z.1 z.2
  have hvinv : v = (condLaplacianU c U)⁻¹ *ᵥ fun z : U => g z.1 := by
    rw [← hLv, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  intro x
  have := congrFun (sum_dirichletGreen_mul_eq_zeroExtension c U g) x
  rw [← hvinv, hext] at this
  exact this.symm

/-- **Uniqueness with a scale factor**: for `a ≠ 0`, a function `u` vanishing off `U` with
`a L_c u = s` on `U` is `a⁻¹ Σ_{z∈U} g_U(·, z) s_z`. -/
theorem eq_inv_mul_dirichletGreen_of_mul_condLaplacian (hd : 1 ≤ d) (c : Edge d → ℝ)
    (hc : ∀ e, 0 < c e) (U : Finset (Site d)) (u s : Site d → ℝ) {a : ℝ} (ha : a ≠ 0)
    (hu : ∀ x, x ∉ U → u x = 0) (h : ∀ x ∈ U, a * condLaplacian c u x = s x) :
    ∀ x, u x = a⁻¹ * ∑ z ∈ U, dirichletGreen c U x z * s z := by
  intro x
  rw [eq_dirichletGreen_of_condLaplacian hd c hc U u (fun y => s y / a) hu (fun y hy => by
    rw [eq_div_iff ha, mul_comm]
    exact h y hy) x, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- **Summation by parts**: for `u` vanishing off `U` and a finite `S` containing every `x` with
`x ∈ U` or `x + e_j ∈ U`, `Σ_{x∈U} u(x) L_c u(x) = Σ_{x∈S} Σ_j c(x,j) (u(x+e_j) − u(x))²`. -/
theorem sum_mul_condLaplacian_eq (c : Edge d → ℝ) (U S : Finset (Site d)) (u : Site d → ℝ)
    (hu : ∀ x, x ∉ U → u x = 0) (hS : ∀ x (j : Fin d), (x ∈ U ∨ x + unit j ∈ U) → x ∈ S) :
    ∑ x ∈ U, u x * condLaplacian c u x =
      ∑ x ∈ S, ∑ j : Fin d, c (x, j) * (u (x + unit j) - u x) ^ 2 := by
  rw [sum_mul_condLaplacian_eq_sum_gradient_mul c U S u u hu hS]
  simp only [sq]

end LatticeHC

end
