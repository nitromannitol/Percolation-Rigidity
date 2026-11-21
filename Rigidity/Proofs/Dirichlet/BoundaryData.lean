import Rigidity.Vendor.LHCH.Support.TwoScale.DirichletProblem

/-!
# The discrete Dirichlet problem with boundary data

For positive conductances `c` on the edges of `ℤ^d` (`d ≥ 1`), a finite set `U` and a function `f`,
there is exactly one `u` with `u = f` off `U` and `L_c u = 0` on `U`, namely
`dirichletSolution c U f = f − g_U (L_c f)`. It minimizes the Dirichlet energy among the functions
equal to `f` off `U`, with the Pythagoras identity `E(v) = E(u) + E(v − u)`, its energy is the
pairing of the gradients of `u` and `f`, and it satisfies the maximum principle: a function
`c`-harmonic on `U` is bounded on `U` by its values at the lattice neighbours of `U` outside `U`.

This is the discrete form of the homogenized Dirichlet problem of Armstrong–Dario, §6, solved
here on the lattice: for the homogenized matrix `ā` the conductances are `c(x, j) = ā_{jj}`.
-/

open LatticeProb LatticeHC

noncomputable section

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The finite set `S` contains the lower endpoint of every edge with an endpoint in `U`. -/
def CoversEdges (U S : Finset (Site d)) : Prop :=
  ∀ x (j : Fin d), (x ∈ U ∨ x + unit j ∈ U) → x ∈ S

/-- The bilinear Dirichlet form `Σ_{x∈S} Σ_j c(x,j) ∇_j u(x) ∇_j v(x)` over the edges `(x, j)`
with `x ∈ S`. -/
def edgeForm (c : Edge d → ℝ) (S : Finset (Site d)) (u v : Site d → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ j : Fin d, c (x, j) * ((u (x + unit j) - u x) * (v (x + unit j) - v x))

/-- The Dirichlet energy `Σ_{x∈S} Σ_j c(x,j) (∇_j u(x))²`. -/
def edgeEnergy (c : Edge d → ℝ) (S : Finset (Site d)) (u : Site d → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ j : Fin d, c (x, j) * (u (x + unit j) - u x) ^ 2

/-- The solution `f − g_U (L_c f)` of the Dirichlet problem `L_c u = 0` on `U`, `u = f` off `U`. -/
def dirichletSolution (c : Edge d → ℝ) (U : Finset (Site d)) (f : Site d → ℝ) : Site d → ℝ :=
  fun x => f x - ∑ z ∈ U, dirichletGreen c U x z * condLaplacian c f z

theorem edgeEnergy_eq_edgeForm (c : Edge d → ℝ) (S : Finset (Site d)) (u : Site d → ℝ) :
    edgeEnergy c S u = edgeForm c S u u := by
  simp only [edgeEnergy, edgeForm, sq]

theorem edgeEnergy_nonneg {c : Edge d → ℝ} (hc : ∀ e, 0 ≤ c e) (S : Finset (Site d))
    (u : Site d → ℝ) : 0 ≤ edgeEnergy c S u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (hc _) (sq_nonneg _)

theorem exists_coversEdges (U : Finset (Site d)) : ∃ S : Finset (Site d), CoversEdges U S :=
  exists_finset_covering_edges U

/-- `L_c` is additive in the function. -/
theorem condLaplacian_sub (c : Edge d → ℝ) (u v : Site d → ℝ) (x : Site d) :
    condLaplacian c (u - v) x = condLaplacian c u x - condLaplacian c v x := by
  simp only [condLaplacian, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `L_c` commutes with negation. -/
theorem condLaplacian_neg (c : Edge d → ℝ) (u : Site d → ℝ) (x : Site d) :
    condLaplacian c (-u) x = -condLaplacian c u x := by
  simp only [condLaplacian, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dirichletSolution_eq_of_not_mem (c : Edge d → ℝ) (U : Finset (Site d))
    (f : Site d → ℝ) {x : Site d} (hx : x ∉ U) : dirichletSolution c U f x = f x := by
  simp [dirichletSolution, dirichletGreen, hx]

/-- **Existence**: the Dirichlet solution is `c`-harmonic on `U`. -/
theorem condLaplacian_dirichletSolution (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (f : Site d → ℝ) :
    ∀ x ∈ U, condLaplacian c (dirichletSolution c U f) x = 0 := by
  intro x hx
  have hsol : dirichletSolution c U f =
      f - fun y => ∑ z ∈ U, dirichletGreen c U y z * condLaplacian c f z := rfl
  rw [hsol, condLaplacian_sub, condLaplacian_dirichletGreen hd c hc U _ x hx, sub_self]

/-- **Uniqueness**: a function equal to `f` off `U` and `c`-harmonic on `U` is the Dirichlet
solution. -/
theorem eq_dirichletSolution (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (f u : Site d → ℝ) (hu : ∀ x, x ∉ U → u x = f x)
    (hL : ∀ x ∈ U, condLaplacian c u x = 0) : u = dirichletSolution c U f := by
  have h0 := eq_dirichletGreen_of_condLaplacian hd c hc U (u - dirichletSolution c U f) 0
    (fun x hx => by
      simp [hu x hx, dirichletSolution_eq_of_not_mem c U f hx])
    (fun x hx => by
      rw [condLaplacian_sub, hL x hx, condLaplacian_dirichletSolution hd c hc U f x hx,
        sub_zero, Pi.zero_apply])
  funext x
  have := h0 x
  simp only [Pi.sub_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at this
  linarith

/-- The Dirichlet problem `L_c u = 0` on `U`, `u = f` off `U`, has exactly one solution. -/
theorem existsUnique_dirichlet (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (f : Site d → ℝ) :
    ∃! u : Site d → ℝ, (∀ x, x ∉ U → u x = f x) ∧ ∀ x ∈ U, condLaplacian c u x = 0 :=
  ⟨dirichletSolution c U f,
    ⟨fun _ hx => dirichletSolution_eq_of_not_mem c U f hx,
      condLaplacian_dirichletSolution hd c hc U f⟩,
    fun u hu => eq_dirichletSolution hd c hc U f u hu.1 hu.2⟩

/-- A function vanishing off `U` is orthogonal, for the Dirichlet form, to every function
`c`-harmonic on `U`. -/
theorem edgeForm_eq_zero_of_condLaplacian (c : Edge d → ℝ) {U S : Finset (Site d)}
    (hS : CoversEdges U S) {v w : Site d → ℝ} (hv : ∀ x, x ∉ U → v x = 0)
    (hw : ∀ x ∈ U, condLaplacian c w x = 0) : edgeForm c S v w = 0 := by
  rw [edgeForm, ← sum_mul_condLaplacian_eq_sum_gradient_mul c U S v w hv hS]
  exact Finset.sum_eq_zero fun x hx => by rw [hw x hx, mul_zero]

/-- **Pythagoras identity** for the Dirichlet energy: if `u` is `c`-harmonic on `U` and `v = u`
off `U`, then `E(v) = E(u) + E(v − u)`. -/
theorem edgeEnergy_eq_add_of_condLaplacian (c : Edge d → ℝ) {U S : Finset (Site d)}
    (hS : CoversEdges U S) {u v : Site d → ℝ} (hu : ∀ x ∈ U, condLaplacian c u x = 0)
    (hvu : ∀ x, x ∉ U → v x = u x) :
    edgeEnergy c S v = edgeEnergy c S u + edgeEnergy c S (v - u) := by
  have h0 := edgeForm_eq_zero_of_condLaplacian c hS (v := v - u) (w := u)
    (fun x hx => by simp [hvu x hx]) hu
  have hexp : edgeEnergy c S v =
      edgeEnergy c S u + edgeEnergy c S (v - u) + 2 * edgeForm c S (v - u) u := by
    simp only [edgeEnergy, edgeForm, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp, h0, mul_zero, add_zero]

/-- **Dirichlet principle**: the Dirichlet solution has the least energy among the functions equal
to `f` off `U`. -/
theorem edgeEnergy_dirichletSolution_le (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    {U S : Finset (Site d)} (hS : CoversEdges U S) (f v : Site d → ℝ)
    (hv : ∀ x, x ∉ U → v x = f x) :
    edgeEnergy c S (dirichletSolution c U f) ≤ edgeEnergy c S v := by
  rw [edgeEnergy_eq_add_of_condLaplacian c hS (v := v) (condLaplacian_dirichletSolution hd c hc U f)
    (fun x hx => by rw [hv x hx, dirichletSolution_eq_of_not_mem c U f hx])]
  exact le_add_of_nonneg_right (edgeEnergy_nonneg (fun e => (hc e).le) S _)

/-- **Energy identity**: the energy of the Dirichlet solution `u` with data `f` is the pairing
`Σ c ∇f ∇u` of the gradients of the data and of the solution. -/
theorem edgeEnergy_dirichletSolution_eq (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    {U S : Finset (Site d)} (hS : CoversEdges U S) (f : Site d → ℝ) :
    edgeEnergy c S (dirichletSolution c U f) = edgeForm c S f (dirichletSolution c U f) := by
  set u := dirichletSolution c U f
  have h0 := edgeForm_eq_zero_of_condLaplacian c hS (v := u - f) (w := u)
    (fun x hx => by simp [u, dirichletSolution_eq_of_not_mem c U f hx])
    (condLaplacian_dirichletSolution hd c hc U f)
  have hsplit : edgeForm c S (u - f) u = edgeForm c S u u - edgeForm c S f u := by
    simp only [edgeForm, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [edgeEnergy_eq_edgeForm]
  linarith

/-- **Maximum principle**: a function `c`-harmonic on a finite set `U` (positive conductances,
`d ≥ 1`) that is at most `M` at every lattice neighbour of `U` outside `U` is at most `M` on `U`. -/
theorem le_of_condLaplacian_eq_zero (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (u : Site d → ℝ) (M : ℝ) (hu : ∀ x ∈ U, condLaplacian c u x = 0)
    (hM : ∀ x ∈ U, ∀ j : Fin d, (x + unit j ∉ U → u (x + unit j) ≤ M) ∧
      (x - unit j ∉ U → u (x - unit j) ≤ M)) :
    ∀ x ∈ U, u x ≤ M := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨x₁, hx₁U, hx₁M⟩ := hne
  obtain ⟨x₀, hx₀U, hx₀max⟩ := U.exists_max_image u ⟨x₁, hx₁U⟩
  have hmM : M < u x₀ := lt_of_lt_of_le hx₁M (hx₀max x₁ hx₁U)
  have key : ∀ x ∈ U, u x = u x₀ → ∀ j : Fin d, x + unit j ∈ U ∧ u (x + unit j) = u x₀ := by
    intro x hxU hxm j
    have hle : ∀ y, (y ∉ U → u y ≤ M) → u y ≤ u x₀ := fun y hy => by
      by_cases hyU : y ∈ U
      · exact hx₀max y hyU
      · exact (hy hyU).trans hmM.le
    have hup : ∀ i : Fin d, u (x + unit i) ≤ u x₀ := fun i => hle _ (hM x hxU i).1
    have hdn : ∀ i : Fin d, u (x - unit i) ≤ u x₀ := fun i => hle _ (hM x hxU i).2
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ c (x, i) * (u x - u (x + unit i)) + c (x - unit i, i) * (u x - u (x - unit i)) :=
      fun i _ => add_nonneg (mul_nonneg (hc _).le (by linarith [hup i]))
        (mul_nonneg (hc _).le (by linarith [hdn i]))
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hu x hxU) j (Finset.mem_univ _)
    have h1 : c (x, j) * (u x - u (x + unit j)) = 0 := by
      have := mul_nonneg (hc (x, j)).le (show 0 ≤ u x - u (x + unit j) by linarith [hup j])
      have := mul_nonneg (hc (x - unit j, j)).le
        (show 0 ≤ u x - u (x - unit j) by linarith [hdn j])
      linarith
    have hval : u (x + unit j) = u x₀ := by
      have := (mul_eq_zero.mp h1).resolve_left (hc _).ne'
      linarith
    refine ⟨by_contra fun hnot => ?_, hval⟩
    have := (hM x hxU j).1 hnot
    linarith
  set T := U.filter fun x => u x = u x₀
  have hT : x₀ ∈ T := Finset.mem_filter.mpr ⟨hx₀U, rfl⟩
  obtain ⟨y, hyT, hymax⟩ := T.exists_max_image (fun x => x ⟨0, hd⟩) ⟨x₀, hT⟩
  obtain ⟨hyU, hym⟩ := Finset.mem_filter.mp hyT
  obtain ⟨h1, h2⟩ := key y hyU hym ⟨0, hd⟩
  have hle := hymax _ (Finset.mem_filter.mpr ⟨h1, h2⟩)
  simp [unit] at hle

/-- **Minimum principle**: a function `c`-harmonic on `U` that is at least `m` at every lattice
neighbour of `U` outside `U` is at least `m` on `U`. -/
theorem le_of_condLaplacian_eq_zero' (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (u : Site d → ℝ) (m : ℝ) (hu : ∀ x ∈ U, condLaplacian c u x = 0)
    (hm : ∀ x ∈ U, ∀ j : Fin d, (x + unit j ∉ U → m ≤ u (x + unit j)) ∧
      (x - unit j ∉ U → m ≤ u (x - unit j))) :
    ∀ x ∈ U, m ≤ u x := by
  have h := le_of_condLaplacian_eq_zero hd c hc U (-u) (-m)
    (fun x hx => by rw [condLaplacian_neg, hu x hx, neg_zero])
    (fun x hx j => ⟨fun h => by simpa using (hm x hx j).1 h,
      fun h => by simpa using (hm x hx j).2 h⟩)
  intro x hx
  simpa using h x hx

/-- The Dirichlet solution is bounded on `U` by the largest absolute value of the data at the
lattice neighbours of `U` outside `U`. -/
theorem abs_dirichletSolution_le (hd : 1 ≤ d) (c : Edge d → ℝ) (hc : ∀ e, 0 < c e)
    (U : Finset (Site d)) (f : Site d → ℝ) (M : ℝ)
    (hM : ∀ x ∈ U, ∀ j : Fin d, (x + unit j ∉ U → |f (x + unit j)| ≤ M) ∧
      (x - unit j ∉ U → |f (x - unit j)| ≤ M)) :
    ∀ x ∈ U, |dirichletSolution c U f x| ≤ M := by
  have hL := condLaplacian_dirichletSolution hd c hc U f
  have hval : ∀ y, y ∉ U → dirichletSolution c U f y = f y :=
    fun y hy => dirichletSolution_eq_of_not_mem c U f hy
  intro x hx
  rw [abs_le]
  constructor
  · refine le_of_condLaplacian_eq_zero' hd c hc U _ (-M) hL (fun y hy j => ⟨fun h => ?_,
      fun h => ?_⟩) x hx
    · rw [hval _ h]; exact neg_le_of_abs_le ((hM y hy j).1 h)
    · rw [hval _ h]; exact neg_le_of_abs_le ((hM y hy j).2 h)
  · refine le_of_condLaplacian_eq_zero hd c hc U _ M hL (fun y hy j => ⟨fun h => ?_,
      fun h => ?_⟩) x hx
    · rw [hval _ h]; exact le_of_abs_le ((hM y hy j).1 h)
    · rw [hval _ h]; exact le_of_abs_le ((hM y hy j).2 h)

end Rigidity.Dirichlet
