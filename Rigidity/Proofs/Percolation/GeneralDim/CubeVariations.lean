import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergyBounds

/-!
# Second variations, the values at the optimizers and the comparison identity

For a resolved triadic cube `U` of `ℤ^d` on the partition event, if `u ∈ A_*(U)` solves the
first variation equation of `μ(U, q)`, then for every `w ∈ A_*(U)`

`|U| μ(U, q) + B(w - u, w - u) / 2 = B(w, w) / 2 - ℓ_q(w)`,

and, if `v ∈ A_*(U)` solves the first variation equation of `ν(U, p)`,

`F_p(w) - B(w, w) / 2 + B(w - v, w - v) / 2 = |U| ν(U, p)`

(Armstrong and Dario, Lemma 4.2, (4.4) and (4.6)). With `w` the solution itself,
`|U| μ(U, q) = -B(u, u) / 2` and `|U| ν(U, p) = B(v, v) / 2` ((4.7)), and testing the second
variation of `μ` with `v` gives the comparison identity

`|U| ν(U, p) - |U| μ(U, q) - ℓ_q(v) = B(v - u, v - u) / 2`

((4.8)). Since sums and multiples of solutions solve the first variation equations for the
corresponding sums and multiples of the slopes, `q ↦ μ(U, q)` and `p ↦ ν(U, p)` are quadratic
forms (Armstrong and Dario, after Definition 4.1).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- Expansion of the energy of a difference. -/
theorem cubeForm_sub_sub {U : TriadicCube d} (u w : CubeFun ω U) :
    cubeForm ω U (w - u) (w - u) = cubeForm ω U w w - 2 * cubeForm ω U w u + cubeForm ω U u u := by
  simp only [map_sub, LinearMap.sub_apply]
  rw [cubeForm_symm u w]
  ring

/-- **Second variation for `μ`** (Armstrong and Dario, Lemma 4.2, (4.4)). -/
theorem cubeMu_mul_latticeVolume_add_cubeForm_sub (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (q : Fin d → ℝ) {u : CubeFun ω U}
    (hu : u ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w)
    {w : CubeFun ω U} (hw : w ∈ cubeHarmonic ω U) :
    cubeMu ω U q * U.latticeVolume + cubeForm ω U (w - u) (w - u) / 2 =
      cubeForm ω U w w / 2 - cubeCoarsePairing ω U q w := by
  obtain ⟨u', hu', hvar', hμ'⟩ := exists_cubeMu_minimizer hd hP hU q
  have h1 := hvar u' hu'
  have h2 := hvar' u hu
  have h3 := hvar u hu
  have h4 := hvar' u' hu'
  have h5 := hvar w hw
  have hs := cubeForm_symm u' u
  have hμ : cubeMu ω U q * U.latticeVolume =
      cubeForm ω U u' u' / 2 - cubeCoarsePairing ω U q u' := by
    rw [hμ', div_mul_cancel₀ _ U.latticeVolume_pos.ne']
  rw [hμ, cubeForm_sub_sub]
  linarith

/-- The value of `μ(U, q)` at any solution of the first variation equation
(Armstrong and Dario, first line of (4.19), with the sign corrected). -/
theorem cubeMu_mul_latticeVolume_eq (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) {u : CubeFun ω U}
    (hu : u ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w) :
    cubeMu ω U q * U.latticeVolume = -(cubeForm ω U u u / 2) := by
  have h := cubeMu_mul_latticeVolume_add_cubeForm_sub hd hP hU q hu hvar hu
  have h3 := hvar u hu
  simp only [sub_self, map_zero, zero_div, add_zero] at h
  linarith

/-- `μ` is minus half the energy, per vertex, of any solution of its first variation equation. -/
theorem cubeMu_eq_of_forall_cubeForm_eq (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {q : Fin d → ℝ} {u : CubeFun ω U}
    (hu : u ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w) :
    cubeMu ω U q = -(cubeForm ω U u u / 2) / U.latticeVolume := by
  rw [← cubeMu_mul_latticeVolume_eq hd hP hU q hu hvar,
    mul_div_cancel_right₀ _ U.latticeVolume_pos.ne']

/-- **Second variation for `ν`** (Armstrong and Dario, Lemma 4.2, (4.6)). -/
theorem cubeFluxPairing_sub_add_cubeForm_sub {U : TriadicCube d} (p : Fin d → ℝ)
    {v : CubeFun ω U} (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w)
    {w : CubeFun ω U} (hw : w ∈ cubeHarmonic ω U) :
    cubeFluxPairing ω U p w - cubeForm ω U w w / 2 + cubeForm ω U (w - v) (w - v) / 2 =
      cubeNu ω U p * U.latticeVolume := by
  obtain ⟨v', hv', hvar', hν'⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  have h1 := hvar v' hv'
  have h2 := hvar' v hv
  have h3 := hvar v hv
  have h4 := hvar' v' hv'
  have h5 := hvar w hw
  have hs := cubeForm_symm v' v
  have hν : cubeNu ω U p * U.latticeVolume =
      cubeFluxPairing ω U p v' - cubeForm ω U v' v' / 2 := by
    rw [hν', div_mul_cancel₀ _ U.latticeVolume_pos.ne']
  rw [hν, cubeForm_sub_sub]
  linarith

/-- The value of `ν(U, p)` at any solution of the first variation equation
(Armstrong and Dario, (4.7) and the second line of (4.19)). -/
theorem cubeNu_mul_latticeVolume_eq {U : TriadicCube d} (p : Fin d → ℝ) {v : CubeFun ω U}
    (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w) :
    cubeNu ω U p * U.latticeVolume = cubeForm ω U v v / 2 := by
  have h := cubeFluxPairing_sub_add_cubeForm_sub p hv hvar hv
  have h3 := hvar v hv
  simp only [sub_self, map_zero, zero_div, add_zero] at h
  linarith

/-- `ν` is half the energy, per vertex, of any solution of its first variation equation. -/
theorem cubeNu_eq_of_forall_cubeForm_eq {U : TriadicCube d} {p : Fin d → ℝ}
    {v : CubeFun ω U} (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w) :
    cubeNu ω U p = cubeForm ω U v v / 2 / U.latticeVolume := by
  rw [← cubeNu_mul_latticeVolume_eq p hv hvar, mul_div_cancel_right₀ _ U.latticeVolume_pos.ne']

/-- **The comparison identity** (Armstrong and Dario, (4.8)). -/
theorem cubeNu_sub_cubeMu_eq (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p q : Fin d → ℝ) {u v : CubeFun ω U}
    (hu : u ∈ cubeHarmonic ω U)
    (hvar_u : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w)
    (hv : v ∈ cubeHarmonic ω U)
    (hvar_v : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w) :
    cubeNu ω U p * U.latticeVolume - cubeMu ω U q * U.latticeVolume -
        cubeCoarsePairing ω U q v = cubeForm ω U (v - u) (v - u) / 2 := by
  have h1 := cubeMu_mul_latticeVolume_add_cubeForm_sub hd hP hU q hu hvar_u hv
  have h2 := cubeNu_mul_latticeVolume_eq p hv hvar_v
  linarith

/-- The coarse pairing is linear in the slope. -/
theorem cubeCoarsePairing_smul_add_smul {U : TriadicCube d} (q r : Fin d → ℝ) (a b : ℝ)
    (w : CubeFun ω U) :
    cubeCoarsePairing ω U (a • q + b • r) w =
      a * cubeCoarsePairing ω U q w + b * cubeCoarsePairing ω U r w := by
  simp only [cubeCoarsePairing_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ring

/-- A linear combination of slopes paired with a vector. -/
theorem sum_smul_add_smul_mul (p q c : Fin d → ℝ) (a b : ℝ) :
    ∑ i, (a • p + b • q) i * c i = a * ∑ i, p i * c i + b * ∑ i, q i * c i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The flux pairing is linear in the slope. -/
theorem cubeFluxPairing_smul_add_smul {U : TriadicCube d} (p q : Fin d → ℝ) (a b : ℝ)
    (w : CubeFun ω U) :
    cubeFluxPairing ω U (a • p + b • q) w =
      a * cubeFluxPairing ω U p w + b * cubeFluxPairing ω U q w := by
  simp only [cubeFluxPairing_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · rw [sum_smul_add_smul_mul p q (fun i => (y.1 i : ℝ) - x.1 i)]
    ring
  · ring

/-- **`μ` is a quadratic form in the slope** on resolved cubes. -/
theorem cubeMu_smul_add_smul (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q r : Fin d → ℝ) (a b : ℝ) :
    cubeMu ω U (a • q + b • r) = a ^ 2 * cubeMu ω U q + b ^ 2 * cubeMu ω U r +
      a * b * (cubeMu ω U (q + r) - cubeMu ω U q - cubeMu ω U r) := by
  obtain ⟨uq, huq, hsq, -⟩ := exists_cubeMu_minimizer hd hP hU q
  obtain ⟨ur, hur, hsr, -⟩ := exists_cubeMu_minimizer hd hP hU r
  have hμ : ∀ a b : ℝ, cubeMu ω U (a • q + b • r) =
      -(cubeForm ω U (a • uq + b • ur) (a • uq + b • ur) / 2) / U.latticeVolume := by
    intro a b
    refine cubeMu_eq_of_forall_cubeForm_eq hd hP hU
      (Submodule.add_mem _ (Submodule.smul_mem _ a huq) (Submodule.smul_mem _ b hur))
      fun w hw => ?_
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hsq w hw, hsr w hw,
      cubeCoarsePairing_smul_add_smul]
  have e1 := hμ 1 0
  have e2 := hμ 0 1
  have e3 := hμ 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at e1 e2 e3
  have hvol := U.latticeVolume_pos
  rw [hμ a b, e1, e2, e3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [cubeForm_symm ur uq]
  field_simp
  ring

/-- **`ν` is a quadratic form in the slope.** -/
theorem cubeNu_smul_add_smul (U : TriadicCube d) (p q : Fin d → ℝ) (a b : ℝ) :
    cubeNu ω U (a • p + b • q) = a ^ 2 * cubeNu ω U p + b ^ 2 * cubeNu ω U q +
      a * b * (cubeNu ω U (p + q) - cubeNu ω U p - cubeNu ω U q) := by
  obtain ⟨vp, hvp, hsp, -⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  obtain ⟨vq, hvq, hsq, -⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) q
  have hν : ∀ a b : ℝ, cubeNu ω U (a • p + b • q) =
      cubeForm ω U (a • vp + b • vq) (a • vp + b • vq) / 2 / U.latticeVolume := by
    intro a b
    refine cubeNu_eq_of_forall_cubeForm_eq
      (Submodule.add_mem _ (Submodule.smul_mem _ a hvp) (Submodule.smul_mem _ b hvq))
      fun w hw => ?_
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hsp w hw, hsq w hw,
      cubeFluxPairing_smul_add_smul]
  have e1 := hν 1 0
  have e2 := hν 0 1
  have e3 := hν 1 1
  simp only [one_smul, zero_smul, add_zero, zero_add] at e1 e2 e3
  have hvol := U.latticeVolume_pos
  rw [hν a b, e1, e2, e3]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [cubeForm_symm vq vp]
  field_simp
  ring

end Rigidity.Percolation
