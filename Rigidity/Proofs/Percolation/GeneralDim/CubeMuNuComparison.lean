import Rigidity.Proofs.Percolation.GeneralDim.CubeNablaAffine

/-!
# Comparison of `μ` and `ν` on triadic cubes of `ℤ^d`

For a resolved triadic cube `U` of side `L` on the partition event and slopes `p, q`, let `u` be
the minimizer of `μ(U, q)` and `v` the maximizer of `ν(U, p)`, affine at the boundary vertices of
the cluster. By the comparison identity `|U| ν(U, p) - |U| μ(U, q) - ℓ_q(v) = B(v - u, v - u) / 2`
((4.8)) and the control of the coarse pairing of `v` (Lemma 4.5),

`|ν(U, p) - μ(U, q) - q · p - B(v - u, v - u) / (2 |U|)| ≤ |q · p| / L + |q|₁ E_p(v) / |U|`,

with the boundary error `E_p(v)` of `CubeNablaAffine`. This is the deterministic form of
Corollary 4.6 of Armstrong and Dario ((4.29)), which is also the first display of the proof of
their Lemma 5.9. Since the energy term is nonnegative, `μ(U, q) ≤ ν(U, p) - q · p` up to the same
errors.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

theorem TriadicCube.cast_size_toIntegerCube (U : TriadicCube d) :
    (U.toIntegerCube.size : ℝ) = (3 : ℝ) ^ U.scale := by
  change ((3 ^ U.scale : ℕ) : ℝ) = _
  push_cast
  rfl

/-- `|U| = L^d`. -/
theorem TriadicCube.latticeVolume_eq_size_pow (U : TriadicCube d) :
    U.latticeVolume = (U.toIntegerCube.size : ℝ) ^ d := by
  rw [U.cast_size_toIntegerCube]
  rfl

/-- **Comparison of `μ` and `ν`** (Armstrong and Dario, Corollary 4.6, (4.29), deterministic
form, and the first display of the proof of Lemma 5.9). -/
theorem exists_abs_cubeNu_sub_cubeMu_sub_le (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (p q : Fin d → ℝ) :
    ∃ u ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w u = cubeCoarsePairing ω U q w) ∧
      ∃ v ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w v = cubeFluxPairing ω U p w) ∧
      |cubeNu ω U p - cubeMu ω U q - ∑ i, q i * p i -
          cubeForm ω U (v - u) (v - u) / 2 / U.latticeVolume| ≤
        |∑ i, q i * p i| / (U.toIntegerCube.size : ℝ) +
          (∑ i, |q i|) * cubeBoundaryError ω U p v / U.latticeVolume := by
  obtain ⟨u, hu, hvar_u, -⟩ := exists_cubeMu_minimizer hd hP hU q
  obtain ⟨v, hv, hvar_v, -, c, hc⟩ := exists_cubeNu_maximizer_affine hd hP hU p
  refine ⟨u, hu, hvar_u, v, hv, hvar_v, ?_⟩
  have hid := cubeNu_sub_cubeMu_eq hd hP hU p q hu hvar_u hv hvar_v
  have hb := abs_cubeCoarsePairing_sub_le hd hP hU p q hc
  have hvol := U.latticeVolume_pos
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL0 : 0 < L := by
    rw [hL, U.cast_size_toIntegerCube]
    positivity
  have hLvol : L ^ (d - 1) * L = U.latticeVolume := by
    rw [U.latticeVolume_eq_size_pow, ← hL, ← pow_succ, Nat.sub_add_cancel hd]
  set s := ∑ i, q i * p i
  set E := (∑ i, |q i|) * cubeBoundaryError ω U p v
  set B := cubeForm ω U (v - u) (v - u)
  have key : cubeNu ω U p - cubeMu ω U q - s - B / 2 / U.latticeVolume =
      ((cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1))) - s * L ^ (d - 1)) /
        U.latticeVolume := by
    rw [eq_div_iff hvol.ne']
    rw [← hLvol] at hid ⊢
    have hB : B / 2 / (L ^ (d - 1) * L) * (L ^ (d - 1) * L) = B / 2 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [hB]
  rw [key, abs_div, abs_of_pos hvol]
  have hLd : 0 < L ^ (d - 1) := by positivity
  have h1 : |cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1)) - s * L ^ (d - 1)| ≤
      E + |s| * L ^ (d - 1) := by
    calc |cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1)) - s * L ^ (d - 1)|
        ≤ |cubeCoarsePairing ω U q v - s * (L ^ (d - 1) * (L - 1))| + |s * L ^ (d - 1)| :=
          abs_sub _ _
      _ ≤ E + |s| * L ^ (d - 1) := by rw [abs_mul, abs_of_pos hLd]; linarith
  have e : |s| / L + E / U.latticeVolume = (E + |s| * L ^ (d - 1)) / U.latticeVolume := by
    rw [← hLvol]
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right h1 hvol.le

/-- **Ordering of `μ` and `ν`** (Armstrong and Dario, Corollary 4.6, deterministic form):
`μ(U, q) ≤ ν(U, p) - q · p` up to the boundary errors. -/
theorem exists_cubeMu_le_cubeNu_sub (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p q : Fin d → ℝ) :
    ∃ v ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w v = cubeFluxPairing ω U p w) ∧
      cubeMu ω U q ≤ cubeNu ω U p - ∑ i, q i * p i +
        (|∑ i, q i * p i| / (U.toIntegerCube.size : ℝ) +
          (∑ i, |q i|) * cubeBoundaryError ω U p v / U.latticeVolume) := by
  obtain ⟨u, -, -, v, hv, hvar_v, h⟩ := exists_abs_cubeNu_sub_cubeMu_sub_le hd hP hU p q
  refine ⟨v, hv, hvar_v, ?_⟩
  have hpos : 0 ≤ cubeForm ω U (v - u) (v - u) / 2 / U.latticeVolume :=
    div_nonneg (div_nonneg (cubeForm_self_nonneg _) (by norm_num)) U.latticeVolume_pos.le
  have := neg_abs_le (cubeNu ω U p - cubeMu ω U q - ∑ i, q i * p i -
    cubeForm ω U (v - u) (v - u) / 2 / U.latticeVolume)
  linarith

end Rigidity.Percolation
