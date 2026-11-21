import Rigidity.Proofs.Percolation.PlanarMuNuComparison

/-!
# Quadratic response for `ν - μ`

For a resolved cube `U` with side `L` and slopes `p, q`, let `u` be the minimizer of `μ(U, q)` and
`v` the maximizer of `ν(U, p)` (affine on the boundary). By the comparison identity
`|U| ν(U, p) - |U| μ(U, q) - ℓ_q(v) = B(v - u, v - u) / 2` and the control of the spatial average of
the coarsened gradient of `v`,

`|ν(U, p) - μ(U, q) - q · p - B(v - u, v - u) / (2 |U|)| ≤ |q · p| / L + |q|₁ E_p(v) / |U|`,

with the boundary error `E_p(v)`. This is the first display of the proof of Lemma 5.9 of Armstrong
and Dario (the quantity `ν - μ - q · p` is controlled by the energy of `u - v`), in dimension two.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **Quadratic response for `ν - μ`** (Armstrong and Dario, proof of Lemma 5.9, first display, in
dimension two). -/
theorem exists_abs_planarNu_sub_planarMu_sub_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p q : Fin 2 → ℝ) :
    ∃ u ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w u = coarsePairing ω U q w) ∧
      ∃ v ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w v = fluxPairing ω U p w) ∧
      |planarNu ω U p - planarMu ω U q - ∑ i, q i * p i -
          clusterForm ω U (v - u) (v - u) / 2 / U.volume| ≤
        |∑ i, q i * p i| / (U.toIntegerCube.size : ℝ) +
          (|q 0| + |q 1|) * boundaryError ω U p v / U.volume := by
  obtain ⟨u, hu, hvar_u, hμ⟩ := exists_planarMu_minimizer hP hU q
  obtain ⟨v, hv, hvar_v, hν, c, hc⟩ := exists_planarNu_maximizer_affine hP hU p
  refine ⟨u, hu, hvar_u, v, hv, hvar_v, ?_⟩
  have hid := planarNu_sub_planarMu_eq p q hu hvar_u hμ hv hν
  have hb := abs_coarsePairing_sub_le hP hU p q hc
  have hvol := U.volume_pos
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hLvol : L * L = U.volume := by
    rw [hL]
    change ((3 ^ U.scale : ℕ) : ℝ) * ((3 ^ U.scale : ℕ) : ℝ) = (9 : ℝ) ^ U.scale
    push_cast
    rw [← mul_pow]
    norm_num
  have hL0 : 0 < L := by
    rw [hL]
    exact_mod_cast (show 0 < U.toIntegerCube.size from by
      change 0 < 3 ^ U.scale
      positivity)
  set s := ∑ i, q i * p i
  set E := (|q 0| + |q 1|) * boundaryError ω U p v
  set B := clusterForm ω U (v - u) (v - u)
  have key : planarNu ω U p - planarMu ω U q - s - B / 2 / U.volume =
      ((coarsePairing ω U q v - s * (L * (L - 1))) - s * L) / U.volume := by
    rw [← hLvol] at hid ⊢
    field_simp
    linarith
  rw [key, abs_div, abs_of_pos hvol]
  have h1 : |coarsePairing ω U q v - s * (L * (L - 1)) - s * L| ≤ E + |s| * L := by
    calc |coarsePairing ω U q v - s * (L * (L - 1)) - s * L|
        ≤ |coarsePairing ω U q v - s * (L * (L - 1))| + |s * L| := abs_sub _ _
      _ ≤ E + |s| * L := by rw [abs_mul, abs_of_pos hL0]; linarith
  have e : |s| / L + E / U.volume = (E + |s| * L) / U.volume := by
    rw [← hLvol]
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right h1 hvol.le

end Rigidity.Percolation
