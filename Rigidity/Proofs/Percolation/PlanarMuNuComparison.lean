import Rigidity.Proofs.Percolation.PlanarNablaAffineBound

/-!
# Comparison of `μ` and `ν`

For the minimizer `u` of `μ(U, q)` and the maximizer `v` of `ν(U, p)`,

`ν(U, p) |U| - μ(U, q) |U| - ℓ_q v = B (v - u) (v - u) / 2`

(Armstrong and Dario, (4.8)). Combined with the boundary expansion of `ℓ_q v`, this gives the
comparison `μ(U, q) ≤ ν(U, p) - p · q` up to boundary errors, and with `p = q / 9` the lower bound
`-μ(U, q) ≥ |q|² / 18` up to boundary errors (Armstrong and Dario, Corollary 4.6 and Lemma 4.7).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **The comparison identity** (Armstrong and Dario, (4.8)). -/
theorem planarNu_sub_planarMu_eq {U : TriadicCube 2} (p q : Fin 2 → ℝ) {u v : ClusterFun ω U}
    (hu : u ∈ clusterHarmonic ω U)
    (hvar_u : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w u = coarsePairing ω U q w)
    (hμ : planarMu ω U q = (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume)
    (hv : v ∈ clusterHarmonic ω U) (hν : planarNu ω U p = clusterForm ω U v v / 2 / U.volume) :
    planarNu ω U p * U.volume - planarMu ω U q * U.volume - coarsePairing ω U q v =
      clusterForm ω U (v - u) (v - u) / 2 := by
  have hvol := U.volume_pos.ne'
  rw [hν, hμ, div_mul_cancel₀ _ hvol, div_mul_cancel₀ _ hvol]
  have h1 := hvar_u v hv
  have h2 := hvar_u u hu
  rw [LinearMap.map_sub₂, map_sub, map_sub, clusterForm_symm u v]
  linarith

/-- **Comparison of `μ` and `ν` with boundary errors** (planar form of Armstrong and Dario,
Corollary 4.6). -/
theorem planarMu_le_planarNu_sub (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p q : Fin 2 → ℝ) :
    ∃ v ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w v = fluxPairing ω U p w) ∧
      planarMu ω U q ≤ planarNu ω U p - (∑ i, q i * p i) +
        (|∑ i, q i * p i| / (U.toIntegerCube.size : ℝ) +
          (|q 0| + |q 1|) * boundaryError ω U p v / U.volume) := by
  obtain ⟨u, hu, hvar_u, hμ⟩ := exists_planarMu_minimizer hP hU q
  obtain ⟨v, hv, hvar_v, hν, c, hc⟩ := exists_planarNu_maximizer_affine hP hU p
  refine ⟨v, hv, hvar_v, ?_⟩
  have hid := planarNu_sub_planarMu_eq p q hu hvar_u hμ hv hν
  have hpos := clusterForm_self_nonneg (v - u)
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
  -- `ℓ_q v ≥ s L (L - 1) - E`
  have hℓ : s * (L * (L - 1)) - E ≤ coarsePairing ω U q v := by
    have := neg_abs_le (coarsePairing ω U q v - s * (L * (L - 1)))
    linarith
  -- `μ |U| ≤ ν |U| - ℓ_q v`
  have hμν : planarMu ω U q * U.volume ≤ planarNu ω U p * U.volume -
      coarsePairing ω U q v := by linarith
  have hkey : planarMu ω U q * U.volume ≤
      (planarNu ω U p - s + (|s| / L + E / U.volume)) * U.volume := by
    rw [add_mul, sub_mul, add_mul, div_mul_cancel₀ _ hvol.ne', ← hLvol]
    have hs : s * L ≤ |s| / L * (L * L) := by
      rw [show |s| / L * (L * L) = |s| * L by field_simp]
      exact mul_le_mul_of_nonneg_right (le_abs_self s) hL0.le
    rw [← hLvol] at hμν
    nlinarith
  exact le_of_mul_le_mul_right hkey hvol

/-- **Lower bound for `-μ`** (planar form of Armstrong and Dario, Lemma 4.7). -/
theorem planarMu_le_neg_sq (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    ∃ v ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w v = fluxPairing ω U (fun i => q i / 9) w) ∧
      planarMu ω U q ≤ -(q 0 ^ 2 + q 1 ^ 2) / 18 +
        ((q 0 ^ 2 + q 1 ^ 2) / 9 / (U.toIntegerCube.size : ℝ) +
          (|q 0| + |q 1|) * boundaryError ω U (fun i => q i / 9) v / U.volume) := by
  obtain ⟨v, hv, hvar, hle⟩ := planarMu_le_planarNu_sub hP hU (fun i => q i / 9) q
  refine ⟨v, hv, hvar, ?_⟩
  have hν := planarNu_le (ω := ω) (U := U) (fun i => q i / 9)
  have hs : ∑ i, q i * (q i / 9) = (q 0 ^ 2 + q 1 ^ 2) / 9 := by
    rw [Fin.sum_univ_two]
    ring
  rw [hs] at hle
  have habs : |(q 0 ^ 2 + q 1 ^ 2) / 9| = (q 0 ^ 2 + q 1 ^ 2) / 9 :=
    abs_of_nonneg (by positivity)
  rw [habs] at hle
  have hp : (|q 0 / 9| + |q 1 / 9|) ^ 2 ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) / 81 := by
    rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
    have h1 : (|q 0| / 9 + |q 1| / 9) ^ 2 ≤ 2 * (|q 0| ^ 2 + |q 1| ^ 2) / 81 := by
      nlinarith [sq_nonneg (|q 0| - |q 1|)]
    rwa [sq_abs, sq_abs] at h1
  have hν' : planarNu ω U (fun i => q i / 9) ≤ (q 0 ^ 2 + q 1 ^ 2) / 18 := by
    nlinarith [hν, hp]
  linarith

end Rigidity.Percolation
