import Rigidity.Proofs.Percolation.PlanarOmegaCaccioppoli
import Rigidity.Proofs.Percolation.PlanarQuadraticResponse
import Rigidity.Proofs.Cluster.PlanarCoarseReach

/-!
# The pointwise chain of the proof of Lemma 5.9 of Armstrong and Dario

Let `V = □_n`, `U = □_{n+1}`, `n ≥ 1`, both resolved, on the partition event. Let `u_V, u_U` be the
minimizers of `μ(·, q)` and `v_V, v_U` the maximizers of `ν(·, p)`, `|p|₁ > 0`. Then, following the
proof of Lemma 5.9 of Armstrong and Dario (displays (5.38)-(5.41)):

* quadratic response (5.38): `ν(V, p) - μ(V, q) - q · p ≤ B_V(v_V - u_V)/(2|V|) + |q · p|/L
  + 9 |q|₁ |p|₁ Y_V`, with the boundary term `Y_V` of the maximizer of `ν`;
* `B_V(v_V - u_V) ≤ 3 (B_V(v_V - v_U) + B_V(v_U - u_U) + B_V(u_U - u_V))`, the outer terms being at
  most twice the energies of the differences of Lemma 5.4;
* the Caccioppoli inequality for the harmonic function `w = v_U - u_U` (5.39);
* the coarsening `w - [w]_P` (5.40), and `[w]_P - c = ([v_U]_P - ℓ_ξ - c_v) - ([u_U]_P - ℓ_ξ - c_u)`,
  whose mean squares are the flatness errors of Lemma 5.8 for any slope `ξ`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

open Rigidity.Proofs.Multiscale (finsetMean affineFun)

variable {ω : Configuration 2}

/-- `B(a + b + c) ≤ 3 (B(a) + B(b) + B(c))` for the Dirichlet form of a cluster. -/
theorem clusterForm_add_add_le {U : TriadicCube 2} (a b c : ClusterFun ω U) :
    clusterForm ω U (a + b + c) (a + b + c) ≤
      3 * (clusterForm ω U a a + clusterForm ω U b b + clusterForm ω U c c) := by
  have h2 : ∀ x y : ClusterFun ω U,
      2 * clusterForm ω U x y ≤ clusterForm ω U x x + clusterForm ω U y y := by
    intro x y
    have h := clusterForm_self_nonneg (x - y)
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [clusterForm_symm y x] at h
    linarith
  have hab := h2 a b
  have hac := h2 a c
  have hbc := h2 b c
  have e : clusterForm ω U (a + b + c) (a + b + c) = clusterForm ω U a a + clusterForm ω U b b +
      clusterForm ω U c c + 2 * clusterForm ω U a b + 2 * clusterForm ω U a c +
      2 * clusterForm ω U b c := by
    simp only [map_add, LinearMap.add_apply]
    rw [clusterForm_symm b a, clusterForm_symm c a, clusterForm_symm c b]
    ring
  rw [e]
  linarith

/-- `ν(U, p)` is half the energy of its maximizer, divided by the volume. -/
theorem planarNu_eq_planarNuMaximizer (U : TriadicCube 2) (p : Fin 2 → ℝ) :
    planarNu ω U p = clusterForm ω U (planarNuMaximizer ω U p) (planarNuMaximizer ω U p) / 2 /
      U.volume := by
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (exists_planarNu_maximizer (ω := ω) (U := U) p)
  have h1' : planarNuMaximizer ω U p ∈ clusterHarmonic ω U := h1
  have h2' : ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w (planarNuMaximizer ω U p) = fluxPairing ω U p w := h2
  change planarNu ω U p = (fluxPairing ω U p (planarNuMaximizer ω U p) -
    clusterForm ω U (planarNuMaximizer ω U p) (planarNuMaximizer ω U p) / 2) / U.volume at h3
  rw [h3, ← h2' _ h1']
  ring

/-- **Quadratic response** (Armstrong and Dario, (5.38), pointwise, in dimension two) for the
minimizer of `μ` and the maximizer of `ν`. -/
theorem planarNu_sub_planarMu_sub_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p q : Fin 2 → ℝ) :
    planarNu ω U p - planarMu ω U q - ∑ i, q i * p i ≤
      clusterForm ω U (planarNuMaximizer ω U p - planarMuMinimizer ω U q)
          (planarNuMaximizer ω U p - planarMuMinimizer ω U q) / 2 / U.volume +
        |∑ i, q i * p i| / (U.toIntegerCube.size : ℝ) +
        (|q 0| + |q 1|) * boundaryError ω U p (planarNuMaximizer ω U p) / U.volume := by
  set u := planarMuMinimizer ω U q with hu
  set v := planarNuMaximizer ω U p with hv
  obtain ⟨huA, hvar_u⟩ := planarMuMinimizer_spec hP hU q
  obtain ⟨hvA, hvar_v⟩ := planarNuMaximizer_spec (ω := ω) U p
  rw [← hu] at huA hvar_u
  rw [← hv] at hvA hvar_v
  have hvol := U.volume_pos
  have hμ : planarMu ω U q = (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume := by
    have h := planarMu_mul_volume_eq hP hU q huA hvar_u
    rw [← hvar_u u huA]
    field_simp
    linarith
  have hν : planarNu ω U p = clusterForm ω U v v / 2 / U.volume :=
    planarNu_eq_planarNuMaximizer U p
  obtain ⟨c, hc⟩ := exists_affine_boundary_of_variation hP hU p hvar_v
  have hid := planarNu_sub_planarMu_eq p q huA hvar_u hμ hvA hν
  have hb := abs_coarsePairing_sub_le hP hU p q hc
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hLvol : L * L = U.volume := cast_size_mul_self U
  have hL0 : 0 < L := by have := one_le_cast_size U; linarith
  set s := ∑ i, q i * p i
  set E := (|q 0| + |q 1|) * boundaryError ω U p v
  set B := clusterForm ω U (v - u) (v - u)
  have key : planarNu ω U p - planarMu ω U q - s - B / 2 / U.volume =
      ((coarsePairing ω U q v - s * (L * (L - 1))) - s * L) / U.volume := by
    rw [← hLvol] at hid ⊢
    field_simp
    linarith
  have h1 : (coarsePairing ω U q v - s * (L * (L - 1))) - s * L ≤ E + |s| * L := by
    have := le_abs_self (coarsePairing ω U q v - s * (L * (L - 1)))
    have := neg_abs_le s
    nlinarith
  have h2 : planarNu ω U p - planarMu ω U q - s - B / 2 / U.volume ≤ |s| / L + E / U.volume := by
    rw [key]
    have e : |s| / L + E / U.volume = (E + |s| * L) / U.volume := by
      rw [← hLvol]
      field_simp
      ring
    rw [e]
    exact div_le_div_of_nonneg_right h1 hvol.le
  have e3 : E / U.volume = (|q 0| + |q 1|) * boundaryError ω U p v / U.volume := rfl
  linarith

/-- The boundary error of the maximizer of `ν`, for `|p|₁ > 0`:
`E_p(v) / |U| ≤ 9 |p|₁ (162001 S / (L √L) + 1 / (2 √L))`. -/
theorem boundaryError_div_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p : Fin 2 → ℝ) (hp : 0 < |p 0| + |p 1|) :
    boundaryError ω U p (planarNuMaximizer ω U p) / U.volume ≤
      9 * (|p 0| + |p 1|) * (162001 * (∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4) /
        ((U.toIntegerCube.size : ℝ) * Real.sqrt (U.toIntegerCube.size : ℝ)) +
        1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ)) := by
  obtain ⟨hvA, hvar⟩ := planarNuMaximizer_spec (ω := ω) U p
  have h := mul_boundaryError_div_le hP hU p hvA hvar
  set P₁ := |p 0| + |p 1|
  set Y := 162001 * (∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4) /
    ((U.toIntegerCube.size : ℝ) * Real.sqrt (U.toIntegerCube.size : ℝ)) +
    1 / 2 / Real.sqrt (U.toIntegerCube.size : ℝ)
  set E := boundaryError ω U p (planarNuMaximizer ω U p)
  have h1 : P₁ * (E / U.volume) ≤ P₁ * (9 * P₁ * Y) := by
    have e1 : P₁ * (E / U.volume) = P₁ * E / U.volume := by ring
    have e2 : P₁ * (9 * P₁ * Y) = 9 * P₁ ^ 2 * Y := by ring
    rw [e1, e2]
    exact h
  exact le_of_mul_le_mul_left h1 hp

end Rigidity.Percolation
