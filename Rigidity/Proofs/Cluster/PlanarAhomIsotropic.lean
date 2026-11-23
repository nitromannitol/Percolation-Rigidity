import Rigidity.Proofs.Cluster.PlanarSignedPermCluster
import Rigidity.Proofs.Cluster.PlanarReflectionMesh

/-!
# The homogenized matrix of the plane is a multiple of the identity

The limit `ν̄(ξ) = lim_m E[ν(□_m, ξ); 𝒫, □_m resolved] = (1/2) ξ · ā ξ` is invariant under the
reflection `ξ ↦ (-ξ₀, ξ₁)` and the transposition `ξ ↦ (ξ₁, ξ₀)`
(`planarNuLimit_signedPermSlope` with `planarMesh_reflect_iff` and `planarMesh_swap_iff`). The
first gives `ν̄(1, 1) = ν̄(-1, 1)`, hence, `ν̄` being quadratic, `ν̄(1, 1) = ν̄(1, 0) + ν̄(0, 1)`, so
the off-diagonal entries of `ā` vanish; the second gives `ν̄(1, 0) = ν̄(0, 1)`, so the diagonal
entries agree. Hence `ā = σ I` with `σ = 2 ν̄(1, 0) > 0`. Armstrong and Dario note this after
(5.22) (from the invariance of the model under the permutations and reflections of the coordinate
axes) but do not use it; the lattice proof of Section 6 here needs a diagonal `ā`, and the
regularity theory uses the harmonic functions of the plane.
-/

open LatticeProb.Percolation Rigidity.Proofs.S3

namespace Rigidity.Percolation

theorem meshInvariant_reflect : MeshInvariant (Equiv.refl (Fin 2)) reflectSigns :=
  planarMesh_reflect_iff

theorem meshInvariant_swap : MeshInvariant (Equiv.swap 0 1) (fun _ => 1) :=
  planarMesh_swap_iff

/-- `ν̄` is invariant under the reflection of the first coordinate. -/
theorem planarNuLimit_reflect (p : unitInterval) :
    planarNuLimit p ![-1, 1] = planarNuLimit p ![1, 1] := by
  have h := planarNuLimit_signedPermSlope meshInvariant_reflect p ![1, 1]
  have e : signedPermSlope (Equiv.refl (Fin 2)) reflectSigns ![1, 1] = ![-1, 1] := by
    funext i
    fin_cases i <;> simp [signedPermSlope]
  rw [e] at h
  exact h

/-- `ν̄` is invariant under the transposition of the coordinates. -/
theorem planarNuLimit_swap (p : unitInterval) :
    planarNuLimit p ![0, 1] = planarNuLimit p ![1, 0] := by
  have h := planarNuLimit_signedPermSlope meshInvariant_swap p ![1, 0]
  have e : signedPermSlope (Equiv.swap 0 1) (fun _ => 1) ![1, 0] = ![0, 1] := by
    funext i
    fin_cases i <;> simp [signedPermSlope]
  rw [e] at h
  exact h

/-- **The homogenized matrix is a multiple of the identity** (Armstrong and Dario, the remark
after (5.22), in dimension two): `ā = σ I` with `σ > 0`. -/
theorem exists_planarAhom_eq_smul_one {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ σ : ℝ, 0 < σ ∧ planarAhom p = σ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hq := planarNuLimit_smul_add_smul hpc ![1, 0] ![0, 1] (-1) 1
  have e1 : (-1 : ℝ) • (![1, 0] : Fin 2 → ℝ) + (1 : ℝ) • ![0, 1] = ![-1, 1] := by
    funext i
    fin_cases i <;> simp
  have e2 : (![1, 0] : Fin 2 → ℝ) + ![0, 1] = ![1, 1] := by
    funext i
    fin_cases i <;> simp
  rw [e1, e2, planarNuLimit_reflect] at hq
  have hoff : planarNuLimit p ![1, 1] - planarNuLimit p ![1, 0] - planarNuLimit p ![0, 1] = 0 := by
    linarith
  have hdiag := planarNuLimit_swap p
  obtain ⟨c, hc, hb⟩ := exists_planarAhom_bounds hpc
  have hlow := (hb ![1, 0]).1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    one_mul, zero_mul, mul_zero, add_zero, mul_one, one_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hlow
  refine ⟨2 * planarNuLimit p ![1, 0], ?_, ?_⟩
  · have h00 : planarAhom p 0 0 = 2 * planarNuLimit p ![1, 0] := rfl
    rw [h00] at hlow
    linarith
  · have e00 : planarAhom p 0 0 = 2 * planarNuLimit p ![1, 0] := rfl
    have e01 : planarAhom p 0 1 = 0 := hoff
    have e10 : planarAhom p 1 0 = 0 := hoff
    have e11 : planarAhom p 1 1 = 2 * planarNuLimit p ![1, 0] := by
      change 2 * planarNuLimit p ![0, 1] = _
      rw [hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

end Rigidity.Percolation
