import Rigidity.Proofs.Percolation.PlanarCoarseGradientMean

/-!
# The finite-volume homogenized matrices

The expectation `E[-μ(□_n, ·)]` is a quadratic form; we write it as `(1/2) q · ā_{□_n}⁻¹ q` with
the symmetric matrix `ā_{□_n}⁻¹` of its polarization (Armstrong and Dario, Section 5, the matrices
`ā_{□_n}` of Lemmas 5.6, 5.8 and 5.9, in dimension two). By the identity for the coarse pairing of
the minimizer of `μ`, the expected spatial average of the coarsened gradient of `u(·, □_n, q)` is
`ā_{□_n}⁻¹ q`:

`E[|□_n|⁻¹ ℓ_p(u(·, □_n, q)); P, □_n res] = p · ā_{□_n}⁻¹ q`,

which is the centering in Lemma 5.6 of Armstrong and Dario.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

/-- The matrix `ā_{□_n}⁻¹` of the quadratic form `2 E[-μ(□_n, ·)]` (in dimension two). -/
noncomputable def planarAhomInvFinite (p : unitInterval) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * planarMuMean p n ![1, 0],
    planarMuMean p n ![1, 1] - planarMuMean p n ![1, 0] - planarMuMean p n ![0, 1];
    planarMuMean p n ![1, 1] - planarMuMean p n ![1, 0] - planarMuMean p n ![0, 1],
    2 * planarMuMean p n ![0, 1]]

theorem planarAhomInvFinite_symm (p : unitInterval) (n : ℕ) (i j : Fin 2) :
    planarAhomInvFinite p n i j = planarAhomInvFinite p n j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- `E[-μ(□_n, q)] = (1/2) q · ā_{□_n}⁻¹ q`. -/
theorem planarMuMean_eq_planarAhomInvFinite {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (n : ℕ) (q : Fin 2 → ℝ) :
    planarMuMean p n q = 1 / 2 * ∑ i, ∑ j, q i * planarAhomInvFinite p n i j * q j := by
  have h := planarMuMean_smul_add_smul hpc n ![1, 0] ![0, 1] (q 0) (q 1)
  have hq : q 0 • (![1, 0] : Fin 2 → ℝ) + q 1 • ![0, 1] = q := by
    funext i
    fin_cases i <;> simp
  have h11 : (![1, 0] : Fin 2 → ℝ) + ![0, 1] = ![1, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hq, h11] at h
  rw [h]
  simp only [planarAhomInvFinite, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The polarization of `E[-μ(□_n, ·)]` is the bilinear form of `ā_{□_n}⁻¹`. -/
theorem planarMuMean_polarization {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (n : ℕ) (r q : Fin 2 → ℝ) :
    planarMuMean p n (r + q) - planarMuMean p n r - planarMuMean p n q =
      ∑ i, ∑ j, r i * planarAhomInvFinite p n i j * q j := by
  rw [planarMuMean_eq_planarAhomInvFinite hpc, planarMuMean_eq_planarAhomInvFinite hpc,
    planarMuMean_eq_planarAhomInvFinite hpc]
  simp only [Fin.sum_univ_two, Pi.add_apply]
  rw [planarAhomInvFinite_symm p n 1 0]
  ring

/-- **The expected spatial average of the coarsened gradient** (Armstrong and Dario, the centering
`ā_{□_n}⁻¹ q` in Lemma 5.6, in dimension two):
`E[|□_n|⁻¹ ℓ_r(u(·, □_n, q)); P, □_n res] = r · ā_{□_n}⁻¹ q`. -/
theorem integral_coarsePairing_planarMuMinimizer {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (n : ℕ) (r q : Fin 2 → ℝ) :
    ∫ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        coarsePairing ω ⟨n, 0⟩ r (planarMuMinimizer ω ⟨n, 0⟩ q) /
          (⟨n, 0⟩ : TriadicCube 2).volume else 0) ∂(latticeBondLaw 2 p) =
      ∑ i, ∑ j, r i * planarAhomInvFinite p n i j * q j := by
  set f : (Fin 2 → ℝ) → Configuration 2 → ℝ := fun s ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then -planarMu ω ⟨n, 0⟩ s else 0 with hf
  have hpt : (fun ω => if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
        coarsePairing ω ⟨n, 0⟩ r (planarMuMinimizer ω ⟨n, 0⟩ q) /
          (⟨n, 0⟩ : TriadicCube 2).volume else 0) =
      fun ω => f (r + q) ω - f r ω - f q ω := by
    funext ω
    simp only [hf]
    split_ifs with hω
    · rw [coarsePairing_planarMuMinimizer hω.1 hω.2]
      field_simp [(⟨n, 0⟩ : TriadicCube 2).volume_pos.ne']
      ring
    · ring
  have i1 : Integrable (f (r + q)) (latticeBondLaw 2 p) :=
    integrable_neg_planarMu_indicator hpc _ _
  have i2 : Integrable (f r) (latticeBondLaw 2 p) := integrable_neg_planarMu_indicator hpc _ _
  have i3 : Integrable (f q) (latticeBondLaw 2 p) := integrable_neg_planarMu_indicator hpc _ _
  have i12 : Integrable (fun ω => f (r + q) ω - f r ω) (latticeBondLaw 2 p) := i1.sub i2
  rw [hpt, integral_sub i12 i3, integral_sub i1 i2]
  have e : ∀ s, ∫ ω, f s ω ∂(latticeBondLaw 2 p) = planarMuMean p n s := fun s =>
    (planarMuMean_eq_integral p n s).symm
  rw [e, e, e]
  exact planarMuMean_polarization hpc n r q

/-- The matrix of the quadratic form `2 lim E[-μ(□_n, ·)]` (in dimension two). -/
noncomputable def planarAhomInvLimit (p : unitInterval) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * planarMuLimit p ![1, 0],
    planarMuLimit p ![1, 1] - planarMuLimit p ![1, 0] - planarMuLimit p ![0, 1];
    planarMuLimit p ![1, 1] - planarMuLimit p ![1, 0] - planarMuLimit p ![0, 1],
    2 * planarMuLimit p ![0, 1]]

/-- **The finite-volume matrices converge** (entrywise) to the matrix of `2 lim E[-μ]`. -/
theorem tendsto_planarAhomInvFinite {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (i j : Fin 2) :
    Tendsto (fun n => planarAhomInvFinite p n i j) atTop (𝓝 (planarAhomInvLimit p i j)) := by
  have h10 := tendsto_planarMuLimit hpc ![1, 0]
  have h01 := tendsto_planarMuLimit hpc ![0, 1]
  have h11 := tendsto_planarMuLimit hpc ![1, 1]
  fin_cases i <;> fin_cases j <;>
    simp only [planarAhomInvFinite, planarAhomInvLimit, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one]
  · exact h10.const_mul 2
  · exact (h11.sub h10).sub h01
  · exact (h11.sub h10).sub h01
  · exact h01.const_mul 2

/-- `lim E[-μ(□_n, q)] = (1/2) q · L q` for the limit matrix `L` of the finite-volume matrices. -/
theorem planarMuLimit_eq_planarAhomInvLimit {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (q : Fin 2 → ℝ) :
    planarMuLimit p q = 1 / 2 * ∑ i, ∑ j, q i * planarAhomInvLimit p i j * q j := by
  have hR : Tendsto (fun n => 1 / 2 * ∑ i, ∑ j, q i * planarAhomInvFinite p n i j * q j) atTop
      (𝓝 (1 / 2 * ∑ i, ∑ j, q i * planarAhomInvLimit p i j * q j)) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_)
    exact ((tendsto_planarAhomInvFinite hpc i j).const_mul (q i)).mul_const (q j)
  have hL := tendsto_planarMuLimit hpc q
  have heq : (fun n => planarMuMean p n q) =
      fun n => 1 / 2 * ∑ i, ∑ j, q i * planarAhomInvFinite p n i j * q j := by
    funext n
    exact planarMuMean_eq_planarAhomInvFinite hpc n q
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR

end Rigidity.Percolation
