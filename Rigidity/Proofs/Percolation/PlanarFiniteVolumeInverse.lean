import Rigidity.Proofs.Percolation.PlanarFiniteVolumeBounds

/-!
# The finite-volume homogenized matrices `ā_{□_n}`

From the scale `N` of the uniform ellipticity bound on, the matrices `ā_{□_n}⁻¹` are invertible; let
`ā_{□_n}` be their inverses. Writing `M_n = E[-μ(□_n, ·)] = (1/2) q · ā_{□_n}⁻¹ q`, we have
`M_n(ā_{□_n} r) = (1/2) r · ā_{□_n} r`, and the function `q ↦ M_n(q) - r · q` attains its minimum at
`q = ā_{□_n} r`:

`M_n(ā_{□_n} r) - r · ā_{□_n} r ≤ M_n(q) - r · q`

(Armstrong and Dario, Step 1 of the proof of Lemma 5.10, in dimension two). Moreover
`|ā_{□_n} eᵢ|² ≤ 324` and the entries of `ā_{□_n}⁻¹` are bounded.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

/-- The finite-volume homogenized matrix `ā_{□_n}`. -/
noncomputable def planarAhomFinite (p : unitInterval) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (planarAhomInvFinite p n)⁻¹

theorem sum_mul_planarAhomInvFinite_eq (p : unitInterval) (n : ℕ) (x : Fin 2 → ℝ) :
    ∑ i, ∑ j, x i * planarAhomInvFinite p n i j * x j =
      ∑ i, x i * (planarAhomInvFinite p n *ᵥ x) i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- **Invertibility of `ā_{□_n}⁻¹` from the scale `N` on.** -/
theorem exists_planarAhomInvFinite_mulVec_planarAhomFinite {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (∀ q : Fin 2 → ℝ, planarAhomInvFinite p n *ᵥ (planarAhomFinite p n *ᵥ q) = q) ∧
      ∀ q : Fin 2 → ℝ, (q 0 ^ 2 + q 1 ^ 2) / 36 ≤ planarMuMean p n q ∧
        planarMuMean p n q ≤ C * (q 0 ^ 2 + q 1 ^ 2) := by
  obtain ⟨C, hC, N, hb⟩ := exists_planarMuMean_bounds hpc
  refine ⟨C, hC, N, fun n hn => ⟨fun q => ?_, hb n hn⟩⟩
  have hdet : (planarAhomInvFinite p n).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have h1 := (hb n hn v).1
    rw [planarMuMean_eq_planarAhomInvFinite hpc, sum_mul_planarAhomInvFinite_eq, hBv] at h1
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
    apply hv
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.zero_apply]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Pi.zero_apply]
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  rw [planarAhomFinite, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet),
    Matrix.one_mulVec]

/-- `M_n(ā_{□_n} r) = (1/2) r · ā_{□_n} r` once `ā_{□_n}⁻¹ ā_{□_n} = I`. -/
theorem planarMuMean_planarAhomFinite {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {n : ℕ} (hinv : ∀ q : Fin 2 → ℝ, planarAhomInvFinite p n *ᵥ (planarAhomFinite p n *ᵥ q) = q)
    (r : Fin 2 → ℝ) :
    planarMuMean p n (planarAhomFinite p n *ᵥ r) =
      1 / 2 * ∑ i, r i * (planarAhomFinite p n *ᵥ r) i := by
  rw [planarMuMean_eq_planarAhomInvFinite hpc, sum_mul_planarAhomInvFinite_eq, hinv]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The minimum of `M_n(q) - r · q` is attained at `ā_{□_n} r`** (Armstrong and Dario, Step 1
of the proof of Lemma 5.10, in dimension two). -/
theorem planarMuMean_planarAhomFinite_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {n : ℕ}
    (hinv : ∀ q : Fin 2 → ℝ, planarAhomInvFinite p n *ᵥ (planarAhomFinite p n *ᵥ q) = q)
    (r q : Fin 2 → ℝ) :
    planarMuMean p n (planarAhomFinite p n *ᵥ r) - ∑ i, r i * (planarAhomFinite p n *ᵥ r) i ≤
      planarMuMean p n q - ∑ i, r i * q i := by
  set x := planarAhomFinite p n *ᵥ r with hx
  have h0 : 0 ≤ planarMuMean p n ((1 : ℝ) • q + (-1 : ℝ) • x) := ENNReal.toReal_nonneg
  rw [planarMuMean_smul_add_smul hpc, planarMuMean_polarization hpc] at h0
  have hpol : ∑ i, ∑ j, q i * planarAhomInvFinite p n i j * x j = ∑ i, q i * r i := by
    have : ∀ i, ∑ j, q i * planarAhomInvFinite p n i j * x j =
        q i * (planarAhomInvFinite p n *ᵥ x) i := fun i => by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    simp_rw [this, hx, hinv]
  rw [hpol] at h0
  have hM := planarMuMean_planarAhomFinite hpc hinv r
  rw [← hx] at hM
  have hc : ∑ i, q i * r i = ∑ i, r i * q i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hM]
  rw [hM] at h0
  linarith

/-- **Bound on `ā_{□_n} eᵢ`**: `|ā_{□_n} eᵢ|² ≤ 324` under the ellipticity bound `M_n ≥ |q|²/36`. -/
theorem planarAhomFinite_single_sq_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {n : ℕ} (hinv : ∀ q : Fin 2 → ℝ, planarAhomInvFinite p n *ᵥ (planarAhomFinite p n *ᵥ q) = q)
    (hlow : ∀ q : Fin 2 → ℝ, (q 0 ^ 2 + q 1 ^ 2) / 36 ≤ planarMuMean p n q) (i : Fin 2) :
    (planarAhomFinite p n *ᵥ Pi.single i 1) 0 ^ 2 +
      (planarAhomFinite p n *ᵥ Pi.single i 1) 1 ^ 2 ≤ 324 := by
  set x := planarAhomFinite p n *ᵥ Pi.single i 1 with hx
  have hM := planarMuMean_planarAhomFinite hpc hinv (Pi.single i 1)
  rw [← hx] at hM
  have hsum : ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j * x j = x i := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [hsum] at hM
  have hl := hlow x
  rw [hM] at hl
  have hxi : x i ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2 := by
    fin_cases i
    · simp only [Fin.zero_eta]
      nlinarith [sq_nonneg (x 1)]
    · simp only [Fin.mk_one]
      nlinarith [sq_nonneg (x 0)]
  set s := x 0 ^ 2 + x 1 ^ 2
  have hs0 : 0 ≤ s := by positivity
  have h18 : s ≤ 18 * x i := by linarith
  nlinarith [sq_nonneg (x i), sq_nonneg (s - 324)]

end Rigidity.Percolation
