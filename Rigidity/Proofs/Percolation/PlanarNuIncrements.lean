import Rigidity.Proofs.Percolation.PlanarNuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarMuIncrements

/-!
# The increments of the expectation of `ν` between successive triadic scales

Let `N_k(ξ) = E[ν(□_k, ξ)]` (on the partition event and the resolution of `□_k`). The increment
`J_k(ξ) = N_k(ξ) - N_{k+1}(ξ)` is a quadratic form in `ξ`, almost nonnegative by the approximate
monotonicity of `N`: `J_k(ξ) ≥ -C |ξ|₁² (3 ^ (-k/2) + exp (-c 3 ^ k))`. With
`f_i = ā⁻¹ e_i`, let `τ^ν_k = ∑_i (J_k(f_i))⁺` be the part of the quantity `τ_k` of Armstrong and
Dario (Section 5, before Lemma 5.4) coming from `ν`, and `τ_k = τ^μ_k + τ^ν_k`. For every basis
`f, g` and coefficients `a, b`,
`J_k(a f + b g) + J_k(a f - b g) = 2 (a² J_k(f) + b² J_k(g))`, so that

`J_k(ā⁻¹ q) ≤ 2 |q|² τ^ν_k + C |ā⁻¹ q̄|₁² (3 ^ (-k/2) + exp (-c 3 ^ k))`, `q̄ = (q₀, -q₁)`

(the part of display (5.9) of Armstrong and Dario coming from `ν`, in dimension two). Summing the
increments and inserting the bound on the energy of the differences between the maximizers at the
scales `m` and `n` gives Lemma 5.4 for `ν` in terms of `τ^ν` (display (5.10), second term).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- The increment `E[ν(□_k, ξ)] - E[ν(□_{k+1}, ξ)]`. -/
noncomputable def planarNuIncrement (p : unitInterval) (k : ℕ) (ξ : Fin 2 → ℝ) : ℝ :=
  planarNuMean p k ξ - planarNuMean p (k + 1) ξ

/-- The vector `ā⁻¹ e_i`. -/
noncomputable def planarAhomInvSingle (p : unitInterval) (i : Fin 2) : Fin 2 → ℝ :=
  (planarAhom p)⁻¹ *ᵥ (Pi.single i 1 : Fin 2 → ℝ)

/-- The part `∑_i (E[ν(□_k, ā⁻¹ e_i)] - E[ν(□_{k+1}, ā⁻¹ e_i)])⁺` of the quantity `τ_k` of
Armstrong and Dario coming from `ν`. -/
noncomputable def planarNuTau (p : unitInterval) (k : ℕ) : ℝ :=
  ∑ i : Fin 2, max (planarNuIncrement p k (planarAhomInvSingle p i)) 0

/-- The quantity `τ_k` of Armstrong and Dario (Section 5, before Lemma 5.4), in dimension two. -/
noncomputable def planarTau (p : unitInterval) (k : ℕ) : ℝ :=
  planarMuTau p k + planarNuTau p k

theorem planarNuTau_nonneg (p : unitInterval) (k : ℕ) : 0 ≤ planarNuTau p k :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem planarTau_nonneg (p : unitInterval) (k : ℕ) : 0 ≤ planarTau p k :=
  add_nonneg (planarMuTau_nonneg p k) (planarNuTau_nonneg p k)

/-- **Parallelogram identity for the increments of `E[ν]`.** -/
theorem planarNuIncrement_add_reflect (p : unitInterval) (k : ℕ) (f g : Fin 2 → ℝ) (a b : ℝ) :
    planarNuIncrement p k (a • f + b • g) + planarNuIncrement p k (a • f + (-b) • g) =
      2 * (a ^ 2 * planarNuIncrement p k f + b ^ 2 * planarNuIncrement p k g) := by
  simp only [planarNuIncrement]
  rw [planarNuMean_smul_add_smul p k, planarNuMean_smul_add_smul p (k + 1),
    planarNuMean_smul_add_smul p k, planarNuMean_smul_add_smul p (k + 1)]
  ring

/-- **Approximate nonnegativity of the increments of `E[ν]`.** -/
theorem exists_neg_le_planarNuIncrement {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (ξ : Fin 2 → ℝ),
      -(C * ((|ξ 0| + |ξ 1|) ^ 2 *
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)))) ≤
        planarNuIncrement p k ξ := by
  obtain ⟨C, hC, c, hc, hmono⟩ := exists_lintegral_planarNu_le_of_scale_le hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun k ξ => ?_⟩
  have h := hmono ⟨k + 1, 0⟩ ⟨k, 0⟩ (Nat.le_succ k) ξ
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p ⟨k, 0⟩ ξ)
  have h' := toReal_le_toReal_add_of_lintegral_le hfin hC (by positivity) h
  simp only [planarNuIncrement, planarNuMean]
  linarith

/-- **Sums control suprema for the increments of `E[ν]`** (the part of display (5.9) of Armstrong
and Dario coming from `ν`, in dimension two), for any pair of vectors `f, g`. -/
theorem exists_planarNuIncrement_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (f g : Fin 2 → ℝ) (a b : ℝ),
      planarNuIncrement p k (a • f + b • g) ≤
        2 * (a ^ 2 + b ^ 2) * (max (planarNuIncrement p k f) 0 + max (planarNuIncrement p k g) 0) +
        C * ((|(a • f + (-b) • g) 0| + |(a • f + (-b) • g) 1|) ^ 2 *
          (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))) := by
  obtain ⟨C, hC, c, hc, hlow⟩ := exists_neg_le_planarNuIncrement hpc
  refine ⟨C, hC, c, hc, fun k f g a b => ?_⟩
  have hpar := planarNuIncrement_add_reflect p k f g a b
  have hlr := hlow k (a • f + (-b) • g)
  set J₀ := planarNuIncrement p k f
  set J₁ := planarNuIncrement p k g
  have h0 : a ^ 2 * J₀ ≤ a ^ 2 * max J₀ 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
  have h1 : b ^ 2 * J₁ ≤ b ^ 2 * max J₁ 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
  have h0' : 0 ≤ b ^ 2 * max J₀ 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have h1' : 0 ≤ a ^ 2 * max J₁ 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  linarith

/-- The decomposition of `ā⁻¹ q` along the vectors `ā⁻¹ e_i`. -/
theorem planarAhom_inv_mulVec_eq (p : unitInterval) (q : Fin 2 → ℝ) :
    (planarAhom p)⁻¹ *ᵥ q = q 0 • planarAhomInvSingle p 0 + q 1 • planarAhomInvSingle p 1 := by
  have h := congrArg (fun r => (planarAhom p)⁻¹ *ᵥ r) (eq_smul_single_add_smul_single q)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul] at h
  exact h

/-- **The increments of `E[ν]` at `ā⁻¹ q` are controlled by `τ^ν`.** -/
theorem exists_planarNuIncrement_ahomInv_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (q : Fin 2 → ℝ),
      planarNuIncrement p k ((planarAhom p)⁻¹ *ᵥ q) ≤
        2 * (q 0 ^ 2 + q 1 ^ 2) * planarNuTau p k +
        C * ((|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
            |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2 *
          (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))) := by
  obtain ⟨C, hC, c, hc, hinc⟩ := exists_planarNuIncrement_le hpc
  refine ⟨C, hC, c, hc, fun k q => ?_⟩
  have h := hinc k (planarAhomInvSingle p 0) (planarAhomInvSingle p 1) (q 0) (q 1)
  have hr : (planarAhom p)⁻¹ *ᵥ ![q 0, -q 1] =
      q 0 • planarAhomInvSingle p 0 + (-q 1) • planarAhomInvSingle p 1 := by
    rw [planarAhom_inv_mulVec_eq]
    simp
  rw [planarAhom_inv_mulVec_eq, hr, planarNuTau, Fin.sum_univ_two]
  exact h

/-- The difference of the expectations of `ν` at two scales is the sum of the increments. -/
theorem planarNuMean_sub_planarNuMean_eq_sum (p : unitInterval) {n m : ℕ} (hnm : n ≤ m)
    (ξ : Fin 2 → ℝ) :
    planarNuMean p n ξ - planarNuMean p m ξ = ∑ k ∈ Finset.Ico n m, planarNuIncrement p k ξ := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [Finset.sum_Ico_succ_top hnm, ← ih, planarNuIncrement]
    ring

/-- **The decrease of `E[ν(·, ā⁻¹ q)]` between two scales is controlled by `τ^ν`.** -/
theorem exists_planarNuMean_ahomInv_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      planarNuMean p n ((planarAhom p)⁻¹ *ᵥ q) - planarNuMean p m ((planarAhom p)⁻¹ *ᵥ q) ≤
        2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarNuTau p k +
          C * (|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
            |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2 * ∑ k ∈ Finset.Ico n m,
            (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) := by
  obtain ⟨C, hC, c, hc, hinc⟩ := exists_planarNuIncrement_ahomInv_le hpc
  refine ⟨C, hC, c, hc, fun n m hnm q => ?_⟩
  rw [planarNuMean_sub_planarNuMean_eq_sum p hnm, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => (hinc k q).trans (le_of_eq ?_)
  ring

end Rigidity.Percolation
