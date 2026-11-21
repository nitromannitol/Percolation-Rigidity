/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/CoefficientUpperB.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Coarse

/-!
# The upper bound on the coarse-grained matrix `B_□`

For every `u`,
`2 q · 𝒢_□(u) - ℰ_□(u) = L^{-d} Σ_e w_□(e) (2 q_{j(e)} ∇u(e) - c_e ∇u(e)²)`,
and each summand is at most `q_{j(e)}²/c_e` (maximizing edge by edge). So
`q · B_□ q ≤ Σ_j q_j² L^{-d} Σ_{e ∥ e_j} w_□(e) c_e⁻¹`, the second half of
`(e:coefficient-upper)`.
-/

namespace LatticeHC

open LatticeProb Matrix

variable {d : ℕ}

/-- For `c > 0`, `2 q x - c x² ≤ q² / c` (complete the square). -/
private lemma two_mul_sub_mul_sq_le_div (q c x : ℝ) (hc : 0 < c) :
    2 * q * x - c * x ^ 2 ≤ q ^ 2 / c := by
  rw [le_div_iff₀ hc]
  nlinarith [sq_nonneg (q - c * x)]

/-- Factoring `L^{-d}` out of the mean-gradient pairing writes `2 q · 𝒢_□(u) - ℰ_□(u)` as
`L^{-d}` times the unnormalized objective. -/
private lemma objective_factor (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (q : Fin d → ℝ) (u : Site d → ℝ) :
    2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u =
      ((L : ℝ) ^ d)⁻¹ *
        (2 * (∑ j, q j * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
              faceWeight z L e * (u e.tgt - u e.src))
          - ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2) := by
  have hdot : (∑ j, q j * (((L : ℝ) ^ d)⁻¹ *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * (u e.tgt - u e.src)))
      = ((L : ℝ) ^ d)⁻¹ * (∑ j, q j *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * (u e.tgt - u e.src)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp only [dotProduct, cubeMeanGrad, cubeEnergy]
  rw [hdot]
  ring

/-- The unnormalized objective is the sum of the edgewise objectives over the edges of `□`. -/
private lemma objective_edge_sum (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (q : Fin d → ℝ) (u : Site d → ℝ) :
    2 * (∑ j, q j * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          faceWeight z L e * (u e.tgt - u e.src))
      - ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2
      = ∑ e ∈ edgesOf z L, faceWeight z L e *
          (2 * q e.2 * (u e.tgt - u e.src) - c e * (u e.tgt - u e.src) ^ 2) := by
  have h2Q : 2 * (∑ j, q j * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
        faceWeight z L e * (u e.tgt - u e.src))
      = ∑ e ∈ edgesOf z L,
          2 * q e.2 * (faceWeight z L e * (u e.tgt - u e.src)) := by
    rw [← Finset.sum_fiberwise (edgesOf z L) (fun e => e.2)
      (fun e => 2 * q e.2 * (faceWeight z L e * (u e.tgt - u e.src)))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [(Finset.mem_filter.1 he).2]
    ring
  have hE : ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2
      = ∑ e ∈ edgesOf z L,
          faceWeight z L e * (c e * (u e.tgt - u e.src) ^ 2) := by
    refine Finset.sum_congr rfl fun e _ => by ring
  rw [h2Q, hE, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => by ring

/-- `q · B_□ q ≤ Σ_j q_j² L^{-d} Σ_{e ∥ e_j} w_□(e) c_e⁻¹`. -/
theorem dotProduct_coarseB_le (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (q : Fin d → ℝ) :
    q ⬝ᵥ (coarseB c z L hc *ᵥ q) ≤
      ∑ j, q j ^ 2 * (((L : ℝ) ^ d)⁻¹ *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (c e)⁻¹) := by
  obtain ⟨u, hu⟩ := ((coarseB_spec c z L hc).2 q).1
  rw [hu]
  have hA : 0 ≤ ((L : ℝ) ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d)
  calc
    2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u
        = ((L : ℝ) ^ d)⁻¹ *
            (2 * (∑ j, q j * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
                  faceWeight z L e * (u e.tgt - u e.src))
              - ∑ e ∈ edgesOf z L,
                  faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2) :=
          objective_factor c z L q u
    _ ≤ ((L : ℝ) ^ d)⁻¹ *
          (∑ j, q j ^ 2 * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
              faceWeight z L e * (c e)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          rw [objective_edge_sum]
          calc
            ∑ e ∈ edgesOf z L, faceWeight z L e *
                (2 * q e.2 * (u e.tgt - u e.src) - c e * (u e.tgt - u e.src) ^ 2)
                ≤ ∑ e ∈ edgesOf z L, faceWeight z L e * (q e.2 ^ 2 / c e) := by
                  refine Finset.sum_le_sum fun e he => ?_
                  exact mul_le_mul_of_nonneg_left
                    (two_mul_sub_mul_sq_le_div (q e.2) (c e) (u e.tgt - u e.src)
                      (hc e he))
                    (by unfold faceWeight; positivity)
            _ = ∑ e ∈ edgesOf z L, q e.2 ^ 2 * (faceWeight z L e * (c e)⁻¹) := by
                  refine Finset.sum_congr rfl fun e _ => ?_
                  rw [div_eq_mul_inv]; ring
            _ = ∑ j, ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
                  q e.2 ^ 2 * (faceWeight z L e * (c e)⁻¹) := by
                  rw [← Finset.sum_fiberwise (edgesOf z L) (fun e => e.2)
                    (fun e => q e.2 ^ 2 * (faceWeight z L e * (c e)⁻¹))]
            _ = ∑ j, q j ^ 2 * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
                  faceWeight z L e * (c e)⁻¹ := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun e he => ?_
                  rw [(Finset.mem_filter.1 he).2]
    _ = ∑ j, q j ^ 2 * (((L : ℝ) ^ d)⁻¹ *
          ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
            faceWeight z L e * (c e)⁻¹) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring

end LatticeHC
