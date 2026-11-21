import Rigidity.Proofs.Percolation.BondShellKernelBound

/-!
# Moment-order growth of planar shell kernels

When the decay rate is divided by the moment order, the total quadratic shell weight grows at
most as the eighth power of that order.
-/

namespace Rigidity.Percolation

/-- The quadratic shell kernel at rate `c/r` has eighth-order growth in `r`. -/
theorem shell_kernel_sum_order_growth (c : ℝ) (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℕ, 1 ≤ r →
      Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 *
        Real.exp (-(c * (1 / (r : ℝ))) * Real.sqrt n)) ∧
      1 + (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 *
        Real.exp (-(c * (1 / (r : ℝ))) * Real.sqrt n)) ≤ D * (r : ℝ) ^ 8 := by
  obtain ⟨E, hE, hkernel⟩ := shell_kernel_sum_le_inverse_eighth
  let D : ℝ := 1 + E * (1 + (1 / c) ^ 8)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun r hr => ?_⟩
  have hu1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hu : 0 < (r : ℝ) := zero_lt_one.trans_le hu1
  have hu0 : (r : ℝ) ≠ 0 := ne_of_gt hu
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hrate : 0 < c * (1 / (r : ℝ)) := by positivity
  obtain ⟨hs, hsum⟩ := hkernel (c * (1 / (r : ℝ))) hrate
  have hinv : 1 / (c * (1 / (r : ℝ))) = (1 / c) * (r : ℝ) := by field_simp
  rw [hinv, mul_pow] at hsum
  have hp : (1 : ℝ) ≤ (r : ℝ) ^ 8 := one_le_pow₀ hu1
  refine ⟨hs, ?_⟩
  calc
    _ ≤ 1 + E * (1 + (1 / c) ^ 8 * (r : ℝ) ^ 8) := add_le_add le_rfl hsum
    _ ≤ (r : ℝ) ^ 8 + E * ((r : ℝ) ^ 8 + (1 / c) ^ 8 * (r : ℝ) ^ 8) :=
      add_le_add hp (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) hE.le)
    _ = D * (r : ℝ) ^ 8 := by dsimp [D]; ring

end Rigidity.Percolation
