import Rigidity.Proofs.S2.InfluenceMomentRootSummation
import Rigidity.Proofs.Percolation.BondShellKernelBound

/-!
# Factorial growth of influence moments

A factorial bound with an exponential prefactor can be controlled by a fixed multiple of the
moment order raised to that order.
-/

namespace Rigidity.Proofs.S2

/-- Factorial moment bounds are at most a constant times the order, to that order. -/
theorem factorial_moment_le_order_pow (a A : ℝ) (ha : 0 < a) (hA : 0 < A) :
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, 1 ≤ n →
      (4 : ℝ) ^ (n + 1) * ((n.factorial : ℝ) / a ^ n) * A ≤ (L * n) ^ n := by
  let t : ℝ := max 2 (max A (1 / a))
  let L : ℝ := 16 * t ^ 2
  have ht2 : 2 ≤ t := le_max_left _ _
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 ≤ t := by linarith
  have hAt : A ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have hit : 1 / a ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨L, by dsimp [L]; positivity, fun n hn => ?_⟩
  have h4 : (4 : ℝ) ^ (n + 1) ≤ (16 : ℝ) ^ n := by
    calc
      _ ≤ (4 : ℝ) ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = (16 : ℝ) ^ n := by rw [pow_mul]; norm_num
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hA' : A ≤ t ^ n := hAt.trans (le_self_pow₀ ht1 (by omega))
  have hi0 : 0 ≤ 1 / a := by positivity
  have hi : (1 / a) ^ n ≤ t ^ n := pow_le_pow_left₀ hi0 hit n
  calc
    _ = (4 : ℝ) ^ (n + 1) * (n.factorial : ℝ) * (1 / a) ^ n * A := by
      simp only [div_eq_mul_inv, one_mul, inv_pow]
      ring
    _ ≤ (16 : ℝ) ^ n * (n : ℝ) ^ n * t ^ n * t ^ n := by gcongr
    _ = (L * n) ^ n := by dsimp [L]; simp only [mul_pow, pow_two]; ring

end Rigidity.Proofs.S2
