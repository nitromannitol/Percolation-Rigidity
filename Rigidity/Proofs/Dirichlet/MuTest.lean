import Mathlib

/-!
# The algebra of the `μ` test

Let `ā = diag(a_1, …, a_d)` with `a_k > 0`, `p, G ∈ ℝ^d`, `q = ā p`, and real numbers `μ`, `E`
with the test inequality `μ ≤ E/2 − q · G` and the convergence `|q · ā⁻¹ q / 2 + μ| ≤ δ`. Then
`p · ā p ≤ E + 2 δ + 2 |q| |G − p|`.

This is the computation of Step 1 of the proof of Armstrong–Dario, Lemma 6.2 (testing `u` in the
definition of `μ(y + □_n, q(y))` with `q(y) = ā p(y)` and using (6.10)), with `E` the normalized
energy of `u` on the mesoscopic cube and `G` the normalized coarse gradient; the error
`|G − p|` is bounded by the face estimate `sq_avg_grad_sub_avg_inner_le`.
-/

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- **The `μ` test.** -/
theorem quadratic_le_of_mu_test (a p G : Fin d → ℝ) (ha : ∀ k, 0 < a k) {μ E δ : ℝ}
    (htest : μ ≤ E / 2 - ∑ k, a k * p k * G k)
    (hconv : |(∑ k, (a k * p k) ^ 2 / a k) / 2 + μ| ≤ δ) :
    ∑ k, a k * p k ^ 2 ≤ E + 2 * δ +
      2 * (√(∑ k, (a k * p k) ^ 2) * √(∑ k, (G k - p k) ^ 2)) := by
  have hq : ∑ k, (a k * p k) ^ 2 / a k = ∑ k, a k * p k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by
      have := (ha k).ne'
      field_simp
  rw [hq] at hconv
  have hsplit : ∑ k, a k * p k * G k = ∑ k, a k * p k ^ 2 + ∑ k, (a k * p k) * (G k - p k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hcs : |∑ k, (a k * p k) * (G k - p k)| ≤
      √(∑ k, (a k * p k) ^ 2) * √(∑ k, (G k - p k) ^ 2) := by
    have h := Real.inner_le_Lp_mul_Lq Finset.univ (fun k => a k * p k) (fun k => G k - p k)
      Real.HolderConjugate.two_two
    have h' := Real.inner_le_Lp_mul_Lq Finset.univ (fun k => -(a k * p k)) (fun k => G k - p k)
      Real.HolderConjugate.two_two
    simp only [abs_neg, Real.rpow_two, sq_abs] at h h'
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h h'
    rw [abs_le]
    constructor
    · have : ∑ k, -(a k * p k) * (G k - p k) = -∑ k, (a k * p k) * (G k - p k) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this] at h'
      linarith
    · exact h
  have hlow := (abs_le.mp hconv).1
  rw [hsplit] at htest
  have := neg_abs_le (∑ k, (a k * p k) * (G k - p k))
  linarith

end Rigidity.Dirichlet
