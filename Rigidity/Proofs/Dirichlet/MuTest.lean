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

/-- **The `μ` test with the coordinatewise defect**: under the hypotheses of
`quadratic_le_of_mu_test`, `p · ā p ≤ E + 2 δ + 2 Σ_k |a_k p_k| |G_k − p_k|`. -/
theorem quadratic_le_of_mu_test' (a p G : Fin d → ℝ) (ha : ∀ k, 0 < a k) {μ E δ : ℝ}
    (htest : μ ≤ E / 2 - ∑ k, a k * p k * G k)
    (hconv : |(∑ k, (a k * p k) ^ 2 / a k) / 2 + μ| ≤ δ) :
    ∑ k, a k * p k ^ 2 ≤ E + 2 * δ + 2 * ∑ k, |a k * p k| * |G k - p k| := by
  have hq : ∑ k, (a k * p k) ^ 2 / a k = ∑ k, a k * p k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by
      have := (ha k).ne'
      field_simp
  rw [hq] at hconv
  have hsplit : ∑ k, a k * p k * G k = ∑ k, a k * p k ^ 2 + ∑ k, (a k * p k) * (G k - p k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have habs : -(∑ k, |a k * p k| * |G k - p k|) ≤ ∑ k, (a k * p k) * (G k - p k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← abs_mul]
    exact neg_abs_le _
  have hlow := (abs_le.mp hconv).1
  rw [hsplit] at htest
  linarith

/-- **First variation along a line**: if `J(t) = −B t²/2 + L t` is maximal at `t = 1`, then
`B = L`. -/
theorem eq_of_isMaxOn_line {B L : ℝ} (h : ∀ t : ℝ, -(B * t ^ 2) / 2 + L * t ≤ -B / 2 + L) :
    B = L := by
  by_contra hne
  have h1 := h (1 + (L - B) / (|B| + 1))
  have hpos : 0 < |B| + 1 := by positivity
  set s := (L - B) / (|B| + 1) with hs
  -- `J(1 + s) − J(1) = s (L − B) − B s² / 2 > 0`
  have hsLB : s * (L - B) = (L - B) ^ 2 / (|B| + 1) := by rw [hs]; ring
  have hsq : B * s ^ 2 ≤ |B| * s ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg s)
  have hs2 : (|B| + 1) * s ^ 2 = s * (L - B) := by
    rw [hs]
    field_simp
  have hpos2 : 0 < (L - B) ^ 2 / (|B| + 1) := by
    have : (L - B) ^ 2 > 0 := by
      have : L - B ≠ 0 := fun h0 => hne (by linarith)
      positivity
    positivity
  nlinarith [sq_nonneg s]

/-- **Energy of the maximizer of `ν`**: if `v` maximizes `J(w) = (−B(w)/2 + L(w))/V` on a set of
competitors containing all multiples `t v` (with `B(t v) = t² B(v)` and `L(t v) = t L(v)`), then
`ν = J(v) = B(v)/(2V)`, and the convergence `|ν − P/2| ≤ δ` gives `B(v)/V ≤ P + 2δ`. -/
theorem energy_le_of_nu_maximizer {Bv Lv V ν P δ : ℝ} (hV : 0 < V)
    (hmax : ∀ t : ℝ, (-(Bv * t ^ 2) / 2 + Lv * t) / V ≤ ν) (hν : ν = (-Bv / 2 + Lv) / V)
    (hconv : |ν - P / 2| ≤ δ) : Bv / V ≤ P + 2 * δ := by
  have hline : ∀ t : ℝ, -(Bv * t ^ 2) / 2 + Lv * t ≤ -Bv / 2 + Lv := by
    intro t
    have := hmax t
    rw [hν, div_le_div_iff_of_pos_right hV] at this
    exact this
  have hBL := eq_of_isMaxOn_line hline
  have hνB : ν = Bv / 2 / V := by
    rw [hν, ← hBL]
    ring
  have := (abs_le.mp hconv).2
  rw [hνB] at this
  have e : Bv / V = 2 * (Bv / 2 / V) := by ring
  rw [e]
  linarith

end Rigidity.Dirichlet
