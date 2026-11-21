import Rigidity.Proofs.Dirichlet.BoundaryLayer

/-!
# Averages: Jensen and weighted Hölder inequalities on finite sets

* Jensen's inequality for a nonnegative diagonal quadratic form: the quadratic form of the average
  is at most the average of the quadratic form. This is the convexity step (6.36) of the proof of
  Armstrong–Dario, Lemma 6.3: `p(y)·ā p(y) ≤ |□_n|^{-1} Σ_{y + □_n} ∇u_hom·ā ∇u_hom` for the
  mesoscopic average `p(y)` of `∇u_hom`; on the lattice it holds without the factor
  `(3^n − 1)^d / 3^{dn}` of the continuum cube.
* The normalized weighted Hölder inequality: for `0 < p' < p` and nonnegative weights `W`,
  `N⁻¹ Σ W |g|^{p'} ≤ (N⁻¹ Σ W^{p/(p−p')})^{1 − p'/p} (N⁻¹ Σ |g|^p)^{p'/p}`. This is the step of the
  proof of Armstrong–Dario, Lemma 6.4 (iii), that turns the coarse-gradient bound of Lemma 3.3
  (weights `size(□_𝒫(x))^{p'd − 1}`) into `(⨍ |∇w|^{p'})^{1/p'} ≤ C M` once the moments of the
  partition sizes are bounded.
-/

open Finset

namespace Rigidity.Dirichlet

/-- `#T (T⁻¹ Σ F)² ≤ Σ F²`. -/
theorem card_mul_sq_sum_div_card_le {ι : Type*} (T : Finset ι) (F : ι → ℝ) :
    (#T : ℝ) * ((∑ x ∈ T, F x) / #T) ^ 2 ≤ ∑ x ∈ T, F x ^ 2 := by
  rcases Nat.eq_zero_or_pos #T with h | h
  · rw [h, Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · have hT : (0 : ℝ) < #T := by exact_mod_cast h
    have h1 : (#T : ℝ) * ((∑ x ∈ T, F x) / #T) ^ 2 = (∑ x ∈ T, F x) ^ 2 / #T := by
      field_simp
    rw [h1, div_le_iff₀ hT, mul_comm]
    exact sq_sum_le_card_mul_sum_sq

/-- **Jensen's inequality for a diagonal quadratic form**: for `a_j ≥ 0`,
`#T Σ_j a_j (T⁻¹ Σ_{x∈T} F_j(x))² ≤ Σ_{x∈T} Σ_j a_j F_j(x)²`. -/
theorem card_mul_sum_quadratic_avg_le {ι : Type*} {d : ℕ} (T : Finset ι) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j) (F : ι → Fin d → ℝ) :
    (#T : ℝ) * ∑ j, a j * ((∑ x ∈ T, F x j) / #T) ^ 2 ≤ ∑ x ∈ T, ∑ j, a j * F x j ^ 2 := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← Finset.mul_sum, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (card_mul_sq_sum_div_card_le T fun x => F x j) (ha j)

/-- **Normalized weighted Hölder inequality**: for `0 < p' < p`, nonnegative weights `W` and
`N > 0`, `N⁻¹ Σ W |g|^{p'} ≤ (N⁻¹ Σ W^{p/(p − p')})^{1 − p'/p} (N⁻¹ Σ |g|^p)^{p'/p}`. -/
theorem sum_mul_rpow_div_le {ι : Type*} (T : Finset ι) (W g : ι → ℝ) (hW : ∀ x ∈ T, 0 ≤ W x)
    {p p' : ℝ} (hp' : 0 < p') (hpp : p' < p) {N : ℝ} (hN : 0 < N) :
    (∑ x ∈ T, W x * |g x| ^ p') / N ≤
      ((∑ x ∈ T, W x ^ (p / (p - p'))) / N) ^ (1 - p' / p) *
        ((∑ x ∈ T, |g x| ^ p) / N) ^ (p' / p) := by
  have hp : 0 < p := hp'.trans hpp
  have hpp' : 0 < p - p' := sub_pos.mpr hpp
  have hconj : (p / (p - p')).HolderConjugate (p / p') := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [one_lt_div hpp']; linarith, ?_⟩
    rw [inv_div, inv_div, ← add_div, sub_add_cancel, div_self hp.ne']
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg T hconj hW
    (g := fun x => |g x| ^ p') fun x _ => by positivity
  have hpow : ∀ x, (|g x| ^ p') ^ (p / p') = |g x| ^ p := fun x => by
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hp'.ne']
  simp only [hpow] at hH
  have he1 : 1 / (p / (p - p')) = 1 - p' / p := by field_simp
  have he2 : 1 / (p / p') = p' / p := by field_simp
  rw [he1, he2] at hH
  have hA : 0 ≤ ∑ x ∈ T, W x ^ (p / (p - p')) :=
    Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hW x hx) _
  have hB : 0 ≤ ∑ x ∈ T, |g x| ^ p := Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.div_rpow hA hN.le, Real.div_rpow hB hN.le, div_mul_div_comm, ← Real.rpow_add hN,
    show 1 - p' / p + p' / p = 1 by ring, Real.rpow_one]
  exact div_le_div_of_nonneg_right hH hN.le

end Rigidity.Dirichlet
