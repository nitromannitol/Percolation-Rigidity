import Rigidity.Proofs.Dirichlet.CubeStokes

/-!
# A directional discrete Hardy inequality

Let `Ω > 0` be a weight on `ℤ^d`, `k` a direction, `g = ∇_k Ω`, `Ω̄(x) = (Ω(x) + Ω(x + e_k))/2`,
`R = g²/Ω̄` and `ΔΩ(x) = Ω(x + e_k) + Ω(x − e_k) − 2 Ω(x)`. If `R(x) + R(x − e_k) ≤ κ ΔΩ(x)` on a
finite set `U`, then for every `φ` vanishing off `U` and every finite `Q ⊇ U` containing
`U − e_k`, `Σ_Q φ² ΔΩ ≤ 2κ Σ_Q Ω̄ (∇_k φ)²`: summation by parts in the direction `k` and Young's
inequality, as for the one-dimensional inequality `sum_sq_mul_secondDiff_le`.

This is the multidimensional form of the Hardy inequality used for the weighted energy estimate
of the discrete homogenized Dirichlet problem near the boundary of a cube, which replaces the
global Meyers estimate in the proof of Armstrong–Dario, Lemma 6.3, Step 3.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Shift invariance of sums of functions supported in `U`**: if `F` vanishes off `U`,
`U ⊆ Q` and `U − v ⊆ Q`, then `Σ_{x∈Q} F(x + v) = Σ_{x∈Q} F(x)`. -/
theorem sum_add_eq_sum_of_support {U Q : Finset (Vertex d)} (F : Vertex d → ℝ) (v : Vertex d)
    (hF : ∀ x, x ∉ U → F x = 0) (hUQ : U ⊆ Q) (hUv : ∀ y ∈ U, y - v ∈ Q) :
    ∑ x ∈ Q, F (x + v) = ∑ x ∈ Q, F x := by
  classical
  have h1 : ∑ x ∈ Q, F (x + v) = ∑ y ∈ Q.map (addRightEmbedding v), F y := by
    rw [Finset.sum_map]
    rfl
  have hU1 : U ⊆ Q.map (addRightEmbedding v) := fun y hy =>
    Finset.mem_map.mpr ⟨y - v, hUv y hy, by simp⟩
  rw [h1, ← Finset.sum_subset hU1 fun y _ hy => hF y hy,
    ← Finset.sum_subset hUQ fun y _ hy => hF y hy]

/-- Young's inequality `a b (−g) ≤ κ m a² + (4κ)⁻¹ (g²/m) b²` for `κ, m > 0`. -/
theorem mul_mul_neg_le_young {κ m : ℝ} (hκ : 0 < κ) (hm : 0 < m) (a b g : ℝ) :
    a * b * (-g) ≤ κ * (m * a ^ 2) + 1 / (4 * κ) * (g ^ 2 / m) * b ^ 2 := by
  rw [← sub_nonneg]
  have h : κ * (m * a ^ 2) + 1 / (4 * κ) * (g ^ 2 / m) * b ^ 2 - a * b * (-g) =
      (2 * κ * m * a + g * b) ^ 2 / (4 * κ * m) := by
    field_simp
    ring
  rw [h]
  positivity

/-- **Directional discrete Hardy inequality**. -/
theorem sum_sq_mul_dirSecondDiff_le (Ω : Vertex d → ℝ) (hΩ : ∀ x, 0 < Ω x) (k : Fin d)
    {U Q : Finset (Vertex d)} (hUQ : U ⊆ Q) (hUk : ∀ y ∈ U, y - unit k ∈ Q) {κ : ℝ}
    (hκ : 0 < κ)
    (hR : ∀ x ∈ U, (Ω (x + unit k) - Ω x) ^ 2 / ((Ω x + Ω (x + unit k)) / 2) +
      (Ω x - Ω (x - unit k)) ^ 2 / ((Ω (x - unit k) + Ω x) / 2) ≤
        κ * (Ω (x + unit k) + Ω (x - unit k) - 2 * Ω x))
    (φ : Vertex d → ℝ) (hφ : ∀ x, x ∉ U → φ x = 0) :
    ∑ x ∈ Q, φ x ^ 2 * (Ω (x + unit k) + Ω (x - unit k) - 2 * Ω x) ≤
      2 * κ * ∑ x ∈ Q, (Ω x + Ω (x + unit k)) / 2 * (φ (x + unit k) - φ x) ^ 2 := by
  set g : Vertex d → ℝ := fun x => Ω (x + unit k) - Ω x with hg
  set m : Vertex d → ℝ := fun x => (Ω x + Ω (x + unit k)) / 2 with hm
  set R : Vertex d → ℝ := fun x => g x ^ 2 / m x with hRdef
  have hm0 : ∀ x, 0 < m x := fun x => by
    have := hΩ x
    have := hΩ (x + unit k)
    simp only [hm]
    positivity
  have hR0 : ∀ x, 0 ≤ R x := fun x => div_nonneg (sq_nonneg _) (hm0 x).le
  have hsub : ∀ x, x - unit k + unit k = x := fun x => by abel
  set H := ∑ x ∈ Q, φ x ^ 2 * (Ω (x + unit k) + Ω (x - unit k) - 2 * Ω x) with hH
  set G := ∑ x ∈ Q, (Ω x + Ω (x + unit k)) / 2 * (φ (x + unit k) - φ x) ^ 2 with hG
  -- summation by parts in the direction `k`
  have hshift1 : ∑ x ∈ Q, φ (x + unit k) ^ 2 * g x = ∑ x ∈ Q, φ x ^ 2 * g (x - unit k) := by
    have := sum_add_eq_sum_of_support (fun y => φ y ^ 2 * g (y - unit k)) (unit k)
      (fun y hy => by simp [hφ y hy]) hUQ hUk
    simpa only [add_sub_cancel_right] using this
  have habel : H = ∑ x ∈ Q, (φ x ^ 2 - φ (x + unit k) ^ 2) * g x := by
    have e : H = ∑ x ∈ Q, φ x ^ 2 * g x - ∑ x ∈ Q, φ x ^ 2 * g (x - unit k) := by
      rw [hH, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hg, hsub]
      ring
    rw [e, ← hshift1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  -- Young's inequality on every edge
  have hpt : ∀ x ∈ Q, (φ x ^ 2 - φ (x + unit k) ^ 2) * g x ≤
      κ * (m x * (φ (x + unit k) - φ x) ^ 2) +
        1 / (4 * κ) * R x * (2 * φ x ^ 2 + 2 * φ (x + unit k) ^ 2) := by
    intro x _
    have hy := mul_mul_neg_le_young hκ (hm0 x) (φ (x + unit k) - φ x) (φ (x + unit k) + φ x)
      (g x)
    have hsq : (φ (x + unit k) + φ x) ^ 2 ≤ 2 * φ x ^ 2 + 2 * φ (x + unit k) ^ 2 := by
      nlinarith [sq_nonneg (φ (x + unit k) - φ x)]
    have hRnn : 0 ≤ 1 / (4 * κ) * R x := mul_nonneg (by positivity) (hR0 x)
    calc (φ x ^ 2 - φ (x + unit k) ^ 2) * g x =
          (φ (x + unit k) - φ x) * (φ (x + unit k) + φ x) * (-g x) := by ring
      _ ≤ κ * (m x * (φ (x + unit k) - φ x) ^ 2) +
            1 / (4 * κ) * (g x ^ 2 / m x) * (φ (x + unit k) + φ x) ^ 2 := hy
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hRnn)
  -- regrouping the ratio terms
  have hshift2 : ∑ x ∈ Q, R x * φ (x + unit k) ^ 2 = ∑ x ∈ Q, R (x - unit k) * φ x ^ 2 := by
    have := sum_add_eq_sum_of_support (fun y => R (y - unit k) * φ y ^ 2) (unit k)
      (fun y hy => by simp [hφ y hy]) hUQ hUk
    simpa only [add_sub_cancel_right] using this
  have hregroup : ∑ x ∈ Q, R x * (φ x ^ 2 + φ (x + unit k) ^ 2) =
      ∑ x ∈ Q, φ x ^ 2 * (R x + R (x - unit k)) := by
    have e0 : ∑ x ∈ Q, R x * (φ x ^ 2 + φ (x + unit k) ^ 2) =
        ∑ x ∈ Q, R x * φ x ^ 2 + ∑ x ∈ Q, R x * φ (x + unit k) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e0, hshift2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hRle : ∑ x ∈ Q, φ x ^ 2 * (R x + R (x - unit k)) ≤ κ * H := by
    rw [hH, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases hx : x ∈ U
    · have h := hR x hx
      have hRx : R x + R (x - unit k) = (Ω (x + unit k) - Ω x) ^ 2 / ((Ω x + Ω (x + unit k)) / 2) +
          (Ω x - Ω (x - unit k)) ^ 2 / ((Ω (x - unit k) + Ω x) / 2) := by
        simp only [hRdef, hg, hm, hsub]
      rw [hRx]
      have := mul_le_mul_of_nonneg_left h (sq_nonneg (φ x))
      linarith
    · rw [hφ x hx]
      simp
  have hsum := Finset.sum_le_sum hpt
  rw [← habel] at hsum
  have hsplit : ∑ x ∈ Q, (κ * (m x * (φ (x + unit k) - φ x) ^ 2) +
      1 / (4 * κ) * R x * (2 * φ x ^ 2 + 2 * φ (x + unit k) ^ 2)) =
      κ * G + 1 / (2 * κ) * ∑ x ∈ Q, R x * (φ x ^ 2 + φ (x + unit k) ^ 2) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [hG, Finset.mul_sum]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsplit, hregroup] at hsum
  have hhalf : 1 / (2 * κ) * ∑ x ∈ Q, φ x ^ 2 * (R x + R (x - unit k)) ≤ H / 2 := by
    calc 1 / (2 * κ) * ∑ x ∈ Q, φ x ^ 2 * (R x + R (x - unit k))
        ≤ 1 / (2 * κ) * (κ * H) := mul_le_mul_of_nonneg_left hRle (by positivity)
      _ = H / 2 := by
        field_simp
  linarith

end Rigidity.Dirichlet
