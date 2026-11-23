import Mathlib

/-!
# The convexity inequality behind Stein's square function bound

For `1 < p ≤ 2` and `0 ≤ α, β ≤ M`,

  `β^p - α^p - p α^{p-1} (β - α) ≥ (p(p-1)/2) M^{p-2} (β - α)²`,

the Taylor bound with the second derivative `p(p-1) τ^{p-2} ≥ p(p-1) M^{p-2}` on `(0, M]`. It is the
lattice replacement of the identity (D.11) of Armstrong, Kuusi and Mourrat,
`Δ|v|^q - ∂_t|v|^q = q(q-1)|v|^{q-2}|∇v|²`, in the proof of their Proposition D.2.
-/

open Set

namespace Rigidity.Poincare

/-- **The strong convexity of `t ↦ t^p` on `[0, M]`**, `1 < p ≤ 2`. -/
theorem rpow_sub_tangent_ge {p M α β : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hα : 0 ≤ α)
    (hαM : α ≤ M) (hβ : 0 ≤ β) (hβM : β ≤ M) :
    p * (p - 1) / 2 * M ^ (p - 2) * (β - α) ^ 2 ≤
      β ^ p - α ^ p - p * α ^ (p - 1) * (β - α) := by
  set c := p * (p - 1) * M ^ (p - 2) with hc
  have hcont1 : Continuous fun t : ℝ => t ^ (p - 1) :=
    continuous_id.rpow_const fun _ => Or.inr (by linarith)
  have hcont0 : Continuous fun t : ℝ => t ^ p :=
    continuous_id.rpow_const fun _ => Or.inr (by linarith)
  have hdh : ∀ t : ℝ, 0 < t → HasDerivAt
      (fun t : ℝ => p * t ^ (p - 1) - p * α ^ (p - 1) - c * (t - α))
      (p * ((p - 1) * t ^ (p - 1 - 1)) - c * 1) t := by
    intro t ht
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := p - 1) (Or.inl ht.ne')
    exact ((h1.const_mul p).sub_const _).sub (((hasDerivAt_id' t).sub_const α).const_mul c)
  have hdg : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => t ^ p - α ^ p - p * α ^ (p - 1) * (t - α) - c / 2 * (t - α) ^ 2)
      (p * t ^ (p - 1) - p * α ^ (p - 1) - c * (t - α)) t := by
    intro t
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := p) (Or.inr hp1.le)
    have h2 : HasDerivAt (fun t : ℝ => (t - α) ^ 2) (2 * (t - α)) t := by
      have := (hasDerivAt_pow 2 (t - α)).comp t ((hasDerivAt_id' t).sub_const α)
      exact this.congr_deriv (by simp)
    have := ((h1.sub_const (α ^ p)).sub (((hasDerivAt_id' t).sub_const α).const_mul
      (p * α ^ (p - 1)))).sub (h2.const_mul (c / 2))
    exact this.congr_deriv (by ring)
  -- the derivative of `g` is nondecreasing on `[0, M]`
  have hmono : MonotoneOn (fun t : ℝ => p * t ^ (p - 1) - p * α ^ (p - 1) - c * (t - α))
      (Icc 0 M) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 M) ?_ ?_ ?_
    · exact (((hcont1.const_mul p).sub continuous_const).sub
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
    · rw [interior_Icc]
      intro t ht
      exact (hdh t ht.1).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hdh t ht.1).deriv]
      have hle : M ^ (p - 2) ≤ t ^ (p - 2) :=
        Real.rpow_le_rpow_of_nonpos ht.1 ht.2.le (by linarith)
      have e : p - 1 - 1 = p - 2 := by ring
      rw [e, hc]
      have hpp : 0 ≤ p * (p - 1) := by nlinarith
      nlinarith
  have hα0 : (fun t : ℝ => p * t ^ (p - 1) - p * α ^ (p - 1) - c * (t - α)) α = 0 := by
    simp only
    ring
  have hgcont : Continuous fun t : ℝ =>
      t ^ p - α ^ p - p * α ^ (p - 1) * (t - α) - c / 2 * (t - α) ^ 2 :=
    continuous_iff_continuousAt.2 fun t => (hdg t).continuousAt
  have key : 0 ≤ β ^ p - α ^ p - p * α ^ (p - 1) * (β - α) - c / 2 * (β - α) ^ 2 := by
    rcases le_total α β with hab | hab
    · have hm : MonotoneOn (fun t : ℝ =>
          t ^ p - α ^ p - p * α ^ (p - 1) * (t - α) - c / 2 * (t - α) ^ 2) (Icc α M) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc α M) hgcont.continuousOn
          (fun t _ => (hdg t).differentiableAt.differentiableWithinAt) ?_
        rw [interior_Icc]
        intro t ht
        rw [(hdg t).deriv]
        have := hmono ⟨hα, hαM⟩ ⟨by linarith [ht.1], ht.2.le⟩ ht.1.le
        rw [hα0] at this
        exact this
      have := hm ⟨le_rfl, hαM⟩ ⟨hab, hβM⟩ hab
      simp only at this
      have e0 : α ^ p - α ^ p - p * α ^ (p - 1) * (α - α) - c / 2 * (α - α) ^ 2 = 0 := by ring
      linarith
    · have hm : AntitoneOn (fun t : ℝ =>
          t ^ p - α ^ p - p * α ^ (p - 1) * (t - α) - c / 2 * (t - α) ^ 2) (Icc 0 α) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc 0 α) hgcont.continuousOn
          (fun t _ => (hdg t).differentiableAt.differentiableWithinAt) ?_
        rw [interior_Icc]
        intro t ht
        rw [(hdg t).deriv]
        have := hmono ⟨ht.1.le, by linarith [ht.2]⟩ ⟨hα, hαM⟩ ht.2.le
        rw [hα0] at this
        exact this
      have := hm ⟨hβ, hab⟩ ⟨hα, le_rfl⟩ hab
      simp only at this
      have e0 : α ^ p - α ^ p - p * α ^ (p - 1) * (α - α) - c / 2 * (α - α) ^ 2 = 0 := by ring
      linarith
  rw [hc] at key
  linarith

end Rigidity.Poincare
