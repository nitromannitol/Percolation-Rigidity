import Rigidity.Steps.Section5.FastDecay

/-!
# Theorem 1.3: the annulus step

Step `step:1.3-annulus`. Applying the annulus decay at the scale
`R = 3|x|/2` (so that `R/2 ≤ |x| < R`) gives `|x| |u(x)| ≤ ε` for `|x|` large: hence `u → 0` at
infinity, and `|x|₁ |u(x)| ≤ 2 |x| |u(x)| → 0` excludes eq. `linear-decay`. Eq.
`compactly-supported` gives finite support since Euclidean balls contain finitely many vertices.
-/

open LatticeProb.Percolation Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-- The annulus decay bounds `|x| |u(x)|` at large `|x|`. -/
theorem eucl_mul_abs_le_of_annulus {C : OpenComponent ω} {u : C → ℝ}
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ x : C,
      R / 2 ≤ eucl x.val → eucl x.val < R → R * |u x| ≤ ε) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → eucl x.val * |u x| ≤ ε := by
  obtain ⟨R₀, hR₀⟩ := hdec ε hε
  refine ⟨max R₀ 1, fun x hx => ?_⟩
  have he : 0 < eucl x.val := one_pos.trans_le ((le_max_right _ _).trans hx)
  have hxR₀ : R₀ ≤ eucl x.val := (le_max_left _ _).trans hx
  have h := hR₀ (3 / 2 * eucl x.val) (by linarith) x (by linarith) (by linarith)
  have hnn := mul_nonneg he.le (abs_nonneg (u x))
  linarith

/-- Step `step:1.3-annulus`. -/
theorem annulusStep : AnnulusStep := by
  intro ω C u hdec
  refine ⟨?_, ?_, ?_⟩
  · refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨R, hR⟩ := eucl_mul_abs_le_of_annulus hdec (half_pos hε)
    refine eventually_cofinite_of_forall_eucl_ge (R := max R 1) fun x hx => ?_
    rw [Real.dist_eq, sub_zero]
    have h1 : 1 ≤ eucl x.val := (le_max_right _ _).trans hx
    have h := hR x ((le_max_left _ _).trans hx)
    have hle := mul_le_mul_of_nonneg_right h1 (abs_nonneg (u x))
    linarith
  · rintro ⟨c, hc, hLD⟩
    obtain ⟨R, hR⟩ := eucl_mul_abs_le_of_annulus hdec (by positivity : 0 < c / 4)
    obtain ⟨x, hx, hcx⟩ := hLD (2 * |R|)
    have h2 := l1_le_two_mul_eucl x.val
    have h := hR x (by linarith [le_abs_self R])
    have hle := mul_le_mul_of_nonneg_right h2 (abs_nonneg (u x))
    linarith
  · rintro ⟨R, hR⟩
    exact (finite_eucl_lt C R).subset fun x hx => not_le.1 fun h => hx (hR x h)

end Rigidity.Proofs.Section5
