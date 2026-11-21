import Rigidity.Proofs.Dirichlet.HardyWeight

/-!
# Size of the power-type weight

The weight `w_t = Π_{s<t} (1 − γ/(s + 1))` of `HardyWeight` satisfies, for `0 ≤ γ ≤ 1/2`,
`e^{−γ − 4γ²} (t + 1)^{−γ} ≤ w_t ≤ (t + 1)^{−γ}`: compare `1 − y` with `e^{−y}` and with
`e^{−y − 2y²}`, and the harmonic numbers with `log(t + 1)` (`log_add_one_le_harmonic`,
`harmonic_le_one_add_log`). Moreover `Σ_{t<N} (t + 1)^{−β} ≤ N^{1−β}/(1 − β)` for `0 ≤ β < 1`,
by Bernoulli's inequality `(1 + s)^p ≤ 1 + p s` and telescoping. These give the moments of the
Hardy weight of a cube and the factor `(ℓ/N)^γ` in the boundary-layer energy bound.
-/

namespace Rigidity.Dirichlet

open Real

/-- `w_t ≤ exp(−γ H_t)` with `H_t` the harmonic number. -/
theorem hardyWeight_le_exp {γ : ℝ} (hγ : γ < 1) (t : ℕ) :
    hardyWeight γ t ≤ exp (-(γ * (harmonic t : ℝ))) := by
  induction t with
  | zero => simp [hardyWeight_zero]
  | succ t ih =>
    rw [hardyWeight_succ, harmonic_succ]
    push_cast
    have h1 : 1 - γ / ((t : ℝ) + 1) ≤ exp (-(γ / ((t : ℝ) + 1))) := by
      have := add_one_le_exp (-(γ / ((t : ℝ) + 1)))
      linarith
    have h2 : 0 ≤ 1 - γ / ((t : ℝ) + 1) := (one_sub_div_pos hγ t).le
    calc hardyWeight γ t * (1 - γ / ((t : ℝ) + 1))
        ≤ exp (-(γ * (harmonic t : ℝ))) * exp (-(γ / ((t : ℝ) + 1))) :=
          mul_le_mul ih h1 h2 (exp_pos _).le
      _ = exp (-(γ * ((harmonic t : ℝ) + ((t : ℝ) + 1)⁻¹))) := by
          rw [← exp_add]
          congr 1
          ring

/-- **Upper bound** `w_t ≤ (t + 1)^{−γ}`. -/
theorem hardyWeight_le_rpow {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) (t : ℕ) :
    hardyWeight γ t ≤ ((t : ℝ) + 1) ^ (-γ) := by
  refine (hardyWeight_le_exp hγ t).trans ?_
  rw [rpow_def_of_pos (by positivity)]
  refine exp_le_exp.mpr ?_
  have h := log_add_one_le_harmonic t
  push_cast at h
  nlinarith

/-- `1 − y ≥ exp(−(y + 2y²))` for `0 ≤ y ≤ 1/2`. -/
theorem exp_neg_le_one_sub {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    exp (-(y + 2 * y ^ 2)) ≤ 1 - y := by
  have h1 := add_one_le_exp (y + 2 * y ^ 2)
  have hpos : 0 < y + 2 * y ^ 2 + 1 := by positivity
  rw [exp_neg, inv_le_comm₀ (exp_pos _) (by linarith)]
  calc (1 - y)⁻¹ ≤ y + 2 * y ^ 2 + 1 := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 1 - 2 * y by linarith)]
    _ ≤ exp (y + 2 * y ^ 2) := h1

/-- `Σ_{s<t} 1/(s + 1)² ≤ 2`. -/
theorem sum_range_inv_sq_le_two (t : ℕ) :
    ∑ s ∈ Finset.range t, (((s : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have hstep : ∀ s : ℕ, (((s : ℝ) + 1) ^ 2)⁻¹ ≤ 2 * (((s : ℝ) + 1)⁻¹ - ((s : ℝ) + 2)⁻¹) := by
    intro s
    have h1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
    have e : ((s : ℝ) + 1)⁻¹ - ((s : ℝ) + 2)⁻¹ = 1 / (((s : ℝ) + 1) * ((s : ℝ) + 2)) := by
      rw [inv_sub_inv h1.ne' h2.ne']
      ring
    rw [e, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htel : ∑ s ∈ Finset.range t, 2 * (((s : ℝ) + 1)⁻¹ - ((s : ℝ) + 2)⁻¹) =
      2 * (1 - ((t : ℝ) + 1)⁻¹) := by
    rw [← Finset.mul_sum]
    congr 1
    have := Finset.sum_range_sub' (fun s : ℕ => ((s : ℝ) + 1)⁻¹) t
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, inv_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring_nf
  calc ∑ s ∈ Finset.range t, (((s : ℝ) + 1) ^ 2)⁻¹
      ≤ ∑ s ∈ Finset.range t, 2 * (((s : ℝ) + 1)⁻¹ - ((s : ℝ) + 2)⁻¹) :=
        Finset.sum_le_sum fun s _ => hstep s
    _ = 2 * (1 - ((t : ℝ) + 1)⁻¹) := htel
    _ ≤ 2 := by
        have : 0 ≤ ((t : ℝ) + 1)⁻¹ := by positivity
        linarith

end Rigidity.Dirichlet
