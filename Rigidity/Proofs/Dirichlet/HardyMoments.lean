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

/-- `w_t ≥ exp(−γ H_t − 2γ² Σ_{s<t} 1/(s + 1)²)` for `0 ≤ γ ≤ 1/2`. -/
theorem exp_le_hardyWeight {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (t : ℕ) :
    exp (-(γ * (harmonic t : ℝ)) - 2 * γ ^ 2 *
      ∑ s ∈ Finset.range t, (((s : ℝ) + 1) ^ 2)⁻¹) ≤ hardyWeight γ t := by
  induction t with
  | zero => simp [hardyWeight_zero]
  | succ t ih =>
    rw [hardyWeight_succ, harmonic_succ, Finset.sum_range_succ]
    push_cast
    have ht : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    have hy0 : 0 ≤ γ / ((t : ℝ) + 1) := by positivity
    have hy : γ / ((t : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h1 := exp_neg_le_one_sub hy0 hy
    calc exp (-(γ * ((harmonic t : ℝ) + ((t : ℝ) + 1)⁻¹)) - 2 * γ ^ 2 *
          (∑ s ∈ Finset.range t, (((s : ℝ) + 1) ^ 2)⁻¹ + (((t : ℝ) + 1) ^ 2)⁻¹))
        = exp (-(γ * (harmonic t : ℝ)) - 2 * γ ^ 2 *
            ∑ s ∈ Finset.range t, (((s : ℝ) + 1) ^ 2)⁻¹) *
          exp (-(γ / ((t : ℝ) + 1) + 2 * (γ / ((t : ℝ) + 1)) ^ 2)) := by
          rw [← exp_add]
          congr 1
          field_simp
          ring
      _ ≤ hardyWeight γ t * (1 - γ / ((t : ℝ) + 1)) :=
          mul_le_mul ih h1 (exp_pos _).le (hardyWeight_pos (by linarith) t).le

/-- **Lower bound** `w_t ≥ e^{−γ − 4γ²} (t + 1)^{−γ}` for `0 ≤ γ ≤ 1/2`. -/
theorem rpow_le_hardyWeight {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 2) (t : ℕ) :
    exp (-γ - 4 * γ ^ 2) * ((t : ℝ) + 1) ^ (-γ) ≤ hardyWeight γ t := by
  refine le_trans ?_ (exp_le_hardyWeight hγ0 hγ t)
  rw [rpow_def_of_pos (by positivity), ← exp_add]
  refine exp_le_exp.mpr ?_
  have hH := harmonic_le_one_add_log t
  have hlog : log (t : ℝ) ≤ log ((t : ℝ) + 1) := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      simp
    · exact log_le_log (by exact_mod_cast h) (by linarith)
  have hS := sum_range_inv_sq_le_two t
  have hS0 : 0 ≤ ∑ s ∈ Finset.range t, (((s : ℝ) + 1) ^ 2)⁻¹ :=
    Finset.sum_nonneg fun s _ => by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * γ ^ 2)]

/-- `(t + 1)^{−β} ≤ ((t + 1)^{1−β} − t^{1−β})/(1 − β)` for `0 ≤ β < 1`, by Bernoulli. -/
theorem rpow_neg_le_sub_rpow {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1) (t : ℕ) :
    ((t : ℝ) + 1) ^ (-β) ≤ (((t : ℝ) + 1) ^ (1 - β) - (t : ℝ) ^ (1 - β)) / (1 - β) := by
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  have hB := rpow_one_add_le_one_add_mul_self (s := -1 / ((t : ℝ) + 1))
    (by rw [neg_div, neg_le_neg_iff, div_le_one ht1]; linarith)
    (p := 1 - β) (by linarith) (by linarith)
  have hfrac : 1 + -1 / ((t : ℝ) + 1) = (t : ℝ) / ((t : ℝ) + 1) := by
    field_simp
    ring
  rw [hfrac, div_rpow ht0 ht1.le, div_le_iff₀ (by positivity)] at hB
  have hsub : ((t : ℝ) + 1) ^ (-β) = ((t : ℝ) + 1) ^ (1 - β) / ((t : ℝ) + 1) := by
    rw [← rpow_sub_one ht1.ne']
    congr 1
    ring
  rw [le_div_iff₀ (by linarith), hsub]
  have : (1 + (1 - β) * (-1 / ((t : ℝ) + 1))) * ((t : ℝ) + 1) ^ (1 - β) =
      ((t : ℝ) + 1) ^ (1 - β) - ((t : ℝ) + 1) ^ (1 - β) / ((t : ℝ) + 1) * (1 - β) := by
    field_simp
    ring
  linarith

/-- **Sum of a negative power**: `Σ_{t<N} (t + 1)^{−β} ≤ N^{1−β}/(1 − β)` for `0 ≤ β < 1`. -/
theorem sum_range_rpow_neg_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1) (N : ℕ) :
    ∑ t ∈ Finset.range N, ((t : ℝ) + 1) ^ (-β) ≤ (N : ℝ) ^ (1 - β) / (1 - β) := by
  have htel := Finset.sum_range_sub (fun t : ℕ => (t : ℝ) ^ (1 - β)) N
  simp only [Nat.cast_zero, zero_rpow (show (1 - β) ≠ 0 by linarith), sub_zero,
    Nat.cast_add, Nat.cast_one] at htel
  calc ∑ t ∈ Finset.range N, ((t : ℝ) + 1) ^ (-β)
      ≤ ∑ t ∈ Finset.range N, (((t : ℝ) + 1) ^ (1 - β) - (t : ℝ) ^ (1 - β)) / (1 - β) :=
        Finset.sum_le_sum fun t _ => rpow_neg_le_sub_rpow hβ0 hβ t
    _ = (N : ℝ) ^ (1 - β) / (1 - β) := by rw [← Finset.sum_div, htel]

end Rigidity.Dirichlet
