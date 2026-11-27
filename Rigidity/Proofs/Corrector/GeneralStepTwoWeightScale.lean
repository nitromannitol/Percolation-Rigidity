import Rigidity.Proofs.Corrector.DarioStepTwoWeightScale

/-!
# The failure probability of the weight bound of a triadic cube of `ℤᵈ`: the real bounds

This is the real-number part of the planar file `DarioStepTwoWeightScale`, in every dimension `d`.
A triadic cube of scale `n` has `(3^d)ⁿ` vertices. At scale `n` take `D = ⌈3 + bq⌉`, the range
`R = 3^{⌊n/D⌋}` and the scale `m = ⌊n/D⌋ + K` of the residue classes, `K = 6κ + 21`. Then
`(3^d)ⁿ ≤ (3^d)^D R^{dD}` (`three_pow_pow_le`), `R^{dD} ≤ (3^d)^K R^d (3^d)^{n-m}`
(`pow_mul_le_three_pow_pow`), and the exponent of the Chernoff bound with a finite-range weight
at most `K₀ R^b` is at least `R / ((3^d)^K K₀^q)` (`exp_chernoff_le`). With the dimension-free
bounds of the planar file (powers of `R` absorbed by a stretched exponential, and
`R^σ ≥ 3^{-σ} (3ⁿ)^{σ/D}`), a domination failure probability `C R^a e^{-c R^σ}` per vertex and a
finite-range weight at most `K₀ R^b` give a failure bound `C_f e^{-c_f (3ⁿ)^{σ/D}}`
(`weight_failure_real_le`).

The planar file has `d = 2`, the base `9 = 3²`, the power `a = 4`, the power `b = 29` with the
constant `K₀ = 18 (49·29)^9 κ^18`, and `σ ≤ 1/2`; here `a`, `b` and `K₀ > 0` are parameters,
`σ ≤ 1` and `q ≥ 0` suffice, and the range constant `6κ + 21` is unchanged (the finite-range boxes
are `ℓ^∞` boxes, whose radii do not depend on `d`).
-/

namespace Rigidity.Corrector.GeneralDim

theorem three_pow_pow_le {d n D : ℕ} (hD : 0 < D) :
    ((3 : ℝ) ^ d) ^ n ≤ ((3 : ℝ) ^ d) ^ D * ((3 : ℝ) ^ (n / D)) ^ (d * D) := by
  have h1 : n ≤ D * (n / D) + D := (Rigidity.Corrector.lt_mul_div_add hD).le
  calc ((3 : ℝ) ^ d) ^ n ≤ ((3 : ℝ) ^ d) ^ (D * (n / D) + D) :=
        pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) h1
    _ = ((3 : ℝ) ^ d) ^ D * ((3 : ℝ) ^ (n / D)) ^ (d * D) := by
        simp only [← pow_mul, ← pow_add]
        congr 1
        ring

theorem pow_mul_le_three_pow_pow {d n D K : ℕ} (hn : n / D + K ≤ n) :
    ((3 : ℝ) ^ (n / D)) ^ (d * D) ≤
      ((3 : ℝ) ^ d) ^ K * ((3 : ℝ) ^ (n / D)) ^ d * ((3 : ℝ) ^ d) ^ (n - (n / D + K)) := by
  have hdr : D * (n / D) ≤ n := Nat.mul_div_le n D
  have e : ((3 : ℝ) ^ d) ^ K * ((3 : ℝ) ^ (n / D)) ^ d * ((3 : ℝ) ^ d) ^ (n - (n / D + K)) =
      ((3 : ℝ) ^ d) ^ n := by
    have e1 : ((3 : ℝ) ^ d) ^ K * ((3 : ℝ) ^ (n / D)) ^ d = ((3 : ℝ) ^ d) ^ (n / D + K) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    rw [e1, ← pow_add, Nat.add_sub_of_le hn]
  rw [e]
  calc ((3 : ℝ) ^ (n / D)) ^ (d * D) = ((3 : ℝ) ^ d) ^ (D * (n / D)) := by
        simp only [← pow_mul]
        congr 1
        ring
    _ ≤ ((3 : ℝ) ^ d) ^ n := pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hdr

/-- The exponent of the Chernoff bound is at least `R / ((3^d)^K K₀^q)`. -/
theorem exp_chernoff_le {R K₀ q J : ℝ} {d b D K : ℕ} (hR : 1 ≤ R) (hK₀ : 0 < K₀)
    (hD : b * q + 1 ≤ ((d * D - d : ℕ) : ℝ)) (hdD : d ≤ d * D)
    (hJ : R ^ (d * D) ≤ ((3 : ℝ) ^ d) ^ K * R ^ d * J) :
    Real.exp (-(J * 1) / (K₀ * R ^ b) ^ q) ≤
      Real.exp (-(1 / (((3 : ℝ) ^ d) ^ K * K₀ ^ q) * R)) := by
  have hR0 : 0 < R := by linarith
  have hA : (K₀ * R ^ b) ^ q = K₀ ^ q * R ^ (b * q) := by
    rw [Real.mul_rpow hK₀.le (by positivity), Real.rpow_natCast_mul hR0.le]
  have hRk : R * R ^ (b * q) ≤ R ^ (d * D - d) := by
    calc R * R ^ (b * q) = R ^ (b * q + 1) := by rw [Real.rpow_add_one hR0.ne']; ring
      _ ≤ R ^ (((d * D - d : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hR hD
      _ = R ^ (d * D - d) := Real.rpow_natCast R _
  have h9 : R ^ (d * D - d) ≤ ((3 : ℝ) ^ d) ^ K * J := by
    have e : R ^ (d * D) = R ^ (d * D - d) * R ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hdD]
    rw [e] at hJ
    have hRd : 0 < R ^ d := by positivity
    nlinarith
  have hJ0 : 0 ≤ J := by
    have : 0 ≤ R ^ (d * D - d) := by positivity
    have h9K : (0 : ℝ) < ((3 : ℝ) ^ d) ^ K := by positivity
    nlinarith
  have hA0 : 0 < K₀ ^ q * R ^ (b * q) := by positivity
  refine Real.exp_le_exp.2 ?_
  rw [hA, mul_one, neg_div, neg_le_neg_iff, div_mul_eq_mul_div, one_mul,
    div_le_div_iff₀ (by positivity) hA0]
  calc R * (K₀ ^ q * R ^ (b * q)) = K₀ ^ q * (R * R ^ (b * q)) := by ring
    _ ≤ K₀ ^ q * (((3 : ℝ) ^ d) ^ K * J) :=
        mul_le_mul_of_nonneg_left (hRk.trans h9) (by positivity)
    _ = J * (((3 : ℝ) ^ d) ^ K * K₀ ^ q) := by ring

/-- **The real form of the failure bound** at scale `n` in dimension `d`, for `R = 3^{⌊n/D⌋}` and
`D = ⌈3 + bq⌉`: a domination failure probability `C R^a e^{-c R^σ}` at each of the `(3^d)ⁿ`
vertices of the cube, and the Chernoff bound over the `(3^d)^m` residue classes, `m = ⌊n/D⌋ + K`,
of `(3^d)^{n-m}` points each, for a finite-range weight at most `K₀ R^b`, add up to at most
`C_f e^{-c_f (3ⁿ)^{σ/D}}`. -/
theorem weight_failure_real_le {d : ℕ} (hd : 1 ≤ d) {κ a b : ℕ} {q K₀ C c σ : ℝ} (hq : 0 ≤ q)
    (hK₀ : 0 < K₀) (hC : 0 ≤ C) (hc : 0 < c) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∃ Cf cf : ℝ, 0 ≤ Cf ∧ 0 < cf ∧ ∀ (n : ℕ) (R : ℝ), R = (3 : ℝ) ^ (n / ⌈3 + b * q⌉₊) →
      n / ⌈3 + b * q⌉₊ + (6 * κ + 21) ≤ n →
      ((3 : ℝ) ^ d) ^ n * (C * R ^ a * Real.exp (-(c * R ^ σ))) +
        ((3 : ℝ) ^ d) ^ (n / ⌈3 + b * q⌉₊ + (6 * κ + 21)) *
          Real.exp (-(((3 : ℝ) ^ d) ^ (n - (n / ⌈3 + b * q⌉₊ + (6 * κ + 21))) * 1) /
            (K₀ * R ^ b) ^ q) ≤
      Cf * Real.exp (-cf * ((3 : ℝ) ^ n) ^ (σ / ⌈3 + b * q⌉₊)) := by
  set D := ⌈3 + b * q⌉₊
  have hbq : 0 ≤ (b : ℝ) * q := mul_nonneg (Nat.cast_nonneg b) hq
  have hD3 : 3 + b * q ≤ (D : ℝ) := Nat.le_ceil _
  have hDpos : 0 < D := by
    have : (0 : ℝ) < D := by linarith
    exact_mod_cast this
  set B : ℝ := (3 : ℝ) ^ d with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  set K := 6 * κ + 21
  set c' : ℝ := 1 / (B ^ K * K₀ ^ q)
  have hc'0 : 0 < c' := by positivity
  set t : ℝ := min c c'
  have ht0 : 0 < t := lt_min hc hc'0
  have htc : t ≤ c := min_le_left _ _
  have htc' : t ≤ c' := min_le_right _ _
  have hdD1 : 1 ≤ d * D + a := le_add_right (Nat.mul_pos hd hDpos)
  obtain ⟨K₁, hK₁, hB1⟩ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ R : ℝ, 1 ≤ R →
      R ^ (d * D + a) * Real.exp (-(t * R ^ σ)) ≤ K₁ * Real.exp (-(t / 2 * R ^ σ)) :=
    ⟨_, by positivity, fun R hR =>
      Rigidity.Corrector.pow_mul_exp_neg_rpow_le_half hR ht0 hσ0 hdD1⟩
  obtain ⟨K₂, hK₂, hB2⟩ : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ R : ℝ, 1 ≤ R →
      R ^ d * Real.exp (-(t * R ^ σ)) ≤ K₂ * Real.exp (-(t / 2 * R ^ σ)) :=
    ⟨_, by positivity, fun R hR => Rigidity.Corrector.pow_mul_exp_neg_rpow_le_half hR ht0 hσ0 hd⟩
  refine ⟨B ^ D * C * K₁ + B ^ K * K₂, t / 2 * (3 : ℝ) ^ (-σ), by positivity,
    by positivity, fun n R hRn hn => ?_⟩
  have hR1 : 1 ≤ R := by rw [hRn]; exact one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by linarith
  set Ea : ℝ := Real.exp (-(t * R ^ σ))
  have hRσ : 0 ≤ R ^ σ := Real.rpow_nonneg hR0.le σ
  have hEc : Real.exp (-(c * R ^ σ)) ≤ Ea := Real.exp_le_exp.2 (by nlinarith)
  have hT1 : B ^ n * (C * R ^ a * Real.exp (-(c * R ^ σ))) ≤
      B ^ D * C * K₁ * Real.exp (-(t / 2 * R ^ σ)) := by
    have h9 : B ^ n ≤ B ^ D * R ^ (d * D) := by rw [hRn]; exact three_pow_pow_le hDpos
    calc B ^ n * (C * R ^ a * Real.exp (-(c * R ^ σ)))
        ≤ B ^ D * R ^ (d * D) * (C * R ^ a * Ea) := by gcongr
      _ = B ^ D * C * (R ^ (d * D + a) * Ea) := by ring
      _ ≤ B ^ D * C * (K₁ * Real.exp (-(t / 2 * R ^ σ))) :=
          mul_le_mul_of_nonneg_left (hB1 R hR1) (by positivity)
      _ = _ := by ring
  have hT2 : B ^ (n / D + K) * Real.exp (-(B ^ (n - (n / D + K)) * 1) / (K₀ * R ^ b) ^ q) ≤
      B ^ K * K₂ * Real.exp (-(t / 2 * R ^ σ)) := by
    have e9 : B ^ (n / D + K) = B ^ K * R ^ d := by
      rw [hRn, hB]
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    have hJ : R ^ (d * D) ≤ B ^ K * R ^ d * B ^ (n - (n / D + K)) := by
      rw [hRn]; exact pow_mul_le_three_pow_pow hn
    have hdD : d ≤ d * D := le_mul_of_one_le_right (Nat.zero_le d) hDpos
    have hDq : b * q + 1 ≤ ((d * D - d : ℕ) : ℝ) := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hD1 : 0 ≤ (D : ℝ) - 1 := by linarith
      rw [Nat.cast_sub hdD]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.2 hd1) hD1]
    have hch := exp_chernoff_le hR1 hK₀ hDq hdD hJ
    have hEa' : Real.exp (-(1 / (B ^ K * K₀ ^ q) * R)) ≤ Ea :=
      Rigidity.Corrector.exp_neg_le_exp_neg_rpow hR1 hσ1 ht0.le htc'
    calc B ^ (n / D + K) * Real.exp (-(B ^ (n - (n / D + K)) * 1) / (K₀ * R ^ b) ^ q)
        ≤ B ^ K * R ^ d * Ea := by
          rw [e9]
          exact mul_le_mul_of_nonneg_left (hch.trans hEa') (by positivity)
      _ = B ^ K * (R ^ d * Ea) := by ring
      _ ≤ B ^ K * (K₂ * Real.exp (-(t / 2 * R ^ σ))) :=
          mul_le_mul_of_nonneg_left (hB2 R hR1) (by positivity)
      _ = _ := by ring
  have hRn' : (3 : ℝ) ^ (-σ) * ((3 : ℝ) ^ n) ^ (σ / D) ≤ R ^ σ := by
    rw [hRn]; exact Rigidity.Corrector.rpow_three_pow_div_le hDpos hσ0
  have hfin : Real.exp (-(t / 2 * R ^ σ)) ≤
      Real.exp (-(t / 2 * (3 : ℝ) ^ (-σ)) * ((3 : ℝ) ^ n) ^ (σ / D)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hRn' (by positivity : (0 : ℝ) ≤ t / 2)
    nlinarith
  calc _ ≤ B ^ D * C * K₁ * Real.exp (-(t / 2 * R ^ σ)) +
        B ^ K * K₂ * Real.exp (-(t / 2 * R ^ σ)) := add_le_add hT1 hT2
    _ = (B ^ D * C * K₁ + B ^ K * K₂) * Real.exp (-(t / 2 * R ^ σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin (by positivity)

end Rigidity.Corrector.GeneralDim
