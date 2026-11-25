import Rigidity.Proofs.Corrector.DarioStepTwoWeightFailure

/-!
# The failure probability of the weight bound of a triadic cube

At scale `n` take `D = ⌈3 + 29q⌉`, the range `R = 3^{⌊n/D⌋}` and the scale `m = ⌊n/D⌋ + K` of the
residue classes, `K = 6κ + 21`. Then `9ⁿ ≤ 9^D R^{2D}` (`nine_pow_le`), `R^{2D} ≤ 9^K R² 9^{n-m}`
(`pow_two_mul_le_nine_pow`), the exponent of the Chernoff bound is at least `R / (9^K K₀^q)`
(`exp_chernoff_le`), powers of `R` are absorbed by half of a stretched exponential in `R`
(`pow_mul_exp_neg_rpow_le_half`), and `R^σ ≥ 3^{-σ} (3ⁿ)^{σ/D}` (`rpow_three_pow_div_le`). Hence the
weight bound of a cube of scale `n` fails with probability at most `C₁ e^{-c (3ⁿ)^{s₀}}`
(`exists_measure_not_weightGood_le`), the failure bound (2.2) of the partition with good cubes
carrying the weight bound.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem lt_three_pow_self (n : ℕ) : n < 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

theorem lt_mul_div_add {n D : ℕ} (hD : 0 < D) : n < D * (n / D) + D := by
  have h1 := Nat.div_add_mod n D
  have h2 := Nat.mod_lt n hD
  omega

theorem nine_pow_le {n D : ℕ} (hD : 0 < D) :
    (9 : ℝ) ^ n ≤ 9 ^ D * ((3 : ℝ) ^ (n / D)) ^ (2 * D) := by
  have h1 : n ≤ D * (n / D) + D := (lt_mul_div_add hD).le
  calc (9 : ℝ) ^ n ≤ 9 ^ (D * (n / D) + D) := pow_le_pow_right₀ (by norm_num) h1
    _ = 9 ^ D * ((3 : ℝ) ^ (n / D)) ^ (2 * D) := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        simp only [← pow_mul, ← pow_add]
        ring_nf

theorem pow_two_mul_le_nine_pow {n D K : ℕ} (hn : n / D + K ≤ n) :
    ((3 : ℝ) ^ (n / D)) ^ (2 * D) ≤ 9 ^ K * ((3 : ℝ) ^ (n / D)) ^ 2 * 9 ^ (n - (n / D + K)) := by
  have hdr : D * (n / D) ≤ n := Nat.mul_div_le n D
  have e : (9 : ℝ) ^ K * ((3 : ℝ) ^ (n / D)) ^ 2 * 9 ^ (n - (n / D + K)) = 9 ^ n := by
    have e1 : (9 : ℝ) ^ K * ((3 : ℝ) ^ (n / D)) ^ 2 = 9 ^ (n / D + K) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
      simp only [← pow_mul, ← pow_add]
      ring_nf
    rw [e1, ← pow_add, Nat.add_sub_of_le hn]
  rw [e]
  calc ((3 : ℝ) ^ (n / D)) ^ (2 * D) = 9 ^ (D * (n / D)) := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
        simp only [← pow_mul]
        ring_nf
    _ ≤ 9 ^ n := pow_le_pow_right₀ (by norm_num) hdr

/-- The exponent of the Chernoff bound is at least `R / (9^K K₀^q)`. -/
theorem exp_chernoff_le {R K₀ q J : ℝ} {D K : ℕ} (hR : 1 ≤ R) (hK₀ : 0 < K₀)
    (hD : 29 * q + 1 ≤ ((2 * D - 2 : ℕ) : ℝ)) (h2D : 2 ≤ 2 * D)
    (hJ : R ^ (2 * D) ≤ 9 ^ K * R ^ 2 * J) :
    Real.exp (-(J * 1) / (K₀ * R ^ 29) ^ q) ≤ Real.exp (-(1 / (9 ^ K * K₀ ^ q) * R)) := by
  have hR0 : 0 < R := by linarith
  have hA : (K₀ * R ^ 29) ^ q = K₀ ^ q * R ^ (29 * q) := by
    rw [Real.mul_rpow hK₀.le (by positivity), show (29 : ℝ) * q = ((29 : ℕ) : ℝ) * q by norm_num,
      Real.rpow_natCast_mul hR0.le]
  have hRk : R * R ^ (29 * q) ≤ R ^ (2 * D - 2) := by
    calc R * R ^ (29 * q) = R ^ (29 * q + 1) := by rw [Real.rpow_add_one hR0.ne']; ring
      _ ≤ R ^ (((2 * D - 2 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hR hD
      _ = R ^ (2 * D - 2) := Real.rpow_natCast R _
  have h9 : R ^ (2 * D - 2) ≤ 9 ^ K * J := by
    have e : R ^ (2 * D) = R ^ (2 * D - 2) * R ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel h2D]
    rw [e] at hJ
    have hR2 : 0 < R ^ 2 := by positivity
    nlinarith
  have hJ0 : 0 ≤ J := by
    have : 0 ≤ R ^ (2 * D - 2) := by positivity
    have h9K : (0 : ℝ) < 9 ^ K := by positivity
    nlinarith
  have hA0 : 0 < K₀ ^ q * R ^ (29 * q) := by positivity
  refine Real.exp_le_exp.2 ?_
  rw [hA, mul_one, neg_div, neg_le_neg_iff, div_mul_eq_mul_div, one_mul,
    div_le_div_iff₀ (by positivity) hA0]
  calc R * (K₀ ^ q * R ^ (29 * q)) = K₀ ^ q * (R * R ^ (29 * q)) := by ring
    _ ≤ K₀ ^ q * (9 ^ K * J) := mul_le_mul_of_nonneg_left (hRk.trans h9) (by positivity)
    _ = J * (9 ^ K * K₀ ^ q) := by ring

/-- Powers of `R` are absorbed by half of a stretched exponential in `R`. -/
theorem pow_mul_exp_neg_rpow_le_half {R a σ : ℝ} {k : ℕ} (hR : 1 ≤ R) (ha : 0 < a) (hσ : 0 < σ)
    (hk : 1 ≤ k) :
    R ^ k * Real.exp (-(a * R ^ σ)) ≤
      (((k : ℝ) / σ) / (a / 2)) ^ ((k : ℝ) / σ) * Real.exp (-(a / 2 * R ^ σ)) := by
  have hR0 : 0 < R := by linarith
  have hy0 : 0 ≤ R ^ σ := Real.rpow_nonneg hR0.le σ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k / σ := by positivity
  have e1 : R ^ k = (R ^ σ) ^ ((k : ℝ) / σ) := by
    rw [← Real.rpow_mul hR0.le, show σ * ((k : ℝ) / σ) = k by field_simp, Real.rpow_natCast]
  have h := rpow_mul_exp_neg_le hy0 hk0 (c := a / 2) (by positivity)
  have e2 : Real.exp (-(a * R ^ σ)) =
      Real.exp (-(a / 2 * R ^ σ)) * Real.exp (-(a / 2 * R ^ σ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e1, e2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- `R^σ ≥ 3^{-σ} (3ⁿ)^{σ/D}` for `R = 3^{⌊n/D⌋}`. -/
theorem rpow_three_pow_div_le {n D : ℕ} (hD : 0 < D) {σ : ℝ} (hσ : 0 < σ) :
    (3 : ℝ) ^ (-σ) * ((3 : ℝ) ^ n) ^ (σ / D) ≤ ((3 : ℝ) ^ (n / D)) ^ σ := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : (n : ℝ) < D * ((n / D : ℕ) : ℝ) + D := by exact_mod_cast lt_mul_div_add (n := n) hD
  have e1 : (3 : ℝ) ^ (-σ) * ((3 : ℝ) ^ n) ^ (σ / D) = (3 : ℝ) ^ (-σ + n * (σ / D)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num)]
  have e2 : ((3 : ℝ) ^ (n / D)) ^ σ = (3 : ℝ) ^ (((n / D : ℕ) : ℝ) * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [e1, e2]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have h2 : (n : ℝ) / D < ((n / D : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hD0]
    linarith
  have e3 : (n : ℝ) * (σ / D) = (n / D) * σ := by ring
  rw [e3]
  nlinarith


/-- **The real form of the failure bound** at scale `n`, for `R = 3^{⌊n/D⌋}`. -/
theorem weight_failure_real_le {κ : ℕ} (hκ : 1 ≤ κ) {q C c σ : ℝ} (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hc : 0 < c) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) :
    ∃ Cf cf : ℝ, 0 ≤ Cf ∧ 0 < cf ∧ ∀ (n : ℕ) (R : ℝ), R = (3 : ℝ) ^ (n / ⌈3 + 29 * q⌉₊) →
      n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21) ≤ n →
      9 ^ n * (C * R ^ 4 * Real.exp (-(c * R ^ σ))) +
        9 ^ (n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21)) *
          Real.exp (-((9 : ℝ) ^ (n - (n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21))) * 1) /
            ((18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * R ^ 29) ^ q) ≤
      Cf * Real.exp (-cf * ((3 : ℝ) ^ n) ^ (σ / ⌈3 + 29 * q⌉₊)) := by
  set D := ⌈3 + 29 * q⌉₊ with hD
  have hD3 : 3 + 29 * q ≤ (D : ℝ) := Nat.le_ceil _
  have hDpos : 0 < D := by
    have : (0 : ℝ) < D := by linarith
    exact_mod_cast this
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  set K₀ : ℝ := 18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18 with hK₀
  have hK₀0 : 0 < K₀ := by positivity
  set c' : ℝ := 1 / (9 ^ (6 * κ + 21) * K₀ ^ q) with hc'
  have hc'0 : 0 < c' := by positivity
  set a : ℝ := min c c' with ha
  have ha0 : 0 < a := lt_min hc hc'0
  have hac : a ≤ c := min_le_left _ _
  have hac' : a ≤ c' := min_le_right _ _
  obtain ⟨K₁, hK₁, hB1⟩ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ R : ℝ, 1 ≤ R →
      R ^ (2 * D + 4) * Real.exp (-(a * R ^ σ)) ≤ K₁ * Real.exp (-(a / 2 * R ^ σ)) :=
    ⟨_, by positivity, fun R hR => pow_mul_exp_neg_rpow_le_half hR ha0 hσ0 (by omega)⟩
  obtain ⟨K₂, hK₂, hB2⟩ : ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ R : ℝ, 1 ≤ R →
      R ^ 2 * Real.exp (-(a * R ^ σ)) ≤ K₂ * Real.exp (-(a / 2 * R ^ σ)) :=
    ⟨_, by positivity, fun R hR => pow_mul_exp_neg_rpow_le_half hR ha0 hσ0 (by norm_num)⟩
  refine ⟨9 ^ D * C * K₁ + 9 ^ (6 * κ + 21) * K₂, a / 2 * (3 : ℝ) ^ (-σ), by positivity,
    by positivity, fun n R hRn hn => ?_⟩
  have hR1 : 1 ≤ R := by rw [hRn]; exact one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by linarith
  set Ea : ℝ := Real.exp (-(a * R ^ σ)) with hEa
  have hRσ : 0 ≤ R ^ σ := Real.rpow_nonneg hR0.le σ
  have hEc : Real.exp (-(c * R ^ σ)) ≤ Ea := Real.exp_le_exp.2 (by nlinarith)
  -- the first term
  have hT1 : 9 ^ n * (C * R ^ 4 * Real.exp (-(c * R ^ σ))) ≤
      9 ^ D * C * K₁ * Real.exp (-(a / 2 * R ^ σ)) := by
    have h9 : (9 : ℝ) ^ n ≤ 9 ^ D * R ^ (2 * D) := by rw [hRn]; exact nine_pow_le hDpos
    calc 9 ^ n * (C * R ^ 4 * Real.exp (-(c * R ^ σ)))
        ≤ 9 ^ D * R ^ (2 * D) * (C * R ^ 4 * Ea) := by gcongr
      _ = 9 ^ D * C * (R ^ (2 * D + 4) * Ea) := by ring
      _ ≤ 9 ^ D * C * (K₁ * Real.exp (-(a / 2 * R ^ σ))) :=
          mul_le_mul_of_nonneg_left (hB1 R hR1) (by positivity)
      _ = _ := by ring
  -- the second term
  have hT2 : 9 ^ (n / D + (6 * κ + 21)) *
      Real.exp (-((9 : ℝ) ^ (n - (n / D + (6 * κ + 21))) * 1) / (K₀ * R ^ 29) ^ q) ≤
      9 ^ (6 * κ + 21) * K₂ * Real.exp (-(a / 2 * R ^ σ)) := by
    have e9 : (9 : ℝ) ^ (n / D + (6 * κ + 21)) = 9 ^ (6 * κ + 21) * R ^ 2 := by
      rw [hRn, pow_add, show (9 : ℝ) = 3 ^ 2 by norm_num]
      simp only [← pow_mul]
      ring_nf
    have hJ : R ^ (2 * D) ≤ 9 ^ (6 * κ + 21) * R ^ 2 * 9 ^ (n - (n / D + (6 * κ + 21))) := by
      rw [hRn]; exact pow_two_mul_le_nine_pow hn
    have hDq : 29 * q + 1 ≤ ((2 * D - 2 : ℕ) : ℝ) := by
      have h2 : 2 ≤ 2 * D := by omega
      rw [Nat.cast_sub h2]
      push_cast
      linarith
    have hch := exp_chernoff_le hR1 hK₀0 hDq (by omega) hJ
    have hEa' : Real.exp (-(1 / (9 ^ (6 * κ + 21) * K₀ ^ q) * R)) ≤ Ea :=
      exp_neg_le_exp_neg_rpow hR1 (by linarith) ha0.le hac'
    calc 9 ^ (n / D + (6 * κ + 21)) *
          Real.exp (-((9 : ℝ) ^ (n - (n / D + (6 * κ + 21))) * 1) / (K₀ * R ^ 29) ^ q)
        ≤ 9 ^ (6 * κ + 21) * R ^ 2 * Ea := by
          rw [e9]
          exact mul_le_mul_of_nonneg_left (hch.trans hEa') (by positivity)
      _ = 9 ^ (6 * κ + 21) * (R ^ 2 * Ea) := by ring
      _ ≤ 9 ^ (6 * κ + 21) * (K₂ * Real.exp (-(a / 2 * R ^ σ))) :=
          mul_le_mul_of_nonneg_left (hB2 R hR1) (by positivity)
      _ = _ := by ring
  -- the stretched exponential in `3ⁿ`
  have hRn' : (3 : ℝ) ^ (-σ) * ((3 : ℝ) ^ n) ^ (σ / D) ≤ R ^ σ := by
    rw [hRn]; exact rpow_three_pow_div_le hDpos hσ0
  have hfin : Real.exp (-(a / 2 * R ^ σ)) ≤
      Real.exp (-(a / 2 * (3 : ℝ) ^ (-σ)) * ((3 : ℝ) ^ n) ^ (σ / D)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hRn' (by positivity : (0 : ℝ) ≤ a / 2)
    nlinarith
  calc _ ≤ 9 ^ D * C * K₁ * Real.exp (-(a / 2 * R ^ σ)) +
        9 ^ (6 * κ + 21) * K₂ * Real.exp (-(a / 2 * R ^ σ)) := add_le_add hT1 hT2
    _ = (9 ^ D * C * K₁ + 9 ^ (6 * κ + 21) * K₂) * Real.exp (-(a / 2 * R ^ σ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin (by positivity)

theorem range_le_three_pow (κ r : ℕ) :
    2 * ((3 * κ + 9) * 3 ^ r + 1) + 1 ≤ 3 ^ (r + (6 * κ + 21)) := by
  rw [pow_add]
  obtain ⟨T, hT⟩ : ∃ T, T = 3 ^ (6 * κ + 21) := ⟨_, rfl⟩
  obtain ⟨R, hRr⟩ : ∃ R, R = 3 ^ r := ⟨_, rfl⟩
  have h1 : 6 * κ + 21 < T := hT ▸ lt_three_pow_self _
  have hR : 1 ≤ R := hRr ▸ Nat.one_le_pow _ _ (by norm_num)
  rw [← hT, ← hRr]
  nlinarith

theorem div_add_le_of_two_mul_le {n D K : ℕ} (hD2 : 2 ≤ D) (hn : 2 * K ≤ n) : n / D + K ≤ n := by
  have : n / D ≤ n / 2 := Nat.div_le_div_left hD2 (by norm_num)
  omega

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The failure bound at the large scales. -/
theorem measure_not_weightGood_le_large {p : unitInterval} {κ : ℕ} (hκ : 1 ≤ κ) {i : Fin 2}
    {q M₀ C c σ Cf cf : ℝ} (hq : 1 ≤ q) (hM₀ : 0 ≤ M₀) (hC : 0 ≤ C)
    (hmom : ∀ R : ℕ, 1 ≤ R → ∀ u, ∫⁻ ω, ENNReal.ofReal (finiteWeight κ R ω u) ^ q
      ∂latticeBondLaw 2 p ≤ ENNReal.ofReal M₀)
    (hdom : ∀ R : ℕ, 1 ≤ R → ∀ u, latticeBondLaw 2 p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
      ENNReal.ofReal (C * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ))))
    (hreal : ∀ (n : ℕ) (R : ℝ), R = (3 : ℝ) ^ (n / ⌈3 + 29 * q⌉₊) →
      n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21) ≤ n →
      9 ^ n * (C * R ^ 4 * Real.exp (-(c * R ^ σ))) +
        9 ^ (n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21)) *
          Real.exp (-((9 : ℝ) ^ (n - (n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21))) * 1) /
            ((18 * (49 * 29 : ℝ) ^ 9 * κ ^ 18) * R ^ 29) ^ q) ≤
      Cf * Real.exp (-cf * ((3 : ℝ) ^ n) ^ (σ / ⌈3 + 29 * q⌉₊)))
    {n : ℕ} (hle : n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21) ≤ n) (idx : Vertex 2) :
    latticeBondLaw 2 p {ω | ¬ weightGood hG hGv κ i q ((Real.exp 1 - 1) * M₀ + 1) ω ⟨n, idx⟩} ≤
      ENNReal.ofReal (Cf * Real.exp (-cf * ((3 : ℝ) ^ n) ^ (σ / ⌈3 + 29 * q⌉₊))) := by
  have hR : 1 ≤ 3 ^ (n / ⌈3 + 29 * q⌉₊) := Nat.one_le_pow _ _ (by norm_num)
  have hA := measure_not_weightGood_le_of_bounds hG hGv
    (j := n - (n / ⌈3 + 29 * q⌉₊ + (6 * κ + 21))) hκ hR hq hM₀ hC
    (fun u => hmom _ hR u) (fun u => hdom _ hR u) (range_le_three_pow κ _) idx
  rw [Nat.add_sub_of_le hle] at hA
  refine hA.trans (ENNReal.ofReal_le_ofReal (hreal n _ ?_ hle))
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- **The failure bound for the weight bound of the triadic cubes**, in place of Lemma 3.7 of
Dario (the minimal scale (3.31)): for each `q ≥ 1` there is `M` such that a triadic cube `T` of
side `3ⁿ` fails `Σ_{u ∈ T} W(u)^q ≤ M |T|` for the weight `W` of the Step 2 sum, or has a vertex of
infinite weight, with probability at most `C₁ exp(−c (3ⁿ)^{s₀})`. Dario states (3.31) on the
cubes `□_m` above a minimal scale, for the weight `size(□_𝒫(z))^{3d} Σ (𝒳^e(x))^d` and the exponent
`(2 + ε)/ε`; here the weight is that of the Step 2 sum in flip form, `q` is any exponent, and the
bound is a tail bound for each triadic cube. -/
theorem exists_measure_not_weightGood_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) {q : ℝ} (hq : 1 ≤ q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧ ∀ (i : Fin 2) (T : TriadicCube 2),
      latticeBondLaw 2 p {ω | ¬ weightGood hG hGv κ i q M ω T} ≤
        ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0)) := by
  obtain ⟨M₀, hM₀, hmom⟩ := exists_lintegral_finiteWeight_rpow_le hpc hp1 hκ hq
  obtain ⟨C, c, σ, hC, hc, hσ0, hσ1, hdom⟩ := measure_not_domGood_le hG hGv hpc hp1 hGae hκ
  obtain ⟨Cf, cf, hCf, hcf, hreal⟩ := weight_failure_real_le hκ hq hC.le hc hσ0 hσ1
  have hD3 : 3 + 29 * q ≤ (⌈3 + 29 * q⌉₊ : ℝ) := Nat.le_ceil _
  have hD2 : 2 ≤ ⌈3 + 29 * q⌉₊ := by
    have : (2 : ℝ) ≤ ⌈3 + 29 * q⌉₊ := by linarith
    exact_mod_cast this
  obtain ⟨s0, hs0e⟩ : ∃ s0 : ℝ, s0 = σ / ⌈3 + 29 * q⌉₊ := ⟨_, rfl⟩
  have hs0 : 0 < s0 := by
    have : (0 : ℝ) < ⌈3 + 29 * q⌉₊ := by linarith
    rw [hs0e]
    positivity
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : ℝ, X₀ = ((3 : ℝ) ^ (2 * (6 * κ + 21))) ^ s0 := ⟨_, rfl⟩
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  refine ⟨(Real.exp 1 - 1) * M₀ + 1, by nlinarith [mul_nonneg (sub_nonneg.2 he1) hM₀],
    max Cf (Real.exp (cf * X₀)), cf, s0, le_max_of_le_left hCf, hcf, hs0, fun i T => ?_⟩
  obtain ⟨n, idx⟩ := T
  show _ ≤ ENNReal.ofReal (max Cf (Real.exp (cf * X₀)) * Real.exp (-cf * ((3 : ℝ) ^ n) ^ s0))
  by_cases hn : 2 * (6 * κ + 21) ≤ n
  · have hA := measure_not_weightGood_le_large hG hGv hκ (i := i) hq hM₀ hC.le hmom
      (fun R hR u => hdom i R hR u) hreal (div_add_le_of_two_mul_le hD2 hn) idx
    rw [← hs0e] at hA
    refine hA.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · refine prob_le_one.trans (ENNReal.one_le_ofReal.2 ?_)
    have hle : ((3 : ℝ) ^ n) ^ s0 ≤ X₀ := by
      rw [hX₀]
      exact Real.rpow_le_rpow (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) hs0.le
    have hexp : Real.exp (-cf * X₀) ≤ Real.exp (-cf * ((3 : ℝ) ^ n) ^ s0) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hle hcf.le
      linarith
    calc (1 : ℝ) = Real.exp (cf * X₀) * Real.exp (-cf * X₀) := by
          rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      _ ≤ _ := mul_le_mul (le_max_right _ _) hexp (Real.exp_pos _).le
          (le_max_of_le_left hCf)

end Grad

end Rigidity.Corrector
