/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/RateArithmetic.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Hypotheses
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Real arithmetic behind the rates of Appendix A

The scalar and matrix-norm inequalities that turn the two sides of the means of the coarse-grained
matrices into the rate (proof of `p:coarse`, `s:homogenization`): the logarithm bound and the
exponent bookkeeping for the choice of the scale `R = 3^{⌈tn⌉}`, the limit `D` of decreasing
means with a decaying gap, the triangle step for the expected norm of `X - x • 1`, and the real
inequality of the last step. Nothing about conductances or cubes is used here, apart from the
exponent `ratioExp` of the hypotheses.
-/

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace LatticeHC

variable {d : ℕ}

/-! ## Real arithmetic for the rates -/

/-- The logarithm of `C₀ (M R + 1)` is at most `log₃ Cb + log₃ R`, `Cb = max (|C₀|(|M|+1)) 1`
(`log 0 = 0` and `log x = log |x|` are the junk values). -/
theorem logb_le_of_abs_le {C₀ M : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    Real.logb 3 (C₀ * (M * R + 1)) ≤
      Real.logb 3 (max (|C₀| * (|M| + 1)) 1) + Real.logb 3 R := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  set Cb := max (|C₀| * (|M| + 1)) 1 with hCb
  have hCb1 : 1 ≤ Cb := le_max_right _ _
  have habs : |C₀ * (M * R + 1)| ≤ Cb * R := by
    rw [abs_mul]
    have h1 : |M * R + 1| ≤ (|M| + 1) * R := by
      calc |M * R + 1| ≤ |M * R| + |(1 : ℝ)| := abs_add_le _ _
        _ = |M| * R + 1 := by rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ R), abs_one]
        _ ≤ |M| * R + R := by linarith
        _ = (|M| + 1) * R := by ring
    calc |C₀| * |M * R + 1| ≤ |C₀| * ((|M| + 1) * R) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = (|C₀| * (|M| + 1)) * R := by ring
      _ ≤ Cb * R := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hpos : 0 < Cb * R := by positivity
  rw [← Real.logb_mul (by linarith) (by linarith)]
  by_cases hx : C₀ * (M * R + 1) = 0
  · rw [hx, Real.logb_zero]
    exact Real.logb_nonneg (by norm_num) (by nlinarith)
  · rw [Real.logb, Real.logb, div_le_div_iff_of_pos_right (Real.log_pos (by norm_num))]
    rw [← Real.log_abs]
    exact Real.log_le_log (abs_pos.2 hx) habs

/-- **Exponent bookkeeping** (proof of `p:coarse`: `R = 3^{⌈tn⌉}`, `t = (κ + α)/(κ + γ)`,
`κ₁ = κ(γ - α)/(κ + γ)`). For `0 ≤ α < γ` and `0 < κ` there are `N` and `K` such that, for
`n ≥ N` and `R = 3^{⌈tn⌉}`, the scale `r_R = ⌈log₃(C₀(MR+1))⌉` is at most `n` and
`3^{-κ(n - r_R)} + 3^{nα} R^{-γ} ≤ K 3^{-κ₁ n}`. Proof: `r_R ≤ tn + log₃ Cb + 2`. -/
theorem triadic_exponent_arithmetic {κ γ α : ℝ} (hκ : 0 < κ) (hγ : 0 < γ) (hα0 : 0 ≤ α)
    (hαγ : α < γ) (C₀ M : ℝ) :
    ∃ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, N ≤ n → ∀ R : ℕ,
      R = 3 ^ ⌈(κ + α) / (κ + γ) * n⌉₊ →
      ⌈Real.logb 3 (C₀ * (M * R + 1))⌉ ≤ (n : ℤ) ∧
      (3 : ℝ) ^ (-(κ * ((n : ℝ) - ⌈Real.logb 3 (C₀ * (M * R + 1))⌉))) +
        (3 : ℝ) ^ ((n : ℝ) * α) * (R : ℝ) ^ (-γ) ≤
      K * (3 : ℝ) ^ (-(κ * (γ - α) / (κ + γ) * n)) := by
  set t : ℝ := (κ + α) / (κ + γ) with ht
  have hκγ : 0 < κ + γ := by linarith
  have ht0 : 0 ≤ t := by positivity
  have h1t : 0 < 1 - t := by
    rw [ht, sub_pos, div_lt_one hκγ]
    linarith
  set K₀ : ℝ := Real.logb 3 (max (|C₀| * (|M| + 1)) 1) with hK₀
  have hK₀0 : 0 ≤ K₀ := Real.logb_nonneg (by norm_num) (le_max_right _ _)
  set κ₁ : ℝ := κ * (γ - α) / (κ + γ) with hκ₁
  have hκ₁t : κ₁ = κ * (1 - t) := by
    rw [hκ₁, ht]
    field_simp
    ring
  refine ⟨⌈(K₀ + 2) / (1 - t)⌉₊, (3 : ℝ) ^ (κ * (K₀ + 2)) + 1, by positivity, ?_⟩
  intro n hn R hR
  set j : ℕ := ⌈t * n⌉₊ with hj
  have hjge : t * n ≤ j := Nat.le_ceil _
  have hjlt : (j : ℝ) < t * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hR1 : 1 ≤ R := by rw [hR]; exact Nat.one_le_pow _ _ (by norm_num)
  have hlogR : Real.logb 3 (R : ℝ) = j := by
    rw [hR]
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hlog : Real.logb 3 (C₀ * (M * R + 1)) ≤ K₀ + j := by
    have := logb_le_of_abs_le (C₀ := C₀) (M := M) hR1
    rwa [hlogR] at this
  set r : ℤ := ⌈Real.logb 3 (C₀ * (M * R + 1))⌉ with hr
  have hrlt : (r : ℝ) < K₀ + t * n + 2 := by
    have := Int.ceil_lt_add_one (Real.logb 3 (C₀ * (M * R + 1)))
    linarith
  have hnN : (K₀ + 2) / (1 - t) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hKn : K₀ + 2 ≤ (1 - t) * n := by
    rwa [div_le_iff₀ h1t, mul_comm] at hnN
  have hrn : (r : ℝ) < n := by nlinarith
  refine ⟨by exact_mod_cast hrn.le, ?_⟩
  have h3 : (3 : ℝ) ^ (-(κ * ((n : ℝ) - r))) ≤
      (3 : ℝ) ^ (κ * (K₀ + 2)) * (3 : ℝ) ^ (-(κ₁ * n)) := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : κ * (K₀ + 2) + -(κ₁ * n) = -(κ * ((1 - t) * n - (K₀ + 2))) := by
      rw [hκ₁t]; ring
    rw [this, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left (by linarith) hκ.le
  have h4 : (3 : ℝ) ^ ((n : ℝ) * α) * (R : ℝ) ^ (-γ) ≤ (3 : ℝ) ^ (-(κ₁ * n)) := by
    have hRj : (R : ℝ) ^ (-γ) = (3 : ℝ) ^ (-(γ * j)) := by
      rw [hR]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hRj, ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : n * α + -(γ * j) ≤ n * α - γ * (t * n) := by nlinarith
    refine this.trans (le_of_eq ?_)
    rw [hκ₁, ht]
    field_simp
    ring
  calc _ ≤ (3 : ℝ) ^ (κ * (K₀ + 2)) * (3 : ℝ) ^ (-(κ₁ * n)) + (3 : ℝ) ^ (-(κ₁ * n)) :=
        add_le_add h3 h4
    _ = _ := by ring

/-- `α = d/P_γ` is at most `γ/2` for `d ≥ 1` (`P_γ = max{64, ⌈2d/γ⌉} ≥ 2d/γ`). -/
theorem div_ratioExp_le {γ : ℝ} (hγ : 0 < γ) (hd : 0 < d) :
    (d : ℝ) / ratioExp d γ ≤ γ / 2 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have h1 : 2 * (d : ℝ) / γ ≤ ratioExp d γ := (Int.le_ceil _).trans (le_max_right _ _)
  have h2 : 0 < 2 * (d : ℝ) / γ := by positivity
  have h3 : 2 * (d : ℝ) ≤ ratioExp d γ * γ := (div_le_iff₀ hγ).1 h1
  rw [div_le_div_iff₀ (h2.trans_le h1) two_pos]
  linarith

/-- **The limit `D`** (proof of `p:coarse`, "the means decrease ... so they converge"): for
decreasing `α, β` in `[M⁻¹, M]` with `β⁻¹ ≤ α` and `α_n - β_n⁻¹ ≤ ε_n`, `D = inf α` satisfies
`D ≤ α_n ≤ D + ε_n` and `β_n⁻¹ ≤ D`, `β_n ≤ D⁻¹ + M²ε_n`. Proof: `β⁻¹` is increasing and
`β_m⁻¹ ≤ α_m` for `m ≥ n` gives `β_n⁻¹ ≤ inf α`. -/
theorem exists_limit_of_gap_decay {M : ℝ} (hM : 1 ≤ M) {α β ε : ℕ → ℝ} (hα : Antitone α)
    (hβ : Antitone β) (hαM : ∀ n, M⁻¹ ≤ α n ∧ α n ≤ M) (hβM : ∀ n, M⁻¹ ≤ β n ∧ β n ≤ M)
    (hgap : ∀ n, (β n)⁻¹ ≤ α n) (hdec : ∀ n, α n - (β n)⁻¹ ≤ ε n) :
    ∃ D : ℝ, M⁻¹ ≤ D ∧ D ≤ M ∧ ∀ n, D ≤ α n ∧ α n ≤ D + ε n ∧ (β n)⁻¹ ≤ D ∧
      β n ≤ D⁻¹ + M ^ 2 * ε n := by
  have hM0 : 0 < M := by linarith
  have hbdd : BddBelow (Set.range α) := ⟨M⁻¹, by rintro _ ⟨n, rfl⟩; exact (hαM n).1⟩
  have hDle : ∀ n, (⨅ m, α m) ≤ α n := fun n => ciInf_le hbdd n
  have hDlow : M⁻¹ ≤ ⨅ m, α m := le_ciInf fun n => (hαM n).1
  have hβinv : ∀ n, (β n)⁻¹ ≤ ⨅ m, α m := fun n => by
    refine le_ciInf fun m => ?_
    have hβpos : ∀ k, 0 < β k := fun k => lt_of_lt_of_le (inv_pos.2 hM0) (hβM k).1
    calc (β n)⁻¹ ≤ (β (max n m))⁻¹ := inv_anti₀ (hβpos _) (hβ (le_max_left n m))
      _ ≤ α (max n m) := hgap _
      _ ≤ α m := hα (le_max_right n m)
  refine ⟨⨅ m, α m, hDlow, (hDle 0).trans (hαM 0).2, fun n => ⟨hDle n, ?_, hβinv n, ?_⟩⟩
  · linarith [hdec n, hβinv n]
  · set D := ⨅ m, α m with hD
    have hD0 : 0 < D := lt_of_lt_of_le (inv_pos.2 hM0) hDlow
    have hβ0 : 0 < β n := lt_of_lt_of_le (inv_pos.2 hM0) (hβM n).1
    have hu : (β n)⁻¹ ≤ D := hβinv n
    have h1 : D - (β n)⁻¹ ≤ ε n := by linarith [hdec n, hDle n]
    have h2 : 0 ≤ D - (β n)⁻¹ := sub_nonneg.2 hu
    have hDinv : D⁻¹ ≤ M := by
      rw [inv_le_comm₀ hD0 hM0]
      exact hDlow
    have h3 : β n - D⁻¹ = β n * (D - (β n)⁻¹) * D⁻¹ := by
      field_simp
    have h4 : β n * (D - (β n)⁻¹) * D⁻¹ ≤ M * ε n * M := by
      have := mul_le_mul (mul_le_mul (hβM n).2 h1 h2 hM0.le) hDinv (inv_nonneg.2 hD0.le)
        (mul_nonneg hM0.le (h2.trans h1))
      exact this
    nlinarith [h3, h4]

/-! ## From the two sides of the means to the rate -/

/-- The identity matrix has operator norm at most `1` (it is `0` for `d = 0`). -/
theorem norm_one_matrix_le : ‖(1 : Matrix (Fin d) (Fin d) ℝ)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Subsingleton.elim (1 : Matrix (Fin 0) (Fin 0) ℝ) 0, norm_zero]
    exact zero_le_one
  · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact le_of_eq norm_one

/-- The extended norm of a scalar matrix `t • 1` is at most `|t|`. -/
theorem enorm_smul_one_le (t : ℝ) :
    ‖t • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ≤ ENNReal.ofReal |t| := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_smul, Real.norm_eq_abs]
  calc |t| * ‖(1 : Matrix (Fin d) (Fin d) ℝ)‖ ≤ |t| * 1 :=
        mul_le_mul_of_nonneg_left norm_one_matrix_le (abs_nonneg t)
    _ = |t| := mul_one _

/-- **Triangle step.** If `E‖X - x • 1‖ ≤ ε` and `|x - y| ≤ η` on a probability space, then
`E‖X - y • 1‖ ≤ ε + ofReal |x - y|`. -/
theorem lintegral_enorm_sub_smul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → Matrix (Fin d) (Fin d) ℝ) {x y : ℝ} {ε : ℝ≥0∞}
    (h : ∫⁻ ω, ‖X ω - x • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ ≤ ε) :
    ∫⁻ ω, ‖X ω - y • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ ≤ ε + ENNReal.ofReal |x - y| := by
  have hpt : ∀ ω, ‖X ω - y • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ≤
      ‖X ω - x • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ + ENNReal.ofReal |x - y| := by
    intro ω
    have : X ω - y • (1 : Matrix (Fin d) (Fin d) ℝ) =
        (X ω - x • (1 : Matrix (Fin d) (Fin d) ℝ)) + (x - y) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      rw [sub_smul]
      abel
    rw [this]
    exact (enorm_add_le _ _).trans (add_le_add le_rfl (enorm_smul_one_le _))
  calc ∫⁻ ω, ‖X ω - y • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ
      ≤ ∫⁻ ω, (‖X ω - x • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ + ENNReal.ofReal |x - y|) ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ ω, ‖X ω - x • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ + ENNReal.ofReal |x - y| := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ε + ENNReal.ofReal |x - y| := add_le_add h le_rfl

/-- **Real inequality behind the rate.** With `δ = a - b⁻¹`, `|a - D|, |b⁻¹ - D| ≤ C s²`,
`M⁻¹ ≤ a, D` and `0 ≤ s ≤ 1`:
`2 d M² √δ + |b⁻¹ - D| + |a⁻¹ - D⁻¹| ≤ (2 d M² √(2C) + (1 + M²) C) s`. -/
theorem real_rate_bound {M a b D C s : ℝ} (hM : 1 ≤ M) (haM : M⁻¹ ≤ a)
    (hDM : M⁻¹ ≤ D) (hC : 0 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ha : |a - D| ≤ C * s ^ 2)
    (hb : |b⁻¹ - D| ≤ C * s ^ 2) :
    2 * (d * M ^ 2 * Real.sqrt (a - b⁻¹)) + |b⁻¹ - D| + |a⁻¹ - D⁻¹| ≤
      (2 * d * M ^ 2 * Real.sqrt (2 * C) + (1 + M ^ 2) * C) * s := by
  have hM0 : 0 < M := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (inv_pos.2 hM0) haM
  have hD0 : 0 < D := lt_of_lt_of_le (inv_pos.2 hM0) hDM
  have hδ : a - b⁻¹ ≤ 2 * C * s ^ 2 := by
    have h1 := (le_abs_self (a - D)).trans ha
    have h4 : -(b⁻¹ - D) ≤ |b⁻¹ - D| := neg_le_abs _
    linarith
  have hsq : Real.sqrt (a - b⁻¹) ≤ Real.sqrt (2 * C) * s := by
    calc Real.sqrt (a - b⁻¹) ≤ Real.sqrt (2 * C * s ^ 2) := Real.sqrt_le_sqrt hδ
      _ = Real.sqrt (2 * C) * s := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs]
  have hinv : |a⁻¹ - D⁻¹| ≤ M ^ 2 * (C * s ^ 2) := by
    rw [inv_sub_inv ha0.ne' hD0.ne', abs_div, abs_mul, abs_of_pos ha0, abs_of_pos hD0,
      abs_sub_comm, div_le_iff₀ (mul_pos ha0 hD0)]
    have haD : M⁻¹ * M⁻¹ ≤ a * D := mul_le_mul haM hDM (inv_nonneg.2 hM0.le) ha0.le
    have h1 : M ^ 2 * (M⁻¹ * M⁻¹) = 1 := by field_simp
    calc |a - D| ≤ C * s ^ 2 := ha
      _ = M ^ 2 * (M⁻¹ * M⁻¹) * (C * s ^ 2) := by rw [h1, one_mul]
      _ = M ^ 2 * (C * s ^ 2) * (M⁻¹ * M⁻¹) := by ring
      _ ≤ M ^ 2 * (C * s ^ 2) * (a * D) :=
        mul_le_mul_of_nonneg_left haD (by positivity)
  have hss : s ^ 2 ≤ s := by nlinarith
  calc 2 * (d * M ^ 2 * Real.sqrt (a - b⁻¹)) + |b⁻¹ - D| + |a⁻¹ - D⁻¹|
      ≤ 2 * (d * M ^ 2 * (Real.sqrt (2 * C) * s)) + C * s ^ 2 + M ^ 2 * (C * s ^ 2) := by
        have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (d : ℝ) * M ^ 2)
        linarith
    _ = 2 * d * M ^ 2 * Real.sqrt (2 * C) * s + (1 + M ^ 2) * C * s ^ 2 := by ring
    _ ≤ 2 * d * M ^ 2 * Real.sqrt (2 * C) * s + (1 + M ^ 2) * C * s := by
        have : 0 ≤ (1 + M ^ 2) * C := by positivity
        nlinarith
    _ = _ := by ring

/-- **From the two sides to the rate** (last step of `p:coarse`). If `|a - D|, |b⁻¹ - D| ≤ C s²`,
`M⁻¹ ≤ a, D`, `0 ≤ s ≤ 1`, and `E‖A - b⁻¹ Id‖, E‖B - a⁻¹ Id‖ ≤ d M² √(a - b⁻¹)`, then
`E‖A - D Id‖ + E‖B - D⁻¹ Id‖ ≤ K s` with `K = 2 d M² √(2C) + (1 + M²) C`
(`s = L^{-κ/2}` for `L ≥ 1`). Route: two uses of `lintegral_enorm_sub_smul_le`, then
`real_rate_bound`. -/
theorem lintegral_coarse_sub_le_of_gap {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B : Ω → Matrix (Fin d) (Fin d) ℝ) {M a b D C s : ℝ}
    (hM : 1 ≤ M) (haM : M⁻¹ ≤ a) (hDM : M⁻¹ ≤ D) (hC : 0 ≤ C) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a - D| ≤ C * s ^ 2) (hb : |b⁻¹ - D| ≤ C * s ^ 2)
    (hA : ∫⁻ ω, ‖A ω - b⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ ≤
      ENNReal.ofReal (d * M ^ 2 * Real.sqrt (a - b⁻¹)))
    (hB : ∫⁻ ω, ‖B ω - a⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ ≤
      ENNReal.ofReal (d * M ^ 2 * Real.sqrt (a - b⁻¹))) :
    ∫⁻ ω, ‖A ω - D • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ +
      ∫⁻ ω, ‖B ω - D⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)‖ₑ ∂μ ≤
        ENNReal.ofReal ((2 * d * M ^ 2 * Real.sqrt (2 * C) + (1 + M ^ 2) * C) * s) := by
  have h1 := lintegral_enorm_sub_smul_le (μ := μ) A (y := D) hA
  have h2 := lintegral_enorm_sub_smul_le (μ := μ) B (y := D⁻¹) hB
  have hn : (0 : ℝ) ≤ d * M ^ 2 * Real.sqrt (a - b⁻¹) := by positivity
  calc _ ≤ (ENNReal.ofReal (d * M ^ 2 * Real.sqrt (a - b⁻¹)) + ENNReal.ofReal |b⁻¹ - D|) +
        (ENNReal.ofReal (d * M ^ 2 * Real.sqrt (a - b⁻¹)) + ENNReal.ofReal |a⁻¹ - D⁻¹|) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (d * M ^ 2 * Real.sqrt (a - b⁻¹)) + |b⁻¹ - D| + |a⁻¹ - D⁻¹|) := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (by positivity) (abs_nonneg _), two_mul,
          ENNReal.ofReal_add hn hn]
        ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (real_rate_bound hM haM hDM hC hs hs1 ha hb)

end LatticeHC
