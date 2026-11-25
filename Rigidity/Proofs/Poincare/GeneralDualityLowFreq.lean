import Rigidity.Proofs.Poincare.DualityLowFreq
import Rigidity.Proofs.Poincare.GeneralDualityBilinear

/-!
# The low-frequency term of the duality identity on `ℤ^d`

The extension of `DualityLowFreq.lean` from `ℤ²` to `ℤ^d`, `d ≥ 1`. The term
`Σ_j Σ_y G_j(y) A_j(8R², y)` of the duality identity is controlled through the semigroup property
`A_j(8R², y) = Σ_w Φ_{8R² - s}(y, w) A_j(s, w)`, averaged over `s ∈ (2R², 4R²]`, and the heat
kernel bound `Φ_τ(y, w) ≤ (C/(2R)^d) e^{-2|w - y|₁/(3R)}` for `τ ∈ [4R², 6R²]`
(`exists_zdHeat_le_exp`):

  `A_j(8R², y)² ≤ (K/R²) (Σ_w R^{-d} e^{-|w|/(2R)} Sq(w)^{q/2})^{2/q}`

for `|y|₁ ≤ R` (`exists_ofReal_sq_heatGrad_le`), by Hölder's inequality with the exponents
`1 - 2/q` and `2/q`. The lattice sum `Σ_x e^{-|x - v|/κ} ≤ (2(1 + dκ))^d`
(`tsum_exp_neg_norm_sub_le`) replaces the planar one.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ} {u : Vertex d → ℝ}

/-- The Euclidean norm is at most the `ℓ¹` norm. -/
theorem norm_euclid_le_sum_abs (v : Vertex d) :
    ‖latticeEuclideanEmbedding v‖ ≤ ∑ i, |((v i : ℤ) : ℝ)| := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖latticeEuclideanEmbedding v i‖ = |((v i : ℤ) : ℝ)| := fun i => Real.norm_eq_abs _
  simp only [h, sq_abs]
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  have := sum_sq_le_sq_sum_abs (fun i => ((v i : ℤ) : ℝ))
  simpa only [sq_abs] using this

/-- `Σ_{x : Fin n → ℤ} Π_i f(x_i) = (Σ_k f(k))^n`. -/
theorem tsum_prod_eq_pow (f : ℤ → ENNReal) :
    ∀ n : ℕ, ∑' x : Fin n → ℤ, ∏ i, f (x i) = (∑' k, f k) ^ n
  | 0 => by simp
  | n + 1 => by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq]
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => f a * ∏ x, f (b x))]
      simp_rw [ENNReal.tsum_mul_left, tsum_prod_eq_pow f n, ENNReal.tsum_mul_right]
      ring

/-- `Σ_{x ∈ ℤ^d} e^{-|x - v|/κ} ≤ (2 (1 + dκ))^d`. -/
theorem tsum_exp_neg_norm_sub_le [NeZero d] (v : Vertex d) {κ : ℝ} (hκ : 0 < κ) :
    ∑' x : Vertex d, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (x - v)‖ / κ)) ≤
      ENNReal.ofReal ((2 * (1 + d * κ)) ^ d) := by
  rw [← (Equiv.addRight v).tsum_eq]
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  set c : ℝ := 1 / (d * κ) with hc
  have hc0 : 0 < c := by positivity
  set f : ℤ → ENNReal := fun n => ENNReal.ofReal (Real.exp (-(c * |(n : ℝ)|))) with hf
  have hpt : ∀ x : Vertex d, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / κ)) ≤
      ∏ i, f (x i) := by
    intro x
    have hcoord : ∀ i, |((x i : ℤ) : ℝ)| ≤ ‖latticeEuclideanEmbedding x‖ := by
      intro i
      have h := PiLp.norm_apply_le (latticeEuclideanEmbedding x) i
      change ‖((x i : ℤ) : ℝ)‖ ≤ _ at h
      rwa [Real.norm_eq_abs] at h
    simp only [hf]
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le, ← Real.exp_sum]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    set e := ‖latticeEuclideanEmbedding x‖
    have hsum : ∑ i, |((x i : ℤ) : ℝ)| ≤ d * e := by
      calc ∑ i, |((x i : ℤ) : ℝ)| ≤ ∑ _i : Fin d, e := Finset.sum_le_sum fun i _ => hcoord i
        _ = d * e := by simp
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, neg_div, neg_le_neg_iff, hc,
      div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hκ]
    nlinarith
  have hsum : ∑' n : ℤ, f n ≤ ENNReal.ofReal (2 * (1 + d * κ)) := by
    have := Rigidity.Corrector.tsum_int_exp_neg_le hc0
    rwa [hc, one_div_one_div] at this
  calc ∑' x : Vertex d, ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / κ))
      ≤ ∑' x : Vertex d, ∏ i, f (x i) := ENNReal.tsum_le_tsum hpt
    _ = (∑' n : ℤ, f n) ^ d := tsum_prod_eq_pow f d
    _ ≤ ENNReal.ofReal (2 * (1 + d * κ)) ^ d := by gcongr
    _ = ENNReal.ofReal ((2 * (1 + d * κ)) ^ d) := (ENNReal.ofReal_pow (by positivity) d).symm

/-- The weight `R^{-d} e^{-|x|/(2R)}` of Dario's (2.26) in dimension `d`. -/
noncomputable def dwt (R : ℝ) (x : Vertex d) : ENNReal :=
  ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * R)) / R ^ d)

/-- **The heat kernel at times `τ ∈ [4R², 6R²]`**. -/
theorem exists_zdHeat_le_exp [NeZero d] : ∃ C : ℝ, 1 ≤ C ∧ ∀ R : ℝ, 3 ≤ R → ∀ τ : ℝ,
    4 * R ^ 2 ≤ τ → τ ≤ 6 * R ^ 2 → ∀ y w : Vertex d, zdHeat d τ y w ≤
      C / (2 * R) ^ d * Real.exp (-(2 / (3 * R)) * ∑ i, |(((w - y) i : ℤ) : ℝ)|) := by
  obtain ⟨C₁, hC₁, h⟩ := exists_zdHeat_mul_exp_le (d := d)
  refine ⟨C₁ ^ d, one_le_pow₀ hC₁, fun R hR τ hτ1 hτ2 y w => ?_⟩
  have hR0 : 0 < R := by linarith
  have hτ0 : 0 < τ := by nlinarith
  set z := ∑ i, |(((w - y) i : ℤ) : ℝ)| with hz
  have hz0 : 0 ≤ z := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsq1 : 1 ≤ Real.sqrt τ := Real.one_le_sqrt.2 (by nlinarith)
  have hσ : max (Real.sqrt τ) 1 = Real.sqrt τ := max_eq_left hsq1
  have hsqle : Real.sqrt τ ≤ 3 * R := by
    rw [show 3 * R = Real.sqrt ((3 * R) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsqge : 2 * R ≤ Real.sqrt τ := by
    rw [show 2 * R = Real.sqrt ((2 * R) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ha6 : 1 / (3 * R) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have haσ : 1 / (3 * R) * max (Real.sqrt τ) 1 ≤ 1 := by
    rw [hσ, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    exact hsqle
  have hk := h τ hτ0.le (1 / (3 * R)) (by positivity) ha6 haσ y w
  rw [hσ] at hk
  have hexp : Real.exp (1 / (3 * R) * z) * Real.exp (-(2 / (3 * R)) * z) ≥
      Real.exp (-z / Real.sqrt τ) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : z / (3 * R) ≤ z / Real.sqrt τ :=
      div_le_div_of_nonneg_left hz0 (by linarith) hsqle
    have e : 1 / (3 * R) * z + -(2 / (3 * R)) * z = -(z / (3 * R)) := by ring
    rw [e, neg_div]
    linarith
  have hCd : C₁ ^ d / Real.sqrt τ ^ d ≤ C₁ ^ d / (2 * R) ^ d :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ (by positivity) hsqge d)
  have hpos : 0 < Real.exp (1 / (3 * R) * z) := Real.exp_pos _
  have key : zdHeat d τ y w * Real.exp (1 / (3 * R) * z) ≤
      C₁ ^ d / (2 * R) ^ d * Real.exp (-(2 / (3 * R)) * z) * Real.exp (1 / (3 * R) * z) := by
    calc zdHeat d τ y w * Real.exp (1 / (3 * R) * z)
        ≤ C₁ ^ d / Real.sqrt τ ^ d * Real.exp (-z / Real.sqrt τ) := hk
      _ ≤ C₁ ^ d / (2 * R) ^ d * (Real.exp (1 / (3 * R) * z) * Real.exp (-(2 / (3 * R)) * z)) :=
          mul_le_mul hCd hexp (Real.exp_pos _).le (by positivity)
      _ = C₁ ^ d / (2 * R) ^ d * Real.exp (-(2 / (3 * R)) * z) * Real.exp (1 / (3 * R) * z) := by
          ring
  exact le_of_mul_le_mul_right key hpos

/-- **Jensen for the heat semigroup** in lower sums:
`(Σ_w Φ_τ(y, w) a(w))² ≤ Σ_w Φ_τ(y, w) a(w)²`. -/
theorem ofReal_sq_tsum_heat_le [NeZero d] {τ : ℝ} (hτ : 0 ≤ τ) (y : Vertex d) (a : Vertex d → ℝ) :
    ENNReal.ofReal ((∑' w, zdHeat d τ y w * a w) ^ 2) ≤
      ∑' w, ENNReal.ofReal (zdHeat d τ y w * a w ^ 2) := by
  set Φ := fun w => zdHeat d τ y w with hΦ
  have hΦ0 : ∀ w, 0 ≤ Φ w := fun w => zdHeat_nonneg hτ y w
  have h1 : ENNReal.ofReal |∑' w, Φ w * a w| ≤
      ∑' w, ENNReal.ofReal (Real.sqrt (Φ w)) * ENNReal.ofReal (Real.sqrt (Φ w) * |a w|) := by
    refine (ofReal_abs_tsum_le' _).trans (ENNReal.tsum_le_tsum fun w => ?_)
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc, Real.mul_self_sqrt (hΦ0 w),
      abs_mul, abs_of_nonneg (hΦ0 w)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count (α := Vertex d))
    Real.HolderConjugate.two_two (f := fun w => ENNReal.ofReal (Real.sqrt (Φ w)))
    (g := fun w => ENNReal.ofReal (Real.sqrt (Φ w) * |a w|))
    (Measurable.of_discrete).aemeasurable (Measurable.of_discrete).aemeasurable
  simp only [lintegral_count, Pi.mul_apply] at hH
  have hsq : ∀ z : ℝ, 0 ≤ z → ENNReal.ofReal z ^ (2 : ℝ) = ENNReal.ofReal (z ^ 2) := by
    intro z hz
    rw [ENNReal.ofReal_rpow_of_nonneg hz (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  have e1 : ∑' w, ENNReal.ofReal (Real.sqrt (Φ w)) ^ (2 : ℝ) = 1 := by
    simp only [hsq _ (Real.sqrt_nonneg _), Real.sq_sqrt (hΦ0 _)]
    exact tsum_ofReal_zdHeat hτ y
  have e2 : ∑' w, ENNReal.ofReal (Real.sqrt (Φ w) * |a w|) ^ (2 : ℝ) =
      ∑' w, ENNReal.ofReal (Φ w * a w ^ 2) := by
    refine tsum_congr fun w => ?_
    rw [hsq _ (by positivity), mul_pow, Real.sq_sqrt (hΦ0 w), sq_abs]
  rw [e1, e2, ENNReal.one_rpow, one_mul] at hH
  have h2 := h1.trans hH
  have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    hsq _ (abs_nonneg _), sq_abs] at h3
  exact h3

/-- Hölder's inequality with the exponents `1 - 2/q` and `2/q` on `ℤ^d`. -/
theorem tsum_mul_le_holder {q : ℝ} (hq : 2 ≤ q) (a S : Vertex d → ENNReal)
    (ha : ∀ w, a w ≠ ⊤) :
    ∑' w, a w * S w ≤ (∑' w, a w) ^ (1 - 2 / q) * (∑' w, a w * S w ^ (q / 2)) ^ (2 / q) := by
  have hq0 : 0 < q := by linarith
  have hβ : 0 < 2 / q := by positivity
  have hα : 0 ≤ 1 - 2 / q := by rw [sub_nonneg, div_le_one hq0]; exact hq
  have hpt : ∀ w, a w * S w = a w ^ (1 - 2 / q) * (a w * S w ^ (q / 2)) ^ (2 / q) := by
    intro w
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ.le, ← ENNReal.rpow_mul,
      show q / 2 * (2 / q) = 1 by field_simp, ENNReal.rpow_one, ← mul_assoc]
    congr 1
    by_cases h0 : a w = 0
    · rw [h0, ENNReal.zero_rpow_of_pos hβ, mul_zero]
    · rw [← ENNReal.rpow_add _ _ h0 (ha w), sub_add_cancel, ENNReal.rpow_one]
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := Measure.count (α := Vertex d))
    (f := a) (g := fun w => a w * S w ^ (q / 2)) (Measurable.of_discrete).aemeasurable
    (Measurable.of_discrete).aemeasurable hα hβ.le (by ring)
  simp only [lintegral_count] at h
  simp only [hpt]
  exact h

end Rigidity.Poincare.GeneralDim
