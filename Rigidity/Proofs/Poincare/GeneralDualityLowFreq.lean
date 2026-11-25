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

/-- **The low-frequency bound**: for `|y|₁ ≤ R`,
`A_j(8R², y)² ≤ (K/R²) (Σ_w R^{-d} e^{-|w|/(2R)} Sq(w)^{q/2})^{2/q}`. -/
theorem exists_ofReal_sq_heatGrad_le [NeZero d] : ∃ K : ℝ, 0 < K ∧ ∀ u : Vertex d → ℝ,
    HeatSummable u → ∀ (j : Fin d) (R : ℝ), 3 ≤ R → ∀ q : ℝ, 2 ≤ q → ∀ y : Vertex d,
      ∑ i, |((y i : ℤ) : ℝ)| ≤ R →
      ENNReal.ofReal (heatGrad u j (8 * R ^ 2) y ^ 2) ≤ ENNReal.ofReal (K / R ^ 2) *
        (∑' w, dwt R w * sqInt u (2 * R) w ^ (q / 2)) ^ (2 / q) := by
  obtain ⟨C, hC, hker⟩ := exists_zdHeat_le_exp (d := d)
  set K' := C * Real.exp (2 / 3) / 2 ^ d with hK'
  set KB := C * (1 + 2 * d) ^ d with hKB
  refine ⟨KB * max K' 1, by positivity, fun u hu j R hR q hq y hy => ?_⟩
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  set T := 8 * R ^ 2 with hT
  set B : Vertex d → ℝ := fun w => C / (2 * R) ^ d *
    Real.exp (-(2 / (3 * R)) * ∑ i, |(((w - y) i : ℤ) : ℝ)|) with hB
  have hB0 : ∀ w, 0 ≤ B w := fun w => by positivity
  set RHS := ∑' w, dwt R w * sqInt u (2 * R) w ^ (q / 2) with hRHS
  set I := Set.Ioc (2 * R ^ 2) (4 * R ^ 2) with hI
  have hIsub : I ⊆ Set.Icc 0 T := fun s hs => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  -- Jensen at each time `s ∈ I`
  have hJ : ∀ s ∈ I, ENNReal.ofReal (heatGrad u j T y ^ 2) ≤
      ∑' w, ENNReal.ofReal (zdHeat d (T - s) y w * heatGrad u j s w ^ 2) := by
    intro s hs
    have hs' := hIsub hs
    rw [heatGrad_eq_tsum hu j hs'.1 hs'.2 y]
    exact ofReal_sq_tsum_heat_le (by linarith [hs'.2]) y _
  -- the kernel bound on `I`
  have hΦB : ∀ s ∈ I, ∀ w, zdHeat d (T - s) y w ≤ B w := fun s hs w =>
    hker R hR (T - s) (by nlinarith [hs.2]) (by nlinarith [hs.1]) y w
  have hmeas : ∀ w, AEMeasurable (fun s => ENNReal.ofReal
      (zdHeat d (T - s) y w * heatGrad u j s w ^ 2)) (volume.restrict I) := by
    intro w
    refine (ContinuousOn.aemeasurable ?_ measurableSet_Ioc).ennreal_ofReal
    exact ((continuous_zdHeat y w).comp (continuous_const.sub continuous_id)).continuousOn.mul
      (((continuousOn_heatGrad hu j (by positivity : (0 : ℝ) ≤ T) w).mono hIsub).pow 2)
  have hA : ∀ w, ∫⁻ s in I, ENNReal.ofReal (heatGrad u j s w ^ 2) ≤
      2 * sqInt u (2 * R) w := by
    intro w
    have h := lintegral_sum_sq_heatGrad_le u (by linarith : 0 ≤ 2 * R) w
    rw [show (2 * R) ^ 2 = 4 * R ^ 2 by ring] at h
    refine le_trans ?_ h
    refine (lintegral_mono_set (Set.Ioc_subset_Ioc_left (by positivity))).trans ?_
    refine setLIntegral_mono' measurableSet_Ioc fun s _ => ENNReal.ofReal_le_ofReal ?_
    exact Finset.single_le_sum (f := fun i => heatGrad u i s w ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hstep : ENNReal.ofReal (heatGrad u j T y ^ 2) * ENNReal.ofReal (2 * R ^ 2) ≤
      2 * ∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w := by
    calc ENNReal.ofReal (heatGrad u j T y ^ 2) * ENNReal.ofReal (2 * R ^ 2)
        = ∫⁻ _ in I, ENNReal.ofReal (heatGrad u j T y ^ 2) := by
          rw [setLIntegral_const, hI, Real.volume_Ioc]
          congr 2
          ring
      _ ≤ ∫⁻ s in I, ∑' w, ENNReal.ofReal
            (zdHeat d (T - s) y w * heatGrad u j s w ^ 2) :=
          setLIntegral_mono' measurableSet_Ioc hJ
      _ = ∑' w, ∫⁻ s in I, ENNReal.ofReal
            (zdHeat d (T - s) y w * heatGrad u j s w ^ 2) := lintegral_tsum hmeas
      _ ≤ ∑' w, ENNReal.ofReal (B w) * (2 * sqInt u (2 * R) w) := by
          refine ENNReal.tsum_le_tsum fun w => ?_
          calc ∫⁻ s in I, ENNReal.ofReal
                (zdHeat d (T - s) y w * heatGrad u j s w ^ 2)
              ≤ ∫⁻ s in I, ENNReal.ofReal (B w) * ENNReal.ofReal (heatGrad u j s w ^ 2) := by
                refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
                rw [← ENNReal.ofReal_mul (hB0 w)]
                exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hΦB s hs w)
                  (sq_nonneg _))
            _ = ENNReal.ofReal (B w) * ∫⁻ s in I, ENNReal.ofReal (heatGrad u j s w ^ 2) :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ ≤ ENNReal.ofReal (B w) * (2 * sqInt u (2 * R) w) := by gcongr; exact hA w
      _ = 2 * ∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun w => by ring
  -- the two sums
  have hsumB : ∑' w, ENNReal.ofReal (B w) ≤ ENNReal.ofReal KB := by
    have hpt : ∀ w, ENNReal.ofReal (B w) ≤ ENNReal.ofReal (C / (2 * R) ^ d) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (w - y)‖ / (3 * R / 2))) := by
      intro w
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
        (by positivity))
      have hn := norm_euclid_le_sum_abs (w - y)
      rw [neg_div, div_div_eq_mul_div, neg_mul, neg_le_neg_iff]
      rw [show ‖latticeEuclideanEmbedding (w - y)‖ * 2 / (3 * R) =
        2 / (3 * R) * ‖latticeEuclideanEmbedding (w - y)‖ by ring]
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc ∑' w, ENNReal.ofReal (B w)
        ≤ ∑' w, ENNReal.ofReal (C / (2 * R) ^ d) *
            ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (w - y)‖ / (3 * R / 2))) :=
          ENNReal.tsum_le_tsum hpt
      _ = ENNReal.ofReal (C / (2 * R) ^ d) * ∑' w,
            ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (w - y)‖ / (3 * R / 2))) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (C / (2 * R) ^ d) *
            ENNReal.ofReal ((2 * (1 + d * (3 * R / 2))) ^ d) := by
          gcongr
          exact tsum_exp_neg_norm_sub_le y (by positivity)
      _ ≤ ENNReal.ofReal KB := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hbase : 2 * (1 + d * (3 * R / 2)) / (2 * R) ≤ 1 + 2 * d := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith
          have hpow := pow_le_pow_left₀ (by positivity) hbase d
          rw [div_pow] at hpow
          calc C / (2 * R) ^ d * (2 * (1 + d * (3 * R / 2))) ^ d =
              C * ((2 * (1 + d * (3 * R / 2))) ^ d / (2 * R) ^ d) := by ring
            _ ≤ C * (1 + 2 * d) ^ d := mul_le_mul_of_nonneg_left hpow (by linarith)
  have hBdwt : ∀ w, ENNReal.ofReal (B w) ≤ ENNReal.ofReal K' * dwt R w := by
    intro w
    rw [dwt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn := norm_euclid_le_sum_abs w
    have hwy : ∑ i, |((w i : ℤ) : ℝ)| ≤ ∑ i, |(((w - y) i : ℤ) : ℝ)| + ∑ i, |((y i : ℤ) : ℝ)| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := abs_sub_abs_le_abs_sub ((w i : ℤ) : ℝ) ((y i : ℤ) : ℝ)
      rw [Pi.sub_apply, Int.cast_sub]
      linarith
    have hexp : Real.exp (-(2 / (3 * R)) * ∑ i, |(((w - y) i : ℤ) : ℝ)|)
        ≤ Real.exp (2 / 3) * Real.exp (-‖latticeEuclideanEmbedding w‖ / (2 * R)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hz : ‖latticeEuclideanEmbedding w‖ - R ≤ ∑ i, |(((w - y) i : ℤ) : ℝ)| := by linarith
      have h2 : 2 / (3 * R) * (‖latticeEuclideanEmbedding w‖ - R) ≤
          2 / (3 * R) * ∑ i, |(((w - y) i : ℤ) : ℝ)| :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      have hnn : 0 ≤ ‖latticeEuclideanEmbedding w‖ := norm_nonneg _
      have h3 : ‖latticeEuclideanEmbedding w‖ / (2 * R) ≤
          2 / (3 * R) * ‖latticeEuclideanEmbedding w‖ := by
        rw [div_le_iff₀ (by positivity)]
        have e : 2 / (3 * R) * ‖latticeEuclideanEmbedding w‖ * (2 * R) =
            4 / 3 * ‖latticeEuclideanEmbedding w‖ := by field_simp; ring
        rw [e]
        nlinarith
      have h4 : 2 / (3 * R) * (‖latticeEuclideanEmbedding w‖ - R) =
          2 / (3 * R) * ‖latticeEuclideanEmbedding w‖ - 2 / 3 := by field_simp
      rw [neg_div, neg_mul]
      linarith
    simp only [hB, hK']
    calc C / (2 * R) ^ d * Real.exp (-(2 / (3 * R)) * ∑ i, |(((w - y) i : ℤ) : ℝ)|)
        ≤ C / (2 * R) ^ d * (Real.exp (2 / 3) *
            Real.exp (-‖latticeEuclideanEmbedding w‖ / (2 * R))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * Real.exp (2 / 3) / 2 ^ d * (Real.exp (-‖latticeEuclideanEmbedding w‖ / (2 * R)) /
            R ^ d) := by rw [mul_pow]; field_simp
  have hsum2 : ∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w ^ (q / 2) ≤
      ENNReal.ofReal K' * RHS := by
    rw [hRHS, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hBdwt w) (by simp)
  have hH := tsum_mul_le_holder hq (fun w => ENNReal.ofReal (B w)) (sqInt u (2 * R))
    fun w => ENNReal.ofReal_ne_top
  have hα : 0 ≤ 1 - 2 / q := by rw [sub_nonneg, div_le_one hq0]; exact hq
  have hα1 : 1 - 2 / q ≤ 1 := by linarith [show (0 : ℝ) ≤ 2 / q by positivity]
  have hβ : 0 ≤ 2 / q := by positivity
  have hβ1 : 2 / q ≤ 1 := by rw [div_le_one hq0]; exact hq
  have hKB1 : 1 ≤ KB := by
    have : (1 : ℝ) ≤ (1 + 2 * d) ^ d :=
      one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    nlinarith
  have hfirst : (∑' w, ENNReal.ofReal (B w)) ^ (1 - 2 / q) ≤ ENNReal.ofReal KB := by
    refine (ENNReal.rpow_le_rpow hsumB hα).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hα]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_self_of_one_le hKB1 hα1)
  have hsecond : (∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w ^ (q / 2)) ^ (2 / q) ≤
      ENNReal.ofReal (max K' 1) * RHS ^ (2 / q) := by
    refine (ENNReal.rpow_le_rpow hsum2 hβ).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hβ]
    gcongr
    calc K' ^ (2 / q) ≤ (max K' 1) ^ (2 / q) :=
          Real.rpow_le_rpow (by positivity) (le_max_left _ _) hβ
      _ ≤ max K' 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) hβ1
  have hfinal : ENNReal.ofReal (heatGrad u j T y ^ 2) * ENNReal.ofReal (2 * R ^ 2) ≤
      ENNReal.ofReal (2 * (KB * max K' 1)) * RHS ^ (2 / q) := by
    refine hstep.trans ?_
    calc 2 * ∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w
        ≤ 2 * (ENNReal.ofReal KB * (ENNReal.ofReal (max K' 1) * RHS ^ (2 / q))) := by
          gcongr
          exact hH.trans (mul_le_mul' hfirst hsecond)
      _ = ENNReal.ofReal (2 * (KB * max K' 1)) * RHS ^ (2 / q) := by
          rw [ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_mul (p := KB) (by positivity), ENNReal.ofReal_ofNat]
          ring
  -- divide by `2R²`
  have h2R : ENNReal.ofReal (2 * R ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hdiv : ENNReal.ofReal (2 * (KB * max K' 1)) =
      ENNReal.ofReal (KB * max K' 1 / R ^ 2) * ENNReal.ofReal (2 * R ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hdiv, mul_right_comm] at hfinal
  exact (ENNReal.mul_le_mul_iff_left h2R ENNReal.ofReal_ne_top).1 hfinal

end Rigidity.Poincare.GeneralDim
