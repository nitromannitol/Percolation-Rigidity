import Rigidity.Proofs.Poincare.DualityBilinear
import Rigidity.Proofs.Corrector.RandomBallSums

/-!
# The low-frequency term of the duality identity

The term `Σ_j Σ_y G_j(y) A_j(8R², y)` of the duality identity (the term `ρ^{(j)}(1)` of
(D.21)-(D.24) of Armstrong, Kuusi and Mourrat) is controlled through the semigroup property
`A_j(8R², y) = Σ_w Φ_{8R² - s}(y, w) A_j(s, w)`, averaged over `s ∈ (2R², 4R²]`, and the heat
kernel bound `Φ_τ(y, w) ≤ (C/(4R²)) e^{-2|w - y|₁/(3R)}` for `τ ∈ [4R², 6R²]`:

  `A_j(8R², y)² ≤ (K/R²) (Σ_w R^{-2} e^{-|w|/(2R)} Sq(w)^{q/2})^{2/q}`

for `|y|₁ ≤ R` (`exists_ofReal_sq_heatGrad_le`), by Hölder's inequality with the exponents
`1 - 2/q` and `2/q`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

variable {u : Vertex 2 → ℝ}

theorem norm_euclid_le_abs_add_abs (v : Vertex 2) :
    ‖latticeEuclideanEmbedding v‖ ≤ |((v 0 : ℤ) : ℝ)| + |((v 1 : ℤ) : ℝ)| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : ‖latticeEuclideanEmbedding v 0‖ = |((v 0 : ℤ) : ℝ)| := Real.norm_eq_abs _
  have h1 : ‖latticeEuclideanEmbedding v 1‖ = |((v 1 : ℤ) : ℝ)| := Real.norm_eq_abs _
  rw [h0, h1, Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg (abs_nonneg ((v 0 : ℤ) : ℝ)) (abs_nonneg ((v 1 : ℤ) : ℝ))]

/-- The weight `R^{-2} e^{-|x|/(2R)}` of Dario's (2.26). -/
noncomputable def dwt (R : ℝ) (x : Vertex 2) : ENNReal :=
  ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * R)) / R ^ 2)

/-- **The heat kernel at times `τ ∈ [4R², 6R²]`**. -/
theorem exists_openHeat_le_exp : ∃ C : ℝ, 1 ≤ C ∧ ∀ R : ℝ, 3 ≤ R → ∀ τ : ℝ, 4 * R ^ 2 ≤ τ →
    τ ≤ 6 * R ^ 2 → ∀ y w : Vertex 2, openHeat (allOpen 2) τ y w ≤
      C / (4 * R ^ 2) *
        Real.exp (-(2 / (3 * R)) * (|(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)|)) := by
  obtain ⟨C, hC, h⟩ := exists_openHeat_mul_exp_le
  refine ⟨C, hC, fun R hR τ hτ1 hτ2 y w => ?_⟩
  have hR0 : 0 < R := by linarith
  have hτ0 : 0 < τ := by nlinarith
  set z := |(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)| with hz
  have hz0 : 0 ≤ z := by positivity
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
  rw [hσ, Real.sq_sqrt hτ0.le] at hk
  have hexp : Real.exp (1 / (3 * R) * z) * Real.exp (-(2 / (3 * R)) * z) ≥
      Real.exp (-z / Real.sqrt τ) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : z / (3 * R) ≤ z / Real.sqrt τ :=
      div_le_div_of_nonneg_left hz0 (by linarith) hsqle
    have e : 1 / (3 * R) * z + -(2 / (3 * R)) * z = -(z / (3 * R)) := by ring
    rw [e, neg_div]
    linarith
  have hC4 : C / τ ≤ C / (4 * R ^ 2) := div_le_div_of_nonneg_left (by linarith) (by positivity)
    hτ1
  have hpos : 0 < Real.exp (1 / (3 * R) * z) := Real.exp_pos _
  have hΦ0 := openHeat_nonneg (allOpen 2) hτ0.le y w
  -- `Φ e^{az} ≤ (C/τ) e^{-z/√τ} ≤ (C/(4R²)) e^{-2z/(3R)} e^{az}`
  have key : openHeat (allOpen 2) τ y w * Real.exp (1 / (3 * R) * z) ≤
      C / (4 * R ^ 2) * Real.exp (-(2 / (3 * R)) * z) * Real.exp (1 / (3 * R) * z) := by
    calc openHeat (allOpen 2) τ y w * Real.exp (1 / (3 * R) * z)
        ≤ C / τ * Real.exp (-z / Real.sqrt τ) := hk
      _ ≤ C / (4 * R ^ 2) * (Real.exp (1 / (3 * R) * z) * Real.exp (-(2 / (3 * R)) * z)) :=
          mul_le_mul hC4 hexp (Real.exp_pos _).le (by positivity)
      _ = C / (4 * R ^ 2) * Real.exp (-(2 / (3 * R)) * z) * Real.exp (1 / (3 * R) * z) := by
          ring
  exact le_of_mul_le_mul_right key hpos

theorem tsum_ofReal_openHeat {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    ∑' y, ENNReal.ofReal (openHeat (allOpen 2) t x y) = 1 :=
  Rigidity.Green.tsum_ofReal_vsrwHeat (by norm_num) (openGraph_degree_le_four _) ht x

/-- **Jensen for the heat semigroup** in lower sums:
`(Σ_w Φ_τ(y, w) a(w))² ≤ Σ_w Φ_τ(y, w) a(w)²`. -/
theorem ofReal_sq_tsum_heat_le {τ : ℝ} (hτ : 0 ≤ τ) (y : Vertex 2) (a : Vertex 2 → ℝ) :
    ENNReal.ofReal ((∑' w, openHeat (allOpen 2) τ y w * a w) ^ 2) ≤
      ∑' w, ENNReal.ofReal (openHeat (allOpen 2) τ y w * a w ^ 2) := by
  set Φ := fun w => openHeat (allOpen 2) τ y w with hΦ
  have hΦ0 : ∀ w, 0 ≤ Φ w := fun w => openHeat_nonneg _ hτ y w
  have h1 : ENNReal.ofReal |∑' w, Φ w * a w| ≤
      ∑' w, ENNReal.ofReal (Real.sqrt (Φ w)) * ENNReal.ofReal (Real.sqrt (Φ w) * |a w|) := by
    refine (ofReal_abs_tsum_le' _).trans (ENNReal.tsum_le_tsum fun w => ?_)
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc, Real.mul_self_sqrt (hΦ0 w),
      abs_mul, abs_of_nonneg (hΦ0 w)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count (α := Vertex 2))
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
    exact tsum_ofReal_openHeat hτ y
  have e2 : ∑' w, ENNReal.ofReal (Real.sqrt (Φ w) * |a w|) ^ (2 : ℝ) =
      ∑' w, ENNReal.ofReal (Φ w * a w ^ 2) := by
    refine tsum_congr fun w => ?_
    rw [hsq _ (by positivity), mul_pow, Real.sq_sqrt (hΦ0 w), sq_abs]
  rw [e1, e2, ENNReal.one_rpow, one_mul] at hH
  have h2 := h1.trans hH
  -- square both sides
  have h3 := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    hsq _ (abs_nonneg _), sq_abs] at h3
  exact h3

/-- Hölder's inequality with the exponents `1 - 2/q` and `2/q` on `ℤ²`. -/
theorem tsum_mul_le_holder {q : ℝ} (hq : 2 ≤ q) (a S : Vertex 2 → ENNReal)
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
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := Measure.count (α := Vertex 2))
    (f := a) (g := fun w => a w * S w ^ (q / 2)) (Measurable.of_discrete).aemeasurable
    (Measurable.of_discrete).aemeasurable hα hβ.le (by ring)
  simp only [lintegral_count] at h
  simp only [hpt]
  exact h

/-- **The low-frequency bound**: for `|y|₁ ≤ R`,
`A_j(8R², y)² ≤ (K/R²) (Σ_w R^{-2} e^{-|w|/(2R)} Sq(w)^{q/2})^{2/q}`. -/
theorem exists_ofReal_sq_heatGrad_le : ∃ K : ℝ, 0 < K ∧ ∀ u : Vertex 2 → ℝ, HeatSummable u →
    ∀ (j : Fin 2) (R : ℝ), 3 ≤ R → ∀ q : ℝ, 2 ≤ q → ∀ y : Vertex 2,
      |((y 0 : ℤ) : ℝ)| + |((y 1 : ℤ) : ℝ)| ≤ R →
      ENNReal.ofReal (heatGrad u j (8 * R ^ 2) y ^ 2) ≤ ENNReal.ofReal (K / R ^ 2) *
        (∑' w, dwt R w * sqInt u (2 * R) w ^ (q / 2)) ^ (2 / q) := by
  obtain ⟨C, hC, hker⟩ := exists_openHeat_le_exp
  set K' := C * Real.exp (2 / 3) / 4 with hK'
  refine ⟨16 * C * max K' 1, by positivity, fun u hu j R hR q hq y hy => ?_⟩
  have hR0 : 0 < R := by linarith
  have hq0 : 0 < q := by linarith
  set T := 8 * R ^ 2 with hT
  set B : Vertex 2 → ℝ := fun w => C / (4 * R ^ 2) *
    Real.exp (-(2 / (3 * R)) * (|(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)|)) with hB
  have hB0 : ∀ w, 0 ≤ B w := fun w => by positivity
  set RHS := ∑' w, dwt R w * sqInt u (2 * R) w ^ (q / 2) with hRHS
  set I := Set.Ioc (2 * R ^ 2) (4 * R ^ 2) with hI
  have hIsub : I ⊆ Set.Icc 0 T := fun s hs => ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  -- Jensen at each time `s ∈ I`
  have hJ : ∀ s ∈ I, ENNReal.ofReal (heatGrad u j T y ^ 2) ≤
      ∑' w, ENNReal.ofReal (openHeat (allOpen 2) (T - s) y w * heatGrad u j s w ^ 2) := by
    intro s hs
    have hs' := hIsub hs
    rw [heatGrad_eq_tsum hu j hs'.1 hs'.2 y]
    exact ofReal_sq_tsum_heat_le (by linarith [hs'.2]) y _
  -- the kernel bound on `I`
  have hΦB : ∀ s ∈ I, ∀ w, openHeat (allOpen 2) (T - s) y w ≤ B w := fun s hs w =>
    hker R hR (T - s) (by nlinarith [hs.2]) (by nlinarith [hs.1]) y w
  have hmeas : ∀ w, AEMeasurable (fun s => ENNReal.ofReal
      (openHeat (allOpen 2) (T - s) y w * heatGrad u j s w ^ 2)) (volume.restrict I) := by
    intro w
    refine (ContinuousOn.aemeasurable ?_ measurableSet_Ioc).ennreal_ofReal
    exact ((continuous_openHeat _ y w).comp (continuous_const.sub continuous_id)).continuousOn.mul
      (((continuousOn_heatGrad hu j (by positivity : (0 : ℝ) ≤ T) w).mono hIsub).pow 2)
  have hA : ∀ w, ∫⁻ s in I, ENNReal.ofReal (heatGrad u j s w ^ 2) ≤
      2 * sqInt u (2 * R) w := by
    intro w
    have h := lintegral_sum_sq_heatGrad_le u (by linarith : 0 ≤ 2 * R) w
    rw [show (2 * R) ^ 2 = 4 * R ^ 2 by ring] at h
    refine le_trans ?_ h
    refine (lintegral_mono_set (Set.Ioc_subset_Ioc_left (by positivity))).trans ?_
    refine setLIntegral_mono' measurableSet_Ioc fun s _ => ENNReal.ofReal_le_ofReal ?_
    fin_cases j <;> simp [Fin.sum_univ_two] <;> positivity
  have hstep : ENNReal.ofReal (heatGrad u j T y ^ 2) * ENNReal.ofReal (2 * R ^ 2) ≤
      2 * ∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w := by
    calc ENNReal.ofReal (heatGrad u j T y ^ 2) * ENNReal.ofReal (2 * R ^ 2)
        = ∫⁻ _ in I, ENNReal.ofReal (heatGrad u j T y ^ 2) := by
          rw [setLIntegral_const, hI, Real.volume_Ioc]
          congr 2
          ring
      _ ≤ ∫⁻ s in I, ∑' w, ENNReal.ofReal
            (openHeat (allOpen 2) (T - s) y w * heatGrad u j s w ^ 2) :=
          setLIntegral_mono' measurableSet_Ioc hJ
      _ = ∑' w, ∫⁻ s in I, ENNReal.ofReal
            (openHeat (allOpen 2) (T - s) y w * heatGrad u j s w ^ 2) := lintegral_tsum hmeas
      _ ≤ ∑' w, ENNReal.ofReal (B w) * (2 * sqInt u (2 * R) w) := by
          refine ENNReal.tsum_le_tsum fun w => ?_
          calc ∫⁻ s in I, ENNReal.ofReal
                (openHeat (allOpen 2) (T - s) y w * heatGrad u j s w ^ 2)
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
  have hsumB : ∑' w, ENNReal.ofReal (B w) ≤ ENNReal.ofReal (16 * C) := by
    have hpt : ∀ w, ENNReal.ofReal (B w) ≤ ENNReal.ofReal (C / (4 * R ^ 2)) *
        ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (w - y)‖ / (3 * R / 2))) := by
      intro w
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
        (by positivity))
      have hn := norm_euclid_le_abs_add_abs (w - y)
      rw [neg_div, div_div_eq_mul_div, neg_mul, neg_le_neg_iff]
      rw [show ‖latticeEuclideanEmbedding (w - y)‖ * 2 / (3 * R) =
        2 / (3 * R) * ‖latticeEuclideanEmbedding (w - y)‖ by ring]
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    calc ∑' w, ENNReal.ofReal (B w)
        ≤ ∑' w, ENNReal.ofReal (C / (4 * R ^ 2)) *
            ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (w - y)‖ / (3 * R / 2))) :=
          ENNReal.tsum_le_tsum hpt
      _ = ENNReal.ofReal (C / (4 * R ^ 2)) * ∑' w,
            ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (w - y)‖ / (3 * R / 2))) :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (C / (4 * R ^ 2)) * ENNReal.ofReal (4 * (1 + 2 * (3 * R / 2)) ^ 2) := by
          gcongr
          exact Rigidity.Corrector.tsum_exp_neg_norm_sub_le y (by positivity)
      _ ≤ ENNReal.ofReal (16 * C) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          have h16 : (1 + 2 * (3 * R / 2)) ^ 2 ≤ 16 * R ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_left h16 (by linarith : (0 : ℝ) ≤ 4 * C)
          nlinarith
  have hBdwt : ∀ w, ENNReal.ofReal (B w) ≤ ENNReal.ofReal K' * dwt R w := by
    intro w
    rw [dwt, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn := norm_euclid_le_abs_add_abs w
    have h0 : |((w 0 : ℤ) : ℝ)| - |((y 0 : ℤ) : ℝ)| ≤ |(((w - y) 0 : ℤ) : ℝ)| := by
      rw [Pi.sub_apply, Int.cast_sub]; exact abs_sub_abs_le_abs_sub _ _
    have h1 : |((w 1 : ℤ) : ℝ)| - |((y 1 : ℤ) : ℝ)| ≤ |(((w - y) 1 : ℤ) : ℝ)| := by
      rw [Pi.sub_apply, Int.cast_sub]; exact abs_sub_abs_le_abs_sub _ _
    have hexp : Real.exp (-(2 / (3 * R)) * (|(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)|))
        ≤ Real.exp (2 / 3) * Real.exp (-‖latticeEuclideanEmbedding w‖ / (2 * R)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hz : ‖latticeEuclideanEmbedding w‖ - R ≤
          |(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)| := by linarith
      have h2 : 2 / (3 * R) * (‖latticeEuclideanEmbedding w‖ - R) ≤
          2 / (3 * R) * (|(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)|) :=
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
    calc C / (4 * R ^ 2) *
          Real.exp (-(2 / (3 * R)) * (|(((w - y) 0 : ℤ) : ℝ)| + |(((w - y) 1 : ℤ) : ℝ)|))
        ≤ C / (4 * R ^ 2) * (Real.exp (2 / 3) *
            Real.exp (-‖latticeEuclideanEmbedding w‖ / (2 * R))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = C * Real.exp (2 / 3) / 4 * (Real.exp (-‖latticeEuclideanEmbedding w‖ / (2 * R)) /
            R ^ 2) := by field_simp
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
  have hfirst : (∑' w, ENNReal.ofReal (B w)) ^ (1 - 2 / q) ≤ ENNReal.ofReal (16 * C) := by
    refine (ENNReal.rpow_le_rpow hsumB hα).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hα]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_self_of_one_le (by linarith) hα1)
  have hsecond : (∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w ^ (q / 2)) ^ (2 / q) ≤
      ENNReal.ofReal (max K' 1) * RHS ^ (2 / q) := by
    refine (ENNReal.rpow_le_rpow hsum2 hβ).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hβ]
    gcongr
    calc K' ^ (2 / q) ≤ (max K' 1) ^ (2 / q) :=
          Real.rpow_le_rpow (by positivity) (le_max_left _ _) hβ
      _ ≤ max K' 1 := Real.rpow_le_self_of_one_le (le_max_right _ _) hβ1
  have hfinal : ENNReal.ofReal (heatGrad u j T y ^ 2) * ENNReal.ofReal (2 * R ^ 2) ≤
      ENNReal.ofReal (2 * (16 * C * max K' 1)) * RHS ^ (2 / q) := by
    refine hstep.trans ?_
    calc 2 * ∑' w, ENNReal.ofReal (B w) * sqInt u (2 * R) w
        ≤ 2 * (ENNReal.ofReal (16 * C) * (ENNReal.ofReal (max K' 1) * RHS ^ (2 / q))) := by
          gcongr
          exact hH.trans (mul_le_mul' hfirst hsecond)
      _ = ENNReal.ofReal (2 * (16 * C * max K' 1)) * RHS ^ (2 / q) := by
          rw [ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_mul (p := 16 * C) (by positivity), ENNReal.ofReal_ofNat]
          ring
  -- divide by `2R²`
  have h2R : ENNReal.ofReal (2 * R ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hdiv : ENNReal.ofReal (2 * (16 * C * max K' 1)) =
      ENNReal.ofReal (16 * C * max K' 1 / R ^ 2) * ENNReal.ofReal (2 * R ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hdiv, mul_right_comm] at hfinal
  exact (ENNReal.mul_le_mul_iff_left h2R ENNReal.ofReal_ne_top).1 hfinal

end Rigidity.Poincare
