import Rigidity.Proofs.Corrector.DarioCoarsenedOs

/-!
# Step 1 of the proof of Dario's Theorem 2 in dimension two, in moment form

Step 1 of the proof of Theorem 2 (Dario, §4) combines the multiscale Poincaré inequality
(Proposition 2.11, (heatmultscaleP.ver)) with the bound of Proposition 3.1 on the heat-kernel
averages of the gradient of the coarsened corrector, `|Φ_{r²} * ∇[χ]_𝒫(x)| ≤ O_s(C r^{-d/2})` for
`r ≥ 1`, and with the Lipschitz bound (lipboundcoarcorr) for `r ≤ 1`, to obtain
(maintoolstep1Linfty).

Here the three inputs are hypotheses on a family `S r x` standing for `|Φ_{r²} * ∇u(x)|`, and the
conclusion (`lintegral_boxOsc_le_of_poincare`) is the moment form (step1LinftyLp), the form used by
Steps 1–4 of the proof of Theorem 1 (`LinftyIterationData.thm2`), with the exponent `k = 3/2 + 1/s`
of the paper. The `O_s`-averaging (e.Oavgs) of the paper is replaced by moments: Jensen's
inequality in `r` for the measure `min(r, 1/r) dr` on `(0, 2R]`, of mass at most `1/2 + log 2R`,
Tonelli's theorem, and the lattice sum `Σ_x R^{-2} e^{-|x|/2R} ≤ 100`. The multiscale Poincaré
inequality is used in the cube form at `R = 3^m`, the form in which (maintoolstep1Linfty) is
applied; the exponents `1 ≤ q < 2` are reduced to `q = 2` by Jensen's inequality, as in the paper.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

variable {p : unitInterval}

/-- Jensen's inequality `E[Y^a] ≤ E[Y]^a` for `0 ≤ a ≤ 1`. -/
theorem lintegral_rpow_le_rpow_lintegral {Y : Configuration 2 → ℝ≥0∞}
    (hY : AEMeasurable Y (latticeBondLaw 2 p)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫⁻ ω, Y ω ^ a ∂latticeBondLaw 2 p ≤ (∫⁻ ω, Y ω ∂latticeBondLaw 2 p) ^ a := by
  have h := ENNReal.lintegral_mul_norm_pow_le hY (aemeasurable_const (b := (1 : ℝ≥0∞))) ha0
    (sub_nonneg.2 ha1) (by ring : a + (1 - a) = 1)
  simpa [ENNReal.one_rpow, lintegral_const, measure_univ] using h

/-- Jensen's inequality for a weight `w`: `(∫ g w)^a ≤ (∫ g^a w) (∫ w)^{a-1}` for `a ≥ 1`. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {g w : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) (hw : AEMeasurable w μ) (hwt : ∀ x, w x ≠ ⊤) {a : ℝ} (ha : 1 ≤ a) :
    (∫⁻ x, g x * w x ∂μ) ^ a ≤ (∫⁻ x, g x ^ a * w x ∂μ) * (∫⁻ x, w x ∂μ) ^ (a - 1) := by
  have ha0 : 0 < a := by linarith
  have h := ENNReal.lintegral_mul_norm_pow_le ((hg.pow_const a).mul hw) hw
    (p := 1 / a) (q := 1 - 1 / a) (by positivity)
    (by rw [sub_nonneg, div_le_one ha0]; exact ha) (by ring)
  have hpt : ∀ x, (g x ^ a * w x) ^ (1 / a) * w x ^ (1 - 1 / a) = g x * w x := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
      mul_one_div_cancel ha0.ne', ENNReal.rpow_one, mul_assoc]
    congr 1
    rcases eq_or_ne (w x) 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos (by positivity), zero_mul]
    · rw [← ENNReal.rpow_add _ _ h0 (hwt x), show 1 / a + (1 - 1 / a) = 1 by ring,
        ENNReal.rpow_one]
  simp only [Pi.mul_apply, hpt] at h
  calc (∫⁻ x, g x * w x ∂μ) ^ a
      ≤ ((∫⁻ x, g x ^ a * w x ∂μ) ^ (1 / a) * (∫⁻ x, w x ∂μ) ^ (1 - 1 / a)) ^ a :=
        ENNReal.rpow_le_rpow h ha0.le
    _ = (∫⁻ x, g x ^ a * w x ∂μ) * (∫⁻ x, w x ∂μ) ^ (a - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel ha0.ne', ENNReal.rpow_one,
          show (1 - 1 / a) * a = a - 1 by field_simp]

/-- The mass of the weight `min(r, 1/r)` on `(0, T]`: at most `1/2 + log T`. -/
theorem lintegral_Ioc_min_inv_le {T : ℝ} (hT : 1 ≤ T) :
    ∫⁻ r in Ioc 0 T, ENNReal.ofReal (min r r⁻¹) ≤ ENNReal.ofReal (1 / 2 + Real.log T) := by
  rw [← Ioc_union_Ioc_eq_Ioc zero_le_one hT,
    lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  have h1 : ∫⁻ r in Ioc 0 1, ENNReal.ofReal (min r r⁻¹) ≤ ENNReal.ofReal (1 / 2) := by
    calc ∫⁻ r in Ioc 0 1, ENNReal.ofReal (min r r⁻¹) ≤ ∫⁻ r in Ioc 0 1, ENNReal.ofReal r :=
          lintegral_mono fun r => ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ENNReal.ofReal (∫ r in Ioc 0 1, r) :=
          (ofReal_integral_eq_lintegral_ofReal
            ((continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => hr.1.le)).symm
      _ = ENNReal.ofReal (1 / 2) := by
          rw [← intervalIntegral.integral_of_le zero_le_one, integral_id]
          norm_num
  have h2 : ∫⁻ r in Ioc 1 T, ENNReal.ofReal (min r r⁻¹) ≤ ENNReal.ofReal (Real.log T) := by
    have hcont : ContinuousOn (fun r : ℝ => r⁻¹) (Icc 1 T) :=
      continuousOn_inv₀.mono fun r hr =>
        Set.mem_compl_singleton_iff.2 (lt_of_lt_of_le zero_lt_one hr.1).ne'
    calc ∫⁻ r in Ioc 1 T, ENNReal.ofReal (min r r⁻¹) ≤ ∫⁻ r in Ioc 1 T, ENNReal.ofReal r⁻¹ :=
          lintegral_mono fun r => ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = ENNReal.ofReal (∫ r in Ioc 1 T, r⁻¹) :=
          (ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
            (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr =>
              inv_nonneg.2 (zero_le_one.trans hr.1.le))).symm
      _ = ENNReal.ofReal (Real.log T) := by
          rw [← intervalIntegral.integral_of_le hT, integral_inv_of_pos zero_lt_one
            (lt_of_lt_of_le zero_lt_one hT), div_one]
  calc _ ≤ ENNReal.ofReal (1 / 2) + ENNReal.ofReal (Real.log T) := add_le_add h1 h2
    _ = ENNReal.ofReal (1 / 2 + Real.log T) :=
        (ENNReal.ofReal_add (by norm_num) (Real.log_nonneg hT)).symm

/-- `Σ_{n ∈ ℤ} e^{-c|n|} ≤ 2 (1 + 1/c)`. -/
theorem tsum_int_exp_neg_le {c : ℝ} (hc : 0 < c) :
    ∑' n : ℤ, ENNReal.ofReal (Real.exp (-(c * |(n : ℝ)|))) ≤ ENNReal.ofReal (2 * (1 + 1 / c)) := by
  have hgeo : ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(c * (k : ℝ)))) ≤
      ENNReal.ofReal (1 + 1 / c) := by
    have hpt : ∀ k : ℕ, ENNReal.ofReal (Real.exp (-(c * (k : ℝ)))) =
        ENNReal.ofReal (Real.exp (-c)) ^ k := by
      intro k
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
      congr 2
      ring
    simp only [hpt]
    rw [ENNReal.tsum_geometric]
    have he1 : Real.exp (-c) < 1 := by
      have := Real.exp_lt_exp.2 (show -c < 0 by linarith)
      rwa [Real.exp_zero] at this
    have hpos : 0 < 1 - Real.exp (-c) := by linarith
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
      ← ENNReal.ofReal_inv_of_pos hpos]
    refine ENNReal.ofReal_le_ofReal ?_
    have hE : Real.exp (-c) * (1 + c) ≤ 1 := by
      have h1 : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
      have h2 : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-c)]
    rw [inv_eq_one_div, div_le_iff₀ hpos,
      show (1 + 1 / c) * (1 - Real.exp (-c)) = ((1 + c) * (1 - Real.exp (-c))) / c by
        field_simp; ring, le_div_iff₀ hc]
    nlinarith
  refine (tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable).trans_le ?_
  have h1 : ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(c * |(((k : ℤ) : ℝ))|))) ≤
      ENNReal.ofReal (1 + 1 / c) := by
    refine le_trans (le_of_eq ?_) hgeo
    congr 1
    funext k
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
  have h2 : ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(c * |(((-((k : ℤ) + 1)) : ℤ) : ℝ)|))) ≤
      ENNReal.ofReal (1 + 1 / c) := by
    refine le_trans (ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_)) hgeo
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]
    nlinarith
  calc _ ≤ ENNReal.ofReal (1 + 1 / c) + ENNReal.ofReal (1 + 1 / c) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (1 + 1 / c)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- The lattice sum of the weights of the multiscale Poincaré inequality at `R = 3^m`:
`Σ_{x ∈ ℤ²} R^{-2} e^{-|x|/2R} ≤ 100`. -/
theorem tsum_poincareWeight_le (m : ℕ) :
    ∑' x : Vertex 2, ENNReal.ofReal
      (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / 9 ^ m) ≤ ENNReal.ofReal 100 := by
  set R : ℝ := 3 ^ m with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR0 : 0 < R := by linarith
  have h9 : (9 : ℝ) ^ m = R ^ 2 := by
    rw [hR, ← pow_mul, mul_comm, pow_mul]
    norm_num
  set c : ℝ := 1 / (4 * R) with hc
  have hc0 : 0 < c := by positivity
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-(c * |(n : ℝ)|))) with hf
  have hpt : ∀ x : Vertex 2, ENNReal.ofReal
      (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / 9 ^ m) ≤
        ENNReal.ofReal (1 / 9 ^ m) * (f (x 0) * f (x 1)) := by
    intro x
    have hc0' := PiLp.norm_apply_le (latticeEuclideanEmbedding x) 0
    have hc1' := PiLp.norm_apply_le (latticeEuclideanEmbedding x) 1
    change ‖((x 0 : ℤ) : ℝ)‖ ≤ _ at hc0'
    change ‖((x 1 : ℤ) : ℝ)‖ ≤ _ at hc1'
    rw [Real.norm_eq_abs] at hc0' hc1'
    simp only [hf]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_eq_mul_one_div, mul_comm]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    set e := ‖latticeEuclideanEmbedding x‖
    have key : (|((x 0 : ℤ) : ℝ)| + |((x 1 : ℤ) : ℝ)|) / (4 * R) ≤ e / (2 * R) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h1 : -e / (2 * 3 ^ m) = -(e / (2 * R)) := by rw [neg_div]
    have h2 : (|((x 0 : ℤ) : ℝ)| + |((x 1 : ℤ) : ℝ)|) / (4 * R) =
        c * |((x 0 : ℤ) : ℝ)| + c * |((x 1 : ℤ) : ℝ)| := by
      rw [hc]
      ring
    rw [h1]
    linarith
  have hsum : ∑' n : ℤ, f n ≤ ENNReal.ofReal (2 * (1 + 4 * R)) := by
    have := tsum_int_exp_neg_le hc0
    rwa [hc, one_div_one_div] at this
  have hprod : ∑' x : Vertex 2, f (x 0) * f (x 1) = (∑' n : ℤ, f n) * ∑' n : ℤ, f n := by
    rw [← ENNReal.tsum_mul_right]
    simp_rw [← ENNReal.tsum_mul_left]
    rw [← ENNReal.tsum_prod]
    exact (finTwoArrowEquiv ℤ).tsum_eq (fun ab => f ab.1 * f ab.2)
  calc ∑' x : Vertex 2, ENNReal.ofReal
        (Real.exp (-‖latticeEuclideanEmbedding x‖ / (2 * 3 ^ m)) / 9 ^ m)
      ≤ ∑' x : Vertex 2, ENNReal.ofReal (1 / 9 ^ m) * (f (x 0) * f (x 1)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (1 / 9 ^ m) * ((∑' n : ℤ, f n) * ∑' n : ℤ, f n) := by
        rw [ENNReal.tsum_mul_left, hprod]
    _ ≤ ENNReal.ofReal (1 / 9 ^ m) *
          (ENNReal.ofReal (2 * (1 + 4 * R)) * ENNReal.ofReal (2 * (1 + 4 * R))) := by
        gcongr
    _ = ENNReal.ofReal (1 / 9 ^ m * (2 * (1 + 4 * R) * (2 * (1 + 4 * R)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal 100 := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h9, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith

theorem half_add_log_le {m : ℕ} (hm : 1 ≤ m) : 1 / 2 + Real.log (2 * 3 ^ m) ≤ 4 * m := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h3 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- **The moment of the heat-kernel square function at one point**: under the bounds of
Proposition 3.1 (`r ≥ 1`) and of the Lipschitz bound (`r ≤ 1`) on `S r x = |Φ_{r²} * ∇u(x)|`,
`E[(∫_0^T r S(r, x)² dr)^{q/2}] ≤ (2 C (1/s)^{1/s} q^{1/s})^q (1/2 + log T)^{q/2}`. -/
theorem lintegral_rpow_heatSquare_le {S : ℝ → Vertex 2 → Configuration 2 → ℝ} {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s)
    (hSm : ∀ x, Measurable fun rω : ℝ × Configuration 2 => S rω.1 x rω.2)
    (hS0 : ∀ r x ω, 0 ≤ S r x ω)
    (hlarge : ∀ r : ℝ, 1 ≤ r → ∀ x, IsOsBond 2 p (S r x) s (C / r))
    (hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, IsOsBond 2 p (S r x) s C)
    {T q : ℝ} (hT : 1 ≤ T) (hq : 2 ≤ q) (x : Vertex 2) :
    ∫⁻ ω, (∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2)) ^ (q / 2) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((2 * C * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) *
        ENNReal.ofReal (1 / 2 + Real.log T) ^ (q / 2) := by
  set a := q / 2 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  set σ := (1 / s) ^ (1 / s) with hσ
  have hσ0 : 0 < σ := by positivity
  set K := (2 * C * σ * q ^ (1 / s)) ^ q with hK
  set W := ENNReal.ofReal (1 / 2 + Real.log T) with hW
  have hW0 : W ≠ 0 := by
    rw [hW, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith [Real.log_nonneg hT]
  have hWt : W ≠ ⊤ := ENNReal.ofReal_ne_top
  set w : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (min r r⁻¹) with hw
  have hwm : Measurable w := (measurable_id.min measurable_inv).ennreal_ofReal
  set g : ℝ → Configuration 2 → ℝ≥0∞ := fun r ω => ENNReal.ofReal (max 1 (r ^ 2) * S r x ω ^ 2)
    with hg
  have hgm : Measurable fun rω : ℝ × Configuration 2 => g rω.1 rω.2 :=
    ((measurable_const.max (measurable_fst.pow_const 2)).mul ((hSm x).pow_const 2)).ennreal_ofReal
  have hid : ∀ ω, EqOn (fun r => ENNReal.ofReal (r * S r x ω ^ 2)) (fun r => g r ω * w r)
      (Ioc 0 T) := by
    intro ω r hr
    simp only [hg, hw]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hr0 : 0 < r := hr.1
    rcases le_or_gt r 1 with h1 | h1
    · rw [max_eq_left (by nlinarith), min_eq_left (h1.trans ((one_le_inv₀ hr0).2 h1))]
      ring
    · rw [max_eq_right (by nlinarith),
        min_eq_right ((inv_lt_one_of_one_lt₀ h1).le.trans h1.le)]
      field_simp
  -- Jensen in `r`, pointwise in `ω`
  have hpt : ∀ ω, (∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2)) ^ a ≤
      (∫⁻ r in Ioc 0 T, g r ω ^ a * w r) * W ^ (a - 1) := by
    intro ω
    rw [setLIntegral_congr_fun measurableSet_Ioc (hid ω)]
    refine (lintegral_mul_rpow_le (hgm.comp (measurable_id.prodMk measurable_const)).aemeasurable
      hwm.aemeasurable (fun r => ENNReal.ofReal_ne_top) ha1).trans ?_
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (lintegral_Ioc_min_inv_le hT) (by linarith)) _
  -- the moment at each `r`
  have hmomr : ∀ r ∈ Ioc (0 : ℝ) T, ∫⁻ ω, g r ω ^ a ∂latticeBondLaw 2 p ≤ ENNReal.ofReal K := by
    intro r hr
    have hr0 : 0 < r := hr.1
    obtain ⟨θ, hθ, hO, hMθ⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond 2 p (S r x) s θ ∧ max 1 r * θ = C := by
      rcases le_or_gt r 1 with h1 | h1
      · exact ⟨C, hC, hsmall r hr0 h1 x, by rw [max_eq_left h1, one_mul]⟩
      · refine ⟨C / r, by positivity, hlarge r h1.le x, ?_⟩
        rw [max_eq_right h1.le]
        field_simp
    have hO' : IsOsBond 2 p (fun ω => |S r x ω|) s θ := by
      have : (fun ω => |S r x ω|) = S r x := funext fun ω => abs_of_nonneg (hS0 r x ω)
      rw [this]
      exact hO
    have hSmr : Measurable (S r x) :=
      (hSm x).comp (measurable_const.prodMk measurable_id)
    have hmom := mom_le_of_isOsBond hs hθ hq1 hSmr hO'
    have hga : ∀ ω, g r ω ^ a = ENNReal.ofReal ((max 1 r) ^ q) * ENNReal.ofReal (|S r x ω| ^ q) := by
      intro ω
      simp only [hg]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hmax : max 1 (r ^ 2) = (max 1 r) ^ 2 := by
        rcases le_or_gt r 1 with h1 | h1
        · rw [max_eq_left (by nlinarith), max_eq_left h1, one_pow]
        · rw [max_eq_right (by nlinarith), max_eq_right h1.le]
      rw [hmax, abs_of_nonneg (hS0 r x ω), ← mul_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul (mul_nonneg (le_max_of_le_left zero_le_one) (hS0 r x ω)),
        Real.mul_rpow (le_max_of_le_left zero_le_one) (hS0 r x ω)]
      rw [show ((2 : ℕ) : ℝ) * a = q by rw [ha]; push_cast; ring]
    simp only [hga]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((max 1 r) ^ q) * mom p (S r x) q
        ≤ ENNReal.ofReal ((max 1 r) ^ q) *
            ENNReal.ofReal ((2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) := by
          gcongr
      _ = ENNReal.ofReal K := by
          rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity)
            (by positivity), hK]
          congr 2
          rw [← hMθ, hσ]
          ring
  -- Tonelli and the mass of the weight
  have hswap : ∫⁻ ω, ∫⁻ r in Ioc 0 T, g r ω ^ a * w r ∂volume ∂latticeBondLaw 2 p =
      ∫⁻ r in Ioc 0 T, ∫⁻ ω, g r ω ^ a * w r ∂latticeBondLaw 2 p := by
    refine lintegral_lintegral_swap ?_
    exact (((hgm.comp measurable_swap).pow_const a).mul (hwm.comp measurable_snd)).aemeasurable
  have hinner : ∫⁻ r in Ioc 0 T, ∫⁻ ω, g r ω ^ a * w r ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal K * W := by
    calc ∫⁻ r in Ioc 0 T, ∫⁻ ω, g r ω ^ a * w r ∂latticeBondLaw 2 p
        ≤ ∫⁻ r in Ioc 0 T, ENNReal.ofReal K * w r := by
          refine setLIntegral_mono' measurableSet_Ioc fun r hr => ?_
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul_left (hmomr r hr) _
      _ = ENNReal.ofReal K * ∫⁻ r in Ioc 0 T, w r := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * W := mul_le_mul_right (lintegral_Ioc_min_inv_le hT) _
  calc ∫⁻ ω, (∫⁻ r in Ioc 0 T, ENNReal.ofReal (r * S r x ω ^ 2)) ^ a ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, (∫⁻ r in Ioc 0 T, g r ω ^ a * w r) * W ^ (a - 1) ∂latticeBondLaw 2 p :=
        lintegral_mono hpt
    _ = (∫⁻ ω, ∫⁻ r in Ioc 0 T, g r ω ^ a * w r ∂volume ∂latticeBondLaw 2 p) * W ^ (a - 1) :=
        lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hWt)
    _ ≤ ENNReal.ofReal K * W * W ^ (a - 1) := by
        rw [hswap]
        exact mul_le_mul_left hinner _
    _ = ENNReal.ofReal K * W ^ a := by
        rw [mul_assoc]
        congr 1
        conv_rhs => rw [show a = 1 + (a - 1) by ring, ENNReal.rpow_add _ _ hW0 hWt,
          ENNReal.rpow_one]

end Rigidity.Corrector
