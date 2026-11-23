import Rigidity.Proofs.Green.HeatTimeIntegrals
import Rigidity.Proofs.Section5.PlanarGreenUniqueness

/-!
# The planar Green function as a time integral of the heat kernel (deterministic part)

Dario–Gu, §5, in dimension two: on an infinite open component `K ∋ y`, if the heat kernel
`p(t, x, y)` satisfies the bound of Theorem 1 for `t ≥ max(T₀, |x - y|)` and the Carne–Varopoulos
bound `p(t, x, y) ≤ C₂ e^{-|x-y|/C₂}` for `t ≤ |x - y|` (`HeatBounds`), then

* `G(x) = ∫_0^∞ (p(t, x, y) - p(t, y, y)) dt` converges, and it is a Green column with pole `y`
  (the identity `g(x, y) = ∫_0^∞ (p(t, x, y) - p(t, y, y)) dt` of Dario–Gu, DG21.tex:333 and (5.4), which
  the source states without proof): `-Δ G = δ_y` follows from the heat equation and
  `p(t, x, y) → 0`, and `G` grows logarithmically;
* `G(x) - ḡ(x - y) - K = ∫_0^∞ (p(t, x, y) - θ^{-1} p̄(t, x - y)) dt` with
  `K = -∫_0^∞ (p(t, y, y) - θ^{-1} p̄(t, e)) dt`, `|e| = 1`, and `ḡ(z) = -log |z| / (π σ θ)`;
* `|K| ≤ (1 + θ^{-1}) T₀ + (C₁ + θ^{-1}/(4πσ²))/(β - 1)` and, for `|x - y| ≥ T₀`,
  `|∫_0^∞ (p(t, x, y) - θ^{-1} p̄(t, x - y)) dt| ≤ (2C₂³ + θ^{-1} + C₁^β Γ(β - 1)) |x - y|^{2 - 2β}`
  (splitting the time integral at `|x - y|`, as in the proof of the source for `d ≥ 3`, which the
  source says carries over to `d = 2`).

Here `β = 3/2 - δ/2` is the exponent of Theorem 1, `1 < β ≤ 3/2`.
-/

open MeasureTheory Set Real Filter Topology LatticeProb.Percolation

namespace Rigidity.Green

/-- The displacement `x - y` in the Euclidean plane. -/
abbrev edz (x y : Vertex 2) : EuclideanSpace ℝ (Fin 2) :=
  latticeEuclideanEmbedding x - latticeEuclideanEmbedding y

/-- A unit vector of the plane. -/
noncomputable def unitE : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

theorem norm_unitE : ‖unitE‖ = 1 := by
  simp [unitE]

/-- Distinct lattice points are at distance at least one. -/
theorem one_le_norm_edz {x y : Vertex 2} (hxy : x ≠ y) : 1 ≤ ‖edz x y‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
  have hc := PiLp.norm_apply_le (edz x y) i
  change |(x i : ℝ) - (y i : ℝ)| ≤ ‖edz x y‖ at hc
  have h1 : (1 : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := by
    have : (1 : ℤ) ≤ |x i - y i| := Int.one_le_abs (sub_ne_zero.2 hi)
    exact_mod_cast this
  exact h1.trans hc

theorem edz_self (y : Vertex 2) : edz y y = 0 := sub_self _

theorem gaussianHeat_le_one {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : 1 ≤ ‖z‖) : gaussianHeat σ t z ≤ 1 := by
  unfold gaussianHeat
  have hpi := Real.pi_pos
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
  set x := ‖z‖ ^ 2 / (2 * σ * t) with hx
  have hinv : (2 * Real.pi * σ * t)⁻¹ = x / (Real.pi * ‖z‖ ^ 2) := by rw [hx]; field_simp
  rw [hinv]
  have h1 := mul_exp_neg_le_one x
  have hden : 1 ≤ Real.pi * ‖z‖ ^ 2 := by nlinarith [Real.pi_gt_three]
  calc x / (Real.pi * ‖z‖ ^ 2) * Real.exp (-x) = x * Real.exp (-x) / (Real.pi * ‖z‖ ^ 2) := by
        ring
    _ ≤ 1 / (Real.pi * ‖z‖ ^ 2) := by gcongr
    _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hden

theorem measurable_gaussianHeat_time (σ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    Measurable fun t => gaussianHeat σ t z := by
  unfold gaussianHeat
  fun_prop

/-- The hypotheses of the deterministic part of Dario–Gu, §5, at one configuration. -/
structure HeatBounds {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2)
    (σ θ C₁ C₂ β T₀ : ℝ) : Prop where
  hσ : 0 < σ
  hθ : 0 < θ
  hC₁ : 0 < C₁
  hC₂ : 0 < C₂
  hβ1 : 1 < β
  hβ2 : β ≤ 3 / 2
  hT₀ : 1 ≤ T₀
  hy : y ∈ K.supp
  thm1 : ∀ x ∈ K.supp, ∀ t : ℝ, T₀ ≤ t → ‖edz x y‖ ≤ t →
    |openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y)| ≤
      C₁ * t ^ (-β) * Real.exp (-(‖edz x y‖ ^ 2 / (C₁ * t)))
  cv : ∀ x ∈ K.supp, ∀ t : ℝ, 0 < t → t ≤ ‖edz x y‖ →
    openHeat ω t x y ≤ C₂ * Real.exp (-(‖edz x y‖ / C₂))

namespace HeatBounds

variable {ω : Configuration 2} {K : OpenComponent ω} {y : Vertex 2} {σ θ C₁ C₂ β T₀ : ℝ}

theorem _root_.Rigidity.Green.aestronglyMeasurable_openHeat_sub (ω : Configuration 2)
    (x y : Vertex 2) (σ θ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    AEStronglyMeasurable (fun t => openHeat ω t x y - θ⁻¹ * gaussianHeat σ t z) volume :=
  ((continuous_openHeat ω x y).measurable.sub
    (measurable_const.mul (measurable_gaussianHeat_time σ z))).aestronglyMeasurable

/-- `t ↦ p(t, x, y) - θ^{-1} p̄(t, x - y)` is integrable on `(0, ∞)` for `x ≠ y` in `K`. -/
theorem integrableOn_sub_gaussian (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : Vertex 2}
    (hx : x ∈ K.supp) (hxy : x ≠ y) :
    IntegrableOn (fun t => openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y)) (Ioi 0) := by
  have hr := one_le_norm_edz hxy
  have hS : 0 < max T₀ ‖edz x y‖ := lt_of_lt_of_le one_pos (hb.hT₀.trans (le_max_left _ _))
  refine (integrableOn_Ioi_of_le (aestronglyMeasurable_openHeat_sub ω x y σ θ _) hS hb.hβ1
    (A := C₁)
    (B := 1 + θ⁻¹) (fun t ht => ?_) (fun t ht => ?_)).1
  · have ht0 : 0 < t := ht.1
    have h0 := openHeat_nonneg ω ht0.le x y
    have h1 := openHeat_le_one ω ht0.le x y
    have hg0 := gaussianHeat_nonneg hb.hσ ht0.le (edz x y)
    have hg1 := gaussianHeat_le_one hb.hσ ht0 hr
    have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
    rw [abs_le]
    constructor <;> nlinarith
  · have ht' : max T₀ ‖edz x y‖ < t := ht
    have hb1 := hb.thm1 x hx t ((le_max_left _ _).trans ht'.le) ((le_max_right _ _).trans ht'.le)
    refine hb1.trans ?_
    have he : Real.exp (-(‖edz x y‖ ^ 2 / (C₁ * t))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      have : 0 < t := lt_of_lt_of_le hS ht'.le
      have := hb.hC₁
      positivity
    have hp : 0 ≤ C₁ * t ^ (-β) := mul_nonneg hb.hC₁.le (Real.rpow_nonneg (lt_of_lt_of_le hS ht'.le).le _)
    calc C₁ * t ^ (-β) * Real.exp (-(‖edz x y‖ ^ 2 / (C₁ * t))) ≤ C₁ * t ^ (-β) * 1 := by gcongr
      _ = C₁ * t ^ (-β) := mul_one _

/-- The diagonal integral `∫_0^∞ (p(t, y, y) - θ^{-1} p̄(t, e)) dt` converges and
`|∫| ≤ (1 + θ^{-1}) T₀ + (C₁ + θ^{-1}/(4πσ²))/(β - 1)`. -/
theorem integrableOn_diag (hb : HeatBounds K y σ θ C₁ C₂ β T₀) :
    IntegrableOn (fun t => openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE) (Ioi 0) ∧
      |∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE)| ≤
        (1 + θ⁻¹) * T₀ + (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) / (β - 1) := by
  have hT0 : 0 < T₀ := lt_of_lt_of_le one_pos hb.hT₀
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hpi := Real.pi_pos
  have hσ := hb.hσ
  have hA : 0 ≤ C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹ := by have := hb.hC₁; positivity
  have hsmall : ∀ t ∈ Ioc 0 T₀,
      |openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE| ≤ 1 + θ⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h0 := openHeat_nonneg ω ht0.le y y
    have h1 := openHeat_le_one ω ht0.le y y
    have hg0 := gaussianHeat_nonneg hσ ht0.le unitE
    have hg1 := gaussianHeat_unit_le_one hσ ht0 norm_unitE
    rw [abs_le]
    constructor <;> nlinarith
  have hlarge : ∀ t ∈ Ioi T₀, |openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE| ≤
      (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) * t ^ (-β) := by
    intro t ht
    have ht' : T₀ < t := ht
    have ht1 : 1 ≤ t := hb.hT₀.trans ht'.le
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have hd := hb.thm1 y hb.hy t ht'.le (by rw [edz_self, norm_zero]; exact ht0.le)
    rw [edz_self, norm_zero] at hd
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
      Real.exp_zero, mul_one] at hd
    have hg := abs_gaussianHeat_zero_sub_unit_le hσ ht0 norm_unitE
    have hpow : t ^ (-(2 : ℝ)) ≤ t ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [hb.hβ2])
    have htri : |openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE| ≤
        |openHeat ω t y y - θ⁻¹ * gaussianHeat σ t 0| +
          θ⁻¹ * |gaussianHeat σ t 0 - gaussianHeat σ t unitE| := by
      have : openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE =
          (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t 0) +
            θ⁻¹ * (gaussianHeat σ t 0 - gaussianHeat σ t unitE) := by ring
      rw [this]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos hθi]
    have hc : (4 * Real.pi * σ ^ 2)⁻¹ * t ^ (-(2 : ℝ)) ≤ (4 * Real.pi * σ ^ 2)⁻¹ * t ^ (-β) := by
      gcongr
    calc |openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE|
        ≤ C₁ * t ^ (-β) + θ⁻¹ * ((4 * Real.pi * σ ^ 2)⁻¹ * t ^ (-(2 : ℝ))) := by
          refine htri.trans (add_le_add hd ?_)
          exact mul_le_mul_of_nonneg_left hg hθi.le
      _ ≤ C₁ * t ^ (-β) + θ⁻¹ * ((4 * Real.pi * σ ^ 2)⁻¹ * t ^ (-β)) := by gcongr
      _ = (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) * t ^ (-β) := by ring
  obtain ⟨hint, hle⟩ := integrableOn_Ioi_of_le (aestronglyMeasurable_openHeat_sub ω y y σ θ unitE)
    hT0 hb.hβ1 hsmall hlarge
  refine ⟨hint, (abs_integral_le_integral_abs).trans (hle.trans ?_)⟩
  have hpow : T₀ ^ (1 - β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hb.hT₀ (by linarith [hb.hβ1])
  have hβ' : 0 < β - 1 := by linarith [hb.hβ1]
  have : (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) * (T₀ ^ (1 - β) / (β - 1)) ≤
      (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) / (β - 1) := by
    rw [mul_div_assoc']
    gcongr
    calc (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) * T₀ ^ (1 - β)
        ≤ (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) * 1 := by gcongr
      _ = _ := mul_one _
  linarith

/-- **The time integral at large distance**: for `|x - y| ≥ T₀`,
`|∫_0^∞ (p(t, x, y) - θ^{-1} p̄(t, x - y)) dt| ≤ (2C₂³ + θ^{-1} + C₁^β Γ(β - 1)) |x - y|^{2-2β}`. -/
theorem abs_integral_sub_gaussian_le (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : Vertex 2}
    (hx : x ∈ K.supp) (hr : T₀ ≤ ‖edz x y‖) :
    |∫ t in Ioi (0 : ℝ), (openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y))| ≤
      (2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1)) * ‖edz x y‖ ^ (2 - 2 * β) := by
  set r := ‖edz x y‖ with hrdef
  have hr1 : 1 ≤ r := hb.hT₀.trans hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hσ := hb.hσ
  have hC₁ := hb.hC₁
  have hC₂ := hb.hC₂
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hβ1 := hb.hβ1
  set h : ℝ → ℝ := fun t => openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y) with hhdef
  set Bs : ℝ := C₂ * Real.exp (-(r / C₂)) + θ⁻¹ * (Real.exp (-(r / (4 * σ))) / r ^ 2) with hBs
  set a : ℝ := r ^ 2 / C₁ with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨hgint, hgval⟩ := integral_rpow_neg_mul_exp_neg_div hβ1 ha0
  have hsplit : Ioi (0 : ℝ) = Ioc 0 r ∪ Ioi r := (Ioc_union_Ioi_eq_Ioi hr0.le).symm
  have hm := aestronglyMeasurable_openHeat_sub ω x y σ θ (edz x y)
  have hsmall : ∀ t ∈ Ioc 0 r, |h t| ≤ Bs := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have h0 := openHeat_nonneg ω ht0.le x y
    have hcv := hb.cv x hx t ht0 ht.2
    have hg0 := gaussianHeat_nonneg hσ ht0.le (edz x y)
    have hg1 := gaussianHeat_le_of_le_norm hσ ht0 ht.2
    have hle : |h t| ≤ openHeat ω t x y + θ⁻¹ * gaussianHeat σ t (edz x y) := by
      rw [abs_le]
      constructor <;> nlinarith
    refine hle.trans (add_le_add hcv ?_)
    exact mul_le_mul_of_nonneg_left hg1 hθi.le
  have hlarge : ∀ t ∈ Ioi r, |h t| ≤ C₁ * (t ^ (-β) * Real.exp (-(a / t))) := by
    intro t ht
    have ht' : r < t := ht
    have hd := hb.thm1 x hx t (hr.trans ht'.le) ht'.le
    have : ‖edz x y‖ ^ 2 / (C₁ * t) = a / t := by rw [ha, hrdef, div_div]
    rw [this] at hd
    calc |h t| ≤ C₁ * t ^ (-β) * Real.exp (-(a / t)) := hd
      _ = _ := by ring
  have hI1 : IntegrableOn h (Ioc 0 r) := by
    refine Measure.integrableOn_of_bounded (M := Bs) measure_Ioc_lt_top.ne hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    exact hsmall t ht
  have hg0 : IntegrableOn (fun t => C₁ * (t ^ (-β) * Real.exp (-(a / t)))) (Ioi 0) :=
    Integrable.const_mul hgint C₁
  have hg2 : IntegrableOn (fun t => C₁ * (t ^ (-β) * Real.exp (-(a / t)))) (Ioi r) :=
    IntegrableOn.mono_set hg0 (Ioi_subset_Ioi hr0.le)
  have hI2 : IntegrableOn h (Ioi r) := by
    refine hg2.mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact hlarge t ht
  have hbound : ∫ t in Ioi (0 : ℝ), |h t| ≤ Bs * r + C₁ * (a ^ (1 - β) * Real.Gamma (β - 1)) := by
    rw [hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (Integrable.abs hI1)
      (Integrable.abs hI2)]
    have hb1 : ∫ t in Ioc 0 r, |h t| ≤ Bs * r := by
      calc ∫ t in Ioc 0 r, |h t| ≤ ∫ _t in Ioc 0 r, Bs :=
            setIntegral_mono_on (Integrable.abs hI1) (integrableOn_const measure_Ioc_lt_top.ne)
              measurableSet_Ioc hsmall
        _ = Bs * r := by
            rw [← intervalIntegral.integral_of_le hr0.le, intervalIntegral.integral_const,
              smul_eq_mul]
            ring
    have hb2 : ∫ t in Ioi r, |h t| ≤ C₁ * (a ^ (1 - β) * Real.Gamma (β - 1)) := by
      calc ∫ t in Ioi r, |h t| ≤ ∫ t in Ioi r, C₁ * (t ^ (-β) * Real.exp (-(a / t))) :=
            setIntegral_mono_on (Integrable.abs hI2) hg2 measurableSet_Ioi hlarge
        _ ≤ ∫ t in Ioi (0 : ℝ), C₁ * (t ^ (-β) * Real.exp (-(a / t))) := by
            refine setIntegral_mono_set hg0 ?_
              (Eventually.of_forall (Ioi_subset_Ioi hr0.le))
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht0 : (0 : ℝ) < t := ht
            have := Real.exp_pos (-(a / t))
            positivity
        _ = C₁ * (a ^ (1 - β) * Real.Gamma (β - 1)) := by rw [integral_const_mul, hgval]
    linarith
  -- algebra of the constants
  have hpow1 : r⁻¹ ≤ r ^ (2 - 2 * β) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by linarith [hb.hβ2])
  have hexp1 : C₂ * Real.exp (-(r / C₂)) * r ≤ 2 * C₂ ^ 3 * r⁻¹ := by
    have h := sq_mul_exp_neg_div_le hC₂ hr0.le
    rw [show C₂ * Real.exp (-(r / C₂)) * r = C₂ * (r ^ 2 * Real.exp (-(r / C₂))) * r⁻¹ by
      field_simp]
    calc C₂ * (r ^ 2 * Real.exp (-(r / C₂))) * r⁻¹ ≤ C₂ * (2 * C₂ ^ 2) * r⁻¹ := by gcongr
      _ = 2 * C₂ ^ 3 * r⁻¹ := by ring
  have hexp2 : θ⁻¹ * (Real.exp (-(r / (4 * σ))) / r ^ 2) * r ≤ θ⁻¹ * r⁻¹ := by
    have he : Real.exp (-(r / (4 * σ))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]; positivity
    rw [show θ⁻¹ * (Real.exp (-(r / (4 * σ))) / r ^ 2) * r = θ⁻¹ * Real.exp (-(r / (4 * σ))) * r⁻¹ by
      field_simp]
    calc θ⁻¹ * Real.exp (-(r / (4 * σ))) * r⁻¹ ≤ θ⁻¹ * 1 * r⁻¹ := by gcongr
      _ = θ⁻¹ * r⁻¹ := by ring
  have hgam : C₁ * (a ^ (1 - β) * Real.Gamma (β - 1)) =
      C₁ ^ β * Real.Gamma (β - 1) * r ^ (2 - 2 * β) := by
    rw [ha, Real.div_rpow (by positivity) hC₁.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hr0.le]
    have hC1 : C₁ / C₁ ^ (1 - β) = C₁ ^ β := by
      rw [← Real.rpow_one_sub' hC₁.le] <;> [ring_nf; skip]
      · linarith
    field_simp
    rw [show ((2 : ℕ) : ℝ) * (1 - β) = 2 - 2 * β by push_cast; ring]
    rw [← hC1]
    field_simp
  have hΓ : 0 ≤ Real.Gamma (β - 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc |∫ t in Ioi (0 : ℝ), h t| ≤ ∫ t in Ioi (0 : ℝ), |h t| := abs_integral_le_integral_abs
    _ ≤ Bs * r + C₁ * (a ^ (1 - β) * Real.Gamma (β - 1)) := hbound
    _ ≤ 2 * C₂ ^ 3 * r⁻¹ + θ⁻¹ * r⁻¹ + C₁ ^ β * Real.Gamma (β - 1) * r ^ (2 - 2 * β) := by
        rw [hBs, add_mul, hgam]
        linarith
    _ ≤ 2 * C₂ ^ 3 * r ^ (2 - 2 * β) + θ⁻¹ * r ^ (2 - 2 * β) +
          C₁ ^ β * Real.Gamma (β - 1) * r ^ (2 - 2 * β) := by
        gcongr
    _ = _ := by ring

/-- For `x ≠ y` in `K`, `t ↦ p(t, x, y) - p(t, y, y)` is integrable on `(0, ∞)` and its integral is
`∫ (p(t, x, y) - θ^{-1} p̄(t, x - y)) dt - log |x - y| / (π σ θ) - ∫ (p(t, y, y) - θ^{-1} p̄(t, e)) dt`. -/
theorem integral_sub_diag_eq (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : Vertex 2}
    (hx : x ∈ K.supp) (hxy : x ≠ y) :
    IntegrableOn (fun t => openHeat ω t x y - openHeat ω t y y) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (openHeat ω t x y - openHeat ω t y y) =
        (∫ t in Ioi (0 : ℝ), (openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y))) +
          θ⁻¹ * (-Real.log ‖edz x y‖ / (Real.pi * σ)) -
          ∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE) := by
  have hz : edz x y ≠ 0 := by
    intro h0
    have := one_le_norm_edz hxy
    rw [h0, norm_zero] at this
    linarith
  have h1 := hb.integrableOn_sub_gaussian hx hxy
  obtain ⟨h2, h2v⟩ := integral_gaussianHeat_sub hb.hσ hz norm_unitE
  have h3 := hb.integrableOn_diag.1
  have heq : (fun t => openHeat ω t x y - openHeat ω t y y) = fun t =>
      (openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y)) +
        θ⁻¹ * (gaussianHeat σ t (edz x y) - gaussianHeat σ t unitE) -
        (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE) := by
    funext t
    ring
  have hI2' : IntegrableOn (fun t => θ⁻¹ * (gaussianHeat σ t (edz x y) - gaussianHeat σ t unitE))
      (Ioi 0) := Integrable.const_mul h2 θ⁻¹
  have hI12 : IntegrableOn (fun t => (openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y)) +
      θ⁻¹ * (gaussianHeat σ t (edz x y) - gaussianHeat σ t unitE)) (Ioi 0) :=
    Integrable.add h1 hI2'
  have hI : IntegrableOn (fun t => (openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y)) +
      θ⁻¹ * (gaussianHeat σ t (edz x y) - gaussianHeat σ t unitE) -
      (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE)) (Ioi 0) :=
    Integrable.sub hI12 h3
  rw [heq]
  refine ⟨hI, ?_⟩
  rw [integral_sub hI12 h3, integral_add h1 hI2', integral_const_mul, h2v]

theorem integrableOn_sub_diag (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : Vertex 2}
    (hx : x ∈ K.supp) : IntegrableOn (fun t => openHeat ω t x y - openHeat ω t y y) (Ioi 0) := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self]
    exact integrableOn_zero
  · exact (hb.integral_sub_diag_eq hx hxy).1

/-- `p(t, x, y) → 0` as `t → ∞`. -/
theorem tendsto_openHeat (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : Vertex 2}
    (hx : x ∈ K.supp) : Tendsto (fun t => openHeat ω t x y) atTop (𝓝 0) := by
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hlim : Tendsto (fun t : ℝ => θ⁻¹ * gaussianHeat σ t (edz x y) + C₁ * t ^ (-β)) atTop
      (𝓝 0) := by
    have h1 := (tendsto_gaussianHeat_atTop hb.hσ (edz x y)).const_mul θ⁻¹
    have h2 := (tendsto_rpow_neg_atTop (by linarith [hb.hβ1] : 0 < β)).const_mul C₁
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact openHeat_nonneg ω ht x y
  · filter_upwards [eventually_ge_atTop (max T₀ ‖edz x y‖)] with t ht
    have ht1 : 1 ≤ t := hb.hT₀.trans ((le_max_left _ _).trans ht)
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have hd := hb.thm1 x hx t ((le_max_left _ _).trans ht) ((le_max_right _ _).trans ht)
    have he : Real.exp (-(‖edz x y‖ ^ 2 / (C₁ * t))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      have := hb.hC₁
      positivity
    have hp : 0 ≤ C₁ * t ^ (-β) := mul_nonneg hb.hC₁.le (Real.rpow_nonneg ht0.le _)
    have hd' : |openHeat ω t x y - θ⁻¹ * gaussianHeat σ t (edz x y)| ≤ C₁ * t ^ (-β) :=
      hd.trans (by calc C₁ * t ^ (-β) * Real.exp (-(‖edz x y‖ ^ 2 / (C₁ * t)))
          ≤ C₁ * t ^ (-β) * 1 := by gcongr
        _ = C₁ * t ^ (-β) := mul_one _)
    have := (abs_le.1 hd').2
    linarith

/-! ### The Green column -/

/-- The candidate Green column `G(x) = ∫_0^∞ (p(t, x, y) - p(t, y, y)) dt`. -/
noncomputable def timeGreen (ω : Configuration 2) (K : OpenComponent ω) (y : Vertex 2) (x : K) :
    ℝ :=
  ∫ t in Ioi (0 : ℝ), (openHeat ω t x.val y - openHeat ω t y y)

/-- Sums over the neighbours in the component graph are sums over the open neighbours. -/
theorem sum_componentNeighbor_eq (x : K) (F : Vertex 2 → ℝ) :
    ∑ z ∈ (componentGraph K).neighborFinset x, F z.val =
      ∑ w ∈ (openGraph ω).neighborFinset x.val, F w := by
  refine Finset.sum_bij (fun z _ => z.val) (fun z hz => ?_) (fun z₁ _ z₂ _ h => Subtype.ext h)
    (fun w hw => ?_) (fun z _ => rfl)
  · rw [SimpleGraph.mem_neighborFinset] at hz ⊢
    exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj K x.2 z.2).1 hz
  · rw [SimpleGraph.mem_neighborFinset] at hw
    have hwK : w ∈ K.supp := SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp K x.2 hw
    refine ⟨⟨w, hwK⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj K x.2 hwK).2 hw

/-- `-Δ G = δ_y` on `K`. -/
theorem laplacian_timeGreen (hb : HeatBounds K y σ θ C₁ C₂ β T₀) (x : K) :
    -componentLaplacian K (timeGreen ω K y) x = if x = ⟨y, hb.hy⟩ then 1 else 0 := by
  have hint : ∀ w ∈ K.supp, IntegrableOn (fun t => openHeat ω t w y - openHeat ω t y y) (Ioi 0) :=
    fun w hw => hb.integrableOn_sub_diag hw
  have hdiff : ∀ z : K, timeGreen ω K y z - timeGreen ω K y x =
      ∫ t in Ioi (0 : ℝ), (openHeat ω t z.val y - openHeat ω t x.val y) := by
    intro z
    rw [timeGreen, timeGreen, ← integral_sub (hint z.val z.2) (hint x.val x.2)]
    congr 1
    funext t
    ring
  have hsum : componentLaplacian K (timeGreen ω K y) x =
      ∫ t in Ioi (0 : ℝ), openLaplacian ω (fun w => openHeat ω t w y) x.val := by
    rw [componentLaplacian]
    simp_rw [hdiff]
    have hI : ∀ z : K, IntegrableOn (fun t => openHeat ω t z.val y - openHeat ω t x.val y)
        (Ioi 0) := fun z => by
      refine IntegrableOn.congr_fun (Integrable.sub (hint z.val z.2) (hint x.val x.2))
        (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      ring
    rw [← integral_finsetSum _ fun z _ => hI z]
    congr 1
    funext t
    rw [openLaplacian]
    exact sum_componentNeighbor_eq (K := K) x (fun w => openHeat ω t w y - openHeat ω t x.val y)
  have hf'int : IntegrableOn (fun t => openLaplacian ω (fun w => openHeat ω t w y) x.val)
      (Ioi 0) := by
    have : (fun t => openLaplacian ω (fun w => openHeat ω t w y) x.val) = fun t =>
        ∑ z ∈ (componentGraph K).neighborFinset x,
          ((openHeat ω t z.val y - openHeat ω t y y) - (openHeat ω t x.val y - openHeat ω t y y)) := by
      funext t
      rw [openLaplacian, ← sum_componentNeighbor_eq (K := K) x]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this]
    exact integrable_finsetSum _ fun z _ => Integrable.sub (hint z.val z.2) (hint x.val x.2)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    ((continuous_openHeat ω x.val y).continuousWithinAt)
    (fun t _ => hasDerivAt_openHeat ω t x.val y) hf'int (hb.tendsto_openHeat x.2)
  rw [hsum, hftc, openHeat_zero]
  have hiff : (x = ⟨y, hb.hy⟩) ↔ x.val = y := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : x.val = y
  · rw [if_pos h, if_pos (hiff.2 h)]; ring
  · rw [if_neg h, if_neg (mt hiff.1 h)]; ring

end HeatBounds

end Rigidity.Green
