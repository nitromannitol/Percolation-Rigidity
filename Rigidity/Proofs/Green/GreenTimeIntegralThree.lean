import Rigidity.Proofs.Green.GaussianTimeIntegral
import Rigidity.Proofs.Green.HeatTimeIntegrals

/-!
# The Green function as a time integral of the heat kernel for `d ≥ 3` (deterministic part)

Dario–Gu, §5, for `d ≥ 3`: on an infinite open component `K ∋ y` of `ℤ^d`, let the heat kernel
`p(t, x, y)` of the variable speed random walk on the open graph (`openHeatD`) satisfy the bound
of Theorem 1, `|p(t, x, y) - θ^{-1} p̄(t, x - y)| ≤ C₁ t^{-β} e^{-|x-y|²/(C₁ t)}` for
`t ≥ max(T₀, |x - y|)`, with `d/2 < β ≤ (d+1)/2`, and the Carne–Varopoulos bound
`p(t, x, y) ≤ C₂ e^{-|x-y|/C₂}` for `t ≤ |x - y|` (`HeatBoundsD`). Then

* `G(x) = ∫_0^∞ p(t, x, y) dt` converges (`integrableOn_openHeatD`) and solves `-Δ G = δ_y`
  (`laplacian_timeGreenD`);
* for `|x - y| ≥ T₀`,
  `|G(x) - θ^{-1} ∫_0^∞ p̄(t, x - y) dt| ≤ C |x - y|^{2 - 2β}` (`abs_timeGreenD_sub_le`), splitting the
  time integral at `|x - y|`, as in the proof of the source;
* `G` tends to zero at infinity (`tendsto_timeGreenD`), so that it is a Green column
  (`isGreenColumn_timeGreenD`).
-/

open MeasureTheory Set Real Filter Topology LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- The heat kernel of the variable speed random walk on the open graph of `ℤ^d`. -/
noncomputable def openHeatD (ω : Configuration d) (t : ℝ) (x y : Vertex d) : ℝ :=
  vsrwHeat (openGraph ω) (2 * d) t x y

/-- The displacement `x - y` in `ℝ^d`. -/
abbrev edzD (x y : Vertex d) : EuclideanSpace ℝ (Fin d) :=
  latticeEuclideanEmbedding x - latticeEuclideanEmbedding y

section Basic

variable [NeZero d]

theorem two_mul_dim_pos : 0 < 2 * d := by
  have := NeZero.pos d
  omega

theorem openHeatD_nonneg (ω : Configuration d) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) :
    0 ≤ openHeatD ω t x y :=
  vsrwHeat_nonneg two_mul_dim_pos (openGraph_degree_le ω) ht x y

theorem openHeatD_le_one (ω : Configuration d) {t : ℝ} (ht : 0 ≤ t) (x y : Vertex d) :
    openHeatD ω t x y ≤ 1 :=
  vsrwHeat_le_one two_mul_dim_pos (openGraph_degree_le ω) ht x y

theorem hasDerivAt_openHeatD (ω : Configuration d) (t : ℝ) (x y : Vertex d) :
    HasDerivAt (fun t => openHeatD ω t x y)
      (openLaplacian ω (fun w => openHeatD ω t w y) x) t :=
  hasDerivAt_vsrwHeat two_mul_dim_pos (openGraph_degree_le ω) t x y

theorem continuous_openHeatD (ω : Configuration d) (x y : Vertex d) :
    Continuous fun t => openHeatD ω t x y :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_openHeatD ω t x y).continuousAt

omit [NeZero d] in
theorem openHeatD_zero (ω : Configuration d) (x y : Vertex d) :
    openHeatD ω 0 x y = if x = y then 1 else 0 :=
  (vsrwHeat_zero (G := openGraph ω) (D := 2 * d) x y).trans (by by_cases hxy : x = y <;> simp [hxy])

end Basic

theorem gaussianHeatD_nonneg {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (z : EuclideanSpace ℝ (Fin d)) :
    0 ≤ gaussianHeatD d σ t z := by
  unfold gaussianHeatD
  exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * σ) ht) _)
    (Real.exp_pos _).le

theorem gaussianHeatD_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (z : EuclideanSpace ℝ (Fin d)) :
    gaussianHeatD d σ t z ≤ (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * t ^ (-((d : ℝ) / 2)) := by
  rw [gaussianHeatD_eq hσ ht z, ← mul_assoc]
  apply mul_le_of_le_one_right (by positivity)
  rw [Real.exp_le_one_iff, neg_nonpos]
  positivity

theorem integrableOn_gaussianHeatD {d : ℕ} (hd : 3 ≤ d) {σ : ℝ} (hσ : 0 < σ)
    {z : EuclideanSpace ℝ (Fin d)} (hz : z ≠ 0) :
    IntegrableOn (fun t => gaussianHeatD d σ t z) (Ioi 0) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hb : 0 < ‖z‖ ^ 2 / (2 * σ) := by positivity
  obtain ⟨h0, -⟩ := integral_rpow_neg_mul_exp_neg_div (β := (d : ℝ) / 2) (by linarith) hb
  have h : IntegrableOn (fun t => (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) *
      (t ^ (-((d : ℝ) / 2)) * Real.exp (-((‖z‖ ^ 2 / (2 * σ)) / t)))) (Ioi 0) :=
    h0.const_mul ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)))
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  exact (gaussianHeatD_eq hσ ht z).symm

/-! ### The hypotheses -/

/-- The hypotheses of the deterministic part of Dario–Gu, §5, for `d ≥ 3`, at one configuration. -/
structure HeatBoundsD {ω : Configuration d} (K : OpenComponent ω) (y : Vertex d)
    (σ θ C₁ C₂ β T₀ : ℝ) : Prop where
  hd : 3 ≤ d
  hσ : 0 < σ
  hθ : 0 < θ
  hC₁ : 0 < C₁
  hC₂ : 0 < C₂
  hβ1 : (d : ℝ) / 2 < β
  hβ2 : β ≤ (d : ℝ) / 2 + 1 / 2
  hT₀ : 1 ≤ T₀
  hy : y ∈ K.supp
  thm1 : ∀ x ∈ K.supp, ∀ t : ℝ, T₀ ≤ t → ‖edzD x y‖ ≤ t →
    |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
      C₁ * t ^ (-β) * Real.exp (-(‖edzD x y‖ ^ 2 / (C₁ * t)))
  cv : ∀ x ∈ K.supp, ∀ t : ℝ, 0 < t → t ≤ ‖edzD x y‖ →
    openHeatD ω t x y ≤ C₂ * Real.exp (-(‖edzD x y‖ / C₂))

/-- `r^n e^{-r/C} ≤ n! C^n` for `C > 0`, `r ≥ 0`. -/
theorem pow_mul_exp_neg_div_le {C r : ℝ} (hC : 0 < C) (hr : 0 ≤ r) (n : ℕ) :
    r ^ n * Real.exp (-(r / C)) ≤ n.factorial * C ^ n := by
  have h := Real.pow_div_factorial_le_exp _ (div_nonneg hr hC.le) n
  have hpos := Real.exp_pos (r / C)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
  nlinarith [h]

namespace HeatBoundsD

variable [NeZero d] {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d}
  {σ θ C₁ C₂ β T₀ : ℝ}

omit [NeZero d] in
theorem one_lt_half_dim (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) : 1 < (d : ℝ) / 2 := by
  have : (3 : ℝ) ≤ d := by exact_mod_cast hb.hd
  linarith

omit [NeZero d] in
/-- The bound `p(t, x, y) ≤ (θ^{-1} (2πσ)^{-d/2} + C₁) t^{-d/2}` at large times. -/
theorem openHeatD_le_large (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {x : Vertex d}
    (hx : x ∈ K.supp) {t : ℝ} (ht : max T₀ ‖edzD x y‖ ≤ t) :
    openHeatD ω t x y ≤
      (θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) + C₁) * t ^ (-((d : ℝ) / 2)) := by
  have ht1 : 1 ≤ t := hb.hT₀.trans ((le_max_left _ _).trans ht)
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
  have hd := hb.thm1 x hx t ((le_max_left _ _).trans ht) ((le_max_right _ _).trans ht)
  have he : Real.exp (-(‖edzD x y‖ ^ 2 / (C₁ * t))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    have := hb.hC₁
    positivity
  have hpow : t ^ (-β) ≤ t ^ (-((d : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by linarith [hb.hβ1])
  have hg := gaussianHeatD_le hb.hσ ht0 (edzD x y)
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have h1 := (abs_le.1 hd).2
  have h2 : C₁ * t ^ (-β) * Real.exp (-(‖edzD x y‖ ^ 2 / (C₁ * t))) ≤
      C₁ * t ^ (-((d : ℝ) / 2)) := by
    calc C₁ * t ^ (-β) * Real.exp (-(‖edzD x y‖ ^ 2 / (C₁ * t))) ≤ C₁ * t ^ (-β) * 1 :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hb.hC₁.le (Real.rpow_nonneg ht0.le _))
      _ ≤ C₁ * t ^ (-((d : ℝ) / 2)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hpow hb.hC₁.le
  have h3 : θ⁻¹ * gaussianHeatD d σ t (edzD x y) ≤
      θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * t ^ (-((d : ℝ) / 2))) :=
    mul_le_mul_of_nonneg_left hg hθi.le
  nlinarith

/-- `t ↦ p(t, x, y)` is integrable on `(0, ∞)`. -/
theorem integrableOn_openHeatD (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {x : Vertex d}
    (hx : x ∈ K.supp) : IntegrableOn (fun t => openHeatD ω t x y) (Ioi 0) := by
  have hS : 0 < max T₀ ‖edzD x y‖ := lt_of_lt_of_le one_pos (hb.hT₀.trans (le_max_left _ _))
  refine (integrableOn_Ioi_of_le (continuous_openHeatD ω x y).aestronglyMeasurable hS
    hb.one_lt_half_dim (B := 1) (A := θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) + C₁)
    (fun t ht => ?_) (fun t ht => ?_)).1
  · rw [abs_of_nonneg (openHeatD_nonneg ω ht.1.le x y)]
    exact openHeatD_le_one ω ht.1.le x y
  · have ht' : max T₀ ‖edzD x y‖ ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_of_lt_of_le hS ht'
    rw [abs_of_nonneg (openHeatD_nonneg ω ht0.le x y)]
    exact hb.openHeatD_le_large hx ht'

/-- `p(t, x, y) → 0` as `t → ∞`. -/
theorem tendsto_openHeatD (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {x : Vertex d}
    (hx : x ∈ K.supp) : Tendsto (fun t => openHeatD ω t x y) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ =>
      (θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) + C₁) * t ^ (-((d : ℝ) / 2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith [hb.one_lt_half_dim] : 0 < (d : ℝ) / 2)).const_mul
      (θ⁻¹ * (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) + C₁)
    simpa using h
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact openHeatD_nonneg ω ht x y
  · filter_upwards [eventually_ge_atTop (max T₀ ‖edzD x y‖)] with t ht
    exact hb.openHeatD_le_large hx ht

end HeatBoundsD

/-! ### The Green column -/

/-- The candidate Green column `G(x) = ∫_0^∞ p(t, x, y) dt`. -/
noncomputable def timeGreenD (ω : Configuration d) (K : OpenComponent ω) (y : Vertex d) (x : K) :
    ℝ :=
  ∫ t in Ioi (0 : ℝ), openHeatD ω t x.val y

/-- Sums over the neighbours in the component graph are sums over the open neighbours. -/
theorem sum_componentNeighbor_eq_open {ω : Configuration d} {K : OpenComponent ω} (x : K)
    (F : Vertex d → ℝ) :
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

namespace HeatBoundsD

variable [NeZero d] {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d}
  {σ θ C₁ C₂ β T₀ : ℝ}

/-- `-Δ G = δ_y` on `K`. -/
theorem laplacian_timeGreenD (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) (x : K) :
    -componentLaplacian K (timeGreenD ω K y) x = if x = ⟨y, hb.hy⟩ then 1 else 0 := by
  have hint : ∀ w ∈ K.supp, IntegrableOn (fun t => openHeatD ω t w y) (Ioi 0) :=
    fun w hw => hb.integrableOn_openHeatD hw
  have hdiff : ∀ z : K, timeGreenD ω K y z - timeGreenD ω K y x =
      ∫ t in Ioi (0 : ℝ), (openHeatD ω t z.val y - openHeatD ω t x.val y) := by
    intro z
    rw [timeGreenD, timeGreenD, ← integral_sub (hint z.val z.2) (hint x.val x.2)]
  have hsum : componentLaplacian K (timeGreenD ω K y) x =
      ∫ t in Ioi (0 : ℝ), openLaplacian ω (fun w => openHeatD ω t w y) x.val := by
    rw [componentLaplacian]
    simp_rw [hdiff]
    have hI : ∀ z : K, IntegrableOn (fun t => openHeatD ω t z.val y - openHeatD ω t x.val y)
        (Ioi 0) := fun z => Integrable.sub (hint z.val z.2) (hint x.val x.2)
    rw [← integral_finsetSum _ fun z _ => hI z]
    congr 1
    funext t
    rw [openLaplacian]
    exact sum_componentNeighbor_eq_open (K := K) x
      (fun w => openHeatD ω t w y - openHeatD ω t x.val y)
  have hf'int : IntegrableOn (fun t => openLaplacian ω (fun w => openHeatD ω t w y) x.val)
      (Ioi 0) := by
    have : (fun t => openLaplacian ω (fun w => openHeatD ω t w y) x.val) = fun t =>
        ∑ z ∈ (componentGraph K).neighborFinset x,
          (openHeatD ω t z.val y - openHeatD ω t x.val y) := by
      funext t
      rw [openLaplacian, ← sum_componentNeighbor_eq_open (K := K) x]
    rw [this]
    exact integrable_finsetSum _ fun z _ => Integrable.sub (hint z.val z.2) (hint x.val x.2)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto
    ((continuous_openHeatD ω x.val y).continuousWithinAt)
    (fun t _ => hasDerivAt_openHeatD ω t x.val y) hf'int (hb.tendsto_openHeatD x.2)
  rw [hsum, hftc, openHeatD_zero]
  have hiff : (x = ⟨y, hb.hy⟩) ↔ x.val = y := ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  by_cases h : x.val = y
  · rw [if_pos h, if_pos (hiff.2 h)]; ring
  · rw [if_neg h, if_neg (mt hiff.1 h)]; ring

end HeatBoundsD

/-! ### The comparison with the homogenized Green function -/

namespace HeatBoundsD

variable [NeZero d] {ω : Configuration d} {K : OpenComponent ω} {y : Vertex d}
  {σ θ C₁ C₂ β T₀ : ℝ}

omit [NeZero d] in
/-- Small times for the Gaussian kernel: `∫_0^r p̄(t, z) dt ≤ (2πσ)^{-d/2} e^{-r/(4σ)}
(r²/(4σ))^{1-d/2} Γ(d/2 - 1)` for `|z| = r`. -/
theorem setIntegral_gaussianHeatD_Ioc_le (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀)
    {z : EuclideanSpace ℝ (Fin d)} (hz : z ≠ 0) :
    ∫ t in Ioc 0 ‖z‖, gaussianHeatD d σ t z ≤
      (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖z‖ / (4 * σ))) *
        ((‖z‖ ^ 2 / (4 * σ)) ^ (1 - (d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2 - 1)) := by
  have hσ := hb.hσ
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have ha : 0 < ‖z‖ ^ 2 / (4 * σ) := by positivity
  obtain ⟨hgint, hgval⟩ := integral_rpow_neg_mul_exp_neg_div hb.one_lt_half_dim ha
  set c := (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖z‖ / (4 * σ))) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ t ∈ Ioc 0 ‖z‖, gaussianHeatD d σ t z ≤
      c * (t ^ (-((d : ℝ) / 2)) * Real.exp (-((‖z‖ ^ 2 / (4 * σ)) / t))) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [gaussianHeatD_eq hσ ht0 z, hc]
    have hexp : Real.exp (-((‖z‖ ^ 2 / (2 * σ)) / t)) ≤
        Real.exp (-(‖z‖ / (4 * σ))) * Real.exp (-((‖z‖ ^ 2 / (4 * σ)) / t)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : ‖z‖ / (4 * σ) ≤ (‖z‖ ^ 2 / (4 * σ)) / t := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left ht.2 (by positivity : (0 : ℝ) ≤ ‖z‖ * (4 * σ))
        nlinarith
      have h2 : (‖z‖ ^ 2 / (2 * σ)) / t = (‖z‖ ^ 2 / (4 * σ)) / t + (‖z‖ ^ 2 / (4 * σ)) / t := by
        field_simp; ring
      rw [h2]
      linarith
    have hp : 0 ≤ (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) := by positivity
    have hq : 0 ≤ t ^ (-((d : ℝ) / 2)) := Real.rpow_nonneg ht0.le _
    calc (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) *
          (t ^ (-((d : ℝ) / 2)) * Real.exp (-((‖z‖ ^ 2 / (2 * σ)) / t)))
        ≤ (2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * (t ^ (-((d : ℝ) / 2)) *
            (Real.exp (-(‖z‖ / (4 * σ))) * Real.exp (-((‖z‖ ^ 2 / (4 * σ)) / t)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hq) hp
      _ = _ := by ring
  have hgc : IntegrableOn (fun t => c * (t ^ (-((d : ℝ) / 2)) *
      Real.exp (-((‖z‖ ^ 2 / (4 * σ)) / t)))) (Ioi 0) := hgint.const_mul c
  have hbint : IntegrableOn (fun t => gaussianHeatD d σ t z) (Ioc 0 ‖z‖) :=
    (integrableOn_gaussianHeatD hb.hd hσ hz).mono_set Ioc_subset_Ioi_self
  calc ∫ t in Ioc 0 ‖z‖, gaussianHeatD d σ t z
      ≤ ∫ t in Ioc 0 ‖z‖, c * (t ^ (-((d : ℝ) / 2)) * Real.exp (-((‖z‖ ^ 2 / (4 * σ)) / t))) :=
        setIntegral_mono_on hbint (hgc.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
    _ ≤ ∫ t in Ioi 0, c * (t ^ (-((d : ℝ) / 2)) * Real.exp (-((‖z‖ ^ 2 / (4 * σ)) / t))) := by
        refine setIntegral_mono_set hgc ?_ (Eventually.of_forall Ioc_subset_Ioi_self)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := ht
        have := Real.rpow_nonneg ht0.le (-((d : ℝ) / 2))
        positivity
    _ = c * ((‖z‖ ^ 2 / (4 * σ)) ^ (1 - (d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2 - 1)) := by
        rw [integral_const_mul, hgval]

omit [NeZero d] in
/-- Large times: `∫_r^∞ |p(t, x, y) - θ^{-1} p̄(t, x - y)| dt ≤ C₁ (r²/C₁)^{1-β} Γ(β - 1)`. -/
theorem setIntegral_abs_sub_Ioi_le (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {x : Vertex d}
    (hx : x ∈ K.supp) (hr : T₀ ≤ ‖edzD x y‖)
    (hint : IntegrableOn (fun t => |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)|)
      (Ioi ‖edzD x y‖)) :
    ∫ t in Ioi ‖edzD x y‖, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
      C₁ * ((‖edzD x y‖ ^ 2 / C₁) ^ (1 - β) * Real.Gamma (β - 1)) := by
  have hr0 : 0 < ‖edzD x y‖ := lt_of_lt_of_le one_pos (hb.hT₀.trans hr)
  have hC₁ := hb.hC₁
  have ha : 0 < ‖edzD x y‖ ^ 2 / C₁ := by positivity
  obtain ⟨hgint, hgval⟩ := integral_rpow_neg_mul_exp_neg_div
    (lt_trans hb.one_lt_half_dim hb.hβ1) ha
  have hg0 : IntegrableOn (fun t => C₁ * (t ^ (-β) * Real.exp (-((‖edzD x y‖ ^ 2 / C₁) / t))))
      (Ioi 0) := hgint.const_mul C₁
  have hlarge : ∀ t ∈ Ioi ‖edzD x y‖,
      |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
        C₁ * (t ^ (-β) * Real.exp (-((‖edzD x y‖ ^ 2 / C₁) / t))) := by
    intro t ht
    have ht' : ‖edzD x y‖ < t := ht
    have hd := hb.thm1 x hx t (hr.trans ht'.le) ht'.le
    have e : ‖edzD x y‖ ^ 2 / (C₁ * t) = (‖edzD x y‖ ^ 2 / C₁) / t := by rw [div_div]
    rw [e] at hd
    calc _ ≤ C₁ * t ^ (-β) * Real.exp (-((‖edzD x y‖ ^ 2 / C₁) / t)) := hd
      _ = _ := by ring
  calc ∫ t in Ioi ‖edzD x y‖, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)|
      ≤ ∫ t in Ioi ‖edzD x y‖, C₁ * (t ^ (-β) * Real.exp (-((‖edzD x y‖ ^ 2 / C₁) / t))) :=
        setIntegral_mono_on hint (hg0.mono_set (Ioi_subset_Ioi hr0.le)) measurableSet_Ioi hlarge
    _ ≤ ∫ t in Ioi 0, C₁ * (t ^ (-β) * Real.exp (-((‖edzD x y‖ ^ 2 / C₁) / t))) := by
        refine setIntegral_mono_set hg0 ?_ (Eventually.of_forall (Ioi_subset_Ioi hr0.le))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0 : ℝ) < t := ht
        have := Real.rpow_nonneg ht0.le (-β)
        positivity
    _ = C₁ * ((‖edzD x y‖ ^ 2 / C₁) ^ (1 - β) * Real.Gamma (β - 1)) := by
        rw [integral_const_mul, hgval]

/-- The raw comparison: for `x ≠ y` with `|x - y| = r ≥ T₀`,
`|G(x) - θ^{-1} ∫ p̄| ≤ C₂ e^{-r/C₂} r + θ^{-1} (small Gaussian part) + (large times)`. -/
theorem abs_timeGreenD_sub_le_raw (hb : HeatBoundsD K y σ θ C₁ C₂ β T₀) {x : Vertex d}
    (hx : x ∈ K.supp) (hr : T₀ ≤ ‖edzD x y‖) :
    |timeGreenD ω K y ⟨x, hx⟩ - θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x y)| ≤
      C₂ * Real.exp (-(‖edzD x y‖ / C₂)) * ‖edzD x y‖ +
        θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖edzD x y‖ / (4 * σ))) *
          ((‖edzD x y‖ ^ 2 / (4 * σ)) ^ (1 - (d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2 - 1))) +
        C₁ * ((‖edzD x y‖ ^ 2 / C₁) ^ (1 - β) * Real.Gamma (β - 1)) := by
  set r := ‖edzD x y‖ with hrdef
  have hr1 : 1 ≤ r := hb.hT₀.trans hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hz : edzD x y ≠ 0 := norm_pos_iff.1 hr0
  have hθi : 0 < θ⁻¹ := inv_pos.2 hb.hθ
  have hp := hb.integrableOn_openHeatD hx
  have hg := integrableOn_gaussianHeatD hb.hd hb.hσ hz
  have hgθ : IntegrableOn (fun t => θ⁻¹ * gaussianHeatD d σ t (edzD x y)) (Ioi 0) :=
    hg.const_mul θ⁻¹
  have hdiff : IntegrableOn (fun t => openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y))
      (Ioi 0) := hp.sub hgθ
  have heq : timeGreenD ω K y ⟨x, hx⟩ - θ⁻¹ * ∫ t in Ioi (0 : ℝ), gaussianHeatD d σ t (edzD x y) =
      ∫ t in Ioi (0 : ℝ), (openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)) := by
    rw [integral_sub hp hgθ, integral_const_mul]
    rfl
  rw [heq]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 r ∪ Ioi r := (Ioc_union_Ioi_eq_Ioi hr0.le).symm
  have habs := hdiff.abs
  have hA := IntegrableOn.mono_set habs (Ioc_subset_Ioi_self : Ioc 0 r ⊆ Ioi 0)
  have hB := IntegrableOn.mono_set habs (Ioi_subset_Ioi hr0.le : Ioi r ⊆ Ioi 0)
  have hsmall : ∫ t in Ioc 0 r, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
      C₂ * Real.exp (-(r / C₂)) * r +
        θ⁻¹ * ((2 * Real.pi * σ) ^ (-((d : ℝ) / 2)) * Real.exp (-(r / (4 * σ))) *
          ((r ^ 2 / (4 * σ)) ^ (1 - (d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2 - 1))) := by
    have hpt : ∀ t ∈ Ioc 0 r, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| ≤
        C₂ * Real.exp (-(r / C₂)) + θ⁻¹ * gaussianHeatD d σ t (edzD x y) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have h0 := openHeatD_nonneg ω ht0.le x y
      have hcv := hb.cv x hx t ht0 ht.2
      have hg0 := gaussianHeatD_nonneg (d := d) hb.hσ ht0.le (edzD x y)
      rw [abs_le]
      constructor <;> nlinarith
    have hc : IntegrableOn (fun _ : ℝ => C₂ * Real.exp (-(r / C₂))) (Ioc 0 r) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hgr : IntegrableOn (fun t => θ⁻¹ * gaussianHeatD d σ t (edzD x y)) (Ioc 0 r) :=
      hgθ.mono_set Ioc_subset_Ioi_self
    have hR : IntegrableOn (fun t => C₂ * Real.exp (-(r / C₂)) +
        θ⁻¹ * gaussianHeatD d σ t (edzD x y)) (Ioc 0 r) := Integrable.add hc hgr
    calc ∫ t in Ioc 0 r, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)|
        ≤ ∫ t in Ioc 0 r, (C₂ * Real.exp (-(r / C₂)) + θ⁻¹ * gaussianHeatD d σ t (edzD x y)) :=
          setIntegral_mono_on hA hR measurableSet_Ioc hpt
      _ = C₂ * Real.exp (-(r / C₂)) * r +
            θ⁻¹ * ∫ t in Ioc 0 r, gaussianHeatD d σ t (edzD x y) := by
          rw [integral_add hc hgr,
            integral_const_mul θ⁻¹ (fun t => gaussianHeatD d σ t (edzD x y))]
          congr 1
          rw [← intervalIntegral.integral_of_le hr0.le, intervalIntegral.integral_const,
            smul_eq_mul]
          ring
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hθi.le)
          exact hb.setIntegral_gaussianHeatD_Ioc_le hz
  have hlarge := hb.setIntegral_abs_sub_Ioi_le hx hr hB
  calc |∫ t in Ioi (0 : ℝ), (openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y))|
      ≤ ∫ t in Ioi (0 : ℝ), |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| :=
        abs_integral_le_integral_abs
    _ = (∫ t in Ioc 0 r, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)|) +
          ∫ t in Ioi r, |openHeatD ω t x y - θ⁻¹ * gaussianHeatD d σ t (edzD x y)| := by
        rw [hsplit, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hA hB]
    _ ≤ _ := add_le_add hsmall hlarge

end HeatBoundsD

end Rigidity.Green
