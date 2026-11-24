import Rigidity.Proofs.Green.PlanarGreenDeterministic
import Rigidity.Proofs.Partition.Uniqueness
import PercolationClusterHomogenization.Proofs.Percolation.SupercriticalUniqueness
import Rigidity.Proofs.Green.PlanarGreenColumnCorrector

/-!
# Dario–Gu, Theorem 2, in dimension two, from Theorem 1

`supercriticalBondGreenQuantitativeTwo_of_smallTime` proves the planar quantitative Green function
input `SupercriticalBondGreenQuantitativeTwo` (Dario–Gu, Theorem 2, (1.11)) from

* Theorem 1 of Dario–Gu in dimension two (`DarioGuHeatKernelTwo`),
* the small-time bound `p(t, x, y) ≤ C e^{-|x - y|/C}` for `t ≤ |x - y|` (`HeatSmallTimeTwo`), which
  the source takes from the Carne–Varopoulos bound (`CarneVaropoulosTwo`, Dario–Gu,
  Proposition 2.15) and which is proved in `Rigidity.Proofs.Green.LazyCarneVaropoulos`, and
* the Liouville theorem at order zero (`SublinearLiouville p`, a consequence of the qualitative
  corrector input or of the order-zero regularity input), which identifies every Green column with
  the time integral of the heat kernel.

The proof is that of Dario–Gu, §5: with `κ = σ̄ θ(p)/2`, `ḡ = continuumGreen 2 κ` is
`-log |z| / (π σ̄ θ(p))`; the constant is `K(y) = -∫_0^∞ (p(t, y, y) - θ^{-1} p̄(t, e)) dt` on
`{y ∈ 𝒞_∞}` and `0` elsewhere, and the minimal scale is `max(T_par,δ'(y), 1)` with
`δ' = min(δ, 1/2)/2`. Their tails are stretched exponential since
`|K(y)| ≤ (1 + θ^{-1}) max(T_par, 1) + C`.
-/

open MeasureTheory Set Real Filter Topology LatticeProb.Percolation

namespace Rigidity.Green

/-! ### Tails -/

/-- The constant of `measure_le_affine_le`. -/
noncomputable def affineTailConst (C s A B : ℝ) : ℝ :=
  max (C * (2 * A) ^ s) (max C (max 2 (2 * (2 * (A + B)) ^ s)))

theorem affineTailConst_pos {C s A B : ℝ} : 0 < affineTailConst C s A B :=
  lt_of_lt_of_le two_pos ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem mul_exp_neg_div_mono {C C' x : ℝ} (hC : 0 < C) (hCC' : C ≤ C') (hx : 0 ≤ x) :
    C * Real.exp (-x / C) ≤ C' * Real.exp (-x / C') := by
  have hC' : 0 < C' := lt_of_lt_of_le hC hCC'
  refine mul_le_mul hCC' (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC'.le
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hx hC hCC'

/-- If `T` has the tail `P[T ≥ R] ≤ C e^{-R^s/C}` and almost surely `X ≤ A max(T, 1) + B`
(`A ≥ 1`, `B ≥ 0`), then `X` has the tail `P[X ≥ R] ≤ C' e^{-R^s/C'}`,
`C' = affineTailConst C s A B`. -/
theorem measure_le_affine_le {p : unitInterval} {T X : Configuration 2 → ℝ} {C s A B : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (htail : ∀ R : ℝ, 0 ≤ R →
      latticeBondLaw 2 p {ω | R ≤ T ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C)))
    (hX : ∀ᵐ ω ∂latticeBondLaw 2 p, X ω ≤ A * max (T ω) 1 + B) (R : ℝ) (hR : 0 ≤ R) :
    latticeBondLaw 2 p {ω | R ≤ X ω} ≤
      ENNReal.ofReal (affineTailConst C s A B * Real.exp (-Real.rpow R s / affineTailConst C s A B)) := by
  set C' := affineTailConst C s A B with hC'def
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA
  have hRs : 0 ≤ Real.rpow R s := Real.rpow_nonneg hR s
  by_cases hbig : 2 * (A + B) < R
  · have hsub : {ω | R ≤ X ω} ≤ᵐ[latticeBondLaw 2 p] {ω | R / (2 * A) ≤ T ω} := by
      filter_upwards [hX] with ω hω hR'
      have hR' : R ≤ X ω := hR'
      have h1 : 1 < R / (2 * A) := by
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have h2 : R / (2 * A) ≤ max (T ω) 1 := by
        rw [div_le_iff₀ (by positivity)]
        have : R - B ≤ A * max (T ω) 1 := by linarith
        nlinarith [le_max_right (T ω) 1]
      change R / (2 * A) ≤ T ω
      rcases le_total (T ω) 1 with hT1 | hT1
      · rw [max_eq_right hT1] at h2
        linarith
      · rwa [max_eq_left hT1] at h2
    refine (measure_mono_ae hsub).trans ((htail _ (by positivity)).trans
      (ENNReal.ofReal_le_ofReal ?_))
    have hpow : Real.rpow (R / (2 * A)) s = Real.rpow R s / (2 * A) ^ s :=
      Real.div_rpow hR (by positivity) s
    rw [hpow, show -(Real.rpow R s / (2 * A) ^ s) / C = -Real.rpow R s / (C * (2 * A) ^ s) by ring]
    have hCs : 0 < C * (2 * A) ^ s := by positivity
    have hle : C * (2 * A) ^ s ≤ C' := le_max_left _ _
    have hmono := mul_exp_neg_div_mono (x := Real.rpow R s) hCs hle hRs
    have h2A : 1 ≤ (2 * A) ^ s := Real.one_le_rpow (by linarith) hs.le
    calc C * Real.exp (-Real.rpow R s / (C * (2 * A) ^ s))
        ≤ C * (2 * A) ^ s * Real.exp (-Real.rpow R s / (C * (2 * A) ^ s)) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le h2A) (Real.exp_pos _).le
      _ ≤ C' * Real.exp (-Real.rpow R s / C') := hmono
  · have hbig' : R ≤ 2 * (A + B) := not_lt.1 hbig
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hC'2 : 2 ≤ C' := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hC'pos : 0 < C' := lt_of_lt_of_le two_pos hC'2
    have hRs' : Real.rpow R s ≤ (2 * (A + B)) ^ s := Real.rpow_le_rpow hR hbig' hs.le
    have hC'3 : 2 * (2 * (A + B)) ^ s ≤ C' :=
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hfrac : Real.rpow R s / C' ≤ 1 / 2 := by
      rw [div_le_iff₀ hC'pos]
      linarith
    have he : 1 / 2 ≤ Real.exp (-Real.rpow R s / C') := by
      have := Real.add_one_le_exp (-Real.rpow R s / C')
      rw [neg_div] at this ⊢
      linarith
    nlinarith

/-! ### The constant `K(y)` -/

/-- `K(y) = -∫_0^∞ (p(t, y, y) - θ^{-1} p̄(t, e)) dt` on `{y ∈ 𝒞_∞}`, and `0` elsewhere. -/
noncomputable def greenConstant (σ θ : ℝ) (y : Vertex 2) (ω : Configuration 2) : ℝ :=
  (infiniteComponentEvent y).indicator
    (fun ω => -∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE)) ω

theorem measurable_greenConstant (σ θ : ℝ) (y : Vertex 2) : Measurable (greenConstant σ θ y) := by
  have hF : Measurable fun q : Configuration 2 × ℝ =>
      openHeat q.1 q.2 y y - θ⁻¹ * gaussianHeat σ q.2 unitE :=
    (measurable_openHeat y y).sub
      (measurable_const.mul ((measurable_gaussianHeat_time σ unitE).comp measurable_snd))
  have hI : Measurable fun ω : Configuration 2 =>
      ∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE) :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  exact hI.neg.indicator (measurableSet_infiniteComponentEvent y)

theorem mem_infiniteComponentEvent_of_mem {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {y : Vertex 2}
    (hy : y ∈ (uniqueInfiniteComponent h).supp) : ω ∈ infiniteComponentEvent y := by
  have hmk : (openGraph ω).connectedComponentMk y = uniqueInfiniteComponent h :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy
  change ((openGraph ω).connectedComponentMk y).supp.Infinite
  rw [hmk]
  exact uniqueInfiniteComponent_infinite h

theorem mem_of_mem_infiniteComponentEvent {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {y : Vertex 2} (hω : ω ∈ infiniteComponentEvent y) :
    y ∈ (uniqueInfiniteComponent h).supp := by
  have hinf : ((openGraph ω).connectedComponentMk y).supp.Infinite := hω
  have heq : (openGraph ω).connectedComponentMk y = uniqueInfiniteComponent h :=
    h.unique hinf (uniqueInfiniteComponent_infinite h)
  rw [← heq]
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2 rfl

/-! ### The estimates at one configuration -/

namespace HeatBounds

variable {ω : Configuration 2} {K : OpenComponent ω} {y : Vertex 2} {σ θ C₁ C₂ β T₀ : ℝ}

theorem timeGreen_self (y : Vertex 2) (hy : y ∈ K.supp) : timeGreen ω K y ⟨y, hy⟩ = 0 := by
  simp [timeGreen]

/-- `|G(x)| ≤ K₀ + J₀ + (2/(πσθ)) √|x - y|` for `|x - y| ≥ T₀`. -/
theorem abs_timeGreen_le (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : K}
    (hr : T₀ ≤ ‖edz x.val y‖) :
    |timeGreen ω K y x| ≤ (2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1)) +
      ((1 + θ⁻¹) * T₀ + (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) / (β - 1)) +
      2 * θ⁻¹ / (Real.pi * σ) * Real.sqrt ‖edz x.val y‖ := by
  set r := ‖edz x.val y‖ with hrdef
  have hr1 : 1 ≤ r := hb.hT₀.trans hr
  have hxy : x.val ≠ y := by
    intro h
    rw [hrdef, h, edz_self, norm_zero] at hr1
    linarith
  obtain ⟨-, heq⟩ := hb.integral_sub_diag_eq x.2 hxy
  have hI := hb.abs_integral_sub_gaussian_le x.2 hr
  have hJ := hb.integrableOn_diag.2
  have hpow : r ^ (2 - 2 * β) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith [hb.hβ1])
  have hθi := inv_pos.2 hb.hθ
  have hpi := Real.pi_pos
  have hσ := hb.hσ
  have hK0 : 0 ≤ 2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1) := by
    have := hb.hC₂
    have := hb.hC₁
    have := Real.Gamma_pos_of_pos (show 0 < β - 1 by linarith [hb.hβ1])
    positivity
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlog : Real.log r ≤ 2 * Real.sqrt r := by
    have := Real.log_le_rpow_div (norm_nonneg (edz x.val y)) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]
    linarith
  rw [timeGreen, heq]
  set I := ∫ t in Ioi (0 : ℝ), (openHeat ω t x.val y - θ⁻¹ * gaussianHeat σ t (edz x.val y))
  set J := ∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE)
  have hmid : |θ⁻¹ * (-Real.log r / (Real.pi * σ))| ≤ 2 * θ⁻¹ / (Real.pi * σ) * Real.sqrt r := by
    rw [abs_mul, abs_of_pos hθi, abs_div, abs_neg, abs_of_nonneg hlog0,
      abs_of_pos (by positivity : 0 < Real.pi * σ)]
    calc θ⁻¹ * (Real.log r / (Real.pi * σ)) ≤ θ⁻¹ * (2 * Real.sqrt r / (Real.pi * σ)) := by
          gcongr
      _ = 2 * θ⁻¹ / (Real.pi * σ) * Real.sqrt r := by ring
  calc |I + θ⁻¹ * (-Real.log r / (Real.pi * σ)) - J|
      ≤ |I| + |θ⁻¹ * (-Real.log r / (Real.pi * σ))| + |J| := by
        refine (abs_sub (I + θ⁻¹ * (-Real.log r / (Real.pi * σ))) J).trans ?_
        exact add_le_add (abs_add_le I (θ⁻¹ * (-Real.log r / (Real.pi * σ)))) le_rfl
    _ ≤ (2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1)) * 1 +
          2 * θ⁻¹ / (Real.pi * σ) * Real.sqrt r +
          ((1 + θ⁻¹) * T₀ + (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) / (β - 1)) := by
        gcongr
        exact hI.trans (mul_le_mul_of_nonneg_left hpow hK0)
    _ = _ := by ring

/-- The Green column `G` has sublinear growth. -/
theorem timeGreen_sublinear (hb : HeatBounds K y σ θ C₁ C₂ β T₀) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x : K,
      R ≤ ‖latticeEuclideanEmbedding x.val‖ →
        |timeGreen ω K y x| ≤ ε * ‖latticeEuclideanEmbedding x.val‖ := by
  intro ε hε
  set a := (2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1)) +
      ((1 + θ⁻¹) * T₀ + (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) / (β - 1)) with ha
  set b := 2 * θ⁻¹ / (Real.pi * σ) with hbdef
  set L := ‖latticeEuclideanEmbedding y‖ with hL
  have hθi := inv_pos.2 hb.hθ
  have hpi := Real.pi_pos
  have hσ := hb.hσ
  have hb0 : 0 ≤ b := by positivity
  have hT0 : 0 < T₀ := lt_of_lt_of_le one_pos hb.hT₀
  refine ⟨max (T₀ + L) (max (2 * |a| / ε) (8 * b ^ 2 / ε ^ 2)), ?_, fun x hx => ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set ρ := ‖latticeEuclideanEmbedding x.val‖ with hρ
  have hρ1 : T₀ + L ≤ ρ := (le_max_left _ _).trans hx
  have hρ2 : 2 * |a| / ε ≤ ρ := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hρ3 : 8 * b ^ 2 / ε ^ 2 ≤ ρ := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hL0 : 0 ≤ L := norm_nonneg _
  have hρ0 : 0 < ρ := by linarith
  have hr : T₀ ≤ ‖edz x.val y‖ := by
    have := norm_sub_norm_le (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y)
    linarith
  have hr2 : ‖edz x.val y‖ ≤ 2 * ρ := by
    have := norm_sub_le (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y)
    linarith
  have hG := hb.abs_timeGreen_le hr
  have hsq : b * Real.sqrt ‖edz x.val y‖ ≤ ε * ρ / 2 := by
    have h1 : b * Real.sqrt ‖edz x.val y‖ ≤ b * Real.sqrt (2 * ρ) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr2) hb0
    refine h1.trans ?_
    rw [← Real.sqrt_sq hb0, ← Real.sqrt_mul (sq_nonneg b)]
    rw [show ε * ρ / 2 = Real.sqrt ((ε * ρ / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have : 8 * b ^ 2 ≤ ε ^ 2 * ρ := by
      rw [div_le_iff₀ (by positivity)] at hρ3
      linarith
    nlinarith
  have ha2 : a ≤ ε * ρ / 2 := by
    have : 2 * |a| ≤ ε * ρ := by rw [div_le_iff₀ hε] at hρ2; linarith
    linarith [le_abs_self a]
  calc |timeGreen ω K y x| ≤ a + b * Real.sqrt ‖edz x.val y‖ := hG
    _ ≤ ε * ρ / 2 + ε * ρ / 2 := add_le_add ha2 hsq
    _ = ε * ρ := by ring

/-- `G` is a Green column with pole `y`. -/
theorem isGreenColumn_timeGreen (hb : HeatBounds K y σ θ C₁ C₂ β T₀) :
    IsGreenColumn 2 le_rfl K ⟨y, hb.hy⟩ (timeGreen ω K y) :=
  ⟨hb.laplacian_timeGreen, fun _ => ⟨timeGreen_self y hb.hy, hb.timeGreen_sublinear⟩,
    fun h3 => absurd h3 (by norm_num)⟩

/-- **The main estimate**: for `|x - y| ≥ T₀`,
`|G(x) - ḡ(x - y) - K| ≤ (2C₂³ + θ^{-1} + C₁^β Γ(β - 1)) |x - y|^{2 - 2β}`, with
`ḡ = continuumGreen 2 (σθ/2)` and `K = -∫ (p(t, y, y) - θ^{-1} p̄(t, e)) dt`. -/
theorem abs_timeGreen_sub_le (hb : HeatBounds K y σ θ C₁ C₂ β T₀) {x : K}
    (hr : T₀ ≤ ‖edz x.val y‖) (hz : edz x.val y ≠ 0) (hκ : 0 < σ * θ / 2) :
    |timeGreen ω K y x - continuumGreen 2 le_rfl ⟨σ * θ / 2, hκ⟩ ⟨edz x.val y, hz⟩ -
        -(∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE))| ≤
      (2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1)) * ‖edz x.val y‖ ^ (2 - 2 * β) := by
  have hxy : x.val ≠ y := by
    intro h
    apply hz
    rw [h, edz_self]
  obtain ⟨-, heq⟩ := hb.integral_sub_diag_eq x.2 hxy
  have hI := hb.abs_integral_sub_gaussian_le x.2 hr
  rw [timeGreen, heq]
  have hσ := hb.hσ
  have hθ := hb.hθ
  have hpi := Real.pi_pos
  have hcg : continuumGreen 2 le_rfl ⟨σ * θ / 2, hκ⟩ ⟨edz x.val y, hz⟩ =
      -Real.log ‖edz x.val y‖ / (2 * Real.pi * (σ * θ / 2)) := by
    simp [continuumGreen]
  rw [hcg]
  set I := ∫ t in Ioi (0 : ℝ), (openHeat ω t x.val y - θ⁻¹ * gaussianHeat σ t (edz x.val y))
  set J := ∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE)
  have hexpr : I + θ⁻¹ * (-Real.log ‖edz x.val y‖ / (Real.pi * σ)) - J -
      -Real.log ‖edz x.val y‖ / (2 * Real.pi * (σ * θ / 2)) - -J = I := by
    field_simp
    ring
  rw [hexpr]
  exact hI

end HeatBounds

/-! ### Theorem 2 in dimension two -/

/-- The Carne–Varopoulos bound gives `p(t, x, y) ≤ C e^{-|x - y|/C}` for `0 < t ≤ |x - y|`. -/
theorem openHeat_le_of_le_norm
    {C : ℝ} (hC : 0 < C) (hCV' : ∀ (ω : Configuration 2)
    (K : OpenComponent ω), K.supp.Infinite → ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t →
      (‖edz x y‖ ≤ t → openHeat ω t x y ≤ C * Real.exp (-(‖edz x y‖ ^ 2 / (C * t)))) ∧
      (t ≤ ‖edz x y‖ →
        openHeat ω t x y ≤ C * Real.exp (-(‖edz x y‖ / C * (1 + Real.log (‖edz x y‖ / t))))))
    {ω : Configuration 2} {K : OpenComponent ω} (hK : K.supp.Infinite) {x y : Vertex 2}
    (hx : x ∈ K.supp) (hy : y ∈ K.supp) {t : ℝ} (ht : 0 < t) (htx : t ≤ ‖edz x y‖) :
    openHeat ω t x y ≤ C * Real.exp (-(‖edz x y‖ / C)) := by
  obtain ⟨h1, h2⟩ := hCV' ω K hK x hx y hy t ht
  rcases eq_or_lt_of_le htx with heq | hlt
  · refine (h1 heq.symm.le).trans (le_of_eq ?_)
    rw [← heq]
    congr 2
    field_simp
  · refine (h2 hlt.le).trans ?_
    have hr0 : 0 < ‖edz x y‖ := lt_trans ht hlt
    have hlog : 0 ≤ Real.log (‖edz x y‖ / t) :=
      Real.log_nonneg ((one_le_div ht).2 hlt.le)
    gcongr
    exact le_mul_of_one_le_right (by positivity) (by linarith)

/-- The small-time bound `p(t, x, y) ≤ C e^{-|x - y|/C}` for `0 < t ≤ |x - y|` on infinite
components, the only consequence of the Carne–Varopoulos bound used in Dario–Gu, §5. -/
def HeatSmallTimeTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration 2) (K : OpenComponent ω), K.supp.Infinite →
    ∀ x ∈ K.supp, ∀ y ∈ K.supp, ∀ t : ℝ, 0 < t → t ≤ ‖edz x y‖ →
      openHeat ω t x y ≤ C * Real.exp (-(‖edz x y‖ / C))

/-- The Carne–Varopoulos bound gives the small-time bound. -/
theorem heatSmallTimeTwo_of_carneVaropoulos (hCV : CarneVaropoulosTwo) : HeatSmallTimeTwo := by
  obtain ⟨C₂, hC₂, hcv⟩ := hCV
  exact ⟨C₂, hC₂, fun ω K hK x hx y hy t ht htx =>
    openHeat_le_of_le_norm hC₂ hcv hK hx hy ht htx⟩

/-- **Dario–Gu, Theorem 2** in dimension two (the planar quantitative Green function input), from
Theorem 1 (`DarioGuHeatKernelTwo`), the small-time bound and the Liouville theorem at order zero. -/
theorem supercriticalBondGreenQuantitativeTwo_of_smallTime (hP : DarioGuHeatKernelTwo)
    (hS : HeatSmallTimeTwo)
    (hL : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      Rigidity.Steps.Section5.SublinearLiouville p) :
    Rigidity.External.SupercriticalBondGreenQuantitativeTwo := by
  intro p hpc hp1
  obtain ⟨σ, hσ, hT⟩ := hP p hpc hp1
  obtain ⟨C₂, hC₂, hcv⟩ := hS
  have hθ : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  set θ := theta 2 p with hθdef
  have hκ : 0 < σ * θ / 2 := by positivity
  refine ⟨σ * θ / 2, hκ, greenConstant σ θ, fun y => measurable_greenConstant σ θ y,
    fun δ hδ => ?_⟩
  set δ₁ := min δ (1 / 2) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min hδ (by norm_num)
  have hδ₁2 : δ₁ ≤ 1 / 2 := min_le_right _ _
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  obtain ⟨C₁, s, hC₁, hs, hTy⟩ := hT (δ₁ / 2) (by positivity)
  set β := 3 / 2 - δ₁ / 2 with hβdef
  have hβ1 : 1 < β := by linarith
  have hβ2 : β ≤ 3 / 2 := by linarith
  have hexp : (-1 - (1 / 2 - δ₁ / 2) : ℝ) = -β := by rw [hβdef]; ring
  have hexp2 : 2 - 2 * β = -(1 - δ₁) := by rw [hβdef]; ring
  have hθi : 0 < θ⁻¹ := inv_pos.2 hθ
  set K₀ := 2 * C₂ ^ 3 + θ⁻¹ + C₁ ^ β * Real.Gamma (β - 1) with hK₀def
  have hK₀ : 0 < K₀ := by
    have := Real.Gamma_pos_of_pos (show 0 < β - 1 by linarith)
    positivity
  set JB := (C₁ + θ⁻¹ * (4 * Real.pi * σ ^ 2)⁻¹) / (β - 1) with hJBdef
  have hJB : 0 ≤ JB := by
    have := Real.pi_pos
    have : 0 < β - 1 := by linarith
    positivity
  set Cf := max K₀ (max (affineTailConst C₁ s (1 + θ⁻¹) JB) (affineTailConst C₁ s 1 0)) with hCf
  have hCf0 : 0 < Cf := lt_of_lt_of_le hK₀ (le_max_left _ _)
  refine ⟨Cf, s, hCf0, hs, fun y => ?_⟩
  obtain ⟨T, hTm, hT0, hTtail, hTae⟩ := hTy y
  have hU := Rigidity.Percolation.ae_hasUniqueInfiniteOpenComponent (d := 2) le_rfl hpc
  have hHB : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        HeatBounds (uniqueInfiniteComponent h) y σ θ C₁ C₂ β (max (T ω) 1) := by
    filter_upwards [hTae] with ω hω h hy
    exact
      { hσ := hσ, hθ := hθ, hC₁ := hC₁, hC₂ := hC₂, hβ1 := hβ1, hβ2 := hβ2,
        hT₀ := le_max_right _ _, hy := hy,
        thm1 := fun x hx t ht hxt => by
          have := hω h hy x hx t ((le_max_right _ _).trans ht) ((le_max_left _ _).trans ht) hxt
          rwa [hexp] at this
        cv := fun x hx t ht htx =>
          hcv ω (uniqueInfiniteComponent h) (uniqueInfiniteComponent_infinite h) x hx y hy t ht
            htx }
  constructor
  · have hKb : ∀ᵐ ω ∂latticeBondLaw 2 p,
        |greenConstant σ θ y ω| ≤ (1 + θ⁻¹) * max (T ω) 1 + JB := by
      filter_upwards [hHB, hU] with ω hω hu
      by_cases hmem : ω ∈ infiniteComponentEvent y
      · have hy := mem_of_mem_infiniteComponentEvent hu hmem
        rw [greenConstant, Set.indicator_of_mem hmem, abs_neg]
        exact (hω hu hy).integrableOn_diag.2
      · rw [greenConstant, Set.indicator_of_notMem hmem, abs_zero]
        positivity
    intro R hR
    refine (measure_le_affine_le hC₁ hs (le_add_of_nonneg_right hθi.le) hJB hTtail hKb R hR).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_exp_neg_div_mono affineTailConst_pos
      ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg hR s)
  · refine ⟨fun ω => max (T ω) 1, hTm.max measurable_const,
      fun ω => zero_le_one.trans (le_max_right _ _), fun R hR => ?_, ?_⟩
    · have hMb : ∀ᵐ ω ∂latticeBondLaw 2 p, max (T ω) 1 ≤ 1 * max (T ω) 1 + 0 :=
        Eventually.of_forall fun ω => by simp
      refine (measure_le_affine_le hC₁ hs le_rfl le_rfl hTtail hMb R hR).trans
        (ENNReal.ofReal_le_ofReal ?_)
      exact mul_exp_neg_div_mono affineTailConst_pos
        ((le_max_right _ _).trans (le_max_right _ _)) (Real.rpow_nonneg hR s)
    · filter_upwards [hHB, hL p hpc hp1] with ω hω hωL
      intro h hy g hg
      have hb := hω h hy
      have hgG : g = HeatBounds.timeGreen ω (uniqueInfiniteComponent h) y :=
        Rigidity.Proofs.Section5.eq_of_isGreenColumn (hωL h) hg hb.isGreenColumn_timeGreen
      subst hgG
      have hKval : greenConstant σ θ y ω =
          -∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE) := by
        rw [greenConstant, Set.indicator_of_mem (mem_infiniteComponentEvent_of_mem h hy)]
      rw [hKval]
      have hmain : ∀ (x : uniqueInfiniteComponent h) (z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0}),
          z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y →
          max (T ω) 1 ≤ ‖z.val‖ →
          |HeatBounds.timeGreen ω (uniqueInfiniteComponent h) y x - continuumGreen 2 le_rfl ⟨σ * θ / 2, hκ⟩ z -
              -(∫ t in Ioi (0 : ℝ), (openHeat ω t y y - θ⁻¹ * gaussianHeat σ t unitE))| ≤
            K₀ / ‖z.val‖ ^ (1 - δ₁) := by
        intro x z hz hM
        have hz' : edz x.val y ≠ 0 := fun h0 => z.2 (hz.trans h0)
        have hzeq : z = ⟨edz x.val y, hz'⟩ := Subtype.ext hz
        rw [hzeq] at hM ⊢
        have hr1 : 1 ≤ ‖edz x.val y‖ := (le_max_right _ _).trans hM
        have hr0 : 0 < ‖edz x.val y‖ := lt_of_lt_of_le one_pos hr1
        refine (hb.abs_timeGreen_sub_le hM hz' hκ).trans (le_of_eq ?_)
        rw [hexp2, Real.rpow_neg hr0.le, div_eq_mul_inv]
      constructor
      · intro ε hε
        set L := ‖latticeEuclideanEmbedding y‖
        have hδc : 0 < 1 - δ₁ := by linarith
        refine ⟨max (max (T ω) 1) ((K₀ / ε) ^ (1 / (1 - δ₁))) + L + 1, by positivity,
          fun x z hz hR => ?_⟩
        have hzx : ‖z.val‖ ≥ ‖latticeEuclideanEmbedding x.val‖ - L := by
          rw [hz]
          exact norm_sub_norm_le _ _
        have hr : max (max (T ω) 1) ((K₀ / ε) ^ (1 / (1 - δ₁))) ≤ ‖z.val‖ := by linarith
        have hM : max (T ω) 1 ≤ ‖z.val‖ := (le_max_left _ _).trans hr
        have hr1 : 1 ≤ ‖z.val‖ := (le_max_right _ _).trans hM
        have hr0 : 0 < ‖z.val‖ := lt_of_lt_of_le one_pos hr1
        refine (hmain x z hz hM).trans ?_
        have hq : K₀ / ε ≤ ‖z.val‖ ^ (1 - δ₁) := by
          have h1 : (K₀ / ε) ^ (1 / (1 - δ₁)) ≤ ‖z.val‖ := (le_max_right _ _).trans hr
          have h2 := Real.rpow_le_rpow (by positivity) h1 hδc.le
          rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hδc.ne', Real.rpow_one] at h2
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hε] at hq
        linarith
      · intro x z hz hM
        have hr1 : 1 ≤ ‖z.val‖ := (le_max_right _ _).trans hM
        have hr0 : 0 < ‖z.val‖ := lt_of_lt_of_le one_pos hr1
        refine (hmain x z hz hM).trans ?_
        have hpow : ‖z.val‖ ^ (1 - δ) ≤ ‖z.val‖ ^ (1 - δ₁) :=
          Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
        have hpos : 0 < ‖z.val‖ ^ (1 - δ) := Real.rpow_pos_of_pos hr0 _
        change K₀ / ‖z.val‖ ^ (1 - δ₁) ≤ Cf / ‖z.val‖ ^ (1 - δ)
        calc K₀ / ‖z.val‖ ^ (1 - δ₁) ≤ K₀ / ‖z.val‖ ^ (1 - δ) :=
              div_le_div_of_nonneg_left hK₀.le hpos hpow
          _ ≤ Cf / ‖z.val‖ ^ (1 - δ) := by gcongr; exact le_max_left _ _


/-- **Dario–Gu, Theorem 2** in dimension two from Theorem 1, the Carne–Varopoulos bound
(`CarneVaropoulosTwo`) and the Liouville theorem at order zero. -/
theorem supercriticalBondGreenQuantitativeTwo_of_heatKernel (hP : DarioGuHeatKernelTwo)
    (hCV : CarneVaropoulosTwo)
    (hL : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      Rigidity.Steps.Section5.SublinearLiouville p) :
    Rigidity.External.SupercriticalBondGreenQuantitativeTwo :=
  supercriticalBondGreenQuantitativeTwo_of_smallTime hP (heatSmallTimeTwo_of_carneVaropoulos hCV) hL

/-- Theorem 2 of Dario–Gu in dimension two from Theorem 1, the Carne–Varopoulos bound and the
planar qualitative corrector input. -/
theorem supercriticalBondGreenQuantitativeTwo_of_heatKernel_of_correctorInput
    (hP : DarioGuHeatKernelTwo) (hCV : CarneVaropoulosTwo)
    (hC : Rigidity.External.SupercriticalBondCorrectorInputTwo) :
    Rigidity.External.SupercriticalBondGreenQuantitativeTwo :=
  supercriticalBondGreenQuantitativeTwo_of_heatKernel hP hCV fun p hpc hp1 =>
    sublinearLiouville_two_of_correctorInput hC p hpc hp1

/-- Theorem 2 of Dario–Gu in dimension two from Theorem 1, the Carne–Varopoulos bound and the
planar order-zero regularity input. -/
theorem supercriticalBondGreenQuantitativeTwo_of_heatKernel_of_orderZero
    (hP : DarioGuHeatKernelTwo) (hCV : CarneVaropoulosTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo) :
    Rigidity.External.SupercriticalBondGreenQuantitativeTwo :=
  supercriticalBondGreenQuantitativeTwo_of_heatKernel hP hCV fun p hpc hp1 =>
    Rigidity.Proofs.Section5.sublinearLiouville_two p hpc hp1 hAD

end Rigidity.Green
