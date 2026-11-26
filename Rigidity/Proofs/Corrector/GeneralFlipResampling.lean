import Rigidity.Proofs.Corrector.GeneralPropThreeOne
import Rigidity.Proofs.Corrector.DarioBondResampling

/-!
# Resampling one bond of the Bernoulli bond law of `ℤᵈ`

Dario's proof of Lemma 3.3 bounds the resampling variance `𝕍[X] = Σ_e (X - X'_e)²` of
Proposition 2.17, with `X'_e = E[X | F(𝓑_d \ {e})]`, on the doubled probability space `Ω × Ω`
in which the conductance of `e` is replaced by an independent copy ((3.11)-(3.13)). For the
Bernoulli bond law the conductances take the two values `0` and `1`, and the conditional
expectation is the two-point average `X'_e(ω) = p X(ω^{e,1}) + (1 - p) X(ω^{e,0})`, where `ω^{e,b}`
is `ω` with the state of `e` set to `b` (`condExp_bondsExcept_ae_eq`). Hence `|X - X'_e| ≤ |D_e X|`
for the flip difference `D_e X(ω) = X(ω^{e,1}) - X(ω^{e,0})`, and `𝕍[X] ≤ Σ_e (D_e X)²` almost
surely (`ae_resampleVar_le_tsum_bondFlipDiff`). This is the planar argument of
`Rigidity.Corrector.ae_resampleVar_le_tsum_bondFlipDiff`, in every dimension.

Forcing the state of one bond changes the law by a bounded density:
`∫ f = p ∫ f(ω^{e,1}) + (1 - p) ∫ f(ω^{e,0})` (`lintegral_eq_setBond`). Hence an `O_s(θ)` bound of
`Z` gives `Z(ω^{e,b}) ≤ O_s(θ (2/q)^{1/s})` with `q = p` for `b = 1` and `q = 1 - p` for `b = 0`
(`IsOsBond.comp_setBond`, the form of Dario's (3.12) used here), and an almost sure property holds
almost surely for every `ω^{e,b}` when `0 < p < 1` (`ae_setBond`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- The configuration `ω` with the state of the bond `e` set to `b`. -/
def setBond (e : Bond d) (b : Bool) (ω : Configuration d) : Configuration d :=
  Function.update ω e b

theorem measurable_setBond (e : Bond d) (b : Bool) : Measurable (setBond e b) := by
  refine measurable_pi_lambda _ fun e' => ?_
  by_cases h : e' = e
  · subst h
    simp only [setBond, Function.update_self]
    exact measurable_const
  · simp only [setBond, Function.update_of_ne h]
    exact measurable_pi_apply e'

theorem setBond_self (e : Bond d) (ω : Configuration d) : setBond e (ω e) ω = ω :=
  Function.update_eq_self e ω

theorem setBond_apply_ne {e e' : Bond d} (h : e' ≠ e) (b : Bool) (ω : Configuration d) :
    setBond e b ω e' = ω e' := by
  unfold setBond
  exact Function.update_of_ne h b ω

/-- The flip difference `D_e X(ω) = X(ω^{e,1}) - X(ω^{e,0})`. -/
noncomputable def bondFlipDiff (X : Configuration d → ℝ) (e : Bond d) (ω : Configuration d) :
    ℝ :=
  X (setBond e true ω) - X (setBond e false ω)

theorem measurable_bondFlipDiff {X : Configuration d → ℝ} (hX : Measurable X) (e : Bond d) :
    Measurable (bondFlipDiff X e) :=
  (hX.comp (measurable_setBond e true)).sub (hX.comp (measurable_setBond e false))

theorem measurable_restrictExcept (e : Bond d) :
    Measurable (fun (ω : Configuration d) (b : {b : Bond d // b ≠ e}) => ω b) :=
  measurable_pi_lambda _ fun b => measurable_pi_apply (b : Bond d)

theorem bondsExcept_le (e : Bond d) :
    bondsExcept e ≤ (inferInstance : MeasurableSpace (Configuration d)) :=
  (measurable_restrictExcept e).comap_le

/-- The configuration of the bonds other than `e`, extended by closing `e`. -/
def extendExcept (e : Bond d) (r : {b : Bond d // b ≠ e} → Bool) : Configuration d :=
  fun b => if h : b = e then false else r ⟨b, h⟩

theorem measurable_extendExcept (e : Bond d) : Measurable (extendExcept e) := by
  refine measurable_pi_lambda _ fun b => ?_
  by_cases h : b = e
  · simp only [extendExcept, dif_pos h]
    exact measurable_const
  · simp only [extendExcept, dif_neg h]
    exact measurable_pi_apply _

theorem measurable_resampleVar (p : unitInterval) {X : Configuration d → ℝ} (hX : Measurable X) :
    Measurable (resampleVar p X) := by
  unfold resampleVar
  refine Measurable.tsum fun e => ENNReal.measurable_ofReal.comp ?_
  exact (hX.sub (stronglyMeasurable_condExp.measurable.mono (bondsExcept_le e) le_rfl)).pow_const 2

section CondExp

variable (p : unitInterval)

/-- Averaging out the bond `e` is the two-point average. -/
theorem partialInt_compl_singleton (X : Configuration d → ℝ) (e : Bond d) (ω : Configuration d) :
    LatticeProb.partialInt (fun _ : Bond d => bernoulliMeasure true false p)
        ({e}ᶜ : Set (Bond d)) X ω =
      (p : ℝ) * X (setBond e true ω) + (1 - p) * X (setBond e false ω) := by
  unfold LatticeProb.partialInt
  simp_rw [LatticeProb.comb_compl_singleton]
  have hmp := measurePreserving_eval_infinitePi
    (fun _ : Bond d => bernoulliMeasure true false p) e
  have h := integral_map (μ := Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true false p))
    (φ := Function.eval e) (f := fun b : Bool => X (Function.update ω e b))
    hmp.measurable.aemeasurable (Measurable.of_discrete).aestronglyMeasurable
  rw [hmp.map_eq, integral_bernoulliMeasure] at h
  rw [← h]
  simp only [smul_eq_mul, setBond]

/-- **The conditional expectation given the other bonds is the two-point average**:
`E[X | F(𝓑_d \ {e})] = p X(ω^{e,1}) + (1 - p) X(ω^{e,0})` almost surely. -/
theorem condExp_bondsExcept_ae_eq {X : Configuration d → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw d p)) (e : Bond d) :
    condExp (bondsExcept e) (latticeBondLaw d p) X =ᵐ[latticeBondLaw d p]
      fun ω => (p : ℝ) * X (setBond e true ω) + (1 - p) * X (setBond e false ω) := by
  set μ := fun _ : Bond d => bernoulliMeasure true false p with hμ
  set S : Set (Bond d) := {e}ᶜ with hS
  have hPI : Integrable (LatticeProb.partialInt μ S X) (latticeBondLaw d p) :=
    LatticeProb.integrable_partialInt μ S hX
  have hmeasS : Measurable[bondsExcept e] (LatticeProb.partialInt μ S X) := by
    have hfac : LatticeProb.partialInt μ S X =
        (LatticeProb.partialInt μ S X ∘ extendExcept e) ∘
          (fun (ω : Configuration d) (b : {b : Bond d // b ≠ e}) => ω b) := by
      funext ω
      refine LatticeProb.partialInt_congr μ S X fun b hb => ?_
      have hb' : b ≠ e := hb
      simp only [extendExcept, dif_neg hb']
    rw [hfac]
    exact ((LatticeProb.measurable_partialInt μ S hXm).comp (measurable_extendExcept e)).comp
      (comap_measurable _)
  have key : LatticeProb.partialInt μ S X =ᵐ[latticeBondLaw d p]
      condExp (bondsExcept e) (latticeBondLaw d p) X := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (bondsExcept_le e) hX
      (fun s _ _ => hPI.integrableOn) (fun s hs _ => ?_)
      hmeasS.stronglyMeasurable.aestronglyMeasurable
    have hsm : MeasurableSet s := bondsExcept_le e s hs
    set χ : Configuration d → ℝ := s.indicator (fun _ => (1 : ℝ)) with hχdef
    have hmul : ∀ (g : Configuration d → ℝ) (x : Configuration d), χ x * g x = s.indicator g x := by
      intro g x
      by_cases hx : x ∈ s <;> simp [hχdef, hx]
    have hloc : ∀ ω η : Configuration d, χ (LatticeProb.comb S ω η) = χ ω := by
      intro ω η
      have hmem : LatticeProb.comb S ω η ∈ s ↔ ω ∈ s := by
        obtain ⟨t, -, rfl⟩ := hs
        have hr : (fun b : {b : Bond d // b ≠ e} => LatticeProb.comb S ω η b) =
            fun b : {b : Bond d // b ≠ e} => ω b := by
          funext b
          exact LatticeProb.comb_apply_of_mem (show (b : Bond d) ∈ S from b.2)
        simp only [Set.mem_preimage, hr]
      by_cases hx : ω ∈ s
      · simp [hχdef, hx, hmem.2 hx]
      · simp [hχdef, hx, show LatticeProb.comb S ω η ∉ s from fun h => hx (hmem.1 h)]
    have hint : Integrable (fun ω => χ ω * X ω) (latticeBondLaw d p) := by
      have : (fun ω => χ ω * X ω) = s.indicator X := funext fun x => hmul X x
      rw [this]
      exact hX.indicator hsm
    have hkey := LatticeProb.integral_mul_partialInt μ (F := X) (g := χ) S hloc hint
    rw [← integral_indicator hsm, ← integral_indicator hsm]
    calc ∫ x, s.indicator (LatticeProb.partialInt μ S X) x ∂(latticeBondLaw d p)
        = ∫ x, χ x * LatticeProb.partialInt μ S X x ∂(latticeBondLaw d p) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hmul _ x).symm)
      _ = ∫ x, χ x * X x ∂(latticeBondLaw d p) := hkey
      _ = ∫ x, s.indicator X x ∂(latticeBondLaw d p) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hmul X x)
  filter_upwards [key] with ω hω
  rw [← hω]
  exact partialInt_compl_singleton p X e ω

/-- The distance of `X` to the two-point average is at most the flip difference. -/
theorem sq_sub_twoPoint_le (X : Configuration d → ℝ) (e : Bond d) (ω : Configuration d) :
    (X ω - ((p : ℝ) * X (setBond e true ω) + (1 - p) * X (setBond e false ω))) ^ 2 ≤
      bondFlipDiff X e ω ^ 2 := by
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  unfold bondFlipDiff
  cases h : ω e
  · have hω : setBond e false ω = ω := by
      rw [← h]
      exact setBond_self e ω
    rw [hω]
    have e1 : X ω - ((p : ℝ) * X (setBond e true ω) + (1 - p) * X ω) =
        p * (X ω - X (setBond e true ω)) := by ring
    have hp2 : (p : ℝ) ^ 2 ≤ 1 := by nlinarith
    rw [e1, mul_pow]
    calc (p : ℝ) ^ 2 * (X ω - X (setBond e true ω)) ^ 2
        ≤ 1 * (X ω - X (setBond e true ω)) ^ 2 :=
          mul_le_mul_of_nonneg_right hp2 (sq_nonneg _)
      _ = (X (setBond e true ω) - X ω) ^ 2 := by ring
  · have hω : setBond e true ω = ω := by
      rw [← h]
      exact setBond_self e ω
    rw [hω]
    have e1 : X ω - ((p : ℝ) * X ω + (1 - p) * X (setBond e false ω)) =
        (1 - p) * (X ω - X (setBond e false ω)) := by ring
    have hp2 : (1 - (p : ℝ)) ^ 2 ≤ 1 := by nlinarith
    rw [e1, mul_pow]
    calc (1 - (p : ℝ)) ^ 2 * (X ω - X (setBond e false ω)) ^ 2
        ≤ 1 * (X ω - X (setBond e false ω)) ^ 2 :=
          mul_le_mul_of_nonneg_right hp2 (sq_nonneg _)
      _ = (X ω - X (setBond e false ω)) ^ 2 := by ring

theorem ae_sq_sub_condExp_le {X : Configuration d → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw d p)) (e : Bond d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      (X ω - condExp (bondsExcept e) (latticeBondLaw d p) X ω) ^ 2 ≤ bondFlipDiff X e ω ^ 2 := by
  filter_upwards [condExp_bondsExcept_ae_eq p hXm hX e] with ω hω
  rw [hω]
  exact sq_sub_twoPoint_le p X e ω

/-- **The resampling variance is at most the sum of the squared flip differences**:
`𝕍[X] ≤ Σ_e (X(ω^{e,1}) - X(ω^{e,0}))²` almost surely. -/
theorem ae_resampleVar_le_tsum_bondFlipDiff {X : Configuration d → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw d p)) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      resampleVar p X ω ≤ ∑' e, ENNReal.ofReal (bondFlipDiff X e ω ^ 2) := by
  have h := ae_all_iff.2 fun e => ae_sq_sub_condExp_le p hXm hX e
  filter_upwards [h] with ω hω
  exact ENNReal.tsum_le_tsum fun e => ENNReal.ofReal_le_ofReal (hω e)

end CondExp

section Flip

variable (p : unitInterval)

/-- **Forcing the state of one bond**: `∫ f = p ∫ f(ω^{e,1}) + (1 - p) ∫ f(ω^{e,0})`. -/
theorem lintegral_eq_setBond {f : Configuration d → ℝ≥0∞} (hf : Measurable f) (e : Bond d) :
    ∫⁻ ω, f ω ∂latticeBondLaw d p =
      ENNReal.ofReal p * ∫⁻ ω, f (setBond e true ω) ∂latticeBondLaw d p +
        ENNReal.ofReal (1 - p) * ∫⁻ ω, f (setBond e false ω) ∂latticeBondLaw d p := by
  have hT := LatticeProb.measurePreserving_update_infinitePi
    (fun _ : Bond d => bernoulliMeasure true false p) e
  have hft : Measurable fun ω => f (setBond e true ω) := hf.comp (measurable_setBond e true)
  have hff : Measurable fun ω => f (setBond e false ω) := hf.comp (measurable_setBond e false)
  calc ∫⁻ ω, f ω ∂latticeBondLaw d p
      = ∫⁻ z, f (Function.update z.1 e z.2)
          ∂((Measure.infinitePi fun _ : Bond d => bernoulliMeasure true false p).prod
            (bernoulliMeasure true false p)) := (hT.lintegral_comp hf).symm
    _ = ∫⁻ ω, ∫⁻ b, f (Function.update ω e b) ∂(bernoulliMeasure true false p)
          ∂(latticeBondLaw d p) := lintegral_prod _ (hf.comp hT.measurable).aemeasurable
    _ = ∫⁻ ω, (ENNReal.ofReal p * f (setBond e true ω) +
          ENNReal.ofReal (1 - p) * f (setBond e false ω)) ∂latticeBondLaw d p := by
        congr 1
        funext ω
        exact lintegral_bernoulliMeasure_bool p _
    _ = ENNReal.ofReal p * ∫⁻ ω, f (setBond e true ω) ∂latticeBondLaw d p +
          ENNReal.ofReal (1 - p) * ∫⁻ ω, f (setBond e false ω) ∂latticeBondLaw d p := by
        rw [lintegral_add_left (hft.const_mul _), lintegral_const_mul _ hft,
          lintegral_const_mul _ hff]

theorem ofReal_bondWeight_mul_lintegral_setBond_le {f : Configuration d → ℝ≥0∞}
    (hf : Measurable f) (e : Bond d) (b : Bool) :
    ENNReal.ofReal (bondWeight p b) * ∫⁻ ω, f (setBond e b ω) ∂latticeBondLaw d p ≤
      ∫⁻ ω, f ω ∂latticeBondLaw d p := by
  rw [lintegral_eq_setBond p hf e]
  cases b
  · exact le_add_self
  · exact le_self_add

/-- **`O_s` bounds survive forcing one bond** (the form of Dario's (3.12) used here): if
`Z ≤ O_s(θ)` and `q > 0` is the weight of the forced state, then
`Z(ω^{e,b}) ≤ O_s(θ (2/q)^{1/s})`. -/
theorem IsOsBond.comp_setBond {Z : Configuration d → ℝ} (hZ : Measurable Z) {s θ : ℝ}
    (hs : 0 < s) (h : IsOsBond d p Z s θ) (e : Bond d) (b : Bool) (hq : 0 < bondWeight p b) :
    IsOsBond d p (fun ω => Z (setBond e b ω)) s (θ * (2 / bondWeight p b) ^ (1 / s)) := by
  set q := bondWeight p b with hqdef
  set g : Configuration d → ℝ := fun ω => Real.exp (Real.rpow (max (Z ω / θ) 0) s) with hg
  have hgm : Measurable g :=
    Real.measurable_exp.comp (((hZ.div_const θ).max measurable_const).pow_const s)
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => (Real.exp_pos _).le
  obtain ⟨hint, hle⟩ := h
  have hlin : ∫⁻ ω, ENNReal.ofReal (g ω) ∂latticeBondLaw d p ≤ ENNReal.ofReal 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hg0)]
    exact ENNReal.ofReal_le_ofReal hle
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p (f := fun ω => ENNReal.ofReal (g ω))
    (ENNReal.measurable_ofReal.comp hgm) e b
  have hlin' : ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw d p ≤
      ENNReal.ofReal (2 / q) := by
    have h1 : ENNReal.ofReal q * ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw d p ≤
        ENNReal.ofReal 2 := hflip.trans hlin
    have hq' : ENNReal.ofReal q ≠ 0 := by simp [hq]
    have hq'' : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw d p
        = (ENNReal.ofReal q)⁻¹ * (ENNReal.ofReal q *
            ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw d p) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hq' hq'', one_mul]
      _ ≤ (ENNReal.ofReal q)⁻¹ * ENNReal.ofReal 2 := by gcongr
      _ = ENNReal.ofReal (2 / q) := by
          rw [ENNReal.ofReal_div_of_pos hq, ENNReal.div_eq_inv_mul]
  have hgsm : Measurable fun ω => g (setBond e b ω) := hgm.comp (measurable_setBond e b)
  have hint' : Integrable (fun ω => g (setBond e b ω)) (latticeBondLaw d p) := by
    refine ⟨hgsm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp only [Real.enorm_eq_ofReal (hg0 _)]
    exact lt_of_le_of_lt hlin' ENNReal.ofReal_lt_top
  have hq1 : q ≤ 1 := bondWeight_le_one p b
  have hA : 1 ≤ 2 / q := by
    rw [le_div_iff₀ hq]
    linarith
  have hle' : ∫ ω, g (setBond e b ω) ∂latticeBondLaw d p ≤ 2 / q := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => hg0 _)
      hgsm.aestronglyMeasurable]
    have h2q : (0 : ℝ) ≤ 2 / q := by positivity
    calc (∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw d p).toReal
        ≤ (ENNReal.ofReal (2 / q)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin'
      _ = 2 / q := ENNReal.toReal_ofReal h2q
  exact Rigidity.Proofs.S2.isOsBond_of_integral_le hs hA hint' hle'

end Flip

/-- **Almost sure properties survive forcing one bond**: for the Bernoulli law with `0 < p < 1`,
an almost sure property holds almost surely for every `ω^{e,b}`. -/
theorem ae_setBond {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {P : Configuration d → Prop} (h : ∀ᵐ ω ∂latticeBondLaw d p, P ω) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ (e : Bond d) (b : Bool), P (setBond e b ω) := by
  set N := toMeasurable (latticeBondLaw d p) {ω | ¬ P ω} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : latticeBondLaw d p N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 h
  have hsub : {ω | ¬ P ω} ⊆ N := subset_toMeasurable _ _
  have key : ∀ (e : Bond d) (b : Bool), ∀ᵐ ω ∂latticeBondLaw d p, setBond e b ω ∉ N := by
    intro e b
    have hq : 0 < bondWeight p b := by
      unfold bondWeight
      split_ifs
      · exact hp0
      · linarith
    have hle := ofReal_bondWeight_mul_lintegral_setBond_le p
      (f := N.indicator fun _ => (1 : ℝ≥0∞)) ((measurable_const.indicator hNm)) e b
    rw [lintegral_indicator_const hNm, hN0, mul_zero] at hle
    have hzero : ∫⁻ ω, N.indicator (fun _ => (1 : ℝ≥0∞)) (setBond e b ω)
        ∂latticeBondLaw d p = 0 := by
      have hq' : ENNReal.ofReal (bondWeight p b) ≠ 0 := by simp [hq]
      exact (mul_eq_zero.1 (le_antisymm hle bot_le)).resolve_left hq'
    have hpre : (fun ω => N.indicator (fun _ => (1 : ℝ≥0∞)) (setBond e b ω)) =
        (setBond e b ⁻¹' N).indicator fun _ => 1 := by
      funext ω
      by_cases h : setBond e b ω ∈ N
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show ω ∈ setBond e b ⁻¹' N from h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show ω ∉ setBond e b ⁻¹' N from h)]
    rw [hpre, lintegral_indicator_const (hNm.preimage (measurable_setBond e b)), one_mul]
      at hzero
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with ω hω
    exact hω
  have hall : ∀ᵐ ω ∂latticeBondLaw d p, ∀ (e : Bond d) (b : Bool), setBond e b ω ∉ N := by
    rw [ae_all_iff]
    intro e
    rw [ae_all_iff]
    exact key e
  filter_upwards [hall] with ω hω e b
  by_contra hP
  exact hω e b (hsub hP)

/-- `O_s` bounds pass to almost surely smaller measurable variables. -/
theorem isOsBond_of_ae_le {p : unitInterval} {X Y : Configuration d → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hX : Measurable X)
    (hXY : ∀ᵐ ω ∂latticeBondLaw d p, X ω ≤ Y ω) (hY : IsOsBond d p Y s θ) :
    IsOsBond d p X s θ := by
  have hpoint : ∀ᵐ ω ∂latticeBondLaw d p, Real.exp (Real.rpow (max (X ω / θ) 0) s) ≤
      Real.exp (Real.rpow (max (Y ω / θ) 0) s) := by
    filter_upwards [hXY] with ω hω
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le_max (div_le_div_of_nonneg_right hω hθ.le) le_rfl) hs.le
  have hXi : Integrable (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s))
      (latticeBondLaw d p) := by
    refine Integrable.mono' hY.1
      (Rigidity.Proofs.S2.measurable_exp_rpow_max_div s hX).aestronglyMeasurable ?_
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hω
  exact ⟨hXi, (integral_mono_ae hXi hY.1 hpoint).trans hY.2⟩

end Rigidity.Corrector.GeneralDim
