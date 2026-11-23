import Rigidity.Proofs.Corrector.DarioPropThreeOne
import Rigidity.Proofs.S2.ScaleInputsFaithful
import LatticeProb.Prob.Splice

/-!
# Resampling one bond of the Bernoulli bond law

Dario's proof of Lemma 3.3 bounds the resampling variance `𝕍[X] = Σ_e (X - X'_e)²` of
Proposition 2.17, with `X'_e = E[X | F(𝓑_d \ {e})]`, on the doubled probability space `Ω × Ω`
in which the conductance of `e` is replaced by an independent copy ((3.11)-(3.13)). For the
Bernoulli bond law the conductances take the two values `0` and `1`, and the conditional expectation
is the two-point average `X'_e(ω) = p X(ω^{e,1}) + (1 - p) X(ω^{e,0})`, where `ω^{e,b}` is `ω` with
the state of `e` set to `b` (`condExp_bondsExcept_ae_eq`). Hence `|X - X'_e| ≤ |D_e X|` for the
flip difference `D_e X(ω) = X(ω^{e,1}) - X(ω^{e,0})`, and `𝕍[X] ≤ Σ_e (D_e X)²` almost surely
(`ae_resampleVar_le_tsum_bondFlipDiff`).

Forcing the state of one bond changes the law by a bounded density:
`∫ f = p ∫ f(ω^{e,1}) + (1 - p) ∫ f(ω^{e,0})` (`lintegral_eq_setBond`). This is the form of (3.12)
used here: an `O_s(θ)` bound of `Z` gives `Z(ω^{e,b}) ≤ O_s(θ (2/q)^{1/s})` with `q = p` for
`b = 1` and `q = 1 - p` for `b = 0` (`IsOsBond.comp_setBond`).
-/

namespace Rigidity.Corrector

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- The configuration `ω` with the state of the bond `e` set to `b`. -/
def setBond (e : Bond 2) (b : Bool) (ω : Configuration 2) : Configuration 2 :=
  Function.update ω e b

theorem measurable_setBond (e : Bond 2) (b : Bool) : Measurable (setBond e b) := by
  refine measurable_pi_lambda _ fun e' => ?_
  by_cases h : e' = e
  · subst h
    simp only [setBond, Function.update_self]
    exact measurable_const
  · simp only [setBond, Function.update_of_ne h]
    exact measurable_pi_apply e'

theorem setBond_self (e : Bond 2) (ω : Configuration 2) : setBond e (ω e) ω = ω :=
  Function.update_eq_self e ω

/-- The flip difference `D_e X(ω) = X(ω^{e,1}) - X(ω^{e,0})`. -/
noncomputable def bondFlipDiff (X : Configuration 2 → ℝ) (e : Bond 2) (ω : Configuration 2) :
    ℝ :=
  X (setBond e true ω) - X (setBond e false ω)

theorem measurable_bondFlipDiff {X : Configuration 2 → ℝ} (hX : Measurable X) (e : Bond 2) :
    Measurable (bondFlipDiff X e) :=
  (hX.comp (measurable_setBond e true)).sub (hX.comp (measurable_setBond e false))

theorem measurable_restrictExcept (e : Bond 2) :
    Measurable (fun (ω : Configuration 2) (b : {b : Bond 2 // b ≠ e}) => ω b) :=
  measurable_pi_lambda _ fun b => measurable_pi_apply (b : Bond 2)

theorem bondsExcept_le (e : Bond 2) :
    bondsExcept e ≤ (inferInstance : MeasurableSpace (Configuration 2)) :=
  (measurable_restrictExcept e).comap_le

/-- The configuration of the bonds other than `e`, extended by closing `e`. -/
def extendExcept (e : Bond 2) (r : {b : Bond 2 // b ≠ e} → Bool) : Configuration 2 :=
  fun b => if h : b = e then false else r ⟨b, h⟩

theorem measurable_extendExcept (e : Bond 2) : Measurable (extendExcept e) := by
  refine measurable_pi_lambda _ fun b => ?_
  by_cases h : b = e
  · simp only [extendExcept, dif_pos h]
    exact measurable_const
  · simp only [extendExcept, dif_neg h]
    exact measurable_pi_apply _

section CondExp

variable (p : unitInterval)

theorem latticeBondLaw_two_eq :
    latticeBondLaw 2 p = Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure true false p) :=
  rfl

/-- Averaging out the bond `e` is the two-point average. -/
theorem partialInt_compl_singleton (X : Configuration 2 → ℝ) (e : Bond 2) (ω : Configuration 2) :
    LatticeProb.partialInt (fun _ : Bond 2 => bernoulliMeasure true false p)
        ({e}ᶜ : Set (Bond 2)) X ω =
      (p : ℝ) * X (setBond e true ω) + (1 - p) * X (setBond e false ω) := by
  unfold LatticeProb.partialInt
  simp_rw [LatticeProb.comb_compl_singleton]
  have hmp := measurePreserving_eval_infinitePi
    (fun _ : Bond 2 => bernoulliMeasure true false p) e
  have h := integral_map (μ := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure true false p))
    (φ := Function.eval e) (f := fun b : Bool => X (Function.update ω e b))
    hmp.measurable.aemeasurable (Measurable.of_discrete).aestronglyMeasurable
  rw [hmp.map_eq, integral_bernoulliMeasure] at h
  rw [← h]
  simp only [smul_eq_mul, setBond]

/-- **The conditional expectation given the other bonds is the two-point average**:
`E[X | F(𝓑_d \ {e})] = p X(ω^{e,1}) + (1 - p) X(ω^{e,0})` almost surely. -/
theorem condExp_bondsExcept_ae_eq {X : Configuration 2 → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw 2 p)) (e : Bond 2) :
    condExp (bondsExcept e) (latticeBondLaw 2 p) X =ᵐ[latticeBondLaw 2 p]
      fun ω => (p : ℝ) * X (setBond e true ω) + (1 - p) * X (setBond e false ω) := by
  set μ := fun _ : Bond 2 => bernoulliMeasure true false p with hμ
  set S : Set (Bond 2) := {e}ᶜ with hS
  have hPI : Integrable (LatticeProb.partialInt μ S X) (latticeBondLaw 2 p) :=
    LatticeProb.integrable_partialInt μ S hX
  have hmeasS : Measurable[bondsExcept e] (LatticeProb.partialInt μ S X) := by
    have hfac : LatticeProb.partialInt μ S X =
        (LatticeProb.partialInt μ S X ∘ extendExcept e) ∘
          (fun (ω : Configuration 2) (b : {b : Bond 2 // b ≠ e}) => ω b) := by
      funext ω
      refine LatticeProb.partialInt_congr μ S X fun b hb => ?_
      have hb' : b ≠ e := hb
      simp only [extendExcept, dif_neg hb']
    rw [hfac]
    exact ((LatticeProb.measurable_partialInt μ S hXm).comp (measurable_extendExcept e)).comp
      (comap_measurable _)
  have key : LatticeProb.partialInt μ S X =ᵐ[latticeBondLaw 2 p]
      condExp (bondsExcept e) (latticeBondLaw 2 p) X := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (bondsExcept_le e) hX
      (fun s _ _ => hPI.integrableOn) (fun s hs _ => ?_)
      hmeasS.stronglyMeasurable.aestronglyMeasurable
    have hsm : MeasurableSet s := bondsExcept_le e s hs
    set χ : Configuration 2 → ℝ := s.indicator (fun _ => (1 : ℝ)) with hχdef
    have hmul : ∀ (g : Configuration 2 → ℝ) (x : Configuration 2), χ x * g x = s.indicator g x := by
      intro g x
      by_cases hx : x ∈ s <;> simp [hχdef, hx]
    have hloc : ∀ ω η : Configuration 2, χ (LatticeProb.comb S ω η) = χ ω := by
      intro ω η
      have hmem : LatticeProb.comb S ω η ∈ s ↔ ω ∈ s := by
        obtain ⟨t, -, rfl⟩ := hs
        have hr : (fun b : {b : Bond 2 // b ≠ e} => LatticeProb.comb S ω η b) =
            fun b : {b : Bond 2 // b ≠ e} => ω b := by
          funext b
          exact LatticeProb.comb_apply_of_mem (show (b : Bond 2) ∈ S from b.2)
        simp only [Set.mem_preimage, hr]
      by_cases hx : ω ∈ s
      · simp [hχdef, hx, hmem.2 hx]
      · simp [hχdef, hx, show LatticeProb.comb S ω η ∉ s from fun h => hx (hmem.1 h)]
    have hint : Integrable (fun ω => χ ω * X ω) (latticeBondLaw 2 p) := by
      have : (fun ω => χ ω * X ω) = s.indicator X := funext fun x => hmul X x
      rw [this]
      exact hX.indicator hsm
    have hkey := LatticeProb.integral_mul_partialInt μ (F := X) (g := χ) S hloc hint
    rw [← integral_indicator hsm, ← integral_indicator hsm]
    calc ∫ x, s.indicator (LatticeProb.partialInt μ S X) x ∂(latticeBondLaw 2 p)
        = ∫ x, χ x * LatticeProb.partialInt μ S X x ∂(latticeBondLaw 2 p) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hmul _ x).symm)
      _ = ∫ x, χ x * X x ∂(latticeBondLaw 2 p) := hkey
      _ = ∫ x, s.indicator X x ∂(latticeBondLaw 2 p) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hmul X x)
  filter_upwards [key] with ω hω
  rw [← hω]
  exact partialInt_compl_singleton p X e ω

/-- The distance of `X` to the two-point average is at most the flip difference. -/
theorem sq_sub_twoPoint_le (X : Configuration 2 → ℝ) (e : Bond 2) (ω : Configuration 2) :
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

theorem ae_sq_sub_condExp_le {X : Configuration 2 → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw 2 p)) (e : Bond 2) :
    ∀ᵐ ω ∂latticeBondLaw 2 p,
      (X ω - condExp (bondsExcept e) (latticeBondLaw 2 p) X ω) ^ 2 ≤ bondFlipDiff X e ω ^ 2 := by
  filter_upwards [condExp_bondsExcept_ae_eq p hXm hX e] with ω hω
  rw [hω]
  exact sq_sub_twoPoint_le p X e ω

/-- **The resampling variance is at most the sum of the squared flip differences**:
`𝕍[X] ≤ Σ_e (X(ω^{e,1}) - X(ω^{e,0}))²` almost surely. -/
theorem ae_resampleVar_le_tsum_bondFlipDiff {X : Configuration 2 → ℝ} (hXm : Measurable X)
    (hX : Integrable X (latticeBondLaw 2 p)) :
    ∀ᵐ ω ∂latticeBondLaw 2 p,
      resampleVar p X ω ≤ ∑' e, ENNReal.ofReal (bondFlipDiff X e ω ^ 2) := by
  have h := ae_all_iff.2 fun e => ae_sq_sub_condExp_le p hXm hX e
  filter_upwards [h] with ω hω
  exact ENNReal.tsum_le_tsum fun e => ENNReal.ofReal_le_ofReal (hω e)

end CondExp

section Flip

variable (p : unitInterval)

theorem lintegral_bernoulliMeasure_bool (g : Bool → ℝ≥0∞) :
    ∫⁻ b, g b ∂(bernoulliMeasure true false p) =
      ENNReal.ofReal p * g true + ENNReal.ofReal (1 - p) * g false := by
  have h1 : (unitInterval.toNNReal p : ℝ≥0∞) = ENNReal.ofReal p := by
    rw [ENNReal.ofReal]
    congr 1
    ext
    rw [unitInterval.coe_toNNReal, Real.coe_toNNReal _ p.2.1]
  have h2 : (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) = ENNReal.ofReal (1 - p) := by
    rw [ENNReal.ofReal]
    congr 1
    ext
    rw [unitInterval.coe_toNNReal, Real.coe_toNNReal _ (by linarith [p.2.2]),
      unitInterval.coe_symm_eq]
  rw [bernoulliMeasure_def, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    h1, h2]

/-- **Forcing the state of one bond**: `∫ f = p ∫ f(ω^{e,1}) + (1 - p) ∫ f(ω^{e,0})`. -/
theorem lintegral_eq_setBond {f : Configuration 2 → ℝ≥0∞} (hf : Measurable f) (e : Bond 2) :
    ∫⁻ ω, f ω ∂latticeBondLaw 2 p =
      ENNReal.ofReal p * ∫⁻ ω, f (setBond e true ω) ∂latticeBondLaw 2 p +
        ENNReal.ofReal (1 - p) * ∫⁻ ω, f (setBond e false ω) ∂latticeBondLaw 2 p := by
  have hT := LatticeProb.measurePreserving_update_infinitePi
    (fun _ : Bond 2 => bernoulliMeasure true false p) e
  have hft : Measurable fun ω => f (setBond e true ω) := hf.comp (measurable_setBond e true)
  have hff : Measurable fun ω => f (setBond e false ω) := hf.comp (measurable_setBond e false)
  calc ∫⁻ ω, f ω ∂latticeBondLaw 2 p
      = ∫⁻ z, f (Function.update z.1 e z.2)
          ∂((Measure.infinitePi fun _ : Bond 2 => bernoulliMeasure true false p).prod
            (bernoulliMeasure true false p)) := (hT.lintegral_comp hf).symm
    _ = ∫⁻ ω, ∫⁻ b, f (Function.update ω e b) ∂(bernoulliMeasure true false p)
          ∂(latticeBondLaw 2 p) := lintegral_prod _ (hf.comp hT.measurable).aemeasurable
    _ = ∫⁻ ω, (ENNReal.ofReal p * f (setBond e true ω) +
          ENNReal.ofReal (1 - p) * f (setBond e false ω)) ∂latticeBondLaw 2 p := by
        congr 1
        funext ω
        exact lintegral_bernoulliMeasure_bool p _
    _ = ENNReal.ofReal p * ∫⁻ ω, f (setBond e true ω) ∂latticeBondLaw 2 p +
          ENNReal.ofReal (1 - p) * ∫⁻ ω, f (setBond e false ω) ∂latticeBondLaw 2 p := by
        rw [lintegral_add_left (hft.const_mul _), lintegral_const_mul _ hft,
          lintegral_const_mul _ hff]

/-- The two weights of the forced bond. -/
noncomputable def bondWeight (b : Bool) : ℝ :=
  if b then (p : ℝ) else 1 - p

theorem bondWeight_le_one (b : Bool) : bondWeight p b ≤ 1 := by
  unfold bondWeight
  split_ifs
  · exact p.2.2
  · linarith [p.2.1]

theorem ofReal_bondWeight_mul_lintegral_setBond_le {f : Configuration 2 → ℝ≥0∞}
    (hf : Measurable f) (e : Bond 2) (b : Bool) :
    ENNReal.ofReal (bondWeight p b) * ∫⁻ ω, f (setBond e b ω) ∂latticeBondLaw 2 p ≤
      ∫⁻ ω, f ω ∂latticeBondLaw 2 p := by
  rw [lintegral_eq_setBond p hf e]
  cases b
  · exact le_add_self
  · exact le_self_add

/-- **`O_s` bounds survive forcing one bond** (the form of Dario's (3.12) used here): if
`Z ≤ O_s(θ)` and `q > 0` is the weight of the forced state, then
`Z(ω^{e,b}) ≤ O_s(θ (2/q)^{1/s})`. -/
theorem IsOsBond.comp_setBond {Z : Configuration 2 → ℝ} (hZ : Measurable Z) {s θ : ℝ}
    (hs : 0 < s) (h : IsOsBond 2 p Z s θ) (e : Bond 2) (b : Bool) (hq : 0 < bondWeight p b) :
    IsOsBond 2 p (fun ω => Z (setBond e b ω)) s (θ * (2 / bondWeight p b) ^ (1 / s)) := by
  set q := bondWeight p b with hqdef
  set g : Configuration 2 → ℝ := fun ω => Real.exp (Real.rpow (max (Z ω / θ) 0) s) with hg
  have hgm : Measurable g :=
    Real.measurable_exp.comp (((hZ.div_const θ).max measurable_const).pow_const s)
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => (Real.exp_pos _).le
  obtain ⟨hint, hle⟩ := h
  have hlin : ∫⁻ ω, ENNReal.ofReal (g ω) ∂latticeBondLaw 2 p ≤ ENNReal.ofReal 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hg0)]
    exact ENNReal.ofReal_le_ofReal hle
  have hflip := ofReal_bondWeight_mul_lintegral_setBond_le p (f := fun ω => ENNReal.ofReal (g ω))
    (ENNReal.measurable_ofReal.comp hgm) e b
  have hq1 : q ≤ 1 := bondWeight_le_one p b
  have hlin' : ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (2 / q) := by
    have h1 : ENNReal.ofReal q * ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw 2 p ≤
        ENNReal.ofReal 2 := hflip.trans hlin
    have hq' : ENNReal.ofReal q ≠ 0 := by simp [hq]
    have hq'' : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw 2 p
        = (ENNReal.ofReal q)⁻¹ * (ENNReal.ofReal q *
            ∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw 2 p) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hq' hq'', one_mul]
      _ ≤ (ENNReal.ofReal q)⁻¹ * ENNReal.ofReal 2 := by gcongr
      _ = ENNReal.ofReal (2 / q) := by
          rw [ENNReal.ofReal_div_of_pos hq, ENNReal.div_eq_inv_mul]
  have hgsm : Measurable fun ω => g (setBond e b ω) := hgm.comp (measurable_setBond e b)
  have hint' : Integrable (fun ω => g (setBond e b ω)) (latticeBondLaw 2 p) := by
    refine ⟨hgsm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp only [Real.enorm_eq_ofReal (hg0 _)]
    exact lt_of_le_of_lt hlin' ENNReal.ofReal_lt_top
  have hA : 1 ≤ 2 / q := by
    rw [le_div_iff₀ hq]
    linarith
  have hle' : ∫ ω, g (setBond e b ω) ∂latticeBondLaw 2 p ≤ 2 / q := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => hg0 _)
      hgsm.aestronglyMeasurable]
    have h2q : (0 : ℝ) ≤ 2 / q := by positivity
    calc (∫⁻ ω, ENNReal.ofReal (g (setBond e b ω)) ∂latticeBondLaw 2 p).toReal
        ≤ (ENNReal.ofReal (2 / q)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin'
      _ = 2 / q := ENNReal.toReal_ofReal h2q
  exact Rigidity.Proofs.S2.isOsBond_of_integral_le hs hA hint' hle'

end Flip

end Rigidity.Corrector
