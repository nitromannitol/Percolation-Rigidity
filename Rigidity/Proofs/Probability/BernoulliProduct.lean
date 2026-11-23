import LatticeProb.Prob.UpdateSite
import LatticeProb.Prob.EfronSteinSigma
import LatticeProb.Prob.IndepPi
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.CondVar

/-!
# Conditional expectations under the product Bernoulli law

For an index type `ι` and `p ∈ [0, 1]`, `bernProd ι p` is the product of Bernoulli laws of
parameter `p` on `ι → Bool`. For a set `A` of coordinates, `coordSigma A` is the σ-algebra of the
coordinates in `A`, and `allExcept e` the σ-algebra of the coordinates other than `e` (the
σ-algebra `F(𝓑_d \ {e})` of Dario, Proposition 2.17, when `ι` is the set of lattice bonds).

* `indep_coordSigma`: coordinates in disjoint sets are independent;
* `condExp_allExcept_ae_eq`: `E[X | F(other coordinates)] = p X(ω^{e,1}) + (1 - p) X(ω^{e,0})`,
  where `ω^{e,b}` is `ω` with the coordinate `e` set to `b`;
* `condExp_allExcept_condExp_ae_eq`, `condExp_condExp_allExcept_ae_eq`: for `e ∈ S`, conditioning
  on `F(S)` and on `F(other coordinates than e)` in either order gives `E[X | F(S \ {e})]`;
  hence (`vertical_condExp_ae_eq`) the vertical derivative of `E[X | F(S)]` in `e` is the
  conditional expectation on `F(S)` of the vertical derivative of `X`, and it vanishes for
  `e ∉ S`.
-/

namespace Rigidity.Probability

open MeasureTheory ProbabilityTheory

variable {ι : Type*}

/-- The product of Bernoulli laws of parameter `p` on `ι → Bool`. -/
noncomputable def bernProd (ι : Type*) (p : unitInterval) : Measure (ι → Bool) :=
  Measure.infinitePi fun _ : ι => bernoulliMeasure true false p

instance (p : unitInterval) : IsProbabilityMeasure (bernProd ι p) := by
  unfold bernProd
  infer_instance

/-- The σ-algebra of the coordinates in `A`. -/
abbrev coordSigma (A : Set ι) : MeasurableSpace (ι → Bool) :=
  ⨆ i ∈ A, MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance

/-- The σ-algebra `F(ι \ {e})` of the coordinates other than `e`. -/
abbrev allExcept (e : ι) : MeasurableSpace (ι → Bool) :=
  MeasurableSpace.comap (fun (ω : ι → Bool) (b : {b : ι // b ≠ e}) => ω b) inferInstance

theorem comap_eval_le (i : ι) :
    MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance ≤
      (inferInstance : MeasurableSpace (ι → Bool)) :=
  (measurable_pi_apply i).comap_le

theorem coordSigma_le (A : Set ι) : coordSigma A ≤ (inferInstance : MeasurableSpace (ι → Bool)) :=
  iSup₂_le fun i _ => comap_eval_le i

theorem coordSigma_mono {A B : Set ι} (h : A ⊆ B) : coordSigma A ≤ coordSigma B :=
  iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : i ∈ B) =>
    MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) i (h hi)

theorem coordSigma_union (A B : Set ι) : coordSigma (A ∪ B) = coordSigma A ⊔ coordSigma B :=
  iSup_union

theorem allExcept_eq (e : ι) : allExcept e = coordSigma ({e}ᶜ : Set ι) := by
  rw [allExcept, LatticeProb.comap_pi_eq_iSup (fun (b : {b : ι // b ≠ e}) (ω : ι → Bool) => ω b)]
  refine le_antisymm (iSup_le fun b => ?_) (iSup₂_le fun i hi => ?_)
  · exact le_iSup₂ (f := fun i (_ : i ∈ ({e}ᶜ : Set ι)) =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) b.1 b.2
  · exact le_iSup (fun b : {b : ι // b ≠ e} =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω b) inferInstance) ⟨i, hi⟩

theorem allExcept_le (e : ι) : allExcept e ≤ (inferInstance : MeasurableSpace (ι → Bool)) := by
  rw [allExcept_eq]; exact coordSigma_le _

theorem comap_restrict_eq (S : Finset ι) :
    MeasurableSpace.comap (S.restrict : (ι → Bool) → (S → Bool)) inferInstance =
      coordSigma (S : Set ι) := by
  rw [show (S.restrict : (ι → Bool) → (S → Bool)) = fun ω (i : S) => ω i from rfl,
    LatticeProb.comap_pi_eq_iSup (fun (i : S) (ω : ι → Bool) => ω i)]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun i hi => ?_)
  · exact le_iSup₂ (f := fun i (_ : i ∈ (S : Set ι)) =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) i.1 i.2
  · exact le_iSup (fun i : S =>
      MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance) ⟨i, hi⟩

theorem iIndep_coord (p : unitInterval) :
    iIndep (fun i => MeasurableSpace.comap (fun ω : ι → Bool => ω i) inferInstance)
      (bernProd ι p) := by
  have h := iIndepFun_infinitePi (P := fun _ : ι => bernoulliMeasure true false p)
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  exact (iIndepFun_iff_iIndep (fun _ => inferInstance) _ _).1 h

/-- Coordinates in disjoint sets are independent. -/
theorem indep_coordSigma (p : unitInterval) {A B : Set ι} (h : Disjoint A B) :
    Indep (coordSigma A) (coordSigma B) (bernProd ι p) :=
  indep_iSup_of_disjoint comap_eval_le (iIndep_coord p) h

section Explicit

variable [DecidableEq ι] (p : unitInterval)

/-- The average over the coordinate `e`: `p X(ω^{e,1}) + (1 - p) X(ω^{e,0})`. -/
noncomputable def updAvg (e : ι) (X : (ι → Bool) → ℝ) (ω : ι → Bool) : ℝ :=
  (p : ℝ) * X (Function.update ω e true) + (1 - (p : ℝ)) * X (Function.update ω e false)

omit [DecidableEq ι] in
theorem measurable_update_const [DecidableEq ι] (e : ι) (b : Bool) :
    Measurable fun ω : ι → Bool => Function.update ω e b := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i = e
  · subst h
    simp only [Function.update_self]
    exact measurable_const
  · simp only [Function.update_of_ne h]
    exact measurable_pi_apply i

theorem measurable_updAvg (e : ι) {X : (ι → Bool) → ℝ} (hX : Measurable X) :
    Measurable (updAvg p e X) := by
  unfold updAvg
  exact (measurable_const.mul (hX.comp (measurable_update_const e true))).add
    (measurable_const.mul (hX.comp (measurable_update_const e false)))

theorem updAvg_eq_integral (e : ι) (X : (ι → Bool) → ℝ) (ω : ι → Bool) :
    updAvg p e X ω = ∫ c, X (Function.update ω e c) ∂(bernoulliMeasure true false p) := by
  rw [integral_bernoulliMeasure]
  simp only [updAvg, smul_eq_mul]

theorem updAvg_update (e : ι) (X : (ι → Bool) → ℝ) (ω : ι → Bool) (b : Bool) :
    updAvg p e X (Function.update ω e b) = updAvg p e X ω := by
  simp only [updAvg, Function.update_idem]

/-- The average over the coordinate `e` is measurable for the coordinates other than `e`. -/
theorem measurable_allExcept_updAvg (e : ι) {X : (ι → Bool) → ℝ} (hX : Measurable X) :
    Measurable[allExcept e] (updAvg p e X) := by
  set J : ({b : ι // b ≠ e} → Bool) → (ι → Bool) :=
    fun y i => if h : i = e then false else y ⟨i, h⟩ with hJ_def
  have hJ : Measurable J := by
    refine measurable_pi_lambda _ fun i => ?_
    by_cases h : i = e
    · simp only [hJ_def, h, dif_pos]
      exact measurable_const
    · simp only [hJ_def, h, dif_neg, not_false_eq_true]
      exact measurable_pi_apply _
  have hfac : updAvg p e X =
      (updAvg p e X ∘ J) ∘ (fun (ω : ι → Bool) (b : {b : ι // b ≠ e}) => ω b) := by
    funext ω
    have hJω : J (fun b : {b : ι // b ≠ e} => ω b) = Function.update ω e false := by
      funext i
      by_cases h : i = e
      · subst h
        simp [hJ_def]
      · simp [hJ_def, h]
    simp only [Function.comp_apply, hJω, updAvg_update]
  rw [hfac]
  exact ((measurable_updAvg p e hX).comp hJ).comp (comap_measurable _)

/-- **The conditional expectation on the coordinates other than `e`** is the average over the
coordinate `e`. -/
theorem condExp_allExcept_ae_eq (e : ι) {X : (ι → Bool) → ℝ} (hXm : Measurable X)
    (hX : Integrable X (bernProd ι p)) :
    (bernProd ι p)[X | allExcept e] =ᵐ[bernProd ι p] updAvg p e X := by
  unfold bernProd at hX ⊢
  have hmp := LatticeProb.measurePreserving_update_infinitePi
    (fun _ : ι => bernoulliMeasure true false p) e
  have hint2 : Integrable (fun q : (ι → Bool) × Bool => X (Function.update q.1 e q.2))
      ((Measure.infinitePi fun _ : ι => bernoulliMeasure true false p).prod
        (bernoulliMeasure true false p)) :=
    hmp.integrable_comp_of_integrable hX
  have hR : Integrable (updAvg p e X)
      (Measure.infinitePi fun _ : ι => bernoulliMeasure true false p) := by
    refine hint2.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (updAvg_eq_integral p e X ω).symm
  refine (ae_eq_condExp_of_forall_setIntegral_eq (allExcept_le e) hX
    (fun s _ _ => hR.integrableOn) ?_
    (measurable_allExcept_updAvg p e hXm).stronglyMeasurable.aestronglyMeasurable).symm
  intro s hs _
  have hsm : MeasurableSet s := allExcept_le e s hs
  have hinv : ∀ (ω : ι → Bool) (c : Bool), Function.update ω e c ∈ s ↔ ω ∈ s := by
    obtain ⟨B, _, rfl⟩ := hs
    intro ω c
    simp only [Set.mem_preimage]
    have : (fun b : {b : ι // b ≠ e} => Function.update ω e c b) =
        fun b : {b : ι // b ≠ e} => ω b :=
      funext fun b => Function.update_of_ne b.2 _ _
    rw [this]
  rw [← integral_indicator hsm, ← integral_indicator hsm,
    LatticeProb.integral_infinitePi_update_eq_integral_integral
      (fun _ => bernoulliMeasure true false p) e (hX.indicator hsm)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ s
  · rw [Set.indicator_of_mem hω, updAvg_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    dsimp only
    rw [Set.indicator_of_mem ((hinv ω c).2 hω)]
  · rw [Set.indicator_of_notMem hω]
    have h0 : (fun c => s.indicator X (Function.update ω e c)) = fun _ => (0 : ℝ) :=
      funext fun c => Set.indicator_of_notMem (fun h => hω ((hinv ω c).1 h)) _
    dsimp only
    rw [h0, integral_zero]

end Explicit

section Commute

variable (p : unitInterval)

/-- For `e ∈ S`: conditioning on `F(S)` and then on the coordinates other than `e` gives
`E[X | F(S \ {e})]`. -/
theorem condExp_allExcept_condExp_ae_eq {S : Set ι} {e : ι} (he : e ∈ S)
    (X : (ι → Bool) → ℝ) :
    (bernProd ι p)[(bernProd ι p)[X | coordSigma S] | allExcept e] =ᵐ[bernProd ι p]
      (bernProd ι p)[X | coordSigma (S \ {e})] := by
  have hsplit : allExcept e = coordSigma Sᶜ ⊔ coordSigma (S \ {e}) := by
    rw [allExcept_eq, ← coordSigma_union]
    congr 1
    ext i
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_sdiff]
    constructor
    · intro h
      by_cases hi : i ∈ S
      · exact Or.inr ⟨hi, h⟩
      · exact Or.inl hi
    · rintro (h | ⟨_, h⟩)
      · rintro rfl
        exact h he
      · exact h
  rw [hsplit]
  have h1 := LatticeProb.condExp_sup_indep_eq (μ := bernProd ι p)
    (A := coordSigma (S \ {e})) (G := coordSigma Sᶜ) (H := coordSigma S)
    (Y := (bernProd ι p)[X | coordSigma S]) (coordSigma_mono Set.sdiff_subset) (coordSigma_le S) (coordSigma_le _)
    (indep_coordSigma p disjoint_compl_left) stronglyMeasurable_condExp integrable_condExp
  exact h1.trans (condExp_condExp_of_le (coordSigma_mono Set.sdiff_subset) (coordSigma_le S))

/-- For `e ∈ S`: conditioning on the coordinates other than `e` and then on `F(S)` gives
`E[X | F(S \ {e})]`. -/
theorem condExp_condExp_allExcept_ae_eq {S : Set ι} {e : ι} (he : e ∈ S)
    (X : (ι → Bool) → ℝ) :
    (bernProd ι p)[(bernProd ι p)[X | allExcept e] | coordSigma S] =ᵐ[bernProd ι p]
      (bernProd ι p)[X | coordSigma (S \ {e})] := by
  have hsplit : coordSigma S = coordSigma {e} ⊔ coordSigma (S \ {e}) := by
    rw [← coordSigma_union, Set.union_sdiff_cancel (Set.singleton_subset_iff.2 he)]
  have hAH : coordSigma (S \ {e}) ≤ allExcept e := by
    rw [allExcept_eq]
    exact coordSigma_mono fun i hi => hi.2
  rw [hsplit]
  have h1 := LatticeProb.condExp_sup_indep_eq (μ := bernProd ι p)
    (A := coordSigma (S \ {e})) (G := coordSigma {e}) (H := allExcept e)
    (Y := (bernProd ι p)[X | allExcept e]) hAH (allExcept_le e)
    (coordSigma_le _) (by rw [allExcept_eq]; exact indep_coordSigma p disjoint_compl_right)
    stronglyMeasurable_condExp integrable_condExp
  exact h1.trans (condExp_condExp_of_le hAH (allExcept_le e))

/-- **The vertical derivative of `E[X | F(S)]`** in a coordinate `e ∈ S` is the conditional
expectation on `F(S)` of the vertical derivative of `X`. -/
theorem vertical_condExp_ae_eq {S : Set ι} {e : ι} (he : e ∈ S) {X : (ι → Bool) → ℝ}
    (hX : Integrable X (bernProd ι p)) :
    (fun ω => (bernProd ι p)[X | coordSigma S] ω -
        (bernProd ι p)[(bernProd ι p)[X | coordSigma S] | allExcept e] ω) =ᵐ[bernProd ι p]
      (bernProd ι p)[fun ω => X ω - (bernProd ι p)[X | allExcept e] ω | coordSigma S] := by
  have h1 := condExp_allExcept_condExp_ae_eq p he X
  have h2 := condExp_condExp_allExcept_ae_eq p he X
  have h3 := condExp_sub (m := coordSigma S) hX
    (integrable_condExp (m := allExcept e) (f := X) (μ := bernProd ι p))
  filter_upwards [h1, h2, h3] with ω h1ω h2ω h3ω
  have e3 : (bernProd ι p)[fun ω => X ω - (bernProd ι p)[X | allExcept e] ω | coordSigma S] ω =
      (bernProd ι p)[X - (bernProd ι p)[X | allExcept e] | coordSigma S] ω := rfl
  rw [e3, h3ω, Pi.sub_apply, h1ω, h2ω]

/-- For `e ∉ S`, `E[X | F(S)]` does not depend on the coordinate `e`. -/
theorem condExp_allExcept_condExp_of_notMem {S : Set ι} {e : ι} (he : e ∉ S)
    (X : (ι → Bool) → ℝ) :
    (bernProd ι p)[(bernProd ι p)[X | coordSigma S] | allExcept e] =
      (bernProd ι p)[X | coordSigma S] := by
  have hle : coordSigma S ≤ allExcept e := by
    rw [allExcept_eq]
    exact coordSigma_mono fun i hi h => he (by rw [Set.mem_singleton_iff] at h; exact h ▸ hi)
  exact condExp_of_stronglyMeasurable (allExcept_le e) (stronglyMeasurable_condExp.mono hle)
    integrable_condExp

end Commute

end Rigidity.Probability
