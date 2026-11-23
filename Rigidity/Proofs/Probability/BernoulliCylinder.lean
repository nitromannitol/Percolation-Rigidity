import Rigidity.Proofs.Probability.BernoulliProduct
import Rigidity.Proofs.Probability.CubeMomentBound

/-!
# Functions of finitely many coordinates under the product Bernoulli law

For a finite set `S` of coordinates, the restriction `ω ↦ ω|_S` carries `bernProd ι p` to the
product Bernoulli law on the cube `S → Bool` (`Measure.infinitePi_map_restrict`), so integrals of
`g(ω|_S)` are the finite sums `cubeExp p g`, and the sum of the squared vertical derivatives
`vertSum p X = Σ_e (X - E[X | F(ι \ {e})])²` of `X = g(ω|_S)` is `vertVar p g (ω|_S)`.

* `vertSum p X`: the quantity `𝕍[X]` of Dario, Proposition 2.17, for coordinates indexed by `ι`;
* `lintegral_comp_restrict`, `integral_comp_restrict`: integrals of cylinder functions;
* `vertSum_comp_restrict`: `𝕍[g(ω|_S)] = vertVar p g (ω|_S)` almost surely;
* `lintegral_abs_sub_rpow_le_of_comp_restrict`: the moment inequality of the cube
  (`cubeExp_abs_sub_rpow_le`) for cylinder functions on the infinite product.
-/

namespace Rigidity.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*}

/-- `𝕍[X] = Σ_e (X - E[X | F(ι \ {e})])²`, in `ℝ≥0∞`. -/
noncomputable def vertSum (p : unitInterval) (X : (ι → Bool) → ℝ) (ω : ι → Bool) : ℝ≥0∞ :=
  ∑' e : ι, ENNReal.ofReal ((X ω - (bernProd ι p)[X | allExcept e] ω) ^ 2)

theorem bernoulliMeasure_singleton (p : unitInterval) (b : Bool) :
    bernoulliMeasure true false p {b} = ENNReal.ofReal (bernWeight p b) := by
  rw [bernoulliMeasure_apply p (measurableSet_singleton b)]
  cases b
  · simp only [Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte, bernWeight_false]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  · simp only [Set.mem_singleton_iff, ↓reduceIte, Bool.false_eq_true, bernWeight_true]
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl

section Cylinder

variable (p : unitInterval) (S : Finset ι)

theorem measurable_restrict_bool : Measurable (S.restrict : (ι → Bool) → (S → Bool)) :=
  Finset.measurable_restrict (X := fun _ : ι => Bool) S

theorem measure_pi_singleton (x : S → Bool) :
    (Measure.pi fun _ : S => bernoulliMeasure true false p) {x} =
      ENNReal.ofReal (cubeWeight (p : ℝ) x) := by
  rw [Measure.pi_singleton]
  simp_rw [bernoulliMeasure_singleton]
  rw [cubeWeight, ENNReal.ofReal_prod_of_nonneg fun i _ =>
    bernWeight_nonneg p.2.1 p.2.2 (x i)]

theorem map_restrict_bernProd :
    (bernProd ι p).map S.restrict = Measure.pi fun _ : S => bernoulliMeasure true false p := by
  unfold bernProd
  exact Measure.infinitePi_map_restrict (fun _ : ι => bernoulliMeasure true false p)

variable [DecidableEq ι]

theorem lintegral_comp_restrict {F : (S → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) :
    ∫⁻ ω, ENNReal.ofReal (F (S.restrict ω)) ∂(bernProd ι p) =
      ENNReal.ofReal (cubeExp (p : ℝ) F) := by
  rw [← lintegral_map (f := fun x => ENNReal.ofReal (F x)) (measurable_of_countable _)
    (measurable_restrict_bool S), map_restrict_bernProd, lintegral_fintype]
  simp_rw [measure_pi_singleton]
  rw [cubeExp, ENNReal.ofReal_sum_of_nonneg fun x _ =>
    mul_nonneg (cubeWeight_nonneg p.2.1 p.2.2 x) (hF x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_mul (cubeWeight_nonneg p.2.1 p.2.2 x), mul_comm]

theorem integral_comp_restrict (F : (S → Bool) → ℝ) :
    ∫ ω, F (S.restrict ω) ∂(bernProd ι p) = cubeExp (p : ℝ) F := by
  rw [← integral_map (measurable_restrict_bool S).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable, map_restrict_bernProd,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [measureReal_def, measure_pi_singleton,
    ENNReal.toReal_ofReal (cubeWeight_nonneg p.2.1 p.2.2 x), smul_eq_mul]

theorem restrict_update_of_mem {e : ι} (he : e ∈ S) (ω : ι → Bool) (b : Bool) :
    S.restrict (Function.update ω e b) = Function.update (S.restrict ω) ⟨e, he⟩ b := by
  funext i
  by_cases h : (i : ι) = e
  · have hi : i = ⟨e, he⟩ := Subtype.ext h
    subst hi
    simp
  · have hi : i ≠ ⟨e, he⟩ := fun hc => h (congrArg Subtype.val hc)
    simp [Finset.restrict, Function.update_of_ne h, Function.update_of_ne hi]

theorem restrict_update_of_notMem {e : ι} (he : e ∉ S) (ω : ι → Bool) (b : Bool) :
    S.restrict (Function.update ω e b) = S.restrict ω := by
  funext i
  have h : (i : ι) ≠ e := fun hc => he (hc ▸ i.2)
  simp [Finset.restrict, Function.update_of_ne h]

theorem updAvg_comp_restrict_of_mem {e : ι} (he : e ∈ S) (g : (S → Bool) → ℝ)
    (ω : ι → Bool) :
    updAvg p e (g ∘ S.restrict) ω = coordAvg (p : ℝ) ⟨e, he⟩ g (S.restrict ω) := by
  simp only [updAvg, coordAvg, Function.comp_apply, restrict_update_of_mem S he]

theorem updAvg_comp_restrict_of_notMem {e : ι} (he : e ∉ S) (g : (S → Bool) → ℝ)
    (ω : ι → Bool) : updAvg p e (g ∘ S.restrict) ω = g (S.restrict ω) := by
  simp only [updAvg, Function.comp_apply, restrict_update_of_notMem S he]
  ring

theorem integrable_comp_restrict (g : (S → Bool) → ℝ) :
    Integrable (g ∘ S.restrict) (bernProd ι p) := by
  refine (integrable_const (∑ x, |g x|)).mono'
    ((measurable_of_countable g).comp (measurable_restrict_bool S)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun x => |g x|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ _)

/-- **`𝕍` of a cylinder function**: `𝕍[g(ω|_S)] = vertVar p g (ω|_S)` almost surely. -/
theorem vertSum_comp_restrict [Countable ι] (g : (S → Bool) → ℝ) :
    vertSum p (g ∘ S.restrict) =ᵐ[bernProd ι p]
      fun ω => ENNReal.ofReal (vertVar (p : ℝ) g (S.restrict ω)) := by
  have hm : Measurable (g ∘ (S.restrict : (ι → Bool) → (S → Bool))) :=
    (measurable_of_countable g).comp (measurable_restrict_bool S)
  have hae : ∀ᵐ ω ∂(bernProd ι p), ∀ e : ι,
      (bernProd ι p)[g ∘ S.restrict | allExcept e] ω = updAvg p e (g ∘ S.restrict) ω :=
    ae_all_iff.2 fun e => condExp_allExcept_ae_eq p e hm (integrable_comp_restrict p S g)
  filter_upwards [hae] with ω hω
  unfold vertSum
  simp_rw [hω]
  rw [tsum_eq_sum (s := S) (fun e he => by
    rw [updAvg_comp_restrict_of_notMem p S he]
    simp)]
  rw [← Finset.sum_coe_sort S, vertVar,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [updAvg_comp_restrict_of_mem p S i.2]
  rfl

end Cylinder

end Rigidity.Probability
