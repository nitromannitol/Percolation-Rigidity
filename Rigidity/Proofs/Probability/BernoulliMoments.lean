import Rigidity.Proofs.Probability.BernoulliCylinder
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The moment inequality for the product Bernoulli law on countably many coordinates

For `p ∈ (0, 1)`, `c = min(p, 1 - p)`, `q ≥ 2` and an integrable `X` on `ι → Bool` (`ι`
countable) with `𝕍[X] = Σ_e (X - E[X | F(ι \ {e})])² < ∞` almost surely,

  `E[|X - E X|^q] ≤ 2 (3q/c)^{q/2} E[𝕍[X]^{q/2}]`.

This is the moment inequality used by Armstrong and Lin (proof of their Proposition 2.2), here for
Bernoulli coordinates. It is proved on the finite cube (`cubeExp_abs_sub_rpow_le`) and carried to
countably many coordinates by the conditional expectations `X_S = E[X | F(S)]` on finite sets `S`:
`X_S` is a function of the coordinates in `S` (`lintegral_abs_condExp_sub_rpow_le`), its vertical
derivatives are the conditional expectations of those of `X` (`vertical_condExp_ae_eq`), so that
`𝕍[X_S] ≤ E[𝕍[X] | F(S)]` and `E[𝕍[X_S]^{q/2}] ≤ E[𝕍[X]^{q/2}]`
(`lintegral_vertSum_condExp_le`, by the conditional Jensen inequality), and `X_S → X` almost
surely along an exhaustion of `ι` (Lévy's upward theorem), so Fatou's lemma concludes
(`lintegral_abs_sub_rpow_le_vertSum`).
-/

namespace Rigidity.Probability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {ι : Type*}

/-- **Conditional Jensen for powers**: `E[E[W | m]^r] ≤ E[W^r]` for `W ≥ 0` and `r ≥ 1`. -/
theorem lintegral_ofReal_condExp_rpow_le {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} {W : Ω → ℝ}
    (hW0 : 0 ≤ᵐ[μ] W) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ ω, ENNReal.ofReal ((μ[W | m] ω) ^ r) ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (W ω ^ r) ∂μ := by
  have hr0 : 0 < r := by linarith
  have h := eLpNorm_condExp_le_eLpNorm (μ := μ) (m := m) W (p := ENNReal.ofReal r)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr)
  have hne0 : ENNReal.ofReal r ≠ 0 := by simp [hr0]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr0.le, ENNReal.rpow_le_rpow_iff (by positivity)] at h
  have hc0 : 0 ≤ᵐ[μ] μ[W | m] := condExp_nonneg hW0
  calc ∫⁻ ω, ENNReal.ofReal ((μ[W | m] ω) ^ r) ∂μ = ∫⁻ ω, ‖μ[W | m] ω‖ₑ ^ r ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hc0] with ω hω
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω,
          ENNReal.ofReal_rpow_of_nonneg hω hr0.le]
    _ ≤ ∫⁻ ω, ‖W ω‖ₑ ^ r ∂μ := h
    _ = ∫⁻ ω, ENNReal.ofReal (W ω ^ r) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hW0] with ω hω
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω,
          ENNReal.ofReal_rpow_of_nonneg hω hr0.le]

/-- **Conditional Jensen for squares**: `E[D | m]² ≤ E[D² | m]` for `D ∈ L²`. -/
theorem sq_condExp_ae_le {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m₀) {D : Ω → ℝ}
    (hD : MemLp D 2 μ) : (fun ω => (μ[D | m] ω) ^ 2) ≤ᵐ[μ] μ[fun ω => D ω ^ 2 | m] := by
  have h1 := condVar_ae_eq_condExp_sq_sub_sq_condExp hm hD
  have h2 : 0 ≤ᵐ[μ] Var[D; μ | m] := condExp_nonneg (Filter.Eventually.of_forall fun ω =>
    sq_nonneg _)
  filter_upwards [h1, h2] with ω h1ω h2ω
  rw [h1ω] at h2ω
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.zero_apply, sub_nonneg] at h2ω
  exact h2ω

section Bernoulli

variable [DecidableEq ι] (p : unitInterval)

/-- **The moment inequality for `E[X | F(S)]`**, `S` finite. -/
theorem lintegral_abs_condExp_sub_rpow_le [Countable ι] (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (S : Finset ι) (X : (ι → Bool) → ℝ) {q : ℝ} (hq : 2 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (|(bernProd ι p)[X | coordSigma S] ω -
        ∫ ω', X ω' ∂(bernProd ι p)| ^ q) ∂(bernProd ι p) ≤
      ENNReal.ofReal (2 * (3 / min (p : ℝ) (1 - p) * q) ^ (q / 2)) *
        ∫⁻ ω, ENNReal.ofReal ((vertSum p ((bernProd ι p)[X | coordSigma S]) ω).toReal ^
          (q / 2)) ∂(bernProd ι p) := by
  have hsm : StronglyMeasurable[MeasurableSpace.comap
      (S.restrict : (ι → Bool) → (S → Bool)) inferInstance]
      ((bernProd ι p)[X | coordSigma S]) := by
    rw [comap_restrict_eq]
    exact stronglyMeasurable_condExp
  obtain ⟨g, -, hg⟩ := hsm.exists_eq_measurable_comp
  have hmean : ∫ ω', X ω' ∂(bernProd ι p) = cubeExp (p : ℝ) g := by
    rw [← integral_condExp (coordSigma_le (S : Set ι)), hg, Function.comp_def,
      integral_comp_restrict]
  rw [hg, hmean]
  have hlhs : ∫⁻ ω, ENNReal.ofReal (|(g ∘ S.restrict) ω - cubeExp (p : ℝ) g| ^ q)
      ∂(bernProd ι p) =
      ENNReal.ofReal (cubeExp (p : ℝ) (fun x => |g x - cubeExp (p : ℝ) g| ^ q)) :=
    lintegral_comp_restrict p S (F := fun x => |g x - cubeExp (p : ℝ) g| ^ q)
      fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hrhs : ∫⁻ ω, ENNReal.ofReal ((vertSum p (g ∘ S.restrict) ω).toReal ^ (q / 2))
      ∂(bernProd ι p) =
      ENNReal.ofReal (cubeExp (p : ℝ) (fun x => vertVar (p : ℝ) g x ^ (q / 2))) := by
    rw [← lintegral_comp_restrict p S (F := fun x => vertVar (p : ℝ) g x ^ (q / 2))
      fun x => Real.rpow_nonneg (vertVar_nonneg _ g x) _]
    refine lintegral_congr_ae ?_
    filter_upwards [vertSum_comp_restrict p S g] with ω hω
    rw [hω, ENNReal.toReal_ofReal (vertVar_nonneg _ g _)]
  rw [hlhs, hrhs, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (cubeExp_abs_sub_rpow_le hp0 hp1 hq g)

omit [DecidableEq ι] in
theorem measurable_vertSum [Countable ι] {X : (ι → Bool) → ℝ} (hXm : Measurable X) :
    Measurable (vertSum p X) := by
  refine Measurable.tsum fun e => ?_
  have hc : Measurable ((bernProd ι p)[X | allExcept e]) :=
    (stronglyMeasurable_condExp.mono (allExcept_le e)).measurable
  exact ((hXm.sub hc).pow_const 2).ennreal_ofReal

omit [DecidableEq ι] in
/-- **Contraction of `E[𝕍^r]` under conditioning on finitely many coordinates.** -/
theorem lintegral_vertSum_condExp_le [Countable ι] (S : Finset ι) {X : (ι → Bool) → ℝ}
    (hXm : Measurable X) (hX : Integrable X (bernProd ι p))
    (hfin : ∀ᵐ ω ∂(bernProd ι p), vertSum p X ω < ∞) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ ω, ENNReal.ofReal ((vertSum p ((bernProd ι p)[X | coordSigma S]) ω).toReal ^ r)
        ∂(bernProd ι p) ≤
      ∫⁻ ω, ENNReal.ofReal ((vertSum p X ω).toReal ^ r) ∂(bernProd ι p) := by
  set μ := bernProd ι p with hμ
  set V : (ι → Bool) → ℝ := fun ω => (vertSum p X ω).toReal with hV_def
  have hV0 : ∀ ω, 0 ≤ V ω := fun ω => ENNReal.toReal_nonneg
  have hVm : Measurable V := (measurable_vertSum p hXm).ennreal_toReal
  by_cases hinf : ∫⁻ ω, ENNReal.ofReal (V ω ^ r) ∂μ = ∞
  · rw [hinf]
    exact le_top
  have hVr : Integrable (fun ω => V ω ^ r) μ := by
    refine ⟨(hVm.pow_const r).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (hV0 ω) r)]
    exact lt_top_iff_ne_top.2 hinf
  have hVi : Integrable V μ := by
    refine (hVr.add (integrable_const 1)).mono' hVm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 ω)]
    rcases le_total (V ω) 1 with h | h
    · have := Real.rpow_nonneg (hV0 ω) r
      simp only [Pi.add_apply]
      linarith
    · have := Real.self_le_rpow_of_one_le h hr
      simp only [Pi.add_apply]
      linarith
  set D : ι → (ι → Bool) → ℝ := fun e ω => X ω - μ[X | allExcept e] ω with hD_def
  have hDm : ∀ e, Measurable (D e) := fun e =>
    hXm.sub (stronglyMeasurable_condExp.mono (allExcept_le e)).measurable
  have hDV : ∀ e, ∀ᵐ ω ∂μ, D e ω ^ 2 ≤ V ω := by
    intro e
    filter_upwards [hfin] with ω hω
    rw [hV_def, ← ENNReal.ofReal_le_iff_le_toReal hω.ne]
    exact ENNReal.le_tsum (f := fun e => ENNReal.ofReal ((X ω - μ[X | allExcept e] ω) ^ 2)) e
  have hD2 : ∀ e, Integrable (fun ω => D e ω ^ 2) μ := fun e =>
    hVi.mono' ((hDm e).pow_const 2).aestronglyMeasurable (by
      filter_upwards [hDV e] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hω)
  have hDL2 : ∀ e, MemLp (D e) 2 μ := fun e =>
    (memLp_two_iff_integrable_sq (hDm e).aestronglyMeasurable).2 (hD2 e)
  set W : (ι → Bool) → ℝ := fun ω => ∑ e ∈ S, D e ω ^ 2 with hW_def
  have hW0 : 0 ≤ᵐ[μ] W := Filter.Eventually.of_forall fun ω =>
    Finset.sum_nonneg fun e _ => sq_nonneg _
  have hWV : ∀ᵐ ω ∂μ, W ω ≤ V ω := by
    filter_upwards [hfin] with ω hω
    rw [hV_def, ← ENNReal.ofReal_le_iff_le_toReal hω.ne, hW_def,
      ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _]
    exact ENNReal.sum_le_tsum (f := fun e => ENNReal.ofReal ((X ω - μ[X | allExcept e] ω) ^ 2)) S
  have hcondW : μ[W | coordSigma S] =ᵐ[μ] fun ω => ∑ e ∈ S, μ[fun ω => D e ω ^ 2 |
      coordSigma S] ω := by
    have h := condExp_finsetSum (μ := μ) (m := coordSigma S) (s := S)
      (f := fun e ω => D e ω ^ 2) (fun e _ => hD2 e)
    filter_upwards [h] with ω hω
    rw [show W = ∑ e ∈ S, fun ω => D e ω ^ 2 by
      funext ω; simp [hW_def, Finset.sum_apply]] at *
    rw [hω, Finset.sum_apply]
  have hvert : ∀ᵐ ω ∂μ, ∀ e ∈ S,
      μ[X | coordSigma S] ω - μ[μ[X | coordSigma S] | allExcept e] ω =
        μ[D e | coordSigma S] ω := by
    have : ∀ e : S, ∀ᵐ ω ∂μ, μ[X | coordSigma S] ω -
        μ[μ[X | coordSigma S] | allExcept (e : ι)] ω = μ[D (e : ι) | coordSigma S] ω :=
      fun e => vertical_condExp_ae_eq p (S := (S : Set ι)) (Finset.mem_coe.2 e.2) hX
    filter_upwards [ae_all_iff.2 this] with ω hω e he
    exact hω ⟨e, he⟩
  have hjensen : ∀ᵐ ω ∂μ, ∀ e ∈ S,
      (μ[D e | coordSigma S] ω) ^ 2 ≤ μ[fun ω => D e ω ^ 2 | coordSigma S] ω := by
    have : ∀ e : S, ∀ᵐ ω ∂μ, (μ[D (e : ι) | coordSigma S] ω) ^ 2 ≤
        μ[fun ω => D (e : ι) ω ^ 2 | coordSigma S] ω := fun e =>
      sq_condExp_ae_le (coordSigma_le _) (hDL2 (e : ι))
    filter_upwards [ae_all_iff.2 this] with ω hω e he
    exact hω ⟨e, he⟩
  have hpt : ∀ᵐ ω ∂μ, (vertSum p (μ[X | coordSigma S]) ω).toReal ≤ μ[W | coordSigma S] ω := by
    filter_upwards [hvert, hjensen, hcondW] with ω hvω hjω hcω
    have hsupp : vertSum p (μ[X | coordSigma S]) ω =
        ∑ e ∈ S, ENNReal.ofReal ((μ[D e | coordSigma S] ω) ^ 2) := by
      unfold vertSum
      rw [tsum_eq_sum (s := S) (fun e he => by
        rw [condExp_allExcept_condExp_of_notMem p (S := (S : Set ι))
          (fun h => he (Finset.mem_coe.1 h)) X]
        simp [hμ])]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hvω e he]
    rw [hsupp, ← ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun e _ => sq_nonneg _), hcω]
    exact Finset.sum_le_sum fun e he => hjω e he
  calc ∫⁻ ω, ENNReal.ofReal ((vertSum p (μ[X | coordSigma S]) ω).toReal ^ r) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((μ[W | coordSigma S] ω) ^ r) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with ω hω
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ENNReal.toReal_nonneg hω (by linarith))
    _ ≤ ∫⁻ ω, ENNReal.ofReal (W ω ^ r) ∂μ := lintegral_ofReal_condExp_rpow_le hW0 hr
    _ ≤ ∫⁻ ω, ENNReal.ofReal (V ω ^ r) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hWV, hW0] with ω hω hω0
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hω0 hω (by linarith))

end Bernoulli

end Rigidity.Probability
