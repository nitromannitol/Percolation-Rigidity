import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLimit

/-!
# Lower bound for the expectation of `ν` and for the homogenized matrix, in `ℤ^d`

Taking expectations in the deterministic lower bound of `CubeNuLowerBound`, with the moment
bounds of `CubeSizeMoments` for the partition sizes and the bound `C exp(-c 3^m)` on the
probability that `U` is not resolved, and choosing `κ = 1 / (2 d² C₃² M₁)`, we obtain

`(κ/2) |p|² ≤ E[ν(U, p)] + C |p|₁² / 3^{m/2}`

for every triadic cube `U` of scale `m` (Armstrong and Dario, Lemma 4.7, (4.31), in expectation,
with a deterministic choice of the slope `κ p` in place of their random one). Passing to the limit
gives the lower bound of (5.1) for the homogenized matrix: `c |ξ|² ≤ (1/2) ξ · ā ξ`.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- Integration of an almost sure linear bound. -/
theorem le_integral_add_of_ae_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} {g₀ g₁ g₂ g₃ g₄ : Ω → ℝ} (h₀ : Integrable g₀ μ)
    (h₁ : Integrable g₁ μ) (h₂ : Integrable g₂ μ) (h₃ : Integrable g₃ μ) (h₄ : Integrable g₄ μ)
    (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h : ∀ᵐ ω ∂μ, a ≤ g₀ ω + (c₁ * g₁ ω + c₂ * g₂ ω + c₃ * g₃ ω + c₄ * g₄ ω + c₅)) :
    a ≤ ∫ ω, g₀ ω ∂μ + (c₁ * ∫ ω, g₁ ω ∂μ + c₂ * ∫ ω, g₂ ω ∂μ + c₃ * ∫ ω, g₃ ω ∂μ +
      c₄ * ∫ ω, g₄ ω ∂μ + c₅) := by
  have i1 : Integrable (fun ω => c₁ * g₁ ω) μ := h₁.const_mul c₁
  have i2 : Integrable (fun ω => c₂ * g₂ ω) μ := h₂.const_mul c₂
  have i3 : Integrable (fun ω => c₃ * g₃ ω) μ := h₃.const_mul c₃
  have i4 : Integrable (fun ω => c₄ * g₄ ω) μ := h₄.const_mul c₄
  have i12 : Integrable (fun ω => c₁ * g₁ ω + c₂ * g₂ ω) μ := i1.add i2
  have i123 : Integrable (fun ω => c₁ * g₁ ω + c₂ * g₂ ω + c₃ * g₃ ω) μ := i12.add i3
  have i1234 : Integrable (fun ω => c₁ * g₁ ω + c₂ * g₂ ω + c₃ * g₃ ω + c₄ * g₄ ω) μ :=
    i123.add i4
  have i5 : Integrable (fun ω => c₁ * g₁ ω + c₂ * g₂ ω + c₃ * g₃ ω + c₄ * g₄ ω + c₅) μ :=
    i1234.add (integrable_const c₅)
  have ir : Integrable (fun ω => g₀ ω + (c₁ * g₁ ω + c₂ * g₂ ω + c₃ * g₃ ω + c₄ * g₄ ω + c₅))
      μ := h₀.add i5
  have hm := integral_mono_ae (integrable_const a) ir h
  rw [integral_const, integral_add h₀ i5, integral_add i1234 (integrable_const c₅),
    integral_add i123 i4, integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const] at hm
  simpa only [probReal_univ, smul_eq_mul, one_mul] using hm

/-- **The pointwise lower bound with the unresolved event.** On the partition event, the
deterministic lower bound holds with the extra term `κ |p|² 1{some partition size in U exceeds
the side of U}`, which takes care of the unresolved cubes. -/
theorem le_cubeNu_add_indicator (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω)
    (U : TriadicCube d) (p : Fin d → ℝ) (hp : 0 < ∑ i, |p i|) {κ : ℝ} (hκ : 0 < κ) :
    κ * ∑ i, p i ^ 2 ≤ cubeNu ω U p +
      d * coarseGradConstant d ^ 2 * κ ^ 2 * (∑ i, |p i|) ^ 2 *
        (∑ z ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) /
          U.latticeVolume +
      κ * (∑ i, p i ^ 2) / (3 : ℝ) ^ U.scale +
      κ * (∑ i, |p i|) ^ 2 * ((∑ i : Fin d,
        (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
          ∑ x ∈ U.toIntegerCube.lowerFace i,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)) / U.latticeVolume +
        3 ^ d * (4 * d * (∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
            (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
              then 1 else 0)) * √((3 : ℝ) ^ U.scale) / U.latticeVolume +
          1 / √((3 : ℝ) ^ U.scale)) / 2) +
      κ * (∑ i, p i ^ 2) * {ω : Configuration d | ∃ z ∈ U.toIntegerCube.vertices,
        (3 : ℝ) ^ U.scale < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z}.indicator 1 ω :=
    by
  have hvol := U.latticeVolume_pos
  have hS0 : 0 ≤ ∑ i, p i ^ 2 := by positivity
  have hI0 : (0 : ℝ) ≤ {ω : Configuration d | ∃ z ∈ U.toIntegerCube.vertices,
      (3 : ℝ) ^ U.scale < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z}.indicator
        (1 : Configuration d → ℝ) ω :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  by_cases hU : PartitionResolved ω U
  · have h := le_cubeNu_add_of_resolved hd hP hU p hp hκ
    have : 0 ≤ κ * (∑ i, p i ^ 2) * {ω : Configuration d | ∃ z ∈ U.toIntegerCube.vertices,
        (3 : ℝ) ^ U.scale < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z}.indicator 1 ω :=
      mul_nonneg (by positivity) hI0
    linarith
  · have hA : ω ∈ {ω : Configuration d | ∃ z ∈ U.toIntegerCube.vertices,
        (3 : ℝ) ^ U.scale < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} := by
      unfold PartitionResolved at hU
      push Not at hU
      obtain ⟨z, hz, hlt⟩ := hU
      refine ⟨z, (U.mem_toIntegerCube_vertices z).2 hz, ?_⟩
      rw [stoppingSize_goodCubes_eq hP z]
      exact pow_lt_pow_right₀ (by norm_num) hlt
    rw [Set.indicator_of_mem hA, Pi.one_apply, mul_one]
    have h1 := cubeNu_nonneg (ω := ω) (U := U) p
    have h2 : 0 ≤ d * coarseGradConstant d ^ 2 * κ ^ 2 * (∑ i, |p i|) ^ 2 *
        (∑ z ∈ U.toIntegerCube.vertices,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1))) /
          U.latticeVolume :=
      div_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ =>
        pow_nonneg (stoppingSize_nonneg _ _) _)) hvol.le
    have h3 : 0 ≤ κ * (∑ i, p i ^ 2) / (3 : ℝ) ^ U.scale := by positivity
    have h4 : 0 ≤ κ * (∑ i, |p i|) ^ 2 * ((∑ i : Fin d,
        (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
          ∑ x ∈ U.toIntegerCube.lowerFace i,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x)) / U.latticeVolume +
        3 ^ d * (4 * d * (∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
            (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
              then 1 else 0)) * √((3 : ℝ) ^ U.scale) / U.latticeVolume +
          1 / √((3 : ℝ) ^ U.scale)) / 2) := by
      refine mul_nonneg (by positivity) (add_nonneg (div_nonneg (Finset.sum_nonneg fun i _ =>
        add_nonneg (Finset.sum_nonneg fun x _ => stoppingSize_nonneg _ _)
          (Finset.sum_nonneg fun x _ => stoppingSize_nonneg _ _)) hvol.le)
        (div_nonneg (mul_nonneg (by positivity) (add_nonneg (div_nonneg (mul_nonneg
          (mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun i _ =>
            mul_nonneg (pow_nonneg (stoppingSize_nonneg _ _) _) (by split_ifs <;> norm_num)))
          (Real.sqrt_nonneg _)) hvol.le) (by positivity))) (by norm_num)))
    linarith

/-- `∑ p_i² ≤ (∑ |p_i|)²`. -/
theorem sum_sq_le_sq_sum_abs (p : Fin d → ℝ) : ∑ i, p i ^ 2 ≤ (∑ i, |p i|) ^ 2 := by
  have h : ∑ i, |p i| ^ 2 ≤ (∑ i, |p i|) ^ 2 := by
    rw [sq (∑ i, |p i|), Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => |p j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
  simpa only [sq_abs] using h

/-- `1 / √(3ᵐ) → 0`. -/
theorem tendsto_one_div_sqrt_three_pow_atTop :
    Tendsto (fun m : ℕ => 1 / √((3 : ℝ) ^ m)) atTop (𝓝 0) := by
  simp only [one_div]
  exact (Real.tendsto_sqrt_atTop.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3))).inv_tendsto_atTop

/-- **Lower bound for `E[ν]`** (Armstrong and Dario, Lemma 4.7, (4.31), in expectation, in every
dimension `d ≥ 2`): `c |p|² ≤ E[ν(U, p)] + C |p|₁² / 3^{m/2}` for every triadic cube `U` of scale
`m`. -/
theorem exists_le_integral_cubeNu [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (U : TriadicCube d) (p : Fin d → ℝ),
      c * ∑ i, p i ^ 2 ≤ ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob) +
        C * (∑ i, |p i|) ^ 2 / √((3 : ℝ) ^ U.scale) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨θ₁, hθ₁, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  obtain ⟨C₂, hC₂, hfac⟩ := exists_integral_sum_faces_le hd hpc
  obtain ⟨C₃', hC₃', hmar⟩ := exists_integral_sum_margin_le hd hpc
  obtain ⟨C₄, c₄, hc₄, hres⟩ := exists_measure_not_resolved_le hd hpc
  obtain ⟨C₄', hC₄'⟩ : ∃ x : ℝ, x = max C₄ 0 := ⟨_, rfl⟩
  have hC₄'0 : 0 ≤ C₄' := by rw [hC₄']; exact le_max_right _ _
  have hC₄le : C₄ ≤ C₄' := by rw [hC₄']; exact le_max_left _ _
  obtain ⟨M₁, hM₁def⟩ : ∃ x : ℝ,
      x = max (2 * ((2 * (d - 1)).factorial : ℝ) * θ₁ ^ (2 * (d - 1))) 1 := ⟨_, rfl⟩
  have hM₁ : 0 < M₁ := by rw [hM₁def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM₁le : 2 * ((2 * (d - 1)).factorial : ℝ) * θ₁ ^ (2 * (d - 1)) ≤ M₁ := by
    rw [hM₁def]; exact le_max_left _ _
  obtain ⟨C₃, hC₃def⟩ : ∃ x : ℝ, x = coarseGradConstant d := ⟨_, rfl⟩
  have hC₃ : 0 < C₃ := by rw [hC₃def]; exact coarseGradConstant_pos hd0
  obtain ⟨κ, hκdef⟩ : ∃ x : ℝ, x = 1 / (2 * d ^ 2 * C₃ ^ 2 * M₁) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨C₅, hC₅def⟩ : ∃ x : ℝ, x = (Nat.factorial 1 : ℝ) / (c₄ / 2) ^ 1 := ⟨_, rfl⟩
  have hC₅ : 0 ≤ C₅ := by rw [hC₅def]; positivity
  refine ⟨κ / 2, κ * (1 + C₂ + 3 ^ d * (4 * d * C₃' + 1) / 2 + C₄' * C₅), by positivity,
    by positivity, fun U p => ?_⟩
  set μ := latticeBondLaw d prob
  obtain ⟨P, hPdef⟩ : ∃ x : ℝ, x = ∑ i, |p i| := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ x : ℝ, x = ∑ i, p i ^ 2 := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = (3 : ℝ) ^ U.scale := ⟨_, rfl⟩
  rw [← hPdef, ← hSdef, ← hLdef]
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hSP : S ≤ P ^ 2 := by rw [hSdef, hPdef]; exact sum_sq_le_sq_sum_abs p
  have hPS : P ^ 2 ≤ d * S := by rw [hSdef, hPdef]; exact sq_sum_abs_le_mul_sum_sq p
  have hνint := integrable_cubeNu prob U p
  have hν0 : 0 ≤ ∫ ω, cubeNu ω U p ∂μ := integral_nonneg fun ω => cubeNu_nonneg p
  have hL1 : 1 ≤ L := by rw [hLdef]; exact one_le_pow₀ (by norm_num)
  have hL0 : 0 < L := by linarith
  have hsL : 0 < √L := Real.sqrt_pos.2 hL0
  have hsq : √L * √L = L := Real.mul_self_sqrt hL0.le
  have h1s : 1 ≤ √L := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt hL1
  have hsLL : √L ≤ L :=
    calc √L = √L * 1 := (mul_one _).symm
      _ ≤ √L * √L := mul_le_mul_of_nonneg_left h1s (Real.sqrt_nonneg _)
      _ = L := hsq
  by_cases hp : P = 0
  · have hS : S = 0 := le_antisymm (by rw [hp] at hSP; simpa using hSP) hS0
    rw [hS, hp]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      add_zero]
    exact hν0
  have hPpos : 0 < P := lt_of_le_of_ne hP0 (Ne.symm hp)
  have hvolL : U.latticeVolume = L ^ d := by rw [hLdef]; rfl
  have hvol : 0 < U.latticeVolume := U.latticeVolume_pos
  have hLd : L ^ d = L ^ (d - 1) * L := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
  -- the random terms
  obtain ⟨f₁, hf₁⟩ : ∃ f : Configuration d → ℝ, f = fun ω => ∑ z ∈ U.toIntegerCube.vertices,
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) := ⟨_, rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f : Configuration d → ℝ, f = fun ω => ∑ i : Fin d,
      (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
        ∑ x ∈ U.toIntegerCube.lowerFace i,
          TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) := ⟨_, rfl⟩
  obtain ⟨f₃, hf₃⟩ : ∃ f : Configuration d → ℝ, f = fun ω => ∑ z ∈ U.toIntegerCube.vertices,
      ∑ i : Fin d, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
        (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
          then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Set (Configuration d), A = {ω | ∃ z ∈ U.toIntegerCube.vertices,
      L < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} := ⟨_, rfl⟩
  have hA : MeasurableSet A := by
    rw [hAdef]
    exact measurableSet_setOf.2 (Measurable.exists fun z =>
      measurable_const.and (measurableSet_setOf.1 (measurableSet_lt measurable_const
        (measurable_stoppingSize_goodCubes z))))
  have hi₁ : Integrable f₁ μ := by rw [hf₁]; exact (hmom (2 * (d - 1)) _).1
  have hi₂ : Integrable f₂ μ := by rw [hf₂]; exact (hfac U).1
  have hi₃ : Integrable f₃ μ := by rw [hf₃]; exact (hmar U).1
  have hi₄ : Integrable (A.indicator (1 : Configuration d → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have hb₁ : ∫ ω, f₁ ω ∂μ ≤ M₁ * U.latticeVolume := by
    rw [hf₁]
    refine ((hmom (2 * (d - 1)) _).2).trans ?_
    rw [U.card_toIntegerCube_vertices]
    exact mul_le_mul_of_nonneg_right hM₁le hvol.le
  have hb₂ : ∫ ω, f₂ ω ∂μ ≤ C₂ * L ^ (d - 1) := by
    rw [hf₂, hLdef]; exact (hfac U).2
  have hb₃ : ∫ ω, f₃ ω ∂μ ≤ C₃' * L ^ (d - 1) := by
    rw [hf₃, hLdef]; exact (hmar U).2
  have hb₄ : ∫ ω, A.indicator (1 : Configuration d → ℝ) ω ∂μ ≤ C₄' * Real.exp (-c₄ * L) := by
    rw [integral_indicator_one hA]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (measure_mono_ae ?_).trans ((hres U).trans (ENNReal.ofReal_le_ofReal ?_))
    · rw [hAdef]
      filter_upwards [ae_partitionEvent hd hpc] with ω hP
      rintro ⟨z, hz, hlt⟩
      refine ⟨z, (U.mem_toIntegerCube_vertices z).1 hz, ?_⟩
      rw [stoppingSize_goodCubes_eq hP z, hLdef] at hlt
      exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hlt
    · rw [← hLdef]
      exact mul_le_mul_of_nonneg_right hC₄le (Real.exp_pos _).le
  -- the pointwise inequality
  have hpoint : ∀ᵐ ω ∂μ, κ * S - κ * S / L ≤ cubeNu ω U p +
      (d * C₃ ^ 2 * κ ^ 2 * P ^ 2 / U.latticeVolume * f₁ ω +
        κ * P ^ 2 / U.latticeVolume * f₂ ω +
        κ * P ^ 2 * 3 ^ d * (4 * d) * √L / (2 * U.latticeVolume) * f₃ ω +
        κ * S * A.indicator (1 : Configuration d → ℝ) ω + κ * P ^ 2 * 3 ^ d / (2 * √L)) := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hP
    have h := le_cubeNu_add_indicator hd0 hP U p (by rw [← hPdef]; exact hPpos) hκ
    rw [← hPdef, ← hSdef, ← hLdef, ← hC₃def, ← hAdef] at h
    have e1 : ∑ z ∈ U.toIntegerCube.vertices,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) = f₁ ω := by
      rw [hf₁]
    have e2 : ∑ i : Fin d,
        (∑ x ∈ U.toIntegerCube.upperFace i, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x +
          ∑ x ∈ U.toIntegerCube.lowerFace i,
            TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) = f₂ ω := by
      rw [hf₂]
    have e3 : ∑ z ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (d - 1)) *
          (if (U.margin z i : ℝ) < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
            then 1 else 0) = f₃ ω := by
      rw [hf₃]
    rw [e1, e2, e3] at h
    have e : d * C₃ ^ 2 * κ ^ 2 * P ^ 2 * f₁ ω / U.latticeVolume + κ * S / L +
        κ * P ^ 2 * (f₂ ω / U.latticeVolume +
          3 ^ d * (4 * d * f₃ ω * √L / U.latticeVolume + 1 / √L) / 2) +
        κ * S * A.indicator (1 : Configuration d → ℝ) ω =
        (d * C₃ ^ 2 * κ ^ 2 * P ^ 2 / U.latticeVolume * f₁ ω +
          κ * P ^ 2 / U.latticeVolume * f₂ ω +
          κ * P ^ 2 * 3 ^ d * (4 * d) * √L / (2 * U.latticeVolume) * f₃ ω +
          κ * S * A.indicator (1 : Configuration d → ℝ) ω + κ * P ^ 2 * 3 ^ d / (2 * √L)) +
        κ * S / L := by
      ring
    linarith only [h, e]
  have hm := le_integral_add_of_ae_le hνint hi₁ hi₂ hi₃ hi₄ _ _ _ _ _ hpoint
  -- the bounds
  have hT1 : d * C₃ ^ 2 * κ ^ 2 * P ^ 2 / U.latticeVolume * ∫ ω, f₁ ω ∂μ ≤ κ * S / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hb₁
      (by positivity : 0 ≤ d * C₃ ^ 2 * κ ^ 2 * P ^ 2 / U.latticeVolume)
    have e : d * C₃ ^ 2 * κ ^ 2 * P ^ 2 / U.latticeVolume * (M₁ * U.latticeVolume) =
        d * C₃ ^ 2 * κ ^ 2 * P ^ 2 * M₁ := by
      field_simp
    have e2 : (d : ℝ) * C₃ ^ 2 * κ ^ 2 * (d * S) * M₁ = κ * S / 2 := by
      rw [hκdef]
      field_simp
    have h0 : 0 ≤ (d : ℝ) * C₃ ^ 2 * κ ^ 2 := by positivity
    have h3 : (d : ℝ) * C₃ ^ 2 * κ ^ 2 * P ^ 2 * M₁ ≤ d * C₃ ^ 2 * κ ^ 2 * (d * S) * M₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPS h0) hM₁.le
    linarith only [h1, e, e2, h3]
  have hT2 : κ * P ^ 2 / U.latticeVolume * ∫ ω, f₂ ω ∂μ ≤ κ * P ^ 2 * C₂ / √L := by
    have h1 := mul_le_mul_of_nonneg_left hb₂ (by positivity : 0 ≤ κ * P ^ 2 / U.latticeVolume)
    have e : κ * P ^ 2 / U.latticeVolume * (C₂ * L ^ (d - 1)) = κ * P ^ 2 * C₂ / L := by
      rw [hvolL, hLd]
      field_simp
    have h2 : κ * P ^ 2 * C₂ / L ≤ κ * P ^ 2 * C₂ / √L :=
      div_le_div_of_nonneg_left (by positivity) hsL hsLL
    linarith only [h1, e, h2]
  have hT3 : κ * P ^ 2 * 3 ^ d * (4 * d) * √L / (2 * U.latticeVolume) * ∫ ω, f₃ ω ∂μ ≤
      κ * P ^ 2 * 3 ^ d * (4 * d) * C₃' / (2 * √L) := by
    have h1 := mul_le_mul_of_nonneg_left hb₃
      (by positivity : 0 ≤ κ * P ^ 2 * 3 ^ d * (4 * d) * √L / (2 * U.latticeVolume))
    have e : κ * P ^ 2 * 3 ^ d * (4 * d) * √L / (2 * U.latticeVolume) * (C₃' * L ^ (d - 1)) =
        κ * P ^ 2 * 3 ^ d * (4 * d) * C₃' / (2 * √L) := by
      rw [hvolL, hLd, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      calc _ = κ * P ^ 2 * 3 ^ d * (4 * d) * C₃' * (2 * (L ^ (d - 1) * (√L * √L))) := by ring
        _ = _ := by rw [hsq]
    linarith only [h1, e]
  have hexp : L * Real.exp (-c₄ * L) ≤ C₅ := by
    have h1 := pow_mul_exp_neg_le 1 hc₄ hL0.le
    rw [pow_one, ← hC₅def] at h1
    have h2 : Real.exp (-(c₄ / 2) * L) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 < c₄ / 2 * L := by positivity
      linarith)
    calc L * Real.exp (-c₄ * L) ≤ C₅ * Real.exp (-(c₄ / 2) * L) := h1
      _ ≤ C₅ * 1 := mul_le_mul_of_nonneg_left h2 hC₅
      _ = C₅ := mul_one _
  have hT4 : κ * S * ∫ ω, A.indicator (1 : Configuration d → ℝ) ω ∂μ ≤
      κ * P ^ 2 * (C₄' * C₅) / √L := by
    have h1 := mul_le_mul_of_nonneg_left hb₄ (by positivity : 0 ≤ κ * S)
    have hexp' : Real.exp (-c₄ * L) ≤ C₅ / √L := by
      rw [le_div_iff₀ hsL]
      have : √L * Real.exp (-c₄ * L) ≤ L * Real.exp (-c₄ * L) :=
        mul_le_mul_of_nonneg_right hsLL (Real.exp_pos _).le
      linarith only [this, hexp]
    have h2 : κ * S * (C₄' * Real.exp (-c₄ * L)) ≤ κ * P ^ 2 * (C₄' * Real.exp (-c₄ * L)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSP hκ.le)
        (mul_nonneg hC₄'0 (Real.exp_pos _).le)
    have h3 : κ * P ^ 2 * (C₄' * Real.exp (-c₄ * L)) ≤ κ * P ^ 2 * (C₄' * (C₅ / √L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp' hC₄'0) (by positivity)
    have e : κ * P ^ 2 * (C₄' * (C₅ / √L)) = κ * P ^ 2 * (C₄' * C₅) / √L := by ring
    linarith only [h1, h2, h3, e]
  have hT0 : κ * S / L ≤ κ * P ^ 2 / √L := by
    have h1 : κ * S / L ≤ κ * P ^ 2 / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSP hκ.le) hL0.le
    have h2 : κ * P ^ 2 / L ≤ κ * P ^ 2 / √L := div_le_div_of_nonneg_left (by positivity) hsL hsLL
    linarith only [h1, h2]
  have e : κ * (1 + C₂ + 3 ^ d * (4 * d * C₃' + 1) / 2 + C₄' * C₅) * P ^ 2 / √L =
      κ * P ^ 2 / √L + κ * P ^ 2 * C₂ / √L + κ * P ^ 2 * 3 ^ d * (4 * d) * C₃' / (2 * √L) +
        κ * P ^ 2 * 3 ^ d / (2 * √L) + κ * P ^ 2 * (C₄' * C₅) / √L := by
    ring
  rw [e]
  linarith only [hm, hT0, hT1, hT2, hT3, hT4]

/-- **Lower bound on `ā`** (Armstrong and Dario, (5.1), lower bound, in every dimension `d ≥ 2`):
there is `c > 0` with `c |ξ|² ≤ (1/2) ξ · ā ξ` for every `ξ`. -/
theorem exists_cubeAhom_lower_bound [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin d → ℝ,
      c * ∑ i, ξ i ^ 2 ≤ 1 / 2 * ∑ i, ∑ j, ξ i * cubeAhom prob i j * ξ j := by
  obtain ⟨c, C, hc, hC, hlow⟩ := exists_le_integral_cubeNu hd hpc
  refine ⟨c, hc, fun ξ => ?_⟩
  rw [← cubeNuLimit_eq_cubeAhom hd hpc]
  have h : ∀ m : ℕ, c * ∑ i, ξ i ^ 2 ≤
      cubeNuMean prob m ξ + C * (∑ i, |ξ i|) ^ 2 * (1 / √((3 : ℝ) ^ m)) := by
    intro m
    have := hlow ⟨m, 0⟩ ξ
    unfold cubeNuMean
    calc _ ≤ _ := this
      _ = _ := by ring
  have ht : Tendsto (fun m : ℕ => cubeNuMean prob m ξ +
      C * (∑ i, |ξ i|) ^ 2 * (1 / √((3 : ℝ) ^ m))) atTop (𝓝 (cubeNuLimit prob ξ)) := by
    have := (tendsto_cubeNuLimit hd hpc ξ).add
      (tendsto_one_div_sqrt_three_pow_atTop.const_mul (C * (∑ i, |ξ i|) ^ 2))
    simpa only [mul_zero, add_zero] using this
  exact ge_of_tendsto' ht h

end Rigidity.Percolation
