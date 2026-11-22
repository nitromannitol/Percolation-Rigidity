import Rigidity.Proofs.Percolation.GeneralDim.CubeExceptionalTail
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLocal
import Rigidity.Percolation.PolynomialExponential

/-!
# Approximate monotonicity of the expectation of `ν` in the scale, in `ℤ^d`

For supercritical bond percolation on `ℤ^d`, `d ≥ 2`, and triadic cubes `V`, `U` of scales
`n ≤ m`,

`E[ν(U, p)] ≤ E[ν(V, p)] + C |p|₁² 3^{-n/2}`.

The subadditivity of `ν` with the exceptional vertices (`CubeNuSubadditiveError`), integrated
with `s = 3^{n/2}`, the exact stationarity of `E[ν]` across cubes of the same scale
(`CubeNuLocal`) and the bound `E[G] ≤ |U| (C exp(-c 3ⁿ) + C' 3^{-n})` on the expected number of
exceptional vertices give the bound. This is Armstrong and Dario, (4.48) for `ν` (with the rate
from (4.33) in expectation), in every dimension `d ≥ 2`; the planar form is in
`PlanarNuConvergence`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **Probability of the exceptional majorant.** -/
theorem exists_measure_exceptionalMajorant_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C c θ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < θ ∧ ∀ (n : ℕ) (x : Vertex d),
      latticeBondLaw d prob {ω | ExceptionalMajorant ω n x} ≤
        ENNReal.ofReal (C * Real.exp (-c * (3 : ℝ) ^ n) +
          ∑ i, Real.exp 1 * Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / (3 * θ))) := by
  obtain ⟨C, c, hc, hres⟩ := exists_measure_not_resolved_le hd hpc
  obtain ⟨θ, hθ, hO⟩ := exists_osBound_stoppingSize hd hpc
  refine ⟨max C 0, c, θ, le_max_right _ _, hc, hθ, fun n x => ?_⟩
  set V := triadicCubeAt n x
  set μ := latticeBondLaw d prob
  have hA : μ {ω | ∃ z ∈ V.toIntegerCube.vertices,
      (3 : ℝ) ^ n < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} ≤
      ENNReal.ofReal (max C 0 * Real.exp (-c * (3 : ℝ) ^ n)) := by
    have h := hres V
    rw [scale_triadicCubeAt] at h
    refine le_trans (measure_mono_ae ?_) (h.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)))
    filter_upwards [ae_partitionEvent hd hpc] with ω hP
    rintro ⟨z, hz, hlt⟩
    refine ⟨z, (V.mem_toIntegerCube_vertices z).1 hz, ?_⟩
    rw [stoppingSize_goodCubes_eq hP z] at hlt
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hlt
  have hB : ∀ i, μ {ω | ((V.margin x i : ℤ) : ℝ) <
      3 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(V.margin x i : ℝ) / (3 * θ))) := by
    intro i
    set m : ℝ := (V.margin x i : ℝ)
    by_cases ht : 1 ≤ m / (3 * θ)
    · have hsub : {ω : Configuration d | m < 3 * TriadicCube.stoppingSize
          (TriadicCube.goodCubes ω) x} ⊆ {ω | m / (3 * θ) * θ <
            max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) 0} := by
        intro ω hω
        have hω' : m < 3 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x := hω
        have e : m / (3 * θ) * θ = m / 3 := by field_simp
        show m / (3 * θ) * θ < max (TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x) 0
        rw [e]
        exact lt_max_of_lt_left (by linarith)
      refine (measure_mono hsub).trans ((hO x _ ht).trans (ENNReal.ofReal_le_ofReal ?_))
      rw [Real.rpow_one, neg_div]
      have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have h2 := Real.exp_pos (-(m / (3 * θ)))
      nlinarith
    · push Not at ht
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : m / (3 * θ) = -(-m / (3 * θ)) := by ring
      linarith
  have hunion : {ω : Configuration d | ExceptionalMajorant ω n x} ⊆
      {ω | ∃ z ∈ V.toIntegerCube.vertices,
        (3 : ℝ) ^ n < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} ∪
      ⋃ i, {ω | ((V.margin x i : ℤ) : ℝ) <
        3 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x} := by
    rintro ω (h | ⟨i, h⟩)
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.2 ⟨i, h⟩)
  calc μ {ω | ExceptionalMajorant ω n x}
      ≤ μ {ω | ∃ z ∈ V.toIntegerCube.vertices,
          (3 : ℝ) ^ n < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} +
        μ (⋃ i, {ω | ((V.margin x i : ℤ) : ℝ) <
          3 * TriadicCube.stoppingSize (TriadicCube.goodCubes ω) x}) :=
        (measure_mono hunion).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (max C 0 * Real.exp (-c * (3 : ℝ) ^ n)) +
        ∑ i, ENNReal.ofReal (Real.exp 1 * Real.exp (-(V.margin x i : ℝ) / (3 * θ))) :=
        add_le_add hA ((measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => hB i))
    _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by positivity),
          ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]

/-- The subcubes of scale `n` of `U` have `|U|` vertices in total. -/
theorem card_subcubesAt_mul (U : TriadicCube d) {n : ℕ} (hn : n ≤ U.scale) :
    ((U.subcubesAt n).card : ℝ) * ((3 : ℝ) ^ n) ^ d = U.latticeVolume := by
  have h := sum_triadicCubeAt_eq hn (fun _ _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [← U.card_toIntegerCube_vertices, h, Finset.sum_congr rfl fun V hV => by
    rw [V.card_toIntegerCube_vertices, TriadicCube.latticeVolume,
      TriadicCube.scale_of_mem_subcubesAt hV], Finset.sum_const, nsmul_eq_mul]

/-- **The expected number of exceptional vertices.** -/
theorem exists_sum_measure_exceptionalMajorant_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C₁ c₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 < c₁ ∧ 0 ≤ C₂ ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale →
      ∑ x ∈ U.toIntegerCube.vertices,
          (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal ≤
        U.latticeVolume * (C₁ * Real.exp (-c₁ * (3 : ℝ) ^ n) + C₂ / (3 : ℝ) ^ n) := by
  obtain ⟨C, c, θ, hC, hc, hθ, hμ⟩ := exists_measure_exceptionalMajorant_le hd hpc
  set a := 3 * θ
  have ha : 0 < a := by positivity
  set K := (1 - Real.exp (-1 / a))⁻¹
  have hK : 0 ≤ K := by
    have : Real.exp (-1 / a) < 1 := by
      have h := Real.exp_lt_exp.2 (div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) ha)
      rwa [Real.exp_zero] at h
    exact inv_nonneg.2 (by linarith)
  refine ⟨C, c, 2 * d * Real.exp 1 * K, hC, hc, by positivity, fun U n hn => ?_⟩
  have hpt : ∀ x ∈ U.toIntegerCube.vertices,
      (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal ≤
        C * Real.exp (-c * (3 : ℝ) ^ n) +
          ∑ i, Real.exp 1 * Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / a) := by
    intro x _
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hμ n x)
  have hsumi : ∀ i : Fin d, ∑ x ∈ U.toIntegerCube.vertices,
      Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / a) ≤
      2 * K * U.latticeVolume / (3 : ℝ) ^ n := by
    intro i
    rw [sum_triadicCubeAt_eq hn (fun V x => Real.exp (-(V.margin x i : ℝ) / a))]
    calc ∑ V ∈ U.subcubesAt n, ∑ x ∈ V.toIntegerCube.vertices,
          Real.exp (-(V.margin x i : ℝ) / a)
        ≤ ∑ V ∈ U.subcubesAt n, 2 * ((3 : ℝ) ^ n) ^ (d - 1) * K :=
          Finset.sum_le_sum fun V hV => by
            have h := sum_exp_neg_margin_le V i ha
            rwa [TriadicCube.scale_of_mem_subcubesAt hV] at h
      _ = 2 * K * (((U.subcubesAt n).card : ℝ) * ((3 : ℝ) ^ n) ^ d) / (3 : ℝ) ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have h3 : (0 : ℝ) < 3 ^ n := by positivity
          have h' : ((3 : ℝ) ^ n) ^ d = ((3 : ℝ) ^ n) ^ (d - 1) * 3 ^ n := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
          rw [h']
          field_simp
      _ = 2 * K * U.latticeVolume / (3 : ℝ) ^ n := by rw [card_subcubesAt_mul U hn]
  calc ∑ x ∈ U.toIntegerCube.vertices,
        (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal
      ≤ ∑ x ∈ U.toIntegerCube.vertices, (C * Real.exp (-c * (3 : ℝ) ^ n) +
          ∑ i, Real.exp 1 * Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / a)) :=
        Finset.sum_le_sum hpt
    _ = U.latticeVolume * (C * Real.exp (-c * (3 : ℝ) ^ n)) + Real.exp 1 * ∑ i : Fin d,
          ∑ x ∈ U.toIntegerCube.vertices,
            Real.exp (-((triadicCubeAt n x).margin x i : ℝ) / a) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, U.card_toIntegerCube_vertices,
          Finset.sum_comm, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ U.latticeVolume * (C * Real.exp (-c * (3 : ℝ) ^ n)) + Real.exp 1 * ∑ _i : Fin d,
          2 * K * U.latticeVolume / (3 : ℝ) ^ n := by
        gcongr with i
        exact hsumi i
    _ = U.latticeVolume * (C * Real.exp (-c * (3 : ℝ) ^ n) +
          2 * d * Real.exp 1 * K / (3 : ℝ) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Approximate monotonicity of `E[ν]` in the scale**, for a free parameter `s > 0`. -/
theorem integral_cubeNu_le_of_scale_le_aux [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) {U V : TriadicCube d} (hn : V.scale ≤ U.scale)
    (p : Fin d → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob) ≤
      ∫ ω, cubeNu ω V p ∂(latticeBondLaw d prob) + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
        (s * (∑ x ∈ U.toIntegerCube.vertices,
          (latticeBondLaw d prob {ω | ExceptionalMajorant ω V.scale x}).toReal) /
            U.latticeVolume + 1 / s) := by
  set μ := latticeBondLaw d prob
  set n := V.scale
  have hd0 : 0 < d := by omega
  obtain ⟨G', hG'⟩ : ∃ G' : Configuration d → ℝ, G' = fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      {ω | ExceptionalMajorant ω n x}.indicator 1 ω := ⟨_, rfl⟩
  have hInd : ∀ x, Integrable ({ω : Configuration d | ExceptionalMajorant ω n x}.indicator
      (1 : Configuration d → ℝ)) μ := fun x =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_exceptionalMajorant n x)
  have hGint : Integrable G' μ := by
    rw [hG']
    exact integrable_finsetSum _ fun x _ => hInd x
  have hGval : ∫ ω, G' ω ∂μ = ∑ x ∈ U.toIntegerCube.vertices,
      (μ {ω | ExceptionalMajorant ω n x}).toReal := by
    rw [hG']
    beta_reduce
    rw [integral_finsetSum _ fun x _ => hInd x]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_indicator_one (measurableSet_exceptionalMajorant n x)]
    rfl
  have hK0 : 0 ≤ 3 ^ d / 4 * (∑ i, |p i|) ^ 2 := by positivity
  have hpoint : ∀ᵐ ω ∂μ, cubeNu ω U p * U.latticeVolume ≤
      ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p +
        3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (s * G' ω + U.latticeVolume / s) := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hP
    have h := cubeNu_mul_latticeVolume_le_sum_add hd0 hP hn p hs
    have hGle : subcubeExceptionalCount ω U n ≤ G' ω := by
      have e : ∑ x ∈ U.toIntegerCube.vertices, {ω | ExceptionalMajorant ω n x}.indicator 1 ω =
          ((U.toIntegerCube.vertices.filter fun x => ExceptionalMajorant ω n x).card : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
        split_ifs <;> simp
      rw [hG']
      beta_reduce
      rw [subcubeExceptionalCount, e]
      exact_mod_cast Finset.card_le_card fun x hx => by
        obtain ⟨hxC, hxe⟩ := Finset.mem_filter.1 hx
        exact Finset.mem_filter.2 ⟨Finset.mem_of_mem_filter _ hxC,
          exceptionalMajorant_of_isSubcubeExceptional hP hxe⟩
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGle hs.le) hK0
    nlinarith
  have hint_l : Integrable (fun ω => cubeNu ω U p * U.latticeVolume) μ :=
    (integrable_cubeNu prob U p).mul_const _
  have hint_s : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      cubeNu ω (triadicCubeAt n x) p) μ :=
    integrable_finsetSum _ fun x _ => integrable_cubeNu prob _ p
  have hint_G : Integrable (fun ω => 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
      (s * G' ω + U.latticeVolume / s)) μ :=
    ((hGint.const_mul s).add (integrable_const _)).const_mul _
  have hint_r : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      cubeNu ω (triadicCubeAt n x) p + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
        (s * G' ω + U.latticeVolume / s)) μ := hint_s.add hint_G
  have hmono := integral_mono_ae hint_l hint_r hpoint
  have hL : ∫ ω, cubeNu ω U p * U.latticeVolume ∂μ =
      (∫ ω, cubeNu ω U p ∂μ) * U.latticeVolume := integral_mul_const _ _
  have hS : ∫ ω, ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p ∂μ =
      U.latticeVolume * ∫ ω, cubeNu ω V p ∂μ := by
    rw [integral_finsetSum _ fun x _ => integrable_cubeNu prob _ p,
      Finset.sum_congr rfl fun x _ => integral_cubeNu_eq_of_scale_eq prob
        (scale_triadicCubeAt n x).symm p, Finset.sum_const, nsmul_eq_mul,
      U.card_toIntegerCube_vertices]
  have hGs : Integrable (fun ω => s * G' ω) μ := hGint.const_mul s
  have hG : ∫ ω, 3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (s * G' ω + U.latticeVolume / s) ∂μ =
      3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (s * ∑ x ∈ U.toIntegerCube.vertices,
        (μ {ω | ExceptionalMajorant ω n x}).toReal + U.latticeVolume / s) := by
    rw [integral_const_mul, integral_add hGs (integrable_const _), integral_const_mul, hGval,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hL, integral_add hint_s hint_G, hS, hG] at hmono
  have hvol := U.latticeVolume_pos
  rw [← sub_nonneg] at hmono ⊢
  have e : ∫ ω, cubeNu ω V p ∂μ + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
      (s * (∑ x ∈ U.toIntegerCube.vertices,
        (μ {ω | ExceptionalMajorant ω n x}).toReal) / U.latticeVolume + 1 / s) -
      ∫ ω, cubeNu ω U p ∂μ =
      (U.latticeVolume * ∫ ω, cubeNu ω V p ∂μ + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
        (s * ∑ x ∈ U.toIntegerCube.vertices,
          (μ {ω | ExceptionalMajorant ω n x}).toReal + U.latticeVolume / s) -
        (∫ ω, cubeNu ω U p ∂μ) * U.latticeVolume) / U.latticeVolume := by
    field_simp
  rw [e]
  exact div_nonneg hmono hvol.le

/-- **Approximate monotonicity of `E[ν]` in the scale** (Armstrong and Dario, (4.48) for `ν`, in
every dimension `d ≥ 2`): for triadic cubes `V`, `U` of scales `n ≤ m`,
`E[ν(U, p)] ≤ E[ν(V, p)] + C |p|₁² / 3^{n/2}`. -/
theorem exists_integral_cubeNu_le_of_scale_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U V : TriadicCube d) (p : Fin d → ℝ), V.scale ≤ U.scale →
      ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob) ≤
        ∫ ω, cubeNu ω V p ∂(latticeBondLaw d prob) +
          C * (∑ i, |p i|) ^ 2 / √3 ^ V.scale := by
  obtain ⟨C₁, c₁, C₂, hC₁, hc₁, hC₂, hsum⟩ := exists_sum_measure_exceptionalMajorant_le hd hpc
  set C₃ := (Nat.factorial 1 : ℝ) / (c₁ / 2) ^ 1
  have hC₃ : 0 ≤ C₃ := by positivity
  refine ⟨3 ^ d / 4 * (C₁ * C₃ + C₂ + 1), by positivity, fun U V p hn => ?_⟩
  set n := V.scale
  set t := √3 ^ n with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 = (3 : ℝ) ^ n := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have h := integral_cubeNu_le_of_scale_le_aux hd hpc hn p ht0
  have hb := hsum U n hn
  have hvol := U.latticeVolume_pos
  have hexp : (3 : ℝ) ^ n * Real.exp (-c₁ * (3 : ℝ) ^ n) ≤ C₃ := by
    have h1 := pow_mul_exp_neg_le 1 hc₁ (by positivity : (0 : ℝ) ≤ 3 ^ n)
    rw [pow_one] at h1
    have h2 : Real.exp (-(c₁ / 2) * (3 : ℝ) ^ n) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 < c₁ / 2 * (3 : ℝ) ^ n := by positivity
      linarith)
    calc (3 : ℝ) ^ n * Real.exp (-c₁ * (3 : ℝ) ^ n)
        ≤ C₃ * Real.exp (-(c₁ / 2) * (3 : ℝ) ^ n) := h1
      _ ≤ C₃ * 1 := mul_le_mul_of_nonneg_left h2 hC₃
      _ = C₃ := mul_one _
  have hratio : t * (∑ x ∈ U.toIntegerCube.vertices,
      (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal) / U.latticeVolume + 1 / t ≤
      (C₁ * C₃ + C₂ + 1) / t := by
    have h1 : t * (∑ x ∈ U.toIntegerCube.vertices,
        (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal) / U.latticeVolume ≤
        t * (C₁ * Real.exp (-c₁ * (3 : ℝ) ^ n) + C₂ / (3 : ℝ) ^ n) := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ ht0.le
      rw [div_le_iff₀ hvol]
      linarith
    have h2 : t * (C₁ * Real.exp (-c₁ * (3 : ℝ) ^ n) + C₂ / (3 : ℝ) ^ n) ≤
        (C₁ * C₃ + C₂) / t := by
      rw [le_div_iff₀ ht0]
      have e : t * (C₁ * Real.exp (-c₁ * (3 : ℝ) ^ n) + C₂ / (3 : ℝ) ^ n) * t =
          C₁ * ((3 : ℝ) ^ n * Real.exp (-c₁ * (3 : ℝ) ^ n)) + C₂ := by
        rw [show t * (C₁ * Real.exp (-c₁ * (3 : ℝ) ^ n) + C₂ / (3 : ℝ) ^ n) * t =
          t ^ 2 * (C₁ * Real.exp (-c₁ * (3 : ℝ) ^ n) + C₂ / (3 : ℝ) ^ n) by ring, ht2]
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left hexp hC₁
      linarith
    have e2 : (C₁ * C₃ + C₂) / t + 1 / t = (C₁ * C₃ + C₂ + 1) / t := by ring
    linarith
  have hK0 : 0 ≤ 3 ^ d / 4 * (∑ i, |p i|) ^ 2 := by positivity
  calc ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob)
      ≤ ∫ ω, cubeNu ω V p ∂(latticeBondLaw d prob) + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
          (t * (∑ x ∈ U.toIntegerCube.vertices,
            (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal) /
              U.latticeVolume + 1 / t) := h
    _ ≤ ∫ ω, cubeNu ω V p ∂(latticeBondLaw d prob) + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
          ((C₁ * C₃ + C₂ + 1) / t) := by gcongr
    _ = _ := by ring

end Rigidity.Percolation
