import Rigidity.Proofs.Percolation.GeneralDim.CubeNuMonotone
import Rigidity.Proofs.Percolation.GeneralDim.CubeSecondVariation

/-!
# The energy of the differences between the maximizers of `ν` at two scales, in `ℤ^d`

For a triadic cube `U` of `ℤ^d` and `n ≤ U.scale`, let `v` be the maximizer of `ν(U, p)` and `v_V`
the maximizer of `ν(V, p)` for each resolved subcube `V` of scale `n`. The quantity

`D^ν_n(U, p) = ∑_V B_V(v|_V - v_V, v|_V - v_V) / 2`

is the energy of the differences `v - v_V` on the clusters of the subcubes. By the second
variation (`CubeSecondVariation`) and the flux error bound (`CubeNuSubadditiveError`), on the
partition event,

`D^ν_n(U, p) + |U| ν(U, p) ≤ ∑_{x ∈ U} ν(V(x), p) + (3^d/4) |p|₁² (s G + |U| / s)`,

and, taking expectations, using the stationarity of `E[ν]` and the bound on the expected number
of exceptional vertices, for every triadic cube `V` of scale `n ≤ U.scale`,

`E[D^ν_n(U, p)] ≤ |U| (E[ν(V, p)] - E[ν(U, p)] + C |p|₁² / 3^{n/2})`.

This is Lemma 5.4 of Armstrong and Dario for `ν` (display (5.10), second term, before summing the
increments), in every dimension `d ≥ 2`.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- A maximizer of `ν(U, p)`. -/
noncomputable def cubeNuMaximizer (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ) :
    CubeFun ω U :=
  (exists_cubeNu_maximizer (ω := ω) (U := U) p).choose

theorem cubeNuMaximizer_spec (U : TriadicCube d) (p : Fin d → ℝ) :
    cubeNuMaximizer ω U p ∈ cubeHarmonic ω U ∧ (∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w (cubeNuMaximizer ω U p) = cubeFluxPairing ω U p w) :=
  ⟨(exists_cubeNu_maximizer (ω := ω) (U := U) p).choose_spec.1,
    (exists_cubeNu_maximizer (ω := ω) (U := U) p).choose_spec.2.1⟩

/-- The energy `D^ν_n(U, p)` of the differences between the maximizer of `ν(U, p)` and the
maximizers on the resolved subcubes of scale `n`. -/
noncomputable def cubeNuDefect (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (p : Fin d → ℝ) : ℝ :=
  ∑ V ∈ U.resolvedSubcubesAt ω n,
    cubeForm ω V (cubeRestrictExt V (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V p)
      (cubeRestrictExt V (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V p) / 2

theorem cubeNuDefect_nonneg (U : TriadicCube d) (n : ℕ) (p : Fin d → ℝ) :
    0 ≤ cubeNuDefect ω U n p :=
  Finset.sum_nonneg fun _ _ => div_nonneg (cubeForm_self_nonneg _) (by norm_num)

/-- **Deterministic form of Lemma 5.4 for `ν`.** -/
theorem cubeNuDefect_add_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d} {n : ℕ}
    (hn : n ≤ U.scale) (p : Fin d → ℝ) {s : ℝ} (hs : 0 < s) :
    cubeNuDefect ω U n p + cubeNu ω U p * U.latticeVolume ≤
      ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p +
        3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
          (s * subcubeExceptionalCount ω U n + U.latticeVolume / s) := by
  obtain ⟨hv, hvar⟩ := cubeNuMaximizer_spec (ω := ω) U p
  have h := sum_cubeForm_sub_add_cubeNu_le_sum_subcubes hd hP hn p hv hvar
    (fun V => cubeNuMaximizer ω V p) (fun V _ => cubeNuMaximizer_spec V p)
  have hdrop : ∑ x ∈ U.toIntegerCube.vertices,
      (if PartitionResolved ω (triadicCubeAt n x) then cubeNu ω (triadicCubeAt n x) p else 0) ≤
      ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p :=
    Finset.sum_le_sum fun x _ => by
      split_ifs
      · exact le_rfl
      · exact cubeNu_nonneg p
  have hB : 2 * cubeForm ω U (cubeNuMaximizer ω U p) (cubeNuMaximizer ω U p) ≤
      3 ^ d * U.latticeVolume * (∑ i, |p i|) ^ 2 := by
    have h1 := cubeForm_le_of_cubeNu_variation p hv hvar
    have h2 := cubeNu_le (ω := ω) (U := U) p
    have hvol := U.latticeVolume_pos
    nlinarith
  have herr := flux_error_le hd hP hn p (cubeNuMaximizer ω U p) hs hB
  have hD : cubeNuDefect ω U n p = ∑ V ∈ U.resolvedSubcubesAt ω n,
      cubeForm ω V (cubeRestrictExt V (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V p)
        (cubeRestrictExt V (cubeNuMaximizer ω U p) - cubeNuMaximizer ω V p) / 2 := rfl
  rw [hD]
  linarith

/-- The error term of the subadditivity of `ν` in expectation, with `s = 3^{n/2}`. -/
theorem exists_exceptional_error_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale →
      √3 ^ n * (∑ x ∈ U.toIntegerCube.vertices,
        (latticeBondLaw d prob {ω | ExceptionalMajorant ω n x}).toReal) / U.latticeVolume +
          1 / √3 ^ n ≤ C / √3 ^ n := by
  obtain ⟨C₁, c₁, C₂, hC₁, hc₁, hC₂, hsum⟩ := exists_sum_measure_exceptionalMajorant_le hd hpc
  set C₃ := (Nat.factorial 1 : ℝ) / (c₁ / 2) ^ 1
  have hC₃ : 0 ≤ C₃ := by positivity
  refine ⟨C₁ * C₃ + C₂ + 1, by positivity, fun U n hn => ?_⟩
  set t := √3 ^ n with ht
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 = (3 : ℝ) ^ n := by
    rw [ht, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
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

/-- **Lemma 5.4 of Armstrong and Dario for `ν`** (display (5.10), second term, before summing the
increments), in every dimension `d ≥ 2`: for triadic cubes `V`, `U` with `n = V.scale ≤ U.scale`,
`E[D^ν_n(U, p)] ≤ |U| (E[ν(V, p)] - E[ν(U, p)] + C |p|₁² / 3^{n/2})`. -/
theorem exists_lintegral_cubeNuDefect_le [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U V : TriadicCube d) (p : Fin d → ℝ), V.scale ≤ U.scale →
      ∫⁻ ω, ENNReal.ofReal (cubeNuDefect ω U V.scale p) ∂(latticeBondLaw d prob) ≤
        ENNReal.ofReal (U.latticeVolume * (∫ ω, cubeNu ω V p ∂(latticeBondLaw d prob) -
          ∫ ω, cubeNu ω U p ∂(latticeBondLaw d prob) +
            C * (∑ i, |p i|) ^ 2 / √3 ^ V.scale)) := by
  obtain ⟨C, hC, herr⟩ := exists_exceptional_error_le hd hpc
  refine ⟨3 ^ d / 4 * C, by positivity, fun U V p hn => ?_⟩
  set μ := latticeBondLaw d prob
  set n := V.scale
  set t := √3 ^ n with ht
  have ht0 : 0 < t := by positivity
  have hd0 : 0 < d := by omega
  have hvol := U.latticeVolume_pos
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
  set g : Configuration d → ℝ := fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      cubeNu ω (triadicCubeAt n x) p + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
        (t * G' ω + U.latticeVolume / t) - cubeNu ω U p * U.latticeVolume with hg
  have hpoint : ∀ᵐ ω ∂μ, cubeNuDefect ω U n p ≤ g ω := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hP
    have h := cubeNuDefect_add_le hd0 hP hn p ht0
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
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGle ht0.le) hK0
    simp only [hg]
    nlinarith
  have hint_s : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices,
      cubeNu ω (triadicCubeAt n x) p) μ :=
    integrable_finsetSum _ fun x _ => integrable_cubeNu prob _ p
  have hint_G : Integrable (fun ω => 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
      (t * G' ω + U.latticeVolume / t)) μ :=
    ((hGint.const_mul t).add (integrable_const _)).const_mul _
  have hint_U : Integrable (fun ω => cubeNu ω U p * U.latticeVolume) μ :=
    (integrable_cubeNu prob U p).mul_const _
  have hint_g : Integrable g μ := (hint_s.add hint_G).sub hint_U
  have hg0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [hpoint] with ω hω
    exact (cubeNuDefect_nonneg U n p).trans hω
  have hS : ∫ ω, ∑ x ∈ U.toIntegerCube.vertices, cubeNu ω (triadicCubeAt n x) p ∂μ =
      U.latticeVolume * ∫ ω, cubeNu ω V p ∂μ := by
    rw [integral_finsetSum _ fun x _ => integrable_cubeNu prob _ p,
      Finset.sum_congr rfl fun x _ => integral_cubeNu_eq_of_scale_eq prob
        (scale_triadicCubeAt n x).symm p, Finset.sum_const, nsmul_eq_mul,
      U.card_toIntegerCube_vertices]
  have hGs : Integrable (fun ω => t * G' ω) μ := hGint.const_mul t
  have hG : ∫ ω, 3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (t * G' ω + U.latticeVolume / t) ∂μ =
      3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (t * ∑ x ∈ U.toIntegerCube.vertices,
        (μ {ω | ExceptionalMajorant ω n x}).toReal + U.latticeVolume / t) := by
    rw [integral_const_mul, integral_add hGs (integrable_const _), integral_const_mul, hGval,
      integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
  have hgval : ∫ ω, g ω ∂μ = U.latticeVolume * ∫ ω, cubeNu ω V p ∂μ +
      3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (t * ∑ x ∈ U.toIntegerCube.vertices,
        (μ {ω | ExceptionalMajorant ω n x}).toReal + U.latticeVolume / t) -
      (∫ ω, cubeNu ω U p ∂μ) * U.latticeVolume := by
    have hint_sG : Integrable (fun ω => ∑ x ∈ U.toIntegerCube.vertices,
        cubeNu ω (triadicCubeAt n x) p + 3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
          (t * G' ω + U.latticeVolume / t)) μ := hint_s.add hint_G
    simp only [hg]
    rw [integral_sub hint_sG hint_U, integral_add hint_s hint_G, hS, hG, integral_mul_const]
  have hbound := herr U n hn
  calc ∫⁻ ω, ENNReal.ofReal (cubeNuDefect ω U n p) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ :=
        lintegral_mono_ae (hpoint.mono fun ω h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (∫ ω, g ω ∂μ) := (ofReal_integral_eq_lintegral_ofReal hint_g hg0).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hgval]
        have hK := mul_le_mul_of_nonneg_left hbound hK0
        have e1 : 3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (t * ∑ x ∈ U.toIntegerCube.vertices,
            (μ {ω | ExceptionalMajorant ω n x}).toReal + U.latticeVolume / t) =
            U.latticeVolume * (3 ^ d / 4 * (∑ i, |p i|) ^ 2 *
              (t * (∑ x ∈ U.toIntegerCube.vertices,
                (μ {ω | ExceptionalMajorant ω n x}).toReal) / U.latticeVolume + 1 / t)) := by
          field_simp
        have e2 : U.latticeVolume * (3 ^ d / 4 * (∑ i, |p i|) ^ 2 * (C / t)) =
            U.latticeVolume * (3 ^ d / 4 * C * (∑ i, |p i|) ^ 2 / t) := by ring
        rw [e1]
        have := mul_le_mul_of_nonneg_left hK hvol.le
        rw [e2] at this
        nlinarith

end Rigidity.Percolation
