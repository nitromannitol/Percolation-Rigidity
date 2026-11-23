import Rigidity.Proofs.Cluster.GeneralMuSubadditiveError

/-!
# The expected error in the subadditivity of `μ` on triadic cubes of `ℤ^d`

By the deterministic bound `sum_cubeMu_subcubes_sub_le`, the error in the subadditivity of `μ`
between a resolved cube `U` and its subcubes of scale `n` is at most
`K |q|₁² (t A + B / t) / 2`, with `A = ∑_{z ∈ U} size(z)^{2d-2}` and
`B = ∑_{z ∈ U} size(z)^{2d} 1{z exceptional}`. The moments of the partition sizes give
`E[A] ≤ C |U|`, and Young's inequality `size^{2d} 1_E ≤ (λ size^{4d} + λ⁻¹ 1_E) / 2` with
`λ = 3^{-n/2}`, together with the expected number of exceptional vertices
`|U| (C exp(-c 3ⁿ) + C 3^{-n})`, gives `E[B] ≤ C |U| 3^{-n/2}`. With `t = 3^{-n/4}`, the expected
error is at most `C |q|₁² |U| 3^{-n/4}` (Armstrong and Dario, Lemma 4.8, (4.32), in expectation, in
every dimension `d ≥ 2`; `exists_lintegral_sum_cubeMu_subcubes_sub_le`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The sum of the `k`-th powers of the partition sizes over a finite set. -/
noncomputable def partitionSizeSum (ω : Configuration d) (S : Finset (Vertex d)) (k : ℕ) : ℝ :=
  ∑ z ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ k

/-- The sum of the `2d`-th powers of the partition sizes at the exceptional vertices. -/
noncomputable def exceptionalSizeSum (ω : Configuration d) (S : Finset (Vertex d)) (n : ℕ) :
    ℝ :=
  ∑ z ∈ S, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d) *
    {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator 1 ω

theorem measurable_stoppingSize_goodCubes (z : Vertex d) :
    Measurable fun ω : Configuration d =>
      TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z :=
  TriadicCube.measurable_stoppingSize _ TriadicCube.measurableSet_mem_goodCubes z

theorem stoppingSize_goodCubes_nonneg (ω : Configuration d) (z : Vertex d) :
    0 ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z :=
  TriadicCube.stoppingSize_nonneg _ _

/-- `x e^{-c x²} ≤ 1 / (c x)`. -/
theorem mul_exp_neg_mul_sq_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    x * Real.exp (-c * x ^ 2) ≤ 1 / (c * x) := by
  have h1 : c * x ^ 2 + 1 ≤ Real.exp (c * x ^ 2) := Real.add_one_le_exp _
  have h3 : 0 < Real.exp (c * x ^ 2) := Real.exp_pos _
  have h2 : Real.exp (-c * x ^ 2) = (Real.exp (c * x ^ 2))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [h2, le_div_iff₀ (by positivity)]
  calc x * (Real.exp (c * x ^ 2))⁻¹ * (c * x) = c * x ^ 2 * (Real.exp (c * x ^ 2))⁻¹ := by ring
    _ ≤ Real.exp (c * x ^ 2) * (Real.exp (c * x ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 h3.le)
    _ = 1 := mul_inv_cancel₀ h3.ne'

/-- **The expected error in the subadditivity of `μ`** (Armstrong and Dario, Lemma 4.8, (4.32), in
expectation, in every dimension `d ≥ 2`). -/
theorem exists_lintegral_sum_cubeMu_subcubes_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale → ∀ q : Fin d → ℝ,
      ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
          ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
              (if PartitionResolved ω (triadicCubeAt n x) then
                cubeMu ω (triadicCubeAt n x) q else 0) -
            cubeMu ω U q * U.latticeVolume) else 0) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, |q i|) ^ 2 * U.latticeVolume / √(√((3 : ℝ) ^ n))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  obtain ⟨C₁, c₁, C₂, hC₁, hc₁, hC₂, hEM⟩ := exists_sum_measure_exceptionalMajorant_le hd hpc
  set M₁ : ℝ := 2 * ((2 * (d - 1)).factorial : ℝ) * θ ^ (2 * (d - 1)) with hM₁
  set M₄ : ℝ := 2 * ((2 * (2 * d)).factorial : ℝ) * θ ^ (2 * (2 * d)) with hM₄
  set M' : ℝ := M₄ + C₁ / c₁ + C₂ with hM'
  set K := muSubaddConst d with hK
  have hK0 : 0 ≤ K := muSubaddConst_nonneg d
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₄0 : 0 ≤ M₄ := by positivity
  have hM'0 : 0 ≤ M' := by positivity
  refine ⟨K * (M₁ + M') / 2, by positivity, fun U n hn q => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set S := U.toIntegerCube.vertices with hSdef
  have hcard : (S.card : ℝ) = U.latticeVolume := U.card_toIntegerCube_vertices
  have hvol := U.latticeVolume_pos
  set Qs := (∑ i, |q i|) ^ 2 with hQs
  have hQs0 : 0 ≤ Qs := by positivity
  set X := √((3 : ℝ) ^ n) with hXdef
  set Y := √X with hYdef
  have hX : 0 < X := Real.sqrt_pos.2 (by positivity)
  have hY : 0 < Y := Real.sqrt_pos.2 hX
  have hXY : X = Y ^ 2 := (Real.sq_sqrt hX.le).symm
  have h3X : (3 : ℝ) ^ n = X ^ 2 := (Real.sq_sqrt (by positivity)).symm
  set t := 1 / Y with ht
  have ht0 : 0 < t := by positivity
  set lam := 1 / X with hlam
  have hlam0 : 0 < lam := by positivity
  -- measurability and integrability
  have hsm := measurable_stoppingSize_goodCubes (d := d)
  have hEMm : ∀ z, MeasurableSet {ω : Configuration d | ExceptionalMajorant ω n z} :=
    fun z => measurableSet_exceptionalMajorant n z
  have hA_int : Integrable (fun ω => partitionSizeSum ω S (2 * (d - 1))) μ := (hmom _ S).1
  have hA_le : ∫ ω, partitionSizeSum ω S (2 * (d - 1)) ∂μ ≤ M₁ * U.latticeVolume := by
    rw [← hcard]; exact (hmom _ S).2
  have hA4_int : Integrable (fun ω => partitionSizeSum ω S (2 * (2 * d))) μ := (hmom _ S).1
  have hA4_le : ∫ ω, partitionSizeSum ω S (2 * (2 * d)) ∂μ ≤ M₄ * U.latticeVolume := by
    rw [← hcard]; exact (hmom _ S).2
  have hind_int : ∀ z, Integrable
      ({ω : Configuration d | ExceptionalMajorant ω n z}.indicator 1) μ :=
    fun z => (integrable_const (1 : ℝ)).indicator (hEMm z)
  have hE_int : Integrable (fun ω => ∑ z ∈ S,
      {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator (1 : Configuration d → ℝ) ω)
      μ := integrable_finsetSum _ fun z _ => hind_int z
  have hE_eq : ∫ ω, (∑ z ∈ S, {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator
      (1 : Configuration d → ℝ) ω) ∂μ =
      ∑ z ∈ S, (μ {ω : Configuration d | ExceptionalMajorant ω n z}).toReal := by
    rw [integral_finsetSum _ fun z _ => hind_int z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_indicator_one (hEMm z), measureReal_def]
  have hE_le : ∑ z ∈ S, (μ {ω : Configuration d | ExceptionalMajorant ω n z}).toReal ≤
      U.latticeVolume * (C₁ * Real.exp (-c₁ * X ^ 2) + C₂ / X ^ 2) := by
    rw [← h3X]; exact hEM U n hn
  have hind01 : ∀ ω z, 0 ≤ {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator
      (1 : Configuration d → ℝ) ω ∧ {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator
      (1 : Configuration d → ℝ) ω ≤ 1 := by
    intro ω z
    by_cases h : ω ∈ {ω' : Configuration d | ExceptionalMajorant ω' n z}
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  -- Young's inequality for the exceptional sum
  have hB_pt : ∀ ω, exceptionalSizeSum ω S n ≤
      (lam * partitionSizeSum ω S (2 * (2 * d)) + (∑ z ∈ S,
        {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator
          (1 : Configuration d → ℝ) ω) / lam) / 2 := by
    intro ω
    unfold exceptionalSizeSum partitionSizeSum
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun z _ => ?_
    set a := TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d)
    set b := {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator
      (1 : Configuration d → ℝ) ω
    have hb2 : b ^ 2 = b := by
      rcases hind01 ω z with ⟨h0, h1⟩
      by_cases h : ω ∈ {ω' : Configuration d | ExceptionalMajorant ω' n z}
      · simp only [b, Set.indicator_of_mem h, Pi.one_apply, one_pow]
      · simp only [b, Set.indicator_of_notMem h, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow]
    have ha2 : TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * (2 * d)) = a ^ 2 := by
      rw [← pow_mul, mul_comm (2 * d) 2]
    have h := two_mul_mul_le_add_div hlam0 a b
    rw [hb2] at h
    rw [ha2]
    linarith
  have hB_meas : Measurable fun ω => exceptionalSizeSum ω S n := by
    unfold exceptionalSizeSum
    exact Finset.measurable_sum _ fun z _ =>
      ((hsm z).pow_const _).mul (measurable_one.indicator (hEMm z))
  have hB_nonneg : ∀ ω, 0 ≤ exceptionalSizeSum ω S n := fun ω =>
    Finset.sum_nonneg fun z _ => mul_nonneg (pow_nonneg (stoppingSize_goodCubes_nonneg ω z) _)
      (hind01 ω z).1
  have hB_int : Integrable (fun ω => exceptionalSizeSum ω S n) μ := by
    refine (hA4_int.const_mul (lam / 2) |>.add (hE_int.const_mul (1 / (2 * lam)))).mono'
      hB_meas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hB_nonneg ω)]
    refine (hB_pt ω).trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    field_simp
  have hB_le : ∫ ω, exceptionalSizeSum ω S n ∂μ ≤ U.latticeVolume * M' / X := by
    have h1 : ∫ ω, exceptionalSizeSum ω S n ∂μ ≤ ∫ ω, (lam / 2 * partitionSizeSum ω S (2 * (2 * d)) +
        1 / (2 * lam) * ∑ z ∈ S, {ω' : Configuration d | ExceptionalMajorant ω' n z}.indicator
          (1 : Configuration d → ℝ) ω) ∂μ := by
      refine integral_mono hB_int ((hA4_int.const_mul _).add (hE_int.const_mul _)) fun ω => ?_
      refine (hB_pt ω).trans (le_of_eq ?_)
      field_simp
    rw [integral_add (hA4_int.const_mul _) (hE_int.const_mul _), integral_const_mul,
      integral_const_mul, hE_eq] at h1
    have hxe : X * (C₁ * Real.exp (-c₁ * X ^ 2) + C₂ / X ^ 2) ≤ (C₁ / c₁ + C₂) / X := by
      have h2 := mul_exp_neg_mul_sq_le hc₁ hX
      have e1 : X * (C₁ * Real.exp (-c₁ * X ^ 2) + C₂ / X ^ 2) =
          C₁ * (X * Real.exp (-c₁ * X ^ 2)) + C₂ / X := by field_simp
      have e2 : (C₁ / c₁ + C₂) / X = C₁ * (1 / (c₁ * X)) + C₂ / X := by field_simp
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_left h2 hC₁
      linarith
    calc ∫ ω, exceptionalSizeSum ω S n ∂μ
        ≤ lam / 2 * ∫ ω, partitionSizeSum ω S (2 * (2 * d)) ∂μ +
          1 / (2 * lam) * ∑ z ∈ S, (μ {ω : Configuration d | ExceptionalMajorant ω n z}).toReal :=
          h1
      _ ≤ lam / 2 * (M₄ * U.latticeVolume) +
          1 / (2 * lam) * (U.latticeVolume * (C₁ * Real.exp (-c₁ * X ^ 2) + C₂ / X ^ 2)) := by
          gcongr
      _ = U.latticeVolume * (M₄ / X + X * (C₁ * Real.exp (-c₁ * X ^ 2) + C₂ / X ^ 2)) / 2 := by
          rw [hlam]
          field_simp
      _ ≤ U.latticeVolume * (M₄ / X + (C₁ / c₁ + C₂) / X) / 2 := by gcongr
      _ ≤ U.latticeVolume * M' / X := by
          rw [hM']
          have : U.latticeVolume * (M₄ / X + (C₁ / c₁ + C₂) / X) / 2 =
              U.latticeVolume * (M₄ + C₁ / c₁ + C₂) / X / 2 := by
            field_simp
            ring
          rw [this]
          have h0 : 0 ≤ U.latticeVolume * (M₄ + C₁ / c₁ + C₂) / X := by positivity
          linarith
  -- the pointwise bound
  have hpt : ∀ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then
      ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          (if PartitionResolved ω (triadicCubeAt n x) then
            cubeMu ω (triadicCubeAt n x) q else 0) -
        cubeMu ω U q * U.latticeVolume) else 0) ≤
      ENNReal.ofReal (K * Qs * (t * partitionSizeSum ω S (2 * (d - 1)) +
        exceptionalSizeSum ω S n / t) / 2) := by
    intro ω
    split_ifs with h
    · apply ENNReal.ofReal_le_ofReal
      refine (sum_cubeMu_subcubes_sub_le hd0 h.1 h.2 hn q ht0).trans (le_of_eq ?_)
      unfold partitionSizeSum exceptionalSizeSum
      congr 4
      · exact Finset.sum_congr rfl fun z _ => by rw [stoppingSize_goodCubes_eq h.1 z]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [stoppingSize_goodCubes_eq h.1 z]
        by_cases hz : ExceptionalMajorant ω n z
        · rw [if_pos hz, Set.indicator_of_mem (show ω ∈ {ω' | ExceptionalMajorant ω' n z} from hz),
            Pi.one_apply]
        · rw [if_neg hz, Set.indicator_of_notMem
            (show ω ∉ {ω' | ExceptionalMajorant ω' n z} from hz)]
    · exact zero_le
  have hf_int : Integrable (fun ω => K * Qs * (t * partitionSizeSum ω S (2 * (d - 1)) +
      exceptionalSizeSum ω S n / t) / 2) μ :=
    (((hA_int.const_mul t).add (hB_int.div_const t)).const_mul (K * Qs)).div_const 2
  have hf0 : ∀ ω, 0 ≤ K * Qs * (t * partitionSizeSum ω S (2 * (d - 1)) +
      exceptionalSizeSum ω S n / t) / 2 := fun ω => by
    have hA0 : 0 ≤ partitionSizeSum ω S (2 * (d - 1)) := Finset.sum_nonneg fun z _ =>
      pow_nonneg (stoppingSize_goodCubes_nonneg ω z) _
    have := hB_nonneg ω
    positivity
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (K * Qs * (t * partitionSizeSum ω S (2 * (d - 1)) +
        exceptionalSizeSum ω S n / t) / 2) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ω, K * Qs * (t * partitionSizeSum ω S (2 * (d - 1)) +
        exceptionalSizeSum ω S n / t) / 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hf_int (ae_of_all _ hf0)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div, integral_const_mul, integral_add (hA_int.const_mul t)
          (hB_int.div_const t), integral_const_mul, integral_div]
        calc K * Qs * (t * ∫ ω, partitionSizeSum ω S (2 * (d - 1)) ∂μ +
              (∫ ω, exceptionalSizeSum ω S n ∂μ) / t) / 2
            ≤ K * Qs * (t * (M₁ * U.latticeVolume) + U.latticeVolume * M' / X / t) / 2 := by
              gcongr
          _ = K * (M₁ + M') / 2 * Qs * U.latticeVolume / Y := by
              rw [ht, hXY]
              field_simp

end Rigidity.Percolation
