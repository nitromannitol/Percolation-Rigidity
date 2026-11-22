import Rigidity.Proofs.Percolation.GeneralDim.CubeNuMonotone

/-!
# The limit of the expectation of `ν` and the homogenized matrix in `ℤ^d`

On a triadic cube, `ν(U, ·)` is a quadratic form: if `v_i` solves the first variation equation
of `ν(U, e_i)`, then `∑_i ξ_i v_i` solves it for `ξ`, so that

`ν(U, ξ) = (1/2) ∑_{i,j} ξ_i ξ_j (ν(U, e_i + e_j) - ν(U, e_i) - ν(U, e_j))`.

The expectations `E[ν(□_m, ξ)]` on the triadic cubes `□_m` of scale `m` centred at the origin are
bounded by `(3^d/4) |ξ|₁²` and approximately nonincreasing (`CubeNuMonotone`), hence converge as
`m → ∞`; the limit is again a quadratic form. This defines the homogenized matrix `ā` of Armstrong
and Dario, Definition 5.1, in every dimension `d ≥ 2`:

`(1/2) ξ · ā ξ = lim_{m → ∞} E[ν(□_m, ξ)]`, with `0 ≤ (1/2) ξ · ā ξ ≤ (3^d/4) |ξ|₁²`.

The lower bound `c |ξ|² ≤ (1/2) ξ · ā ξ` of (5.1) needs Lemma 4.7 in expectation and is not proved
here.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- A bounded real sequence with `a m' ≤ a m + ε m` for `m ≤ m'` and `ε m → 0` converges. -/
theorem exists_tendsto_of_le_add_of_bounded {a ε : ℕ → ℝ} {M : ℝ} (ha : ∀ m, a m ∈ Set.Icc 0 M)
    (hε : Tendsto ε atTop (𝓝 0)) (hmono : ∀ m m', m ≤ m' → a m' ≤ a m + ε m) :
    ∃ L, Tendsto a atTop (𝓝 L) := by
  obtain ⟨L, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 M) ha
  refine ⟨L, Metric.tendsto_atTop.2 fun δ hδ => ?_⟩
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hlim (δ / 3) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hε (δ / 3) (by positivity)
  have hK' : ∀ k ≥ K, |a (φ k) - L| < δ / 3 := fun k hk => by
    simpa only [Real.dist_eq, Function.comp_apply] using hK k hk
  have hN' : ∀ m ≥ N, |ε m| < δ / 3 := fun m hm => by
    simpa only [Real.dist_eq, sub_zero] using hN m hm
  refine ⟨φ (max K N), fun m hm => ?_⟩
  have hk₀ := hK' (max K N) (le_max_left _ _)
  have hε₀ := hN' (φ (max K N)) ((le_max_right K N).trans (hφ.id_le _))
  have hup := hmono _ _ hm
  have hmN : N ≤ m := ((le_max_right K N).trans (hφ.id_le _)).trans hm
  have hεm := hN' m hmN
  have hk₁ := hK' (max K m) (le_max_left _ _)
  have hdown := hmono m (φ (max K m)) ((le_max_right K m).trans (hφ.id_le _))
  rw [abs_lt] at hk₀ hε₀ hεm hk₁
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The flux pairing is linear in the slope: `F_ξ = ∑_i ξ_i F_{e_i}`. -/
theorem cubeFluxPairing_eq_sum_single {ω : Configuration d} {U : TriadicCube d} (ξ : Fin d → ℝ)
    (w : CubeFun ω U) :
    cubeFluxPairing ω U ξ w = ∑ i, ξ i * cubeFluxPairing ω U (Pi.single i 1) w := by
  let F : (Fin d → ℝ) →+ ℝ :=
    { toFun := fun p => cubeFluxPairing ω U p w
      map_zero' := by
        have h := cubeFluxPairing_smul_add_smul (ω := ω) (U := U) (0 : Fin d → ℝ) 0 0 0 w
        simp only [smul_zero, add_zero, zero_mul] at h
        exact h
      map_add' := fun p q => by
        have h := cubeFluxPairing_smul_add_smul (ω := ω) (U := U) p q 1 1 w
        simpa only [one_smul, one_mul] using h }
  have hξ : ξ = ∑ i, ξ i • (Pi.single i 1 : Fin d → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : cubeFluxPairing ω U ξ w = F (∑ i, ξ i • (Pi.single i 1 : Fin d → ℝ)) := by
    change cubeFluxPairing ω U ξ w = cubeFluxPairing ω U (∑ i, ξ i • Pi.single i 1) w
    rw [← hξ]
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := cubeFluxPairing_smul_add_smul (ω := ω) (U := U) (Pi.single i 1) 0 (ξ i) 0 w
  simp only [smul_zero, add_zero, zero_mul] at h
  exact h

/-- **Polarization of `ν`.** On every triadic cube, `ν(U, ·)` is the quadratic form
`ν(U, ξ) = (1/2) ∑_{i,j} ξ_i ξ_j (ν(U, e_i + e_j) - ν(U, e_i) - ν(U, e_j))`. -/
theorem cubeNu_eq_sum_polarization (ω : Configuration d) (U : TriadicCube d) (ξ : Fin d → ℝ) :
    cubeNu ω U ξ = 1 / 2 * ∑ i, ∑ j, ξ i * ξ j *
      (cubeNu ω U (Pi.single i 1 + Pi.single j 1) - cubeNu ω U (Pi.single i 1) -
        cubeNu ω U (Pi.single j 1)) := by
  have hex : ∀ i : Fin d, ∃ v ∈ cubeHarmonic ω U, ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w v = cubeFluxPairing ω U (Pi.single i 1) w := fun i => by
    obtain ⟨v, hv, hvar, -⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) (Pi.single i 1)
    exact ⟨v, hv, hvar⟩
  choose v hv hvar using hex
  have hvol := U.latticeVolume_pos
  -- the solution for `ξ`
  have hξ : cubeNu ω U ξ = cubeForm ω U (∑ i, ξ i • v i) (∑ i, ξ i • v i) / 2 /
      U.latticeVolume := by
    refine cubeNu_eq_of_forall_cubeForm_eq
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hv i)) fun w hw => ?_
    rw [map_sum, cubeFluxPairing_eq_sum_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hvar i w hw]
  have hpair : ∀ i j, cubeNu ω U (Pi.single i 1 + Pi.single j 1) =
      cubeForm ω U (v i + v j) (v i + v j) / 2 / U.latticeVolume := by
    intro i j
    refine cubeNu_eq_of_forall_cubeForm_eq (Submodule.add_mem _ (hv i) (hv j)) fun w hw => ?_
    rw [map_add, hvar i w hw, hvar j w hw]
    have h := cubeFluxPairing_smul_add_smul (ω := ω) (U := U) (Pi.single i 1) (Pi.single j 1)
      1 1 w
    simp only [one_smul, one_mul] at h
    rw [h]
  have hone : ∀ i, cubeNu ω U (Pi.single i 1) = cubeForm ω U (v i) (v i) / 2 / U.latticeVolume :=
    fun i => cubeNu_eq_of_forall_cubeForm_eq (hv i) (hvar i)
  have hexp : cubeForm ω U (∑ i, ξ i • v i) (∑ i, ξ i • v i) =
      ∑ i, ∑ j, ξ i * ξ j * cubeForm ω U (v i) (v j) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [cubeForm_symm (v j) (v i)]
    ring
  have hBij : ∀ i j, cubeNu ω U (Pi.single i 1 + Pi.single j 1) - cubeNu ω U (Pi.single i 1) -
      cubeNu ω U (Pi.single j 1) = cubeForm ω U (v i) (v j) / U.latticeVolume := by
    intro i j
    rw [hpair i j, hone i, hone j]
    simp only [map_add, LinearMap.add_apply]
    rw [cubeForm_symm (v j) (v i)]
    field_simp
    ring
  rw [hξ, hexp]
  simp only [hBij]
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- The expectation `E[ν(□_m, ξ)]` on the triadic cube `□_m` of scale `m` centred at the origin. -/
noncomputable def cubeNuMean (prob : unitInterval) (m : ℕ) (ξ : Fin d → ℝ) : ℝ :=
  ∫ ω, cubeNu ω (⟨m, 0⟩ : TriadicCube d) ξ ∂(latticeBondLaw d prob)

/-- The expectations are quadratic forms in the slope. -/
theorem cubeNuMean_eq_sum_polarization (prob : unitInterval) (m : ℕ) (ξ : Fin d → ℝ) :
    cubeNuMean prob m ξ = 1 / 2 * ∑ i, ∑ j, ξ i * ξ j *
      (cubeNuMean prob m (Pi.single i 1 + Pi.single j 1) - cubeNuMean prob m (Pi.single i 1) -
        cubeNuMean prob m (Pi.single j 1)) := by
  have hint := fun η => integrable_cubeNu (d := d) prob ⟨m, 0⟩ η
  unfold cubeNuMean
  rw [integral_congr_ae (ae_of_all _ fun ω => cubeNu_eq_sum_polarization ω ⟨m, 0⟩ ξ),
    integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_sub, integral_sub]
      all_goals first | exact hint _ | exact (hint _).sub (hint _)
    · intro j _
      exact (((hint _).sub (hint _)).sub (hint _)).const_mul _
  · intro i _
    exact integrable_finsetSum _ fun j _ => (((hint _).sub (hint _)).sub (hint _)).const_mul _

/-- `1 / √3ⁿ → 0`. -/
theorem tendsto_one_div_sqrt_three_pow' :
    Tendsto (fun n : ℕ => 1 / √3 ^ n) atTop (𝓝 0) := by
  have h : (1 : ℝ) < √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simp only [one_div]
  exact (tendsto_pow_atTop_atTop_of_one_lt h).inv_tendsto_atTop

/-- **Convergence of `E[ν(□_m, ξ)]`** (Armstrong and Dario, Section 5, before Definition 5.1, in
every dimension `d ≥ 2`). -/
theorem exists_tendsto_cubeNuMean [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) (ξ : Fin d → ℝ) :
    ∃ L : ℝ, Tendsto (fun m => cubeNuMean prob m ξ) atTop (𝓝 L) ∧
      0 ≤ L ∧ L ≤ 3 ^ d / 4 * (∑ i, |ξ i|) ^ 2 := by
  obtain ⟨C, hC, hmono⟩ := exists_integral_cubeNu_le_of_scale_le hd hpc
  set M := 3 ^ d / 4 * (∑ i, |ξ i|) ^ 2
  have hbound : ∀ m, cubeNuMean prob m ξ ∈ Set.Icc 0 M := fun m =>
    ⟨integral_nonneg fun ω => cubeNu_nonneg ξ,
      (integral_mono (integrable_cubeNu prob _ ξ) (integrable_const M) fun ω => cubeNu_le ξ).trans
        (by simp)⟩
  have hstep : ∀ m m', m ≤ m' → cubeNuMean prob m' ξ ≤
      cubeNuMean prob m ξ + C * (∑ i, |ξ i|) ^ 2 * (1 / √3 ^ m) := by
    intro m m' hmm'
    have h := hmono ⟨m', 0⟩ ⟨m, 0⟩ ξ hmm'
    unfold cubeNuMean
    calc _ ≤ _ := h
      _ = _ := by ring
  have hε : Tendsto (fun m => C * (∑ i, |ξ i|) ^ 2 * (1 / √3 ^ m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_sqrt_three_pow'.const_mul (C * (∑ i, |ξ i|) ^ 2)
  obtain ⟨L, hL⟩ := exists_tendsto_of_le_add_of_bounded hbound hε hstep
  exact ⟨L, hL, ge_of_tendsto' hL fun m => (hbound m).1, le_of_tendsto' hL fun m => (hbound m).2⟩

/-- The limit `lim_m E[ν(□_m, ξ)]`. -/
noncomputable def cubeNuLimit (prob : unitInterval) (ξ : Fin d → ℝ) : ℝ :=
  limUnder atTop fun m => cubeNuMean prob m ξ

theorem tendsto_cubeNuLimit [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) (ξ : Fin d → ℝ) :
    Tendsto (fun m => cubeNuMean prob m ξ) atTop (𝓝 (cubeNuLimit prob ξ)) := by
  obtain ⟨L, hL, -⟩ := exists_tendsto_cubeNuMean hd hpc ξ
  rw [cubeNuLimit, hL.limUnder_eq]
  exact hL

/-- **The homogenized matrix** `ā` (Armstrong and Dario, Definition 5.1): the polarization of the
limit of `E[ν(□_m, ·)]`. -/
noncomputable def cubeAhom (prob : unitInterval) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => cubeNuLimit prob (Pi.single i 1 + Pi.single j 1) - cubeNuLimit prob (Pi.single i 1) -
    cubeNuLimit prob (Pi.single j 1)

theorem cubeAhom_symm (prob : unitInterval) (i j : Fin d) :
    cubeAhom (d := d) prob i j = cubeAhom prob j i := by
  simp only [cubeAhom, add_comm (Pi.single i 1 : Fin d → ℝ)]
  ring

/-- **Definition of `ā`** (Armstrong and Dario, Definition 5.1, in every dimension `d ≥ 2`):
`(1/2) ξ · ā ξ = lim_m E[ν(□_m, ξ)]`. -/
theorem cubeNuLimit_eq_cubeAhom [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) (ξ : Fin d → ℝ) :
    cubeNuLimit prob ξ = 1 / 2 * ∑ i, ∑ j, ξ i * cubeAhom prob i j * ξ j := by
  have h : Tendsto (fun m => cubeNuMean prob m ξ) atTop
      (𝓝 (1 / 2 * ∑ i, ∑ j, ξ i * ξ j * cubeAhom prob i j)) := by
    simp only [cubeNuMean_eq_sum_polarization prob _ ξ]
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      Tendsto.const_mul _ ?_)
    exact ((tendsto_cubeNuLimit hd hpc _).sub (tendsto_cubeNuLimit hd hpc _)).sub
      (tendsto_cubeNuLimit hd hpc _)
  rw [tendsto_nhds_unique (tendsto_cubeNuLimit hd hpc ξ) h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Upper bound on `ā`** (Armstrong and Dario, (5.1), upper bound):
`0 ≤ (1/2) ξ · ā ξ ≤ (3^d/4) |ξ|₁²`. -/
theorem cubeAhom_bounds [NeZero d] (hd : 2 ≤ d) {prob : unitInterval}
    (hpc : criticalProbability d < (prob : ℝ)) (ξ : Fin d → ℝ) :
    0 ≤ 1 / 2 * ∑ i, ∑ j, ξ i * cubeAhom prob i j * ξ j ∧
      1 / 2 * ∑ i, ∑ j, ξ i * cubeAhom prob i j * ξ j ≤ 3 ^ d / 4 * (∑ i, |ξ i|) ^ 2 := by
  obtain ⟨L, hL, h0, h1⟩ := exists_tendsto_cubeNuMean hd hpc ξ
  rw [← cubeNuLimit_eq_cubeAhom hd hpc, tendsto_nhds_unique (tendsto_cubeNuLimit hd hpc ξ) hL]
  exact ⟨h0, h1⟩

end Rigidity.Percolation
