import Rigidity.Proofs.Cluster.GeneralRestrictMoments

/-!
# The expected energy of the coarsened maximizers of `ν`, in every dimension

Armstrong and Dario, display (4.25), in expectation, in every dimension `d ≥ 2`: for every `a ≥ 1`
there is `C < ∞` such that for every triadic cube `V` and slope `ξ`,

`E[∑_{x ∈ V} |∇[v(·, V, ξ)]_𝒫|²(x)] ≤ C |ξ|₁² |V|^{1 + 1/a}`

(`exists_lintegral_coarse_cubeNuSolution_le`). Pointwise, by Lemma 3.3 the energy of the
coarsening of `w` is at most `K² ∑_z size(z)^{2d-1} |∇w|²(z) ≤ K² X^{1/a} B(w, w)`,
`X = ∑_{z ∈ V} size(z)^{(2d-1)a}`, since each `size(z)^{2d-1}` is at most `X^{1/a}`
(`sum_gradNormIn_coarse_sq_le_rpow`); with `B(v, v) ≤ (3^d/2) |V| |ξ|₁²`, Jensen's inequality for the
concave power `1/a` (`lintegral_ofReal_rpow_le`) and the moments of the partition sizes give the
bound. Armstrong and Dario state it with the loss `3^{δ n}`, `δ > 0` arbitrary, which is the factor
`|V|^{1/a}` for `a` large. This is the general-dimensional form of
`Rigidity.Proofs.Cluster.exists_lintegral_coarse_minimizer_le`, with the partition sizes in place
of the planar reach.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
open scoped BigOperators Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- A term of a finite sum of nonnegative numbers is at most the `a`-th root of the sum of the
`a`-th powers. -/
theorem le_rpow_sum_pow {ι : Type*} {s : Finset ι} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {a : ℕ}
    (ha : 1 ≤ a) {i : ι} (hi : i ∈ s) : f i ≤ (∑ j ∈ s, f j ^ a) ^ (1 / (a : ℝ)) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 : f i ^ a ≤ ∑ j ∈ s, f j ^ a :=
    Finset.single_le_sum (f := fun j => f j ^ a) (fun j _ => pow_nonneg (hf j) a) hi
  calc f i = (f i ^ a) ^ (1 / (a : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hf i), mul_one_div_cancel ha0.ne',
          Real.rpow_one]
    _ ≤ (∑ j ∈ s, f j ^ a) ^ (1 / (a : ℝ)) :=
        Real.rpow_le_rpow (pow_nonneg (hf i) a) h1 (by positivity)

/-- **The energy of the coarsening by the moments of the sizes**, pointwise: on a resolved cube,
`∑_V |∇[w]_𝒫|² ≤ K² X^{1/a} B(w, w)`, `X = ∑_{z ∈ V} size(z)^{(2d-1)a}`. -/
theorem sum_gradNormIn_coarse_sq_le_rpow (hd : 0 < d) (hP : PartitionEvent ω)
    {V : TriadicCube d} (hV : PartitionResolved ω V) (w : CubeFun ω V) {a : ℕ} (ha : 1 ≤ a) :
    ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V w (partitionAnchor ω x)) x ^ 2 ≤
      coarseGradConstant d ^ 2 *
        (partitionSizeSum ω V.toIntegerCube.vertices ((2 * d - 1) * a) ^ (1 / (a : ℝ)) *
          cubeForm ω V w w) := by
  have h := partition_sum_gradNormIn_coarseAnchor_rpow_le hd hP hV (cubeExtend ω V w) (s := 2)
    (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
  set C := crossingClusterVertices ω V with hC
  set X := partitionSizeSum ω V.toIntegerCube.vertices ((2 * d - 1) * a) with hX
  have hB := sum_clusterGradSq_eq_cubeForm V w
  have hle : ∀ z ∈ C, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1) ≤
      X ^ (1 / (a : ℝ)) := by
    intro z hz
    have hzV : z ∈ V.toIntegerCube.vertices := Finset.filter_subset _ _ hz
    have h1 := le_rpow_sum_pow (s := V.toIntegerCube.vertices)
      (f := fun z => TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1))
      (fun z => pow_nonneg (TriadicCube.stoppingSize_nonneg _ _) _) ha hzV
    refine h1.trans (le_of_eq ?_)
    rw [hX, partitionSizeSum]
    congr 1
    exact Finset.sum_congr rfl fun y _ => by rw [← pow_mul]
  calc ∑ z ∈ C, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ ((2 : ℝ) * (d : ℝ) - 1) *
        gradNormIn (openGraph ω) C (cubeExtend ω V w) z ^ 2
      = ∑ z ∈ C, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z ^ (2 * d - 1) *
          clusterGradSq ω C (cubeExtend ω V w) z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _),
          stoppingSize_goodCubes_eq hP z,
          show (2 : ℝ) * (d : ℝ) - 1 = ((2 * d - 1 : ℕ) : ℝ) by
            rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num, Real.rpow_natCast]
    _ ≤ ∑ z ∈ C, X ^ (1 / (a : ℝ)) * clusterGradSq ω C (cubeExtend ω V w) z :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hle z hz)
          (clusterGradSq_nonneg _ _ _ _)
    _ = X ^ (1 / (a : ℝ)) * cubeForm ω V w w := by rw [← Finset.mul_sum, hB]

theorem measurable_partitionSizeSum_rpow (S : Finset (Vertex d)) (k : ℕ) (r : ℝ) :
    Measurable fun ω : Configuration d => partitionSizeSum ω S k ^ r :=
  (measurable_partitionSizeSum S k).pow_const r

/-- **Jensen's inequality for a concave power**: `E[X^{b/a}] ≤ E[X]^{b/a}` for `b ≤ a`, in the form
used below. -/
theorem lintegral_ofReal_rpow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ r) ∂μ ≤ (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) ^ r := by
  have hpt : ∀ ω, ENNReal.ofReal (X ω ^ r) = ENNReal.ofReal (X ω) ^ r := fun ω =>
    (ENNReal.ofReal_rpow_of_nonneg (hX0 ω) hr0.le).symm
  simp only [hpt]
  rcases hr1.lt_or_eq with hlt | heq
  · have h1 : (1 : ℝ) < 1 / r := by rw [lt_div_iff₀ hr0]; linarith
    have hpq := Real.HolderConjugate.conjExponent h1
    have hY : Measurable fun ω => ENNReal.ofReal (X ω) ^ r :=
      (ENNReal.measurable_ofReal.comp hXm).pow_const r
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hY.aemeasurable
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.one_rpow] at h
    refine h.trans (le_of_eq ?_)
    have e : (1 / (1 / r) : ℝ) = r := by field_simp
    rw [e]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
  · subst heq
    simp

/-- **The expected energy of the coarsened maximizer of `ν`** (Armstrong and Dario, (4.25), in
expectation, every dimension `d ≥ 2`): for every `a ≥ 1`,
`E[∑_{x ∈ V} |∇[v(·, V, ξ)]_𝒫|²(x)] ≤ C |ξ|₁² |V| |V|^{1/a}`. -/
theorem exists_lintegral_coarse_cubeNuSolution_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {a : ℕ} (ha : 1 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : TriadicCube d) (ξ : Fin d → ℝ),
      ∫⁻ ω, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) x ^ 2)
          ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (C * (∑ i, |ξ i|) ^ 2 * V.latticeVolume *
          V.latticeVolume ^ (1 / (a : ℝ))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  set τ : ℕ := (2 * d - 1) * a with hτ
  set Cτ : ℝ := 2 * (τ.factorial : ℝ) * θ ^ τ with hCτ
  have hCτ0 : 0 ≤ Cτ := by positivity
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  set K : ℝ := coarseGradConstant d ^ 2 * (2 * (3 ^ d / 4)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * Cτ ^ (1 / (a : ℝ)), by positivity, fun V ξ => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set P : ℝ := (∑ i, |ξ i|) ^ 2 with hP
  have hP0 : 0 ≤ P := sq_nonneg _
  have hvol := V.latticeVolume_pos
  set X : Configuration d → ℝ := fun ω =>
    partitionSizeSum ω V.toIntegerCube.vertices τ with hXdef
  have hXm : Measurable X := measurable_partitionSizeSum _ _
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => partitionSizeSum_nonneg _ _
  have hpoint : ∀ᵐ ω ∂μ, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
        (fun x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) x ^ 2) ≤
      ENNReal.ofReal (K * P * V.latticeVolume) * ENNReal.ofReal (X ω ^ (1 / (a : ℝ))) := by
    filter_upwards [ae_partitionEvent hd hpc] with ω hPω
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hV : PartitionResolved ω V
    · rw [cubeNuSolution_eq hPω hV]
      refine (sum_gradNormIn_coarse_sq_le_rpow hd0 hPω hV _ ha).trans ?_
      obtain ⟨hv, hvar⟩ := cubeNuMaximizer_spec (ω := ω) V ξ
      have hν := cubeNu_mul_latticeVolume_eq ξ hv hvar
      have hle := cubeNu_le (ω := ω) (U := V) ξ
      have hB : cubeForm ω V (cubeNuMaximizer ω V ξ) (cubeNuMaximizer ω V ξ) ≤
          2 * (3 ^ d / 4) * P * V.latticeVolume := by
        have := mul_le_mul_of_nonneg_right hle hvol.le
        rw [hP]
        nlinarith
      have hXr : 0 ≤ X ω ^ (1 / (a : ℝ)) := Real.rpow_nonneg (hX0 ω) _
      calc coarseGradConstant d ^ 2 *
            (partitionSizeSum ω V.toIntegerCube.vertices ((2 * d - 1) * a) ^ (1 / (a : ℝ)) *
              cubeForm ω V (cubeNuMaximizer ω V ξ) (cubeNuMaximizer ω V ξ))
          ≤ coarseGradConstant d ^ 2 * (X ω ^ (1 / (a : ℝ)) *
              (2 * (3 ^ d / 4) * P * V.latticeVolume)) := by
            gcongr
        _ = K * P * V.latticeVolume * X ω ^ (1 / (a : ℝ)) := by rw [hK]; ring
    · have h0 : cubeNuSolution ω V ξ = 0 := by rw [cubeNuSolution, if_neg fun h => hV h.2]
      rw [h0]
      simp only [map_zero, Pi.zero_apply]
      have hz : ∀ x, gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
          (fun _ => (0 : ℝ)) x ^ 2 = 0 := fun x => by simp [gradNormIn]
      simp only [hz, Finset.sum_const_zero]
      have := Real.rpow_nonneg (hX0 ω) (1 / (a : ℝ))
      positivity
  have hEX : ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ ≤ ENNReal.ofReal (Cτ * V.latticeVolume) := by
    have hint := (hmom τ V.toIntegerCube.vertices).1
    have hint2 := (hmom τ V.toIntegerCube.vertices).2
    calc ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ = ENNReal.ofReal (∫ ω, X ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal (f := X) hint (ae_of_all _ hX0)).symm
      _ ≤ ENNReal.ofReal (Cτ * V.latticeVolume) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← V.card_toIntegerCube_vertices]
          exact hint2
  have hJ := lintegral_ofReal_rpow_le μ hXm hX0 (r := 1 / (a : ℝ)) (by positivity)
    (by rw [div_le_one ha0]; exact_mod_cast ha)
  calc ∫⁻ ω, ENNReal.ofReal (∑ x ∈ V.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph d) V.toIntegerCube.vertices
            (fun x => cubeExtend ω V (cubeNuSolution ω V ξ) (partitionAnchor ω x)) x ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (K * P * V.latticeVolume) *
          ENNReal.ofReal (X ω ^ (1 / (a : ℝ))) ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (K * P * V.latticeVolume) *
          ∫⁻ ω, ENNReal.ofReal (X ω ^ (1 / (a : ℝ))) ∂μ :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hXm.pow_const _))
    _ ≤ ENNReal.ofReal (K * P * V.latticeVolume) *
          ENNReal.ofReal (Cτ * V.latticeVolume) ^ (1 / (a : ℝ)) := by
        gcongr
        exact hJ.trans (ENNReal.rpow_le_rpow hEX (by positivity))
    _ = ENNReal.ofReal (K * Cτ ^ (1 / (a : ℝ)) * P * V.latticeVolume *
          V.latticeVolume ^ (1 / (a : ℝ))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hCτ0 hvol.le]
        congr 1
        ring

end Rigidity.Percolation
