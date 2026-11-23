import Rigidity.Proofs.Cluster.GeneralMuQuadratic
import Rigidity.Proofs.Percolation.GeneralDim.CubeSecondVariation

/-!
# Lemma 5.4 of Armstrong and Dario for `μ`, in every dimension

For a resolved triadic cube `U` of `ℤᵈ` and `n ≤` the scale of `U`, let `u` be the minimizer of
`μ(U, q)` (`cubeMuMinimizer`) and `u_V` the minimizer of `μ(V, q)` for each resolved subcube `V`
of scale `n`. The quantity

`D^μ_n(U, q) = ∑_V B_V(u|_V - u_V, u|_V - u_V) / 2`

(`cubeMuDefect`, zero off the event that the partition exists and resolves `U`) is the energy of
the differences `u - u_V` on the clusters of the subcubes. By the second variation
(`sum_cubeForm_sub_add_sum_cubeMu_subcubes_le`, display (5.11)) and the bound of the coarse
pairing of `u` over the exceptional edges (`exceptionalPairing_le`, the argument of
`sum_cubeMu_subcubes_sub_le` for an arbitrary minimizer), on the partition event,

`D^μ_n(U, q) + ∑_{x ∈ U} 1{V(x) res} μ(V(x), q) - |U| μ(U, q) ≤ K |q|₁² (t A + B / t) / 2`

with `A = ∑_{z ∈ U} size(z)^{2d-2}` and `B = ∑_{z ∈ U} size(z)^{2d} 1{z exceptional}`
(`cubeMuDefect_add_sum_sub_le`). With `t = 3^{-n/4}` the expectation of the right side is at most
`C |q|₁² |U| 3^{-n/4}` (`exists_integral_subaddBound_le`, the moment computation of
`exists_lintegral_sum_cubeMu_subcubes_sub_le`), and by the approximate stationarity of
`E[-μ]` across cubes of the same scale (`exists_lintegral_neg_cubeMu_le_of_scale_eq`), for all
triadic cubes `W`, `U` with `n = W.scale ≤ U.scale`,

`E[D^μ_n(U, q)] ≤ |U| (E[-μ(W, q)] - E[-μ(U, q)] + C |q|₁² (3^{-n/4} + exp(-c 3ⁿ)))`

(`exists_lintegral_cubeMuDefect_le`), the expectations of `-μ` being taken on the event that the
partition exists and resolves the cube. This is Lemma 5.4 of Armstrong and Dario for `μ` (display
(5.10), first term, before summing the increments), in every dimension `d ≥ 2`; the version for
`ν` is `exists_lintegral_cubeNuDefect_le`. The energy is that of the differences of the
functions on the clusters `C_*(V)`, as in dimension two; the rate `3^{-n/4}` is that of (4.32)
in expectation.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **The coarse pairing of a minimizer of `μ` over the exceptional edges** is at most
`K |q|₁² (t ∑_{z ∈ U} size(z)^{2d-2} + t⁻¹ ∑_{z ∈ U} size(z)^{2d} 1{z exceptional}) / 2`, for
every `t > 0`. -/
theorem exceptionalPairing_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (n : ℕ) (q : Fin d → ℝ) {u : CubeFun ω U}
    (hu : u ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w u = cubeCoarsePairing ω U q w) {t : ℝ}
    (ht : 0 < t) :
    ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
          ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
            x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
        q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0) ≤
      muSubaddConst d * (∑ i, |q i|) ^ 2 *
        (t * ∑ z ∈ U.toIntegerCube.vertices,
            ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) +
          (∑ z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
            (if ExceptionalMajorant ω n z then 1 else 0)) / t) / 2 := by
  set C := crossingClusterVertices ω U with hC
  set v : Vertex d → ℝ := fun z => vertexVariation ω C (cubeExtend ω U u) z with hv
  set N : Vertex d → ℝ := fun z => exceptionalEdgeCount ω U n z with hN
  set Q := ∑ i, |q i| with hQ
  set S := ∑ z ∈ U.toIntegerCube.vertices,
    ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) with hS
  set SF := ∑ z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
    (if ExceptionalMajorant ω n z then 1 else 0) with hSF
  set K := muSubaddConst d with hK
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hSF0 : 0 ≤ SF := Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity)
    (by split_ifs <;> norm_num)
  have hK0 : 0 ≤ K := muSubaddConst_nonneg d
  set Err := ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
          ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
            x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
        q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0)
    with hErr
  have herr : Err ≤ Q * ∑ z ∈ C, v z * N z := exceptional_error_le hd hP hU n q u
  have hRHS0 : 0 ≤ K * Q ^ 2 * (t * S + SF / t) / 2 := by positivity
  have hvN0 : 0 ≤ ∑ z ∈ C, v z * N z := Finset.sum_nonneg fun z _ =>
    mul_nonneg (vertexVariation_nonneg _ _ _ _) (exceptionalEdgeCount_nonneg _ _ _)
  by_cases hQz : Q = 0
  · have : Err ≤ 0 := by rw [hQz, zero_mul] at herr; exact herr
    linarith
  have hQpos : 0 < Q := lt_of_le_of_ne hQ0 (Ne.symm hQz)
  have hB : cubeForm ω U u u ≤ 2 * d * coarseGradConstant d ^ 2 * Q ^ 2 * S := by
    have h := cubeForm_cubeMu_minimizer_le hd hP hU q hu hvar
    rw [div_le_div_iff_of_pos_right U.latticeVolume_pos] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => by positivity
  have hv2 : ∑ z ∈ C, v z ^ 2 ≤ 4 * d * cubeForm ω U u u := by
    rw [← sum_gradNormIn_sq_eq_cubeForm u, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have h1 := vertexVariation_le_gradNormIn ω C (cubeExtend ω U u) z
    have h0 := vertexVariation_nonneg ω C (cubeExtend ω U u) z
    have hd' : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
    calc v z ^ 2 ≤ (2 * √(d : ℝ) * gradNormIn (openGraph ω) C (cubeExtend ω U u) z) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = 4 * d * gradNormIn (openGraph ω) C (cubeExtend ω U u) z ^ 2 := by
          rw [mul_pow, mul_pow, hd']
          ring
  have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hN2 : ∑ z ∈ C, N z ^ 2 ≤ d ^ 2 * 9 ^ d * SF := by
    calc ∑ z ∈ C, N z ^ 2 ≤ ∑ z ∈ U.toIntegerCube.vertices, N z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => sq_nonneg _
      _ ≤ ∑ z ∈ U.toIntegerCube.vertices, d ^ 2 * 9 ^ d *
            (((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
              (if ExceptionalMajorant ω n z then 1 else 0)) := by
          refine Finset.sum_le_sum fun z _ => ?_
          have h := exceptionalEdgeCount_le hP U n z
          have h0 := exceptionalEdgeCount_nonneg (ω := ω) U n z
          have h2 := pow_le_pow_left₀ h0 h 2
          refine h2.trans (le_of_eq ?_)
          rw [h9]
          split_ifs <;> ring
      _ = d ^ 2 * 9 ^ d * SF := by rw [hSF, Finset.mul_sum]
  set τ := t / Q with hτdef
  have hτ : 0 < τ := div_pos ht hQpos
  have hY : ∑ z ∈ C, v z * N z ≤ (τ * ∑ z ∈ C, v z ^ 2 + (∑ z ∈ C, N z ^ 2) / τ) / 2 := by
    have h : ∑ z ∈ C, 2 * (v z * N z) ≤ ∑ z ∈ C, (τ * v z ^ 2 + N z ^ 2 / τ) :=
      Finset.sum_le_sum fun z _ => two_mul_mul_le_add_div hτ _ _
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at h
    linarith
  have hfin : Q * ((τ * (4 * d * (2 * d * coarseGradConstant d ^ 2 * Q ^ 2 * S)) +
      (d ^ 2 * 9 ^ d * SF) / τ) / 2) =
      (t * (8 * d ^ 2 * coarseGradConstant d ^ 2) * Q ^ 2 * S +
        Q ^ 2 * ((d : ℝ) ^ 2 * 9 ^ d) * SF / t) / 2 := by
    rw [hτdef]
    field_simp
    ring
  have hsplit : K * Q ^ 2 * (t * S + SF / t) / 2 =
      (t * (8 * d ^ 2 * coarseGradConstant d ^ 2) * Q ^ 2 * S +
        Q ^ 2 * ((d : ℝ) ^ 2 * 9 ^ d) * SF / t) / 2 +
      (Q ^ 2 * ((d : ℝ) ^ 2 * 9 ^ d) * (t * S) +
        8 * d ^ 2 * coarseGradConstant d ^ 2 * Q ^ 2 * (SF / t)) / 2 := by
    rw [hK, muSubaddConst]
    ring
  have hextra : 0 ≤ (Q ^ 2 * ((d : ℝ) ^ 2 * 9 ^ d) * (t * S) +
      8 * d ^ 2 * coarseGradConstant d ^ 2 * Q ^ 2 * (SF / t)) / 2 := by positivity
  calc Err ≤ Q * ∑ z ∈ C, v z * N z := herr
    _ ≤ Q * ((τ * ∑ z ∈ C, v z ^ 2 + (∑ z ∈ C, N z ^ 2) / τ) / 2) :=
        mul_le_mul_of_nonneg_left hY hQ0
    _ ≤ Q * ((τ * (4 * d * (2 * d * coarseGradConstant d ^ 2 * Q ^ 2 * S)) +
          (d ^ 2 * 9 ^ d * SF) / τ) / 2) := by
        gcongr
        · exact hv2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
    _ = _ := hfin
    _ ≤ K * Q ^ 2 * (t * S + SF / t) / 2 := by linarith

/-- A minimizer of `μ(U, q)`, on the partition event and for a resolved cube (zero otherwise). -/
noncomputable def cubeMuMinimizer (ω : Configuration d) (U : TriadicCube d) (q : Fin d → ℝ) :
    CubeFun ω U :=
  if h : 0 < d ∧ PartitionEvent ω ∧ PartitionResolved ω U then
    (exists_cubeMu_minimizer h.1 h.2.1 h.2.2 q).choose
  else 0

theorem cubeMuMinimizer_spec (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    cubeMuMinimizer ω U q ∈ cubeHarmonic ω U ∧ ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w (cubeMuMinimizer ω U q) = cubeCoarsePairing ω U q w := by
  have h : 0 < d ∧ PartitionEvent ω ∧ PartitionResolved ω U := ⟨hd, hP, hU⟩
  rw [cubeMuMinimizer, dif_pos h]
  exact ⟨(exists_cubeMu_minimizer h.1 h.2.1 h.2.2 q).choose_spec.1,
    (exists_cubeMu_minimizer h.1 h.2.1 h.2.2 q).choose_spec.2.1⟩

/-- The energy `D^μ_n(U, q)` of the differences between the minimizer of `μ(U, q)` and the
minimizers on the resolved subcubes of scale `n` (zero off the event that the partition exists
and resolves `U`). -/
noncomputable def cubeMuDefect (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (q : Fin d → ℝ) : ℝ :=
  if PartitionEvent ω ∧ PartitionResolved ω U then
    ∑ V ∈ U.resolvedSubcubesAt ω n,
      cubeForm ω V (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q)
        (cubeRestrictExt V (cubeMuMinimizer ω U q) - cubeMuMinimizer ω V q) / 2
  else 0

theorem cubeMuDefect_nonneg (ω : Configuration d) (U : TriadicCube d) (n : ℕ) (q : Fin d → ℝ) :
    0 ≤ cubeMuDefect ω U n q := by
  unfold cubeMuDefect
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => div_nonneg (cubeForm_self_nonneg _) (by norm_num)
  · exact le_rfl

/-- **Deterministic form of Lemma 5.4 for `μ`** (display (5.11) with the error of (4.32)). -/
theorem cubeMuDefect_add_sum_sub_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin d → ℝ) {t : ℝ}
    (ht : 0 < t) :
    cubeMuDefect ω U n q + (∑ x ∈ U.toIntegerCube.vertices,
        (if PartitionResolved ω (triadicCubeAt n x) then cubeMu ω (triadicCubeAt n x) q
          else 0) - cubeMu ω U q * U.latticeVolume) ≤
      muSubaddConst d * (∑ i, |q i|) ^ 2 *
        (t * ∑ z ∈ U.toIntegerCube.vertices,
            ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) +
          (∑ z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
            (if ExceptionalMajorant ω n z then 1 else 0)) / t) / 2 := by
  obtain ⟨hu, hvar⟩ := cubeMuMinimizer_spec hd hP hU q
  have h := sum_cubeForm_sub_add_sum_cubeMu_subcubes_le hd hP hU hn q hu hvar
    (fun V => cubeMuMinimizer ω V q)
    (fun V hV => cubeMuMinimizer_spec hd hP (mem_resolvedSubcubesAt.1 hV).2 q)
  have he := exceptionalPairing_le hd hP hU n q hu hvar ht
  rw [cubeMuDefect, if_pos ⟨hP, hU⟩]
  linarith

/-- **The expected subadditivity bound** with `t = 3^{-n/4}`:
`E[t A + B / t] ≤ C |U| 3^{-n/4}`, `A = ∑_{z ∈ U} size(z)^{2d-2}`,
`B = ∑_{z ∈ U} size(z)^{2d} 1{z exceptional}`. -/
theorem exists_integral_subaddBound_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube d) (n : ℕ), n ≤ U.scale →
      Integrable (fun ω => 1 / √(√((3 : ℝ) ^ n)) *
          partitionSizeSum ω U.toIntegerCube.vertices (2 * (d - 1)) +
        exceptionalSizeSum ω U.toIntegerCube.vertices n / (1 / √(√((3 : ℝ) ^ n))))
        (latticeBondLaw d p) ∧
      ∫ ω, (1 / √(√((3 : ℝ) ^ n)) * partitionSizeSum ω U.toIntegerCube.vertices (2 * (d - 1)) +
          exceptionalSizeSum ω U.toIntegerCube.vertices n / (1 / √(√((3 : ℝ) ^ n))))
          ∂(latticeBondLaw d p) ≤
        C * U.latticeVolume / √(√((3 : ℝ) ^ n)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨θ, hθ, hmom⟩ := exists_integral_sum_stoppingSize_pow_le hd hpc
  obtain ⟨C₁, c₁, C₂, hC₁, hc₁, hC₂, hEM⟩ := exists_sum_measure_exceptionalMajorant_le hd hpc
  set M₁ : ℝ := 2 * ((2 * (d - 1)).factorial : ℝ) * θ ^ (2 * (d - 1)) with hM₁
  set M₄ : ℝ := 2 * ((2 * (2 * d)).factorial : ℝ) * θ ^ (2 * (2 * d)) with hM₄
  set M' : ℝ := M₄ + C₁ / c₁ + C₂ with hM'
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₄0 : 0 ≤ M₄ := by positivity
  have hM'0 : 0 ≤ M' := by positivity
  refine ⟨M₁ + M', by positivity, fun U n hn => ?_⟩
  set μ := latticeBondLaw d p with hμ
  set S := U.toIntegerCube.vertices with hSdef
  have hcard : (S.card : ℝ) = U.latticeVolume := U.card_toIntegerCube_vertices
  have hvol := U.latticeVolume_pos
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
  refine ⟨(hA_int.const_mul t).add (hB_int.div_const t), ?_⟩
  rw [integral_add (hA_int.const_mul t) (hB_int.div_const t), integral_const_mul, integral_div]
  calc t * ∫ ω, partitionSizeSum ω S (2 * (d - 1)) ∂μ + (∫ ω, exceptionalSizeSum ω S n ∂μ) / t
      ≤ t * (M₁ * U.latticeVolume) + U.latticeVolume * M' / X / t := by gcongr
    _ = (M₁ + M') * U.latticeVolume / Y := by
        rw [ht, hXY]
        field_simp

theorem integral_neg_cubeMu_indicator_eq_toReal (hd : 0 < d) (p : unitInterval)
    (V : TriadicCube d) (q : Fin d → ℝ) :
    ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0)
        ∂(latticeBondLaw d p) =
      (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
        ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p)).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by
    simp only [Pi.zero_apply]
    split_ifs with hω
    · exact neg_nonneg.2 (cubeMu_nonpos hd hω.1 hω.2 q)
    · exact le_rfl) (measurable_neg_cubeMu_indicator_real hd _ q).aestronglyMeasurable]
  congr 2
  funext ω
  split_ifs
  · rfl
  · exact ENNReal.ofReal_zero

/-- **Approximate stationarity of `E[-μ]`** across cubes of the same scale, for the real
expectations on the event that the partition exists and resolves the cube. -/
theorem exists_integral_neg_cubeMu_le_of_scale_eq [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V W : TriadicCube d), V.scale = W.scale →
      ∀ q : Fin d → ℝ,
      ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω W then -cubeMu ω W q else 0)
          ∂(latticeBondLaw d p) ≤
        ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0)
          ∂(latticeBondLaw d p) +
          C * ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_neg_cubeMu_le_of_scale_eq hd hpc
  obtain ⟨C', -, hb⟩ := exists_lintegral_neg_cubeMu_le hd hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun V W hVW q => ?_⟩
  rw [integral_neg_cubeMu_indicator_eq_toReal hd0, integral_neg_cubeMu_indicator_eq_toReal hd0]
  have hV : ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
      ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb V q)
  have hX : C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) ≠ ∞ :=
    ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hV, hX⟩) (h V W hVW q)
  rw [ENNReal.toReal_add hV hX, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at h1
  exact h1

/-- On the partition event, the bound of `exceptionalPairing_le` in terms of the partition sizes
`size(z) = 3^{scale of □_𝒫(z)}`. -/
theorem subaddBound_eq (hP : PartitionEvent ω) (U : TriadicCube d) (n : ℕ) (q : Fin d → ℝ)
    (t : ℝ) :
    muSubaddConst d * (∑ i, |q i|) ^ 2 *
        (t * ∑ z ∈ U.toIntegerCube.vertices,
            ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) +
          (∑ z ∈ U.toIntegerCube.vertices, ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * d) *
            (if ExceptionalMajorant ω n z then 1 else 0)) / t) / 2 =
      muSubaddConst d * (∑ i, |q i|) ^ 2 *
        (t * partitionSizeSum ω U.toIntegerCube.vertices (2 * (d - 1)) +
          exceptionalSizeSum ω U.toIntegerCube.vertices n / t) / 2 := by
  unfold partitionSizeSum exceptionalSizeSum
  congr 4
  · exact Finset.sum_congr rfl fun z _ => by rw [stoppingSize_goodCubes_eq hP z]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [stoppingSize_goodCubes_eq hP z]
    by_cases hz : ExceptionalMajorant ω n z
    · rw [if_pos hz, Set.indicator_of_mem (show ω ∈ {ω' | ExceptionalMajorant ω' n z} from hz),
        Pi.one_apply]
    · rw [if_neg hz, Set.indicator_of_notMem
        (show ω ∉ {ω' | ExceptionalMajorant ω' n z} from hz)]

/-- **Lemma 5.4 of Armstrong and Dario for `μ`** (display (5.10), first term, before summing the
increments), in every dimension `d ≥ 2`: for triadic cubes `W`, `U` with `n = W.scale ≤ U.scale`,
`E[D^μ_n(U, q)] ≤ |U| (E[-μ(W, q)] - E[-μ(U, q)] + C |q|₁² (3^{-n/4} + exp(-c 3ⁿ)))`, the
expectations of `-μ` being taken on the event that the partition exists and resolves the cube. -/
theorem exists_lintegral_cubeMuDefect_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U W : TriadicCube d) (q : Fin d → ℝ),
      W.scale ≤ U.scale →
      ∫⁻ ω, ENNReal.ofReal (cubeMuDefect ω U W.scale q) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal (U.latticeVolume *
          (∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω W then -cubeMu ω W q else 0)
              ∂(latticeBondLaw d p) -
            ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω U then -cubeMu ω U q else 0)
              ∂(latticeBondLaw d p) +
            C * (∑ i, |q i|) ^ 2 *
              (1 / √(√((3 : ℝ) ^ W.scale)) + Real.exp (-c * (3 : ℝ) ^ W.scale)))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₀, hC₀, hbd⟩ := exists_integral_subaddBound_le hd hpc
  obtain ⟨Cs, hCs, c, hc, hstat⟩ := exists_integral_neg_cubeMu_le_of_scale_eq hd hpc
  have hK0 : 0 ≤ muSubaddConst d := muSubaddConst_nonneg d
  refine ⟨muSubaddConst d * C₀ / 2 + Cs, by positivity, c, hc, fun U W q hn => ?_⟩
  obtain ⟨hBint, hBle⟩ := hbd U W.scale hn
  set μ := latticeBondLaw d p with hμ
  set n := W.scale with hndef
  set S := U.toIntegerCube.vertices with hS
  set t : ℝ := 1 / √(√((3 : ℝ) ^ n)) with ht
  have ht0 : 0 < t := by positivity
  have hQs0 : 0 ≤ (∑ i, |q i|) ^ 2 := by positivity
  have hvol := U.latticeVolume_pos
  set f : TriadicCube d → Configuration d → ℝ := fun V ω =>
    if PartitionEvent ω ∧ PartitionResolved ω V then -cubeMu ω V q else 0 with hf
  have hf0 : ∀ V ω, 0 ≤ f V ω := fun V ω => by
    simp only [hf]
    split_ifs with h
    · exact neg_nonneg.2 (cubeMu_nonpos hd0 h.1 h.2 q)
    · exact le_rfl
  have hfint : ∀ V, Integrable (f V) μ := fun V => integrable_neg_cubeMu_indicator hd hpc V q
  have hpoint : ∀ ω, cubeMuDefect ω U n q ≤
      muSubaddConst d * (∑ i, |q i|) ^ 2 *
          (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
        ∑ x ∈ S, f (triadicCubeAt n x) ω - U.latticeVolume * f U ω := by
    intro ω
    have hA0 : 0 ≤ partitionSizeSum ω S (2 * (d - 1)) := Finset.sum_nonneg fun z _ =>
      pow_nonneg (stoppingSize_goodCubes_nonneg ω z) _
    have hB0 : 0 ≤ exceptionalSizeSum ω S n := Finset.sum_nonneg fun z _ =>
      mul_nonneg (pow_nonneg (stoppingSize_goodCubes_nonneg ω z) _)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hbnd0 : 0 ≤ muSubaddConst d * (∑ i, |q i|) ^ 2 *
        (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 := by
      positivity
    have hsum0 : 0 ≤ ∑ x ∈ S, f (triadicCubeAt n x) ω := Finset.sum_nonneg fun x _ => hf0 _ _
    by_cases h : PartitionEvent ω ∧ PartitionResolved ω U
    · have h1 := cubeMuDefect_add_sum_sub_le hd0 h.1 h.2 hn q ht0
      rw [subaddBound_eq h.1] at h1
      have h2 : ∑ x ∈ S, (if PartitionResolved ω (triadicCubeAt n x) then
          cubeMu ω (triadicCubeAt n x) q else 0) = -∑ x ∈ S, f (triadicCubeAt n x) ω := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hf, h.1, true_and]
        split_ifs <;> ring
      have h3 : f U ω = -cubeMu ω U q := by simp only [hf, if_pos h]
      rw [h2] at h1
      rw [h3]
      linarith
    · have h0 : cubeMuDefect ω U n q = 0 := by rw [cubeMuDefect, if_neg h]
      have h3 : f U ω = 0 := by simp only [hf, if_neg h]
      rw [h0, h3]
      linarith
  have hint1 : Integrable (fun ω => muSubaddConst d * (∑ i, |q i|) ^ 2 *
      (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2) μ :=
    (hBint.const_mul _).div_const 2
  have hint2 : Integrable (fun ω => ∑ x ∈ S, f (triadicCubeAt n x) ω) μ :=
    integrable_finsetSum _ fun x _ => hfint _
  have hint3 : Integrable (fun ω => U.latticeVolume * f U ω) μ := (hfint U).const_mul _
  have hint12 : Integrable (fun ω => muSubaddConst d * (∑ i, |q i|) ^ 2 *
      (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
        ∑ x ∈ S, f (triadicCubeAt n x) ω) μ := hint1.add hint2
  have hgint : Integrable (fun ω => muSubaddConst d * (∑ i, |q i|) ^ 2 *
      (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
        ∑ x ∈ S, f (triadicCubeAt n x) ω - U.latticeVolume * f U ω) μ := hint12.sub hint3
  have hgval : ∫ ω, (muSubaddConst d * (∑ i, |q i|) ^ 2 *
      (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
        ∑ x ∈ S, f (triadicCubeAt n x) ω - U.latticeVolume * f U ω) ∂μ =
      muSubaddConst d * (∑ i, |q i|) ^ 2 *
        (∫ ω, (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) ∂μ) / 2 +
        ∑ x ∈ S, ∫ ω, f (triadicCubeAt n x) ω ∂μ - U.latticeVolume * ∫ ω, f U ω ∂μ := by
    rw [integral_sub hint12 hint3, integral_add hint1 hint2, integral_div, integral_const_mul,
      integral_finsetSum _ fun x _ => hfint _, integral_const_mul]
  have hsum : ∑ x ∈ S, ∫ ω, f (triadicCubeAt n x) ω ∂μ ≤
      U.latticeVolume * (∫ ω, f W ω ∂μ +
        Cs * ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ n))) := by
    calc ∑ x ∈ S, ∫ ω, f (triadicCubeAt n x) ω ∂μ ≤ ∑ x ∈ S, (∫ ω, f W ω ∂μ +
          Cs * ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ n))) :=
          Finset.sum_le_sum fun x _ => hstat W (triadicCubeAt n x) (scale_triadicCubeAt n x).symm q
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hS, U.card_toIntegerCube_vertices]
  have hts : C₀ * U.latticeVolume / √(√((3 : ℝ) ^ n)) = C₀ * U.latticeVolume * t := by
    rw [ht]
    ring
  rw [hts] at hBle
  have hI := mul_le_mul_of_nonneg_left hBle
    (by positivity : (0 : ℝ) ≤ muSubaddConst d * (∑ i, |q i|) ^ 2 / 2)
  have he0 : 0 ≤ Real.exp (-c * (3 : ℝ) ^ n) := (Real.exp_pos _).le
  have k1 : 0 ≤ U.latticeVolume * (muSubaddConst d * C₀ / 2 * (∑ i, |q i|) ^ 2 *
      Real.exp (-c * (3 : ℝ) ^ n)) := by positivity
  have k2 : 0 ≤ U.latticeVolume * (Cs * (∑ i, |q i|) ^ 2 * t) := by positivity
  have hg0 : ∀ ω, 0 ≤ muSubaddConst d * (∑ i, |q i|) ^ 2 *
      (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
        ∑ x ∈ S, f (triadicCubeAt n x) ω - U.latticeVolume * f U ω := fun ω =>
    (cubeMuDefect_nonneg ω U n q).trans (hpoint ω)
  calc ∫⁻ ω, ENNReal.ofReal (cubeMuDefect ω U n q) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (muSubaddConst d * (∑ i, |q i|) ^ 2 *
          (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
            ∑ x ∈ S, f (triadicCubeAt n x) ω - U.latticeVolume * f U ω) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpoint ω)
    _ = ENNReal.ofReal (∫ ω, (muSubaddConst d * (∑ i, |q i|) ^ 2 *
          (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) / 2 +
            ∑ x ∈ S, f (triadicCubeAt n x) ω - U.latticeVolume * f U ω) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hgint (ae_of_all _ hg0)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [hgval]
        have e1 : muSubaddConst d * (∑ i, |q i|) ^ 2 *
            (∫ ω, (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) ∂μ) /
              2 = muSubaddConst d * (∑ i, |q i|) ^ 2 / 2 *
            (∫ ω, (t * partitionSizeSum ω S (2 * (d - 1)) + exceptionalSizeSum ω S n / t) ∂μ) :=
          by ring
        rw [e1]
        nlinarith

end Rigidity.Percolation
