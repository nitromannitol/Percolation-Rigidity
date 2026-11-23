import Rigidity.Proofs.Cluster.GeneralMuLocal

/-!
# Stationary local versions of `μ` in every dimension

For a triadic cube `V` of scale `n` with centre `c`, the stationary local version of `-μ` is the
local version on the cube of scale `n` centred at the origin, evaluated at the configuration
translated by `-c`. It is measurable for the σ-algebra of the bonds inside the local region of `V`
(Armstrong and Dario, (4.39)), so that stationary versions on cubes with disjoint local regions are
independent, and it is exactly translation covariant: its value on `V + z` at the configuration
translated by `z` is its value on `V`, for every `z ∈ 3ⁿ ℤ^d`. Since the bond law is translation
invariant, its law does not depend on the position of `V` (Armstrong and Dario, (4.40)).

On the event that the partition agrees with the capped partition on `V` and, after the translation
by `-c`, on the cube at the origin, the stationary version equals `1{P, V res} (-μ(V, q))`; this
event fails with probability at most `C exp(-c 3ⁿ)`. Hence the expectations of the stationary
version and of `1{P, V res} (-μ(V, q))` differ by at most `C |q|₁² exp(-c 3ⁿ)`, and the
expectations of `1{P, V res} (-μ(V, q))` and `1{P, W res} (-μ(W, q))` for cubes of the same scale
differ by at most `C |q|₁² exp(-c 3ⁿ)` (approximate stationarity of `μ`).
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- A function agreeing with another off a measurable set `B` and bounded by `K` has an
expectation exceeding that of the other by at most `K P(B)`. -/
theorem lintegral_le_lintegral_add_of_le_off {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ≥0∞} {B : Set Ω} (hB : MeasurableSet B) {K : ℝ≥0∞} (hf : ∀ ω, f ω ≤ K)
    (hfg : ∀ ω, ω ∉ B → f ω ≤ g ω) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ + K * μ B := by
  calc ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, (g ω + B.indicator (fun _ => K) ω) ∂μ :=
        lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            exact le_add_left (hf ω)
          · rw [Set.indicator_of_notMem hω, add_zero]
            exact hfg ω hω
    _ = ∫⁻ ω, g ω ∂μ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂μ :=
        lintegral_add_right _ (measurable_const.indicator hB)
    _ = ∫⁻ ω, g ω ∂μ + K * μ B := by rw [lintegral_indicator_const hB]

/-- `|V|² exp(-c 3ⁿ) ≤ M exp(-(c/2) 3ⁿ)` for triadic cubes `V` of scale `n`. -/
theorem latticeVolume_sq_mul_exp_le (d : ℕ) {c : ℝ} (hc : 0 < c) (V : TriadicCube d) :
    V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale) ≤
      (max 1 (2 * ((2 * d : ℕ) + 1) / c)) ^ (2 * d) *
        Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale) := by
  have h3 : (0 : ℝ) ≤ 3 ^ V.scale := by positivity
  have hv : V.latticeVolume ^ 2 = ((3 : ℝ) ^ V.scale) ^ (2 * d) := by
    unfold TriadicCube.latticeVolume
    rw [← pow_mul, mul_comm d 2]
  have hle : ((3 : ℝ) ^ V.scale) ^ (2 * d) ≤ ((3 : ℝ) ^ V.scale + 1) ^ (2 * d) :=
    pow_le_pow_left₀ h3 (by linarith) _
  have h := add_one_pow_mul_exp_neg_le (2 * d) hc h3
  rw [hv]
  calc ((3 : ℝ) ^ V.scale) ^ (2 * d) * Real.exp (-c * (3 : ℝ) ^ V.scale)
      ≤ ((3 : ℝ) ^ V.scale + 1) ^ (2 * d) * Real.exp (-(c * (3 : ℝ) ^ V.scale)) := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ ≤ _ := by
        rw [show -(c / 2) * (3 : ℝ) ^ V.scale = -(c / 2 * 3 ^ V.scale) by ring]
        exact h

/-- The triadic cube of the same scale centred at the origin. -/
def TriadicCube.atOrigin (V : TriadicCube d) : TriadicCube d := ⟨V.scale, 0⟩

theorem TriadicCube.atOrigin_shift_center (V : TriadicCube d) :
    V.atOrigin.shift V.center = V := by
  ext i
  · rfl
  · change 0 + V.side * V.index i / V.side = V.index i
    rw [zero_add, Int.mul_ediv_cancel_left _ V.side_pos.ne']

theorem TriadicCube.atOrigin_side_dvd_center (V : TriadicCube d) (i : Fin d) :
    V.atOrigin.side ∣ V.center i :=
  Dvd.intro _ rfl

theorem TriadicCube.atOrigin_shift (V : TriadicCube d) (z : Vertex d) :
    (V.shift z).atOrigin = V.atOrigin := rfl

theorem TriadicCube.atOrigin_eq_of_scale_eq {V W : TriadicCube d} (h : V.scale = W.scale) :
    V.atOrigin = W.atOrigin := by
  unfold TriadicCube.atOrigin
  rw [h]

theorem TriadicCube.center_shift_eq_add {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) : (V.shift z).center = V.center + z :=
  funext fun i => TriadicCube.center_shift' hz i

/-- On the good events of `ω` at `V` and of the translated configuration at the translated cube,
`1{P, V res} (-μ(V, q))` moves with the translation. -/
theorem cubeMu_indicator_shift_eq_of_good {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) {ω : Configuration d} (hω : CubeLocalGood ω V)
    (hω' : CubeLocalGood (configurationTranslation z ω) (V.shift z)) (q : Fin d → ℝ) :
    (if PartitionEvent (configurationTranslation z ω) ∧
        PartitionResolved (configurationTranslation z ω) (V.shift z) then
      ENNReal.ofReal (-cubeMu (configurationTranslation z ω) (V.shift z) q) else 0) =
      if PartitionEvent ω ∧ PartitionResolved ω V then
        ENNReal.ofReal (-cubeMu ω V q) else 0 := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, partitionCube (configurationTranslation z ω) (x + z) =
      (partitionCube ω x).shift z := by
    intro x hx
    rw [partitionCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      partitionCube_eq_cappedCube hω hx]
    exact cappedCube_goodCubes_translation hz' ω x
  by_cases hres : PartitionResolved ω V
  · have hres' := (partitionResolved_shift_iff hz hpart).2 hres
    rw [if_pos ⟨hω'.1, hres'⟩, if_pos ⟨hω.1, hres⟩,
      cubeMu_shift_translation_of_partition hres hz hpart q]
  · have hres' : ¬ PartitionResolved (configurationTranslation z ω) (V.shift z) :=
      fun h => hres ((partitionResolved_shift_iff hz hpart).1 h)
    rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]

/-- **The stationary local version of `-μ`.** -/
noncomputable def cubeMuStat (V : TriadicCube d) (q : Fin d → ℝ) (ω : Configuration d) :
    ℝ≥0∞ :=
  cubeMuLoc V.atOrigin q (configurationTranslation (-V.center) ω)

/-- **Exact translation covariance.** -/
theorem cubeMuStat_shift {V : TriadicCube d} {z : Vertex d} (hz : ∀ i, V.side ∣ z i)
    (q : Fin d → ℝ) (ω : Configuration d) :
    cubeMuStat (V.shift z) q (configurationTranslation z ω) = cubeMuStat V q ω := by
  unfold cubeMuStat
  rw [TriadicCube.atOrigin_shift, configurationTranslation_add,
    TriadicCube.center_shift_eq_add hz, neg_add, neg_add_cancel_right]

theorem measurable_cubeMuStat (V : TriadicCube d) (q : Fin d → ℝ) :
    Measurable (cubeMuStat V q) :=
  (measurable_cubeMuLoc _ q).comp (configurationTranslationMeasurableEquiv _).measurable

/-- **Stationarity in law** (Armstrong and Dario, (4.40)): the law of the stationary local version
of `-μ(z + V, q)` does not depend on `z ∈ 3ⁿ ℤ^d`. -/
theorem map_cubeMuStat_shift (p : unitInterval) {V : TriadicCube d} {z : Vertex d}
    (hz : ∀ i, V.side ∣ z i) (q : Fin d → ℝ) :
    (latticeBondLaw d p).map (cubeMuStat (V.shift z) q) =
      (latticeBondLaw d p).map (cubeMuStat V q) := by
  have hmp := measurePreserving_configurationTranslation p z
  have h : cubeMuStat V q = cubeMuStat (V.shift z) q ∘ configurationTranslation z :=
    funext fun ω => (cubeMuStat_shift hz q ω).symm
  rw [h, ← Measure.map_map (measurable_cubeMuStat _ q) hmp.measurable, hmp.map_eq]

/-- The expectation of the stationary local version depends only on the scale of the cube. -/
theorem lintegral_cubeMuStat_eq (p : unitInterval) (V : TriadicCube d) (q : Fin d → ℝ) :
    ∫⁻ ω, cubeMuStat V q ω ∂(latticeBondLaw d p) =
      ∫⁻ ω, cubeMuLoc V.atOrigin q ω ∂(latticeBondLaw d p) :=
  (measurePreserving_configurationTranslation p (-V.center)).lintegral_comp
    (measurable_cubeMuLoc _ q)

/-- Translating by `-c` carries the bonds of the local region of `V` to those of the cube at the
origin. -/
theorem configurationTranslation_eq_on_localBonds_atOrigin {V : TriadicCube d}
    {ω ω' : Configuration d} (h : ∀ e ∈ localBonds V.localRegion, ω e = ω' e) :
    ∀ e ∈ localBonds V.atOrigin.localRegion,
      configurationTranslation (-V.center) ω e = configurationTranslation (-V.center) ω' e := by
  intro e he
  rw [configurationTranslation_apply, configurationTranslation_apply, neg_neg]
  refine h _ fun x hx => ?_
  rw [bondTranslation_val, Sym2.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := he y hy
  change ∀ i, |y i - V.atOrigin.center i| ≤ 7 * V.atOrigin.side at hy'
  change ∀ i, |(y + V.center) i - V.center i| ≤ 7 * V.side
  intro i
  have := hy' i
  have hc : V.atOrigin.center i = 0 := by
    change V.atOrigin.side * 0 = 0
    rw [mul_zero]
  rw [hc, sub_zero] at this
  have hs : V.atOrigin.side = V.side := rfl
  rw [hs] at this
  simpa only [Pi.add_apply, add_sub_cancel_right] using this

/-- **Locality of the stationary local version** (Armstrong and Dario, (4.39)). -/
theorem measurable_cubeMuStat_localBondSigma (V : TriadicCube d) (q : Fin d → ℝ) :
    Measurable[localBondSigma V.localRegion] (cubeMuStat V q) :=
  measurable_localBondSigma_of_eq _ (measurable_cubeMuStat V q) fun _ _ h =>
    congrArg (cubeMuLocOf V.atOrigin q)
      (cubeLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds_atOrigin h)).symm

/-- **Independence of the stationary local versions.** -/
theorem indepFun_cubeMuStat (p : unitInterval) {V W : TriadicCube d}
    (hVW : Disjoint V.localRegion W.localRegion) (q r : Fin d → ℝ) :
    IndepFun (cubeMuStat V q) (cubeMuStat W r) (latticeBondLaw d p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_cubeMuStat_localBondSigma V q).comap_le)
    (measurable_cubeMuStat_localBondSigma W r).comap_le)

/-- The good event for the stationary local version. -/
def CubeStatGood (ω : Configuration d) (V : TriadicCube d) : Prop :=
  CubeLocalGood ω V ∧ CubeLocalGood (configurationTranslation (-V.center) ω) V.atOrigin

theorem measurableSet_cubeStatGood (V : TriadicCube d) :
    MeasurableSet {ω : Configuration d | CubeStatGood ω V} :=
  (measurableSet_cubeLocalGood V).inter
    ((configurationTranslationMeasurableEquiv _).measurable (measurableSet_cubeLocalGood _))

/-- **Agreement with `μ`.** On the good event, the stationary local version equals
`1{P, V res} (-μ(V, q))`. -/
theorem cubeMuStat_eq_of_good {V : TriadicCube d} {ω : Configuration d}
    (h : CubeStatGood ω V) (q : Fin d → ℝ) :
    cubeMuStat V q ω = if PartitionEvent ω ∧ PartitionResolved ω V then
      ENNReal.ofReal (-cubeMu ω V q) else 0 := by
  unfold cubeMuStat
  rw [cubeMuLoc_eq_of_good h.2]
  have hω : configurationTranslation V.center (configurationTranslation (-V.center) ω) = ω := by
    rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have h2 : CubeLocalGood (configurationTranslation V.center
      (configurationTranslation (-V.center) ω)) (V.atOrigin.shift V.center) := by
    rw [hω, V.atOrigin_shift_center]
    exact h.1
  have := cubeMu_indicator_shift_eq_of_good V.atOrigin_side_dvd_center h.2 h2 q
  rw [hω, V.atOrigin_shift_center] at this
  exact this.symm

/-- The good event of the stationary local version fails with probability at most
`2 C exp(-c 3ⁿ)`. -/
theorem exists_measure_not_cubeStatGood_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube d,
      latticeBondLaw d p {ω | ¬ CubeStatGood ω V} ≤
        2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_measure_not_cubeLocalGood_le hd hpc
  refine ⟨C, hC, c, hc, fun V => ?_⟩
  have hmp := measurePreserving_configurationTranslation p (-V.center)
  have hemb := (configurationTranslationMeasurableEquiv (-V.center)).measurableEmbedding
  have hsub : {ω | ¬ CubeStatGood ω V} ⊆ {ω | ¬ CubeLocalGood ω V} ∪
      (configurationTranslation (-V.center)) ⁻¹' {ω | ¬ CubeLocalGood ω V.atOrigin} := by
    intro ω hω
    simp only [CubeStatGood, not_and_or, Set.mem_setOf_eq] at hω
    exact hω
  calc latticeBondLaw d p {ω | ¬ CubeStatGood ω V}
      ≤ latticeBondLaw d p {ω | ¬ CubeLocalGood ω V} +
        latticeBondLaw d p ((configurationTranslation (-V.center)) ⁻¹'
          {ω | ¬ CubeLocalGood ω V.atOrigin}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) +
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
        rw [hmp.measure_preimage_emb hemb]
        exact add_le_add (h V) (h V.atOrigin)
    _ = _ := by ring

/-- **Localization of `μ` by the stationary version** (Armstrong and Dario, Proposition 4.10, for
`μ`, with the stationary local version). The expectations of the stationary local version and of
`1{P, V res} (-μ(V, q))` differ by at most `C |q|₁² exp(-c 3ⁿ)`. -/
theorem exists_cubeMuStat_localization [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube d) (q : Fin d → ℝ),
      ∫⁻ ω, cubeMuStat V q ω ∂(latticeBondLaw d p) ≤
        ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) ∧
      ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) ≤
        ∫⁻ ω, cubeMuStat V q ω ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC, c, hc, hbad⟩ := exists_measure_not_cubeStatGood_le hd hpc
  set A : ℝ := d * coarseGradConstant d ^ 2 with hA
  set M : ℝ := (max 1 (2 * ((2 * d : ℕ) + 1) / c)) ^ (2 * d) with hM
  refine ⟨ENNReal.ofReal (A * M) * (2 * C), by finiteness, c / 2, by positivity, fun V q => ?_⟩
  set B := {ω : Configuration d | ¬ CubeStatGood ω V} with hBdef
  have hB : MeasurableSet B := (measurableSet_cubeStatGood V).compl
  set s := (∑ i, |q i|) ^ 2 with hs
  set K : ℝ≥0∞ := ENNReal.ofReal (A * s * V.latticeVolume ^ 2) with hK
  have hKe : K * latticeBondLaw d p B ≤
      ENNReal.ofReal (A * M) * (2 * C) *
        ENNReal.ofReal (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
    refine (mul_le_mul' le_rfl (hbad V)).trans ?_
    have hpoly := latticeVolume_sq_mul_exp_le d hc V
    rw [← hM] at hpoly
    have hAB : A * s * V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale) ≤
        A * M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
      calc A * s * V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)
          = A * s * (V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by ring
        _ ≤ A * s * (M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) :=
            mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = A * M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by ring
    calc K * (2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)))
        = 2 * C * ENNReal.ofReal (A * s * V.latticeVolume ^ 2 *
            Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
          rw [hK, ENNReal.ofReal_mul (p := A * s * V.latticeVolume ^ 2) (by positivity)]
          ring
      _ ≤ 2 * C * ENNReal.ofReal (A * M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale))) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hAB)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
  have hle : ∀ ω, cubeMuStat V q ω ≤ K := fun ω => cubeMuLoc_le hd0 _ q _
  refine ⟨?_, ?_⟩
  · refine (lintegral_le_lintegral_add_of_le_off _ hB hle fun ω hω => ?_).trans
      (add_le_add le_rfl hKe)
    simp only [B, Set.mem_setOf_eq, not_not] at hω
    exact (cubeMuStat_eq_of_good hω q).le
  · refine (lintegral_le_lintegral_add_of_le_off _ hB (cubeMu_indicator_le hd0 V q)
      fun ω hω => ?_).trans (add_le_add le_rfl hKe)
    simp only [B, Set.mem_setOf_eq, not_not] at hω
    exact (cubeMuStat_eq_of_good hω q).ge

/-- **Approximate stationarity of `μ`** (Armstrong and Dario, (4.40), in expectation, in every
dimension `d ≥ 2`). For triadic cubes `V`, `W` of the same scale `n`,
`E[-μ(W, q); P, W res] ≤ E[-μ(V, q); P, V res] + C |q|₁² exp(-c 3ⁿ)`. -/
theorem exists_lintegral_neg_cubeMu_le_of_scale_eq [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V W : TriadicCube d), V.scale = W.scale →
      ∀ q : Fin d → ℝ,
      ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω W then
          ENNReal.ofReal (-cubeMu ω W q) else 0) ∂(latticeBondLaw d p) ≤
        ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_cubeMuStat_localization hd hpc
  refine ⟨2 * C, by finiteness, c, hc, fun V W hVW q => ?_⟩
  have hstat : ∫⁻ ω, cubeMuStat W q ω ∂(latticeBondLaw d p) =
      ∫⁻ ω, cubeMuStat V q ω ∂(latticeBondLaw d p) := by
    rw [lintegral_cubeMuStat_eq, lintegral_cubeMuStat_eq, TriadicCube.atOrigin_eq_of_scale_eq hVW]
  have h1 := (h W q).2
  have h2 := (h V q).1
  rw [← hVW] at h1
  calc _ ≤ _ := h1
    _ = ∫⁻ ω, cubeMuStat V q ω ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
        rw [hstat]
    _ ≤ _ := by
        refine (add_le_add h2 le_rfl).trans (le_of_eq ?_)
        ring

end Rigidity.Percolation
