import Rigidity.Proofs.Percolation.PlanarLocalLimits

/-!
# Stationary local versions of `ν` and `μ`

For a triadic cube `V` of scale `n` with centre `c`, the stationary local version of `ν` is the
local version on the cube `□_n` centred at the origin, evaluated at the configuration translated by
`-c`. It is measurable for the σ-algebra of the bonds inside the square of side `14 · 3ⁿ` around
`V`, and it is exactly translation covariant: its value on `V + z` at the configuration translated
by `z` is its value on `V`, for every `z` in `3ⁿ ℤ²`. Since the bond law is translation invariant,
its law does not depend on the position of `V` in `3ⁿ ℤ²` (Armstrong and Dario, (4.39) and (4.40),
in dimension two). On the event that the partition agrees with the capped partition on `V` and,
after the translation by `-c`, on `□_n`, it equals `1{P, V res} ν(V, ξ)`; so its expectation
differs from that of `1{P, V res} ν(V, ξ)` by at most `C |ξ|₁² exp (-c 3ⁿ)`. The same holds for
`μ`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The triadic cube of the same scale centred at the origin. -/
def TriadicCube.originCube (V : TriadicCube 2) : TriadicCube 2 := ⟨V.scale, 0⟩

theorem TriadicCube.originCube_shift_center (V : TriadicCube 2) :
    V.originCube.shift V.center = V := by
  ext i
  · rfl
  · change 0 + V.side * V.index i / V.side = V.index i
    rw [zero_add, Int.mul_ediv_cancel_left _ V.side_pos.ne']

theorem TriadicCube.originCube_side_dvd_center (V : TriadicCube 2) (i : Fin 2) :
    V.originCube.side ∣ V.center i :=
  Dvd.intro _ rfl

theorem TriadicCube.originCube_shift (V : TriadicCube 2) (z : Vertex 2) :
    (V.shift z).originCube = V.originCube := rfl

/-- On the good events of `ω` at `V` and of the translated configuration at the translated cube,
`1{P, V res} ν(V, ξ)` moves with the translation. -/
theorem planarNu_indicator_shift_eq_of_good {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) {ω : Configuration 2} (hω : PlanarLocalGood ω V)
    (hω' : PlanarLocalGood (configurationTranslation z ω) (V.shift z)) (ξ : Fin 2 → ℝ) :
    (if PlanarPartitionEvent (configurationTranslation z ω) ∧
        PlanarResolved (configurationTranslation z ω) (V.shift z) then
      ENNReal.ofReal (planarNu (configurationTranslation z ω) (V.shift z) ξ) else 0) =
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (planarNu ω V ξ) else 0 := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, planarPartCube (configurationTranslation z ω) (x + z) =
      (planarPartCube ω x).shift z := by
    intro x hx
    rw [planarPartCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      planarPartCube_eq_cappedCube hω hx]
    exact cappedCube_planarGoodCubes_translation hz' ω x
  by_cases hres : PlanarResolved ω V
  · have hres' := (planarResolved_shift_iff hz hpart).2 hres
    rw [if_pos ⟨hω'.1, hres'⟩, if_pos ⟨hω.1, hres⟩,
      planarNu_shift_translation hω.1 hres hz hpart]
  · have hres' : ¬ PlanarResolved (configurationTranslation z ω) (V.shift z) :=
      fun h => hres ((planarResolved_shift_iff hz hpart).1 h)
    rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]

/-- The same for `-μ`. -/
theorem planarMu_indicator_shift_eq_of_good {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) {ω : Configuration 2} (hω : PlanarLocalGood ω V)
    (hω' : PlanarLocalGood (configurationTranslation z ω) (V.shift z)) (q : Fin 2 → ℝ) :
    (if PlanarPartitionEvent (configurationTranslation z ω) ∧
        PlanarResolved (configurationTranslation z ω) (V.shift z) then
      ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q) else 0) =
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (-planarMu ω V q) else 0 := by
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hpart : ∀ x ∈ V.vertices, planarPartCube (configurationTranslation z ω) (x + z) =
      (planarPartCube ω x).shift z := by
    intro x hx
    rw [planarPartCube_eq_cappedCube hω' ((TriadicCube.add_mem_shift_iff hz x).2 hx),
      planarPartCube_eq_cappedCube hω hx]
    exact cappedCube_planarGoodCubes_translation hz' ω x
  by_cases hres : PlanarResolved ω V
  · have hres' := (planarResolved_shift_iff hz hpart).2 hres
    rw [if_pos ⟨hω'.1, hres'⟩, if_pos ⟨hω.1, hres⟩,
      planarMu_shift_translation hω.1 hres hz hpart]
  · have hres' : ¬ PlanarResolved (configurationTranslation z ω) (V.shift z) :=
      fun h => hres ((planarResolved_shift_iff hz hpart).1 h)
    rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]

/-- **The stationary local version of `ν`.** -/
noncomputable def planarNuStat (V : TriadicCube 2) (ξ : Fin 2 → ℝ) (ω : Configuration 2) :
    ℝ≥0∞ :=
  planarNuLoc V.originCube ξ (configurationTranslation (-V.center) ω)

/-- **The stationary local version of `-μ`.** -/
noncomputable def planarMuStat (V : TriadicCube 2) (q : Fin 2 → ℝ) (ω : Configuration 2) :
    ℝ≥0∞ :=
  planarMuLoc V.originCube q (configurationTranslation (-V.center) ω)

theorem TriadicCube.center_shift_eq {V : TriadicCube 2} {z : Vertex 2} (hz : ∀ i, V.side ∣ z i) :
    (V.shift z).center = V.center + z :=
  funext fun i => TriadicCube.center_shift hz i

/-- **Exact translation covariance.** -/
theorem planarNuStat_shift {V : TriadicCube 2} {z : Vertex 2} (hz : ∀ i, V.side ∣ z i)
    (ξ : Fin 2 → ℝ) (ω : Configuration 2) :
    planarNuStat (V.shift z) ξ (configurationTranslation z ω) = planarNuStat V ξ ω := by
  unfold planarNuStat
  rw [TriadicCube.originCube_shift, configurationTranslation_add, TriadicCube.center_shift_eq hz,
    neg_add, neg_add_cancel_right]

theorem planarMuStat_shift {V : TriadicCube 2} {z : Vertex 2} (hz : ∀ i, V.side ∣ z i)
    (q : Fin 2 → ℝ) (ω : Configuration 2) :
    planarMuStat (V.shift z) q (configurationTranslation z ω) = planarMuStat V q ω := by
  unfold planarMuStat
  rw [TriadicCube.originCube_shift, configurationTranslation_add, TriadicCube.center_shift_eq hz,
    neg_add, neg_add_cancel_right]

theorem measurable_planarNuStat (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Measurable (planarNuStat V ξ) :=
  (measurable_planarNuLoc _ ξ).comp (configurationTranslationMeasurableEquiv _).measurable

theorem measurable_planarMuStat (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable (planarMuStat V q) :=
  (measurable_planarMuLoc _ q).comp (configurationTranslationMeasurableEquiv _).measurable

/-- **Stationarity in law** (Armstrong and Dario, (4.40), in dimension two). -/
theorem map_planarNuStat_shift (p : unitInterval) {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) (ξ : Fin 2 → ℝ) :
    (latticeBondLaw 2 p).map (planarNuStat (V.shift z) ξ) =
      (latticeBondLaw 2 p).map (planarNuStat V ξ) := by
  have hmp := measurePreserving_configurationTranslation p z
  have h : planarNuStat V ξ = planarNuStat (V.shift z) ξ ∘ configurationTranslation z :=
    funext fun ω => (planarNuStat_shift hz ξ ω).symm
  rw [h, ← Measure.map_map (measurable_planarNuStat _ ξ) hmp.measurable, hmp.map_eq]

theorem map_planarMuStat_shift (p : unitInterval) {V : TriadicCube 2} {z : Vertex 2}
    (hz : ∀ i, V.side ∣ z i) (q : Fin 2 → ℝ) :
    (latticeBondLaw 2 p).map (planarMuStat (V.shift z) q) =
      (latticeBondLaw 2 p).map (planarMuStat V q) := by
  have hmp := measurePreserving_configurationTranslation p z
  have h : planarMuStat V q = planarMuStat (V.shift z) q ∘ configurationTranslation z :=
    funext fun ω => (planarMuStat_shift hz q ω).symm
  rw [h, ← Measure.map_map (measurable_planarMuStat _ q) hmp.measurable, hmp.map_eq]

/-- Translating by `-c` carries the bonds near `V` to the bonds near the cube at the origin. -/
theorem configurationTranslation_eq_on_localBonds {V : TriadicCube 2} {ω ω' : Configuration 2}
    (h : ∀ e ∈ localBonds V.planarLocalRegion, ω e = ω' e) :
    ∀ e ∈ localBonds V.originCube.planarLocalRegion,
      configurationTranslation (-V.center) ω e = configurationTranslation (-V.center) ω' e := by
  intro e he
  rw [configurationTranslation_apply, configurationTranslation_apply, neg_neg]
  refine h _ fun x hx => ?_
  rw [bondTranslation_val, Sym2.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := he y hy
  change ∀ i, |y i - V.originCube.center i| ≤ 7 * V.originCube.side at hy'
  change ∀ i, |(y + V.center) i - V.center i| ≤ 7 * V.side
  intro i
  have := hy' i
  have hc : V.originCube.center i = 0 := by
    change V.originCube.side * 0 = 0
    rw [mul_zero]
  rw [hc, sub_zero] at this
  have hs : V.originCube.side = V.side := rfl
  rw [hs] at this
  simpa only [Pi.add_apply, add_sub_cancel_right] using this

/-- **Locality of the stationary local versions.** -/
theorem measurable_planarNuStat_localBondSigma (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Measurable[localBondSigma V.planarLocalRegion] (planarNuStat V ξ) :=
  measurable_localBondSigma_of_eq _ (measurable_planarNuStat V ξ) fun _ _ h =>
    congrArg (planarNuLocOf V.originCube ξ)
      (planarLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds h)).symm

theorem measurable_planarMuStat_localBondSigma (V : TriadicCube 2) (q : Fin 2 → ℝ) :
    Measurable[localBondSigma V.planarLocalRegion] (planarMuStat V q) :=
  measurable_localBondSigma_of_eq _ (measurable_planarMuStat V q) fun _ _ h =>
    congrArg (planarMuLocOf V.originCube q)
      (planarLocalData_eq_of_localBonds (configurationTranslation_eq_on_localBonds h)).symm

/-- **Independence of the stationary local versions.** -/
theorem indepFun_planarNuStat (p : unitInterval) {V W : TriadicCube 2}
    (hVW : Disjoint V.planarLocalRegion W.planarLocalRegion) (ξ η : Fin 2 → ℝ) :
    IndepFun (planarNuStat V ξ) (planarNuStat W η) (latticeBondLaw 2 p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_planarNuStat_localBondSigma V ξ).comap_le)
    (measurable_planarNuStat_localBondSigma W η).comap_le)

theorem indepFun_planarMuStat (p : unitInterval) {V W : TriadicCube 2}
    (hVW : Disjoint V.planarLocalRegion W.planarLocalRegion) (q r : Fin 2 → ℝ) :
    IndepFun (planarMuStat V q) (planarMuStat W r) (latticeBondLaw 2 p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_planarMuStat_localBondSigma V q).comap_le)
    (measurable_planarMuStat_localBondSigma W r).comap_le)

/-- The good event for the stationary local versions. -/
def PlanarStatGood (ω : Configuration 2) (V : TriadicCube 2) : Prop :=
  PlanarLocalGood ω V ∧
    PlanarLocalGood (configurationTranslation (-V.center) ω) V.originCube

theorem planarNuStat_eq_of_good {V : TriadicCube 2} {ω : Configuration 2}
    (h : PlanarStatGood ω V) (ξ : Fin 2 → ℝ) :
    planarNuStat V ξ ω = if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (planarNu ω V ξ) else 0 := by
  unfold planarNuStat
  rw [planarNuLoc_eq_of_good h.2]
  have hω : configurationTranslation V.center (configurationTranslation (-V.center) ω) = ω := by
    rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have h2 : PlanarLocalGood (configurationTranslation V.center
      (configurationTranslation (-V.center) ω)) (V.originCube.shift V.center) := by
    rw [hω, V.originCube_shift_center]
    exact h.1
  have := planarNu_indicator_shift_eq_of_good V.originCube_side_dvd_center h.2 h2 ξ
  rw [hω, V.originCube_shift_center] at this
  exact this.symm

theorem planarMuStat_eq_of_good {V : TriadicCube 2} {ω : Configuration 2}
    (h : PlanarStatGood ω V) (q : Fin 2 → ℝ) :
    planarMuStat V q ω = if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (-planarMu ω V q) else 0 := by
  unfold planarMuStat
  rw [planarMuLoc_eq_of_good h.2]
  have hω : configurationTranslation V.center (configurationTranslation (-V.center) ω) = ω := by
    rw [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero]
  have h2 : PlanarLocalGood (configurationTranslation V.center
      (configurationTranslation (-V.center) ω)) (V.originCube.shift V.center) := by
    rw [hω, V.originCube_shift_center]
    exact h.1
  have := planarMu_indicator_shift_eq_of_good V.originCube_side_dvd_center h.2 h2 q
  rw [hω, V.originCube_shift_center] at this
  exact this.symm

/-- The good event of the stationary local versions has probability at least
`1 - 2 C exp (-c 3ⁿ)`. -/
theorem exists_measure_not_planarStatGood_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube 2,
      latticeBondLaw 2 p {ω | ¬ PlanarStatGood ω V} ≤
        2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_planarNuLoc_localization hpc
  refine ⟨C, hC, c, hc, fun V => ?_⟩
  have hmp := measurePreserving_configurationTranslation p (-V.center)
  have hemb := (configurationTranslationMeasurableEquiv (-V.center)).measurableEmbedding
  have hsub : {ω | ¬ PlanarStatGood ω V} ⊆ {ω | ¬ PlanarLocalGood ω V} ∪
      (configurationTranslation (-V.center)) ⁻¹' {ω | ¬ PlanarLocalGood ω V.originCube} := by
    intro ω hω
    simp only [PlanarStatGood, not_and_or, Set.mem_setOf_eq] at hω
    exact hω
  calc latticeBondLaw 2 p {ω | ¬ PlanarStatGood ω V}
      ≤ latticeBondLaw 2 p {ω | ¬ PlanarLocalGood ω V} +
        latticeBondLaw 2 p ((configurationTranslation (-V.center)) ⁻¹'
          {ω | ¬ PlanarLocalGood ω V.originCube}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) +
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
        rw [hmp.measure_preimage_emb hemb]
        exact add_le_add (h V 0).1 (h V.originCube 0).1
    _ = _ := by ring

end Rigidity.Percolation
