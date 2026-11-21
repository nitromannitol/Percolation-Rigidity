import Rigidity.Proofs.Percolation.PlanarNuMeasurable
import Rigidity.Proofs.Percolation.PlanarCubeEnergyBounds
import Rigidity.Percolation.TriadicLocalizationCount
import Rigidity.Percolation.TriadicLargeScaleDecay

/-!
# Approximate stationarity of `ν` in the plane

The planar partition is not translation covariant, but the partition capped at a scale `n` is
covariant under translations by `3ⁿ ℤ²`. If the partition differs from the capped partition at a
vertex of a cube `V`, some bad cube of scale at least `n` lies near `V`; for `n` the scale of `V`
this has probability at most `C exp (-c 3ⁿ)` by a union bound over the boundedly many nearby cubes
of each scale (Armstrong and Dario, Proposition 4.9, in dimension two).

Hence, for a translation `z` by a multiple of the side of `V`,
`E[ν(V + z, ξ); P, V + z resolved] ≤ E[ν(V, ξ); P, V resolved] + C |ξ|₁² exp (-c 3ⁿ)`,
an approximate form of the stationarity of Armstrong and Dario, (4.40), in dimension two, with
the error coming from the localization of the partition.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- **Discrepancy with the capped partition.** The probability that a maximal stopping cube at a
vertex of `A` differs from the cube of the partition capped at scale `n` is bounded by a union
bound over the nearby bad cubes of scale at least `n`. -/
theorem TriadicCube.measure_ne_cappedCube_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Ω → Set (TriadicCube d)) (A : TriadicCube d) (n : ℕ)
    (p : ℕ → ℝ≥0∞) (hprob : ∀ T : TriadicCube d, μ {ω | T ∉ G ω} ≤ p T.scale) :
    μ {ω | ∃ x ∈ A.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
        Q.IsMaximalStopping (G ω) ∧ Q ≠ cappedCube (G ω) n x} ≤
      ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + k)) + 29) ^ d : ℕ) : ℝ≥0∞) * p (n + k) := by
  classical
  let cubes : ℕ → Finset (TriadicCube d) := fun k =>
    (A.finite_near_at_scale (n + k)).1.toFinset
  let bad : TriadicCube d → Set Ω := fun T => {ω | T ∉ G ω}
  have hsubset : {ω | ∃ x ∈ A.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
      Q.IsMaximalStopping (G ω) ∧ Q ≠ cappedCube (G ω) n x} ⊆ ⋃ k, ⋃ T ∈ cubes k, bad T := by
    intro ω hω
    obtain ⟨x, hx, Q, hxQ, hQ, hne⟩ := hω
    obtain ⟨T, hbad, hlarge, hnear⟩ := exists_bad_of_ne_cappedCube hxQ hQ hne
    refine Set.mem_iUnion.mpr ⟨T.scale - n, Set.mem_iUnion.mpr ⟨T, ?_⟩⟩
    refine Set.mem_iUnion.mpr ⟨?_, hbad⟩
    simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨by omega, x, hx, T.center, T.center_mem, hnear _ T.center_mem⟩
  calc
    μ {ω | ∃ x ∈ A.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
        Q.IsMaximalStopping (G ω) ∧ Q ≠ cappedCube (G ω) n x} ≤
        μ (⋃ k, ⋃ T ∈ cubes k, bad T) := measure_mono hsubset
    _ ≤ ∑' k, μ (⋃ T ∈ cubes k, bad T) := measure_iUnion_le _
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + k)) + 29) ^ d : ℕ) : ℝ≥0∞) * p (n + k) := by
      apply ENNReal.tsum_le_tsum
      intro k
      calc
        μ (⋃ T ∈ cubes k, bad T) ≤ ∑ T ∈ cubes k, μ (bad T) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ _T ∈ cubes k, p (n + k) := by
          apply Finset.sum_le_sum
          intro T hT
          have hscale : T.scale = n + k := by
            simp only [cubes, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hT
            exact hT.1
          simpa only [bad, hscale] using hprob T
        _ = (cubes k).card * p (n + k) := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (((2 * 3 ^ (A.scale - (n + k)) + 29) ^ d : ℕ) : ℝ≥0∞) * p (n + k) := by
          gcongr
          have hc := (A.finite_near_at_scale (n + k)).2
          rw [Set.ncard_eq_toFinset_card _ (A.finite_near_at_scale (n + k)).1] at hc
          exact_mod_cast hc

/-- A stretched-exponential bad-cube bound gives a stretched-exponential bound for the
discrepancy with the capped partition. -/
theorem TriadicCube.measure_ne_cappedCube_le_stretched {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (G : Ω → Set (TriadicCube d)) (A : TriadicCube d) (n : ℕ)
    (C : ℝ≥0∞) (b c : ℝ) (hb : 1 < b) (hc : 0 < c)
    (hprob : ∀ T : TriadicCube d,
      μ {ω | T ∉ G ω} ≤ C * ENNReal.ofReal (Real.exp (-c * b ^ T.scale))) :
    μ {ω | ∃ x ∈ A.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
        Q.IsMaximalStopping (G ω) ∧ Q ≠ cappedCube (G ω) n x} ≤
      (((2 * 3 ^ (A.scale - n) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
        ENNReal.ofReal (Real.exp (-c * b ^ n)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k := by
  calc
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - (n + k)) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * ENNReal.ofReal (Real.exp (-c * b ^ (n + k)))) :=
      measure_ne_cappedCube_le μ G A n
        (fun j => C * ENNReal.ofReal (Real.exp (-c * b ^ j))) hprob
    _ ≤ ∑' k : ℕ, (((2 * 3 ^ (A.scale - n) + 29) ^ d : ℕ) : ℝ≥0∞) *
        (C * (ENNReal.ofReal (Real.exp (-c * b ^ n)) *
          ENNReal.ofReal (Real.exp (-c * (b - 1))) ^ k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      have hcount : (2 * 3 ^ (A.scale - (n + k)) + 29) ^ d ≤ (2 * 3 ^ (A.scale - n) + 29) ^ d := by
        apply pow_le_pow_left'
        apply Nat.add_le_add_right
        apply Nat.mul_le_mul_left
        exact pow_le_pow_right₀ (by omega) (by omega)
      have hexp := ENNReal.ofReal_le_ofReal (stretched_exp_scale_le b c hb hc n k)
      simp only [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ENNReal.ofReal_pow (Real.exp_nonneg _) k] at hexp
      have hcount' : (((2 * 3 ^ (A.scale - (n + k)) + 29) ^ d : ℕ) : ℝ≥0∞) ≤
          (((2 * 3 ^ (A.scale - n) + 29) ^ d : ℕ) : ℝ≥0∞) := by
        exact_mod_cast hcount
      exact mul_le_mul' hcount' (mul_le_mul' le_rfl hexp)
    _ = _ := by
      simp_rw [← mul_assoc, ENNReal.tsum_mul_left]

/-- **Good planar cubes.** For `p > p_c(2)`, a triadic cube fails to be good with probability at
most `C exp (-c 3ˢ)`, uniformly in the cube. -/
theorem exists_measure_not_mem_planarGoodCubes_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ T : TriadicCube 2,
      latticeBondLaw 2 p {ω | T ∉ planarGoodCubes ω} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ T.scale)) := by
  obtain ⟨C, c, hC, hc, hlarge⟩ := measure_not_planarMeshed_le hpc
  have hall := TriadicCube.measure_le_exp_of_large_scale (latticeBondLaw 2 p)
    (fun Q => {ω | Q ∉ planarMeshedFamily ω}) 7 C c hC hc hlarge
  set B : ℝ := C + Real.exp (c * (3 : ℝ) ^ 7) with hBdef
  have hB : 0 ≤ B := by positivity
  refine ⟨max (ENNReal.ofReal (Real.exp (c / 3))) ((1 + 3 ^ 2) * ENNReal.ofReal B),
    (max_lt ENNReal.ofReal_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)).ne,
    c / 3, by positivity, ?_⟩
  exact TriadicCube.measure_not_mem_goodOfWellConnected_le (latticeBondLaw 2 p)
    planarMeshedFamily (ENNReal.ofReal B) c hc (fun Q => by
      rw [← ENNReal.ofReal_mul hB]
      exact hall Q)

/-- The planar partition differs at some vertex of `V` from the partition capped at the scale
of `V`. -/
def PlanarCappedDiscrepancy (ω : Configuration 2) (V : TriadicCube 2) : Prop :=
  ∃ x ∈ V.vertices, ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧
    Q.IsMaximalStopping (planarGoodCubes ω) ∧
      Q ≠ TriadicCube.cappedCube (planarGoodCubes ω) V.scale x

/-- **Localization of the planar partition** (Armstrong and Dario, Proposition 4.9, in dimension
two, with `n` the scale of `V`). For `p > p_c(2)`, the planar partition differs from the partition
capped at the scale of `V` somewhere in `V` with probability at most `C exp (-c 3ⁿ)`. -/
theorem exists_measure_planarCappedDiscrepancy_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube 2,
      latticeBondLaw 2 p {ω | PlanarCappedDiscrepancy ω V} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, hgood⟩ := exists_measure_not_mem_planarGoodCubes_le hpc
  have hr : ENNReal.ofReal (Real.exp (-c * (3 - 1))) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
    nlinarith
  refine ⟨(((2 * 3 ^ 0 + 29) ^ 2 : ℕ) : ℝ≥0∞) * C *
      (1 - ENNReal.ofReal (Real.exp (-c * (3 - 1))))⁻¹,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hC)
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'), c, hc, fun V => ?_⟩
  have h := TriadicCube.measure_ne_cappedCube_le_stretched (latticeBondLaw 2 p)
    (fun ω => planarGoodCubes ω) V V.scale C 3 c (by norm_num) hc hgood
  rw [Nat.sub_self, ENNReal.tsum_geometric] at h
  calc latticeBondLaw 2 p {ω | PlanarCappedDiscrepancy ω V} ≤ _ := h
    _ = _ := by ring

/-- Two triadic cubes of the same scale differ by a shift by a multiple of their side. -/
theorem TriadicCube.shift_eq_of_scale_eq {d : ℕ} {V W : TriadicCube d} (h : V.scale = W.scale) :
    V.shift (fun i => V.side * (W.index i - V.index i)) = W := by
  ext i
  · exact h
  · change V.index i + V.side * (W.index i - V.index i) / V.side = W.index i
    rw [Int.mul_ediv_cancel_left _ V.side_pos.ne']
    ring

/-- **Approximate stationarity of `ν`** (Armstrong and Dario, (4.40), in dimension two). For a
translation `z` by a multiple of the side of `V`, the expectation of `ν` on the translated cube
exceeds that on `V` by at most `C |ξ|₁² exp (-c 3ⁿ)`, `n` the scale of `V`. -/
theorem exists_lintegral_planarNu_shift_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube 2) (z : Vertex 2),
      (∀ i, V.side ∣ z i) → ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (V.shift z) then
          ENNReal.ofReal (planarNu ω (V.shift z) ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_planarCappedDiscrepancy_le hpc
  refine ⟨2 * ENNReal.ofReal (9 / 4) * C, by finiteness, c, hc, fun V z hz ξ => ?_⟩
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hmp := measurePreserving_configurationTranslation p z
  have hemb := (configurationTranslationMeasurableEquiv z).measurableEmbedding
  have hPnull : latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} = 0 :=
    ae_iff.1 (ae_planarPartitionEvent hpc)
  set K : ℝ≥0∞ := ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) with hK
  set B : Set (Configuration 2) := {ω | ¬ PlanarPartitionEvent ω} ∪
    ((configurationTranslation z) ⁻¹' {ω | ¬ PlanarPartitionEvent ω} ∪
      ({ω | PlanarCappedDiscrepancy ω V} ∪
        (configurationTranslation z) ⁻¹' {ω | PlanarCappedDiscrepancy ω (V.shift z)})) with hB
  have key : ∀ ω, (if PlanarPartitionEvent (configurationTranslation z ω) ∧
      PlanarResolved (configurationTranslation z ω) (V.shift z) then
        ENNReal.ofReal (planarNu (configurationTranslation z ω) (V.shift z) ξ) else 0) ≤
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (planarNu ω V ξ) else 0) + B.indicator (fun _ => K) ω := by
    intro ω
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB]
      refine le_add_left ?_
      split_ifs
      · exact ENNReal.ofReal_le_ofReal (planarNu_le ξ)
      · exact zero_le
    · rw [Set.indicator_of_notMem hωB, add_zero]
      simp only [hB, Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, not_or, not_not] at hωB
      obtain ⟨hP, hP', hDV, hDV'⟩ := hωB
      have hcap : ∀ x ∈ V.vertices,
          planarPartCube ω x = TriadicCube.cappedCube (planarGoodCubes ω) V.scale x := by
        intro x hx
        by_contra hne
        exact hDV ⟨x, hx, _, (planarPartCube_spec hP x).1, (planarPartCube_spec hP x).2, hne⟩
      have hcap' : ∀ y ∈ (V.shift z).vertices,
          planarPartCube (configurationTranslation z ω) y =
            TriadicCube.cappedCube (planarGoodCubes (configurationTranslation z ω)) V.scale y := by
        intro y hy
        by_contra hne
        exact hDV' ⟨y, hy, _, (planarPartCube_spec hP' y).1, (planarPartCube_spec hP' y).2, hne⟩
      have hpart : ∀ x ∈ V.vertices, planarPartCube (configurationTranslation z ω) (x + z) =
          (planarPartCube ω x).shift z := by
        intro x hx
        rw [hcap' _ ((TriadicCube.add_mem_shift_iff hz x).2 hx), hcap x hx]
        exact cappedCube_planarGoodCubes_translation hz' ω x
      by_cases hres : PlanarResolved ω V
      · have hres' := (planarResolved_shift_iff hz hpart).2 hres
        rw [if_pos ⟨hP', hres'⟩, if_pos ⟨hP, hres⟩, planarNu_shift_translation hP hres hz hpart]
      · have hres' : ¬ PlanarResolved (configurationTranslation z ω) (V.shift z) :=
          fun h => hres ((planarResolved_shift_iff hz hpart).1 h)
        rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]
  have hBle : latticeBondLaw 2 p B ≤
      2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
    have h1 := hmp.measure_preimage_emb hemb {ω | ¬ PlanarPartitionEvent ω}
    have h2 := hmp.measure_preimage_emb hemb {ω | PlanarCappedDiscrepancy ω (V.shift z)}
    calc latticeBondLaw 2 p B ≤ latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} +
          (latticeBondLaw 2 p ((configurationTranslation z) ⁻¹' {ω | ¬ PlanarPartitionEvent ω}) +
            (latticeBondLaw 2 p {ω | PlanarCappedDiscrepancy ω V} +
              latticeBondLaw 2 p ((configurationTranslation z) ⁻¹'
                {ω | PlanarCappedDiscrepancy ω (V.shift z)}))) := by
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          exact measure_union_le _ _
      _ = latticeBondLaw 2 p {ω | PlanarCappedDiscrepancy ω V} +
            latticeBondLaw 2 p {ω | PlanarCappedDiscrepancy ω (V.shift z)} := by
          rw [h1, h2, hPnull, zero_add, zero_add]
      _ ≤ C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) +
            C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) :=
          add_le_add (hD V) (hD (V.shift z))
      _ = 2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by ring
  have hmeas := measurable_planarNu_indicator V ξ
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (V.shift z) then
          ENNReal.ofReal (planarNu ω (V.shift z) ξ) else 0) ∂(latticeBondLaw 2 p)
      = ∫⁻ ω, (if PlanarPartitionEvent (configurationTranslation z ω) ∧
          PlanarResolved (configurationTranslation z ω) (V.shift z) then
            ENNReal.ofReal (planarNu (configurationTranslation z ω) (V.shift z) ξ) else 0)
            ∂(latticeBondLaw 2 p) :=
        (hmp.lintegral_comp (measurable_planarNu_indicator (V.shift z) ξ)).symm
    _ ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) + B.indicator (fun _ => K) ω)
            ∂(latticeBondLaw 2 p) := lintegral_mono key
    _ = ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) +
          ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw 2 p) := lintegral_add_left hmeas _
    _ ≤ ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) +
          K * (2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) :=
        add_le_add le_rfl ((lintegral_indicator_const_le _ _).trans (mul_le_mul' le_rfl hBle))
    _ = _ := by
        rw [hK, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity)]
        ring

/-- **Approximate stationarity of `ν` between cubes of the same scale.** -/
theorem exists_lintegral_planarNu_le_of_scale_eq {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V W : TriadicCube 2), V.scale = W.scale →
      ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
          ENNReal.ofReal (planarNu ω W ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_planarNu_shift_le hpc
  refine ⟨C, hC, c, hc, fun V W hVW ξ => ?_⟩
  have hW := TriadicCube.shift_eq_of_scale_eq hVW
  have := h V (fun i => V.side * (W.index i - V.index i)) (fun i => Dvd.intro _ rfl) ξ
  rwa [hW] at this

end Rigidity.Percolation
