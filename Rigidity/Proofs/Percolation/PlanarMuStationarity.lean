import Rigidity.Proofs.Percolation.PlanarMuMeasurable
import Rigidity.Proofs.Percolation.PlanarNuStationarity
import Rigidity.Proofs.Percolation.PlanarMuMoments

/-!
# Approximate stationarity of `μ` in the plane

For a translation `z` by a multiple of the side of `V`, `μ` on the translated cube in the
translated configuration equals `μ` on `V` unless the planar partition differs from the capped
partition in one of the two cubes, an event `B` of probability at most `C exp (-c 3ⁿ)`, `n` the
scale of `V`. Unlike `ν`, the quantity `-μ` is not bounded, but `-μ(V, q) ≤ 9 |q|₁² |V|⁻¹ ∑_a
234256 R_a⁴` with `R_a` the reach of the partition at `a`, whose eighth moments are bounded. The
inequality `y ≤ λ + λ⁻¹ y²` with `λ = exp (c 3ⁿ / 2)` then bounds the expectation of `-μ` on `B` by
`C |q|₁² exp (-c 3ⁿ / 2)`. Hence
`E[-μ(V + z, q); P, V + z res] ≤ E[-μ(V, q); P, V res] + C |q|₁² exp (-c 3ⁿ / 2)`,
which is the approximate stationarity of Armstrong and Dario, (4.40), for `μ` in dimension two.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The elementary inequality `y ≤ λ + λ⁻¹ y²` for `0 < λ < ∞`. -/
theorem ENNReal.le_add_inv_mul_sq {y l : ℝ≥0∞} (h0 : l ≠ 0) (htop : l ≠ ∞) :
    y ≤ l + l⁻¹ * y ^ 2 := by
  rcases le_total y l with h | h
  · exact le_add_right h
  · refine le_add_left ?_
    calc y = l⁻¹ * (l * y) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
      _ ≤ l⁻¹ * (y * y) := by gcongr
      _ = l⁻¹ * y ^ 2 := by rw [sq]

/-- **Approximate stationarity of `μ`** (Armstrong and Dario, (4.40), for `μ`, in dimension
two). -/
theorem exists_lintegral_neg_planarMu_shift_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube 2) (z : Vertex 2),
      (∀ i, V.side ∣ z i) → ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (V.shift z) then
          ENNReal.ofReal (-planarMu ω (V.shift z) q) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_planarCappedDiscrepancy_le hpc
  obtain ⟨C₈, hC₈, h8⟩ := exists_lintegral_tsum_ninefold_le hpc 8
  refine ⟨9 * (2 * C + 234256 ^ 2 * C₈), by finiteness, c / 2, by positivity,
    fun V z hz q => ?_⟩
  have hz' : ∀ i, (3 : ℤ) ^ V.scale ∣ z i := hz
  have hmp := measurePreserving_configurationTranslation p z
  have hemb := (configurationTranslationMeasurableEquiv z).measurableEmbedding
  have hPnull : latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} = 0 :=
    ae_iff.1 (ae_planarPartitionEvent hpc)
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hvol := V.volume_pos
  set l : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c / 2 * (3 : ℝ) ^ V.scale)) with hl
  have hl0 : l ≠ 0 := by
    rw [hl]
    exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hltop : l ≠ ∞ := ENNReal.ofReal_ne_top
  set cc : ℝ≥0∞ := ENNReal.ofReal (9 * s / V.volume) with hcc
  set S := (V.shift z).toIntegerCube.vertices with hS
  set B : Set (Configuration 2) := {ω | ¬ PlanarPartitionEvent ω} ∪
    ((configurationTranslation z) ⁻¹' {ω | ¬ PlanarPartitionEvent ω} ∪
      ({ω | PlanarCappedDiscrepancy ω V} ∪
        (configurationTranslation z) ⁻¹' {ω | PlanarCappedDiscrepancy ω (V.shift z)})) with hB
  have key1 : ∀ ω, (if PlanarPartitionEvent (configurationTranslation z ω) ∧
      PlanarResolved (configurationTranslation z ω) (V.shift z) then
        ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q) else 0) ≤
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
        ENNReal.ofReal (-planarMu ω V q) else 0) +
      B.indicator (fun ω => if PlanarPartitionEvent (configurationTranslation z ω) ∧
        PlanarResolved (configurationTranslation z ω) (V.shift z) then
          ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q) else 0) ω := by
    intro ω
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB]
      exact le_add_self
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
        rw [if_pos ⟨hP', hres'⟩, if_pos ⟨hP, hres⟩, planarMu_shift_translation hP hres hz hpart]
      · have hres' : ¬ PlanarResolved (configurationTranslation z ω) (V.shift z) :=
          fun h => hres ((planarResolved_shift_iff hz hpart).1 h)
        rw [if_neg fun h => hres' h.2, if_neg fun h => hres h.2]
  have key2 : ∀ ω, B.indicator (fun ω => if PlanarPartitionEvent (configurationTranslation z ω) ∧
      PlanarResolved (configurationTranslation z ω) (V.shift z) then
        ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q) else 0) ω ≤
      B.indicator (fun _ => cc * ((S.card : ℝ≥0∞) * l)) ω +
        cc * ∑ a ∈ S, l⁻¹ * 234256 ^ 2 * reachSum (configurationTranslation z ω) 8 a := by
    intro ω
    by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωB, Set.indicator_of_mem hωB]
      split_ifs with h
      · refine (ofReal_neg_planarMu_le h.1 h.2 q).trans ?_
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        calc ∑ a ∈ S, 234256 * planarReach (configurationTranslation z ω) a ^ 4
            ≤ ∑ a ∈ S,
                (l + l⁻¹ * (234256 * planarReach (configurationTranslation z ω) a ^ 4) ^ 2) :=
              Finset.sum_le_sum fun a _ => ENNReal.le_add_inv_mul_sq hl0 hltop
          _ = (S.card : ℝ≥0∞) * l + ∑ a ∈ S,
              l⁻¹ * 234256 ^ 2 * planarReach (configurationTranslation z ω) a ^ 8 := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
              congr 1
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [mul_pow, ← pow_mul, mul_assoc]
          _ ≤ (S.card : ℝ≥0∞) * l + ∑ a ∈ S,
              l⁻¹ * 234256 ^ 2 * reachSum (configurationTranslation z ω) 8 a := by
              gcongr with a
              exact planarReach_pow_le _ a 7
      · exact zero_le
    · rw [Set.indicator_of_notMem hωB, Set.indicator_of_notMem hωB, zero_add]
      exact zero_le
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
  have hreach : ∀ a ∈ S, ∫⁻ ω, reachSum (configurationTranslation z ω) 8 a
      ∂(latticeBondLaw 2 p) ≤ C₈ := fun a _ => by
    rw [hmp.lintegral_comp (measurable_reachSum 8 a)]
    exact h8 a
  have hmeasT : ∀ a ∈ S, Measurable fun ω =>
      l⁻¹ * 234256 ^ 2 * reachSum (configurationTranslation z ω) 8 a :=
    fun a _ => ((measurable_reachSum 8 a).comp hmp.measurable).const_mul _
  have hmeasR : Measurable fun ω => cc * ∑ a ∈ S,
      l⁻¹ * 234256 ^ 2 * reachSum (configurationTranslation z ω) 8 a :=
    (Finset.measurable_sum _ hmeasT).const_mul _
  have hbad : ∫⁻ ω, B.indicator (fun ω => if PlanarPartitionEvent (configurationTranslation z ω) ∧
      PlanarResolved (configurationTranslation z ω) (V.shift z) then
        ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q) else 0) ω
        ∂(latticeBondLaw 2 p) ≤
      cc * ((S.card : ℝ≥0∞) * (l * (2 * C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) +
        l⁻¹ * 234256 ^ 2 * C₈)) := by
    calc _ ≤ ∫⁻ ω, (B.indicator (fun _ => cc * ((S.card : ℝ≥0∞) * l)) ω +
          cc * ∑ a ∈ S, l⁻¹ * 234256 ^ 2 * reachSum (configurationTranslation z ω) 8 a)
          ∂(latticeBondLaw 2 p) := lintegral_mono key2
      _ = ∫⁻ ω, B.indicator (fun _ => cc * ((S.card : ℝ≥0∞) * l)) ω ∂(latticeBondLaw 2 p) +
          cc * ∑ a ∈ S, l⁻¹ * 234256 ^ 2 *
            ∫⁻ ω, reachSum (configurationTranslation z ω) 8 a ∂(latticeBondLaw 2 p) := by
          rw [lintegral_add_right _ hmeasR, lintegral_const_mul' _ _ (by finiteness),
            lintegral_finsetSum _ hmeasT]
          congr 2
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [lintegral_const_mul' _ _ (by finiteness)]
      _ ≤ cc * ((S.card : ℝ≥0∞) * l) * latticeBondLaw 2 p B +
          cc * ∑ _a ∈ S, l⁻¹ * 234256 ^ 2 * C₈ := by
          gcongr with a ha
          · exact lintegral_indicator_const_le _ _
          · exact hreach a ha
      _ ≤ cc * ((S.card : ℝ≥0∞) * l) * (2 * C *
            ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) +
          cc * ∑ _a ∈ S, l⁻¹ * 234256 ^ 2 * C₈ := by gcongr
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hcard : cc * (S.card : ℝ≥0∞) = 9 * ENNReal.ofReal s := by
    rw [hS, card_toIntegerCube_vertices, hcc, ← ENNReal.ofReal_mul (by positivity)]
    change ENNReal.ofReal (9 * s / V.volume * V.volume) = _
    rw [div_mul_cancel₀ _ hvol.ne', ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hexp : l * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) =
      ENNReal.ofReal (Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
    rw [hl, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hinv : l⁻¹ = ENNReal.ofReal (Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
    rw [hl, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
    congr 2
    ring
  have hmeas := measurable_planarMu_indicator V q
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (V.shift z) then
          ENNReal.ofReal (-planarMu ω (V.shift z) q) else 0) ∂(latticeBondLaw 2 p)
      = ∫⁻ ω, (if PlanarPartitionEvent (configurationTranslation z ω) ∧
          PlanarResolved (configurationTranslation z ω) (V.shift z) then
            ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q) else 0)
            ∂(latticeBondLaw 2 p) :=
        (hmp.lintegral_comp (measurable_planarMu_indicator (V.shift z) q)).symm
    _ ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) +
          B.indicator (fun ω => if PlanarPartitionEvent (configurationTranslation z ω) ∧
            PlanarResolved (configurationTranslation z ω) (V.shift z) then
              ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q)
            else 0) ω) ∂(latticeBondLaw 2 p) := lintegral_mono key1
    _ = ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) +
          ∫⁻ ω, B.indicator (fun ω => if PlanarPartitionEvent (configurationTranslation z ω) ∧
            PlanarResolved (configurationTranslation z ω) (V.shift z) then
              ENNReal.ofReal (-planarMu (configurationTranslation z ω) (V.shift z) q)
            else 0) ω ∂(latticeBondLaw 2 p) := lintegral_add_left hmeas _
    _ ≤ ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (-planarMu ω V q) else 0) ∂(latticeBondLaw 2 p) +
          cc * ((S.card : ℝ≥0∞) * (l * (2 * C *
            ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) + l⁻¹ * 234256 ^ 2 * C₈)) :=
        add_le_add le_rfl hbad
    _ = _ := by
        have hre : cc * ((S.card : ℝ≥0∞) * (l * (2 * C *
            ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) + l⁻¹ * 234256 ^ 2 * C₈)) =
            (cc * (S.card : ℝ≥0∞)) * (2 * C *
              (l * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) +
              l⁻¹ * 234256 ^ 2 * C₈) := by ring
        rw [hre, hcard, hexp, hinv, ENNReal.ofReal_mul hs0]
        ring

end Rigidity.Percolation
