import Rigidity.Proofs.Corrector.DarioStationaryCoarsening
import Rigidity.Proofs.Corrector.GeneralPropThreeOne
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLocal

/-!
# The coarsened corrector of Dario's stationary partition in every dimension

For Lemma 3.2, Dario coarsens the corrector with respect to the stationary partition
`𝒫_stat^k`: the partition into good cubes of `ℤᵈ` capped at scale `k`
(`TriadicCube.cappedCube (TriadicCube.goodCubes ω) k`), with the anchor `z̄_stat(□)` of
Dario's Definition 3.4: the anchor of a good cube when it lies in the infinite cluster, and
otherwise the point of the infinite cluster closest to `□`, ties broken by the anchor order
(`TriadicCube.nearestInf`).

* `dario_errorstatpart`: **(3.3)**, `P[∃ x ∈ □, □_𝒫(x) ≠ □_{𝒫_stat^k}(x)] ≤ C exp(-c 3^k)` for
  every triadic cube `□` of scale `k`, from the localization of the partition (Armstrong and
  Dario, Proposition 4.9, `Rigidity.Percolation.exists_measure_cubeCappedDiscrepancy_le`);
* `statAnchor k ω z`: Dario's anchor of the cube of `𝒫_stat^k` containing `z`; it lies in the
  infinite cluster, equals the anchor of the partition where the cube is the partition cube,
  moves with the translations of `3^k ℤᵈ` (`statAnchor_translation`) and is measurable;
* `statGrad hG hGv i k y j ω = χ_{e_i}(z̄_stat(y + e_j)) - χ_{e_i}(z̄_stat(y))`, the gradient of
  the coarsened corrector `[χ_{e_i}]_{𝒫_stat^k}`; it is stationary under `3^k ℤᵈ`
  (`statGrad_translation`).
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical ENNReal

variable {d : ℕ}

/-- **Dario, (3.3)**: the partition into good cubes and the partition capped at the scale `k` of a
triadic cube `□` agree on `□` outside an event of probability at most `C exp(-c 3^k)`. -/
theorem dario_errorstatpart [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube d,
      latticeBondLaw d p {ω | ∃ x ∈ V.vertices,
        partitionCube ω x ≠ TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_measure_cubeCappedDiscrepancy_le hd hpc
  refine ⟨C, hC, c, hc, fun V => (measure_mono_ae ?_).trans (h V)⟩
  filter_upwards [ae_partitionEvent hd hpc] with ω hP
  intro hω
  obtain ⟨x, hx, hne⟩ := hω
  exact ⟨x, hx, partitionCube ω x, (partitionCube_spec hP x).1, (partitionCube_spec hP x).2, hne⟩

/-- Dario's anchor (Definition 3.4) of a cube: its anchor if it is good with anchor in the
infinite cluster, the nearest point of the infinite cluster otherwise. -/
noncomputable def statAnchorOf (ω : Configuration d) (Q : TriadicCube d) : Vertex d :=
  if Q ∈ TriadicCube.goodCubes ω ∧ ω ∈ infiniteComponentEvent (Q.anchor ω) then Q.anchor ω
  else Q.nearestInf ω

/-- The anchor of the cube of `𝒫_stat^k` containing `z`. -/
noncomputable def statAnchor (k : ℕ) (ω : Configuration d) (z : Vertex d) : Vertex d :=
  statAnchorOf ω (TriadicCube.cappedCube (TriadicCube.goodCubes ω) k z)

theorem statAnchorOf_mem_inf {ω : Configuration d} (Q : TriadicCube d) {v₀ : Vertex d}
    (h₀ : ω ∈ infiniteComponentEvent v₀) : ω ∈ infiniteComponentEvent (statAnchorOf ω Q) := by
  unfold statAnchorOf
  split_ifs with h
  · exact h.2
  · exact (Q.isNearestInf_nearestInf h₀).1

theorem statAnchor_mem_inf {ω : Configuration d} (k : ℕ) (z : Vertex d) {v₀ : Vertex d}
    (h₀ : ω ∈ infiniteComponentEvent v₀) : ω ∈ infiniteComponentEvent (statAnchor k ω z) :=
  statAnchorOf_mem_inf _ h₀

theorem statAnchorOf_shift {Q : TriadicCube d} {c : Vertex d} (hc : ∀ i, Q.side ∣ c i)
    (ω : Configuration d) :
    statAnchorOf (configurationTranslation c ω) (Q.shift c) = statAnchorOf ω Q + c := by
  have hcond : (Q.shift c ∈ TriadicCube.goodCubes (configurationTranslation c ω) ∧
      configurationTranslation c ω ∈ infiniteComponentEvent
        ((Q.shift c).anchor (configurationTranslation c ω))) ↔
      (Q ∈ TriadicCube.goodCubes ω ∧ ω ∈ infiniteComponentEvent (Q.anchor ω)) := by
    rw [TriadicCube.anchor_shift hc, mem_infiniteComponentEvent_translation_iff]
    exact and_congr (TriadicCube.shift_mem_goodCubes_translation_iff hc ω) Iff.rfl
  unfold statAnchorOf
  by_cases h : Q ∈ TriadicCube.goodCubes ω ∧ ω ∈ infiniteComponentEvent (Q.anchor ω)
  · rw [if_pos (hcond.2 h), if_pos h, TriadicCube.anchor_shift hc]
  · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h, TriadicCube.nearestInf_shift hc]

/-- **Stationarity of the anchors** (Dario, (3kstationarypartition)): for `c ∈ 3^k ℤᵈ`,
`z̄_stat(τ_c ω, z + c) = z̄_stat(ω, z) + c`. -/
theorem statAnchor_translation {k : ℕ} {c : Vertex d} (hc : ∀ i, (3 : ℤ) ^ k ∣ c i)
    (ω : Configuration d) (z : Vertex d) :
    statAnchor k (configurationTranslation c ω) (z + c) = statAnchor k ω z + c := by
  unfold statAnchor
  rw [cappedCube_goodCubes_translation hc ω z]
  exact statAnchorOf_shift (TriadicCube.side_dvd_of_scale_le hc
    (TriadicCube.scale_cappedCube_le _ k z)) ω

/-- Where the cube of `𝒫_stat^k` is the cube of the partition, the anchors agree. -/
theorem statAnchor_eq_partitionAnchor (hd : 0 < d) {ω : Configuration d} (hP : PartitionEvent ω)
    {k : ℕ} {z : Vertex d}
    (h : TriadicCube.cappedCube (TriadicCube.goodCubes ω) k z = partitionCube ω z) :
    statAnchor k ω z = partitionAnchor ω z := by
  unfold statAnchor statAnchorOf
  rw [h, if_pos ⟨partitionCube_mem_goodCubes hP z, infinite_partitionAnchor hd hP z⟩]
  rfl

/-- The anchor of a fixed cube is measurable. -/
theorem measurable_cubeAnchor (Q : TriadicCube d) :
    Measurable fun ω : Configuration d => Q.anchor ω :=
  measurable_to_countable' fun y => TriadicCube.measurableSet_anchor_eq Q y

theorem measurableSet_mem_cappedGood (k : ℕ) (T : TriadicCube d) :
    MeasurableSet {ω : Configuration d | T ∈ TriadicCube.capped (TriadicCube.goodCubes ω) k} := by
  have h : {ω : Configuration d | T ∈ TriadicCube.capped (TriadicCube.goodCubes ω) k} =
      {ω | T ∈ TriadicCube.goodCubes ω} ∪ {_ω | k ≤ T.scale} := rfl
  rw [h]
  exact (TriadicCube.measurableSet_mem_goodCubes T).union (MeasurableSet.const _)

theorem measurable_statAnchorOf (Q : TriadicCube d) :
    Measurable fun ω => statAnchorOf ω Q := by
  have hA := measurable_cubeAnchor Q
  have hinf : MeasurableSet {ω : Configuration d |
      ω ∈ infiniteComponentEvent (Q.anchor ω)} := by
    have e : {ω : Configuration d | ω ∈ infiniteComponentEvent (Q.anchor ω)} =
        ⋃ v : Vertex d, ((fun ω => Q.anchor ω) ⁻¹' {v} ∩ infiniteComponentEvent v) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨_, rfl, h⟩
      · rintro ⟨v, hv, h⟩
        rw [hv]
        exact h
    rw [e]
    exact MeasurableSet.iUnion fun v => (hA (measurableSet_singleton v)).inter
      (measurableSet_infiniteComponentEvent v)
  have hgood : MeasurableSet {ω : Configuration d | Q ∈ TriadicCube.goodCubes ω} :=
    TriadicCube.measurableSet_mem_goodCubes Q
  unfold statAnchorOf
  exact Measurable.ite (hgood.inter hinf) hA Q.measurable_nearestInf

/-- **The anchors of `𝒫_stat^k` are measurable.** -/
theorem measurable_statAnchor (k : ℕ) (z : Vertex d) :
    Measurable fun ω => statAnchor k ω z := by
  refine measurable_to_countable' fun v => ?_
  have e : (fun ω => statAnchor k ω z) ⁻¹' {v} = ⋃ Q : TriadicCube d,
      ({ω | z ∈ Q.vertices ∧
        Q.IsMaximalStopping (TriadicCube.capped (TriadicCube.goodCubes ω) k)} ∩
        (fun ω => statAnchorOf ω Q) ⁻¹' {v}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨_, TriadicCube.cappedCube_spec _ k z, h⟩
    · rintro ⟨Q, ⟨hz, hQ⟩, h⟩
      unfold statAnchor
      rw [TriadicCube.cappedCube_eq hz hQ]
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun Q => (measurableSet_setOf.2 (measurable_const.and
    (measurableSet_setOf.1 (TriadicCube.measurableSet_isMaximalStopping
      (fun ω => TriadicCube.capped (TriadicCube.goodCubes ω) k)
      (measurableSet_mem_cappedGood k) Q)))).inter
    (measurable_statAnchorOf Q (measurableSet_singleton v))

section Carrier

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The gradient `χ_{e_i}(z̄_stat(y + e_j)) - χ_{e_i}(z̄_stat(y))` of the coarsened corrector
`[χ_{e_i}]_{𝒫_stat^k}`. -/
noncomputable def statGrad (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d) (ω : Configuration d) :
    ℝ :=
  correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω (y + LatticeProb.unit j))
    (statAnchor k ω y)

theorem measurable_statGrad (i : Fin d) (k : ℕ) (y : Vertex d) (j : Fin d) :
    Measurable (statGrad hG hGv i k y j) :=
  measurable_correctorDiff_comp hG hGv _ (measurable_statAnchor k _) (measurable_statAnchor k y)

/-- **Stationarity of the coarsened corrector** (Dario, (statcoarsencorrector)): for
`c ∈ 3^k ℤᵈ`, `∇[χ]_{𝒫_stat^k}(y + c)(τ_c ω) = ∇[χ]_{𝒫_stat^k}(y)(ω)`. -/
theorem statGrad_translation {i : Fin d} {k : ℕ} {c : Vertex d} (hc : ∀ i, (3 : ℤ) ^ k ∣ c i)
    {ω : Configuration d} (hω : ω ∈ G) (hω' : configurationTranslation c ω ∈ G) {v₀ : Vertex d}
    (h₀ : ω ∈ infiniteComponentEvent v₀) (y : Vertex d) (j : Fin d) :
    statGrad hG hGv i k (y + c) j (configurationTranslation c ω) = statGrad hG hGv i k y j ω := by
  unfold statGrad
  rw [show y + c + LatticeProb.unit j = (y + LatticeProb.unit j) + c by abel,
    statAnchor_translation hc, statAnchor_translation hc]
  exact correctorDiff_translate hG hGv c hω hω' (statAnchor_mem_inf k _ h₀)
    (statAnchor_mem_inf k _ h₀)

end Carrier

end Rigidity.Corrector.GeneralDim
