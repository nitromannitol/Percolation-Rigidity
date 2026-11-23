import Rigidity.Proofs.Corrector.DarioStationaryPartition
import Rigidity.Proofs.Corrector.DarioCoarsenedFields
import Rigidity.Proofs.Percolation.PlanarMuMeasurable
import Rigidity.Proofs.Partition.Translation
import Rigidity.Proofs.Percolation.PlanarAnchorTranslation

/-!
# The coarsened corrector of Dario's stationary partition

For Lemma 3.2, Dario coarsens the corrector with respect to the stationary partition
`𝒫_stat^k` (here the planar partition capped at scale `k`, `TriadicCube.cappedCube`), with the
anchor `z̄_stat(□)` of (d.corsenstatio): the anchor `z̄(□)` of a good cube when it lies in the
infinite cluster, and otherwise the point of the infinite cluster closest to `□`, ties broken by
the lexicographic order.

* `TriadicCube.IsNearestInf`, `nearestInf`: the point of the infinite open components which is
  the smallest for main's anchor order of `□` (distance to the centre, then the lexicographic
  order), its existence, uniqueness, translation covariance and measurability;
* `statAnchor k ω z`: Dario's anchor of the cube of `𝒫_stat^k` containing `z`; it lies in the
  infinite cluster, equals the anchor of the planar partition where the cube is the planar
  partition cube, moves with the translations of `3^k ℤ²` (`statAnchor_translation`) and is
  measurable;
* `statGrad hG hGv i k y j ω = χ_{e_i}(z̄_stat(y + e_j)) - χ_{e_i}(z̄_stat(y))`, the gradient of
  the coarsened corrector `[χ_{e_i}]_{𝒫_stat^k}`; it is stationary under `3^k ℤ²`
  (`statGrad_translation`).
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped Classical

/-- `v` is the point of the infinite open components which is the smallest for the anchor order
of `□`. -/
def TriadicCube.IsNearestInf (ω : Configuration 2) (Q : TriadicCube 2) (v : Vertex 2) : Prop :=
  ω ∈ infiniteComponentEvent v ∧ ∀ w, ω ∈ infiniteComponentEvent w → Q.anchorKey v ≤ Q.anchorKey w

theorem TriadicCube.anchorKey_fst (Q : TriadicCube 2) (y : Vertex 2) :
    (ofLex (Q.anchorKey y)).1 = Finset.univ.sup fun i => (y i - Q.center i).natAbs := rfl

/-- A nearest point exists as soon as the infinite open components are not empty. -/
theorem TriadicCube.exists_isNearestInf {ω : Configuration 2} (Q : TriadicCube 2) {v₀ : Vertex 2}
    (h₀ : ω ∈ infiniteComponentEvent v₀) : ∃ v, Q.IsNearestInf ω v := by
  set m : ℕ := (ofLex (Q.anchorKey v₀)).1 with hm
  have hbox : ∀ y : Vertex 2, (ofLex (Q.anchorKey y)).1 ≤ m ↔
      ∀ i, Q.center i - m ≤ y i ∧ y i ≤ Q.center i + m := by
    intro y
    rw [anchorKey_fst, Finset.sup_le_iff]
    refine forall_congr' fun i => ?_
    simp only [Finset.mem_univ, true_implies]
    have h := Int.natCast_natAbs (y i - Q.center i)
    constructor
    · intro hi
      have : ((y i - Q.center i).natAbs : ℤ) ≤ m := by exact_mod_cast hi
      rw [h, abs_le] at this
      constructor <;> linarith [this.1, this.2]
    · rintro ⟨h1, h2⟩
      have : |y i - Q.center i| ≤ (m : ℤ) := abs_le.2 ⟨by linarith, by linarith⟩
      rw [← h] at this
      exact_mod_cast this
  set S : Finset (Vertex 2) := (Fintype.piFinset fun i =>
    Finset.Icc (Q.center i - m) (Q.center i + m)).filter fun v => ω ∈ infiniteComponentEvent v
  have hmemS : ∀ y, y ∈ S ↔ (ofLex (Q.anchorKey y)).1 ≤ m ∧ ω ∈ infiniteComponentEvent y := by
    intro y
    rw [hbox]
    simp only [S, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  have hv₀ : v₀ ∈ S := (hmemS v₀).2 ⟨le_rfl, h₀⟩
  obtain ⟨v, hvS, hmin⟩ := S.exists_min_image Q.anchorKey ⟨v₀, hv₀⟩
  obtain ⟨hvm, hv⟩ := (hmemS v).1 hvS
  refine ⟨v, hv, fun w hw => ?_⟩
  by_cases hwm : (ofLex (Q.anchorKey w)).1 ≤ m
  · exact hmin w ((hmemS w).2 ⟨hwm, hw⟩)
  · refine le_of_lt ?_
    change toLex _ < toLex _
    rw [Prod.Lex.toLex_lt_toLex]
    left
    change (ofLex (Q.anchorKey v)).1 < (ofLex (Q.anchorKey w)).1
    omega

theorem TriadicCube.IsNearestInf.unique {ω : Configuration 2} {Q : TriadicCube 2} {v v' : Vertex 2}
    (h : Q.IsNearestInf ω v) (h' : Q.IsNearestInf ω v') : v = v' :=
  Q.anchorKey_injective (le_antisymm (h.2 v' h'.1) (h'.2 v h.1))

/-- The nearest point of the infinite open components to `□` in the anchor order (the centre of
`□` if there is no infinite open component). -/
noncomputable def TriadicCube.nearestInf (ω : Configuration 2) (Q : TriadicCube 2) : Vertex 2 :=
  if h : ∃ v, Q.IsNearestInf ω v then Classical.choose h else Q.center

theorem TriadicCube.isNearestInf_nearestInf {ω : Configuration 2} (Q : TriadicCube 2)
    {v₀ : Vertex 2} (h₀ : ω ∈ infiniteComponentEvent v₀) : Q.IsNearestInf ω (Q.nearestInf ω) := by
  have h := Q.exists_isNearestInf h₀
  unfold nearestInf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem mem_infiniteComponentEvent_translation_iff (c : Vertex 2) (ω : Configuration 2)
    (v : Vertex 2) :
    configurationTranslation c ω ∈ infiniteComponentEvent (v + c) ↔
      ω ∈ infiniteComponentEvent v := by
  constructor
  · intro h
    have h' := Rigidity.Corrector.mem_infiniteComponentEvent_translation (-c) h
    have e := Rigidity.Corrector.configurationTranslation_neg_cancel (-c) ω
    rw [neg_neg] at e
    rwa [e, add_neg_cancel_right] at h'
  · exact Rigidity.Corrector.mem_infiniteComponentEvent_translation c

/-- The nearest point moves with a translation which moves the cube. -/
theorem TriadicCube.isNearestInf_shift_iff {Q : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, Q.side ∣ c i) (ω : Configuration 2) (v : Vertex 2) :
    (Q.shift c).IsNearestInf (configurationTranslation c ω) (v + c) ↔ Q.IsNearestInf ω v := by
  unfold IsNearestInf
  rw [mem_infiniteComponentEvent_translation_iff]
  refine and_congr Iff.rfl ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · have := h (w + c) ((mem_infiniteComponentEvent_translation_iff c ω w).2 hw)
    exact (anchorKey_shift_le_iff hc v w).1 this
  · have hw' : ω ∈ infiniteComponentEvent (w - c) := by
      rw [← mem_infiniteComponentEvent_translation_iff c ω, sub_add_cancel]
      exact hw
    have := (anchorKey_shift_le_iff hc v (w - c)).2 (h _ hw')
    rwa [sub_add_cancel] at this

theorem TriadicCube.nearestInf_shift {Q : TriadicCube 2} {c : Vertex 2} (hc : ∀ i, Q.side ∣ c i)
    (ω : Configuration 2) :
    (Q.shift c).nearestInf (configurationTranslation c ω) = Q.nearestInf ω + c := by
  by_cases h : ∃ v, ω ∈ infiniteComponentEvent v
  · obtain ⟨v₀, h₀⟩ := h
    have h1 := Q.isNearestInf_nearestInf h₀
    have h₀' := (mem_infiniteComponentEvent_translation_iff c ω v₀).2 h₀
    have h2 := (Q.shift c).isNearestInf_nearestInf h₀'
    exact h2.unique ((isNearestInf_shift_iff hc ω _).2 h1)
  · have hn : ¬ ∃ v, Q.IsNearestInf ω v := fun ⟨v, hv⟩ => h ⟨v, hv.1⟩
    have hn' : ¬ ∃ v, (Q.shift c).IsNearestInf (configurationTranslation c ω) v := by
      rintro ⟨v, hv⟩
      exact h ⟨v - c, by
        rw [← mem_infiniteComponentEvent_translation_iff c ω, sub_add_cancel]
        exact hv.1⟩
    unfold nearestInf
    rw [dif_neg hn, dif_neg hn']
    exact funext fun i => center_shift' hc i

theorem TriadicCube.measurable_isNearestInf (Q : TriadicCube 2) (v : Vertex 2) :
    Measurable fun ω : Configuration 2 => Q.IsNearestInf ω v :=
  (measurableSet_setOf.1 (measurableSet_infiniteComponentEvent v)).and
    (Measurable.forall fun w =>
      (measurableSet_setOf.1 (measurableSet_infiniteComponentEvent w)).imp measurable_const)

theorem TriadicCube.measurable_nearestInf (Q : TriadicCube 2) :
    Measurable fun ω : Configuration 2 => Q.nearestInf ω := by
  refine measurable_to_countable' fun v => ?_
  have heq : (fun ω : Configuration 2 => Q.nearestInf ω) ⁻¹' {v} =
      {ω | Q.IsNearestInf ω v} ∪
        ({ω | ∀ w, ω ∉ infiniteComponentEvent w} ∩ {_ω | Q.center = v}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    by_cases h : ∃ w, ω ∈ infiniteComponentEvent w
    · obtain ⟨w₀, h₀⟩ := h
      have h1 := Q.isNearestInf_nearestInf h₀
      constructor
      · rintro rfl
        exact Or.inl h1
      · rintro (h2 | ⟨h2, -⟩)
        · exact h1.unique h2
        · exact absurd h₀ (h2 w₀)
    · push Not at h
      have hn : ¬ ∃ v, Q.IsNearestInf ω v := fun ⟨v, hv⟩ => h v hv.1
      unfold nearestInf
      rw [dif_neg hn]
      constructor
      · intro hc
        exact Or.inr ⟨h, hc⟩
      · rintro (h2 | ⟨-, h2⟩)
        · exact absurd h2.1 (h v)
        · exact h2
  have h2 : MeasurableSet {ω : Configuration 2 | ∀ w, ω ∉ infiniteComponentEvent w} := by
    have e : {ω : Configuration 2 | ∀ w, ω ∉ infiniteComponentEvent w} =
        ⋂ w, (infiniteComponentEvent w)ᶜ := by
      ext ω
      simp
    rw [e]
    exact MeasurableSet.iInter fun w => (measurableSet_infiniteComponentEvent w).compl
  rw [heq]
  exact (measurableSet_setOf.2 (Q.measurable_isNearestInf v)).union
    (h2.inter (MeasurableSet.const (Q.center = v)))

end Rigidity.Percolation

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

/-- Dario's anchor (d.corsenstatio) of a cube: its anchor if it is good with anchor in the
infinite cluster, the nearest point of the infinite cluster otherwise. -/
noncomputable def statAnchorOf (ω : Configuration 2) (Q : TriadicCube 2) : Vertex 2 :=
  if Q ∈ planarGoodCubes ω ∧ ω ∈ infiniteComponentEvent (Q.planarAnchor ω) then Q.planarAnchor ω
  else Q.nearestInf ω

/-- The anchor of the cube of `𝒫_stat^k` containing `z`. -/
noncomputable def statAnchor (k : ℕ) (ω : Configuration 2) (z : Vertex 2) : Vertex 2 :=
  statAnchorOf ω (TriadicCube.cappedCube (planarGoodCubes ω) k z)

theorem statAnchorOf_mem_inf {ω : Configuration 2} (Q : TriadicCube 2) {v₀ : Vertex 2}
    (h₀ : ω ∈ infiniteComponentEvent v₀) : ω ∈ infiniteComponentEvent (statAnchorOf ω Q) := by
  unfold statAnchorOf
  split_ifs with h
  · exact h.2
  · exact (Q.isNearestInf_nearestInf h₀).1

theorem statAnchor_mem_inf {ω : Configuration 2} (k : ℕ) (z : Vertex 2) {v₀ : Vertex 2}
    (h₀ : ω ∈ infiniteComponentEvent v₀) : ω ∈ infiniteComponentEvent (statAnchor k ω z) :=
  statAnchorOf_mem_inf _ h₀

theorem statAnchorOf_shift {Q : TriadicCube 2} {c : Vertex 2} (hc : ∀ i, Q.side ∣ c i)
    (ω : Configuration 2) :
    statAnchorOf (configurationTranslation c ω) (Q.shift c) = statAnchorOf ω Q + c := by
  have hcond : (Q.shift c ∈ planarGoodCubes (configurationTranslation c ω) ∧
      configurationTranslation c ω ∈ infiniteComponentEvent
        ((Q.shift c).planarAnchor (configurationTranslation c ω))) ↔
      (Q ∈ planarGoodCubes ω ∧ ω ∈ infiniteComponentEvent (Q.planarAnchor ω)) := by
    rw [TriadicCube.planarAnchor_shift hc, mem_infiniteComponentEvent_translation_iff]
    exact and_congr (TriadicCube.shift_mem_planarGoodCubes_translation_iff hc ω) Iff.rfl
  unfold statAnchorOf
  by_cases h : Q ∈ planarGoodCubes ω ∧ ω ∈ infiniteComponentEvent (Q.planarAnchor ω)
  · rw [if_pos (hcond.2 h), if_pos h, TriadicCube.planarAnchor_shift hc]
  · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h, TriadicCube.nearestInf_shift hc]

/-- **Stationarity of the anchors** (Dario, (3kstationarypartition)): for `c ∈ 3^k ℤ²`,
`z̄_stat(τ_c ω, z + c) = z̄_stat(ω, z) + c`. -/
theorem statAnchor_translation {k : ℕ} {c : Vertex 2} (hc : ∀ i, (3 : ℤ) ^ k ∣ c i)
    (ω : Configuration 2) (z : Vertex 2) :
    statAnchor k (configurationTranslation c ω) (z + c) = statAnchor k ω z + c := by
  unfold statAnchor
  rw [cappedCube_planarGoodCubes_translation hc ω z]
  exact statAnchorOf_shift (TriadicCube.side_dvd_of_scale_le hc
    (TriadicCube.scale_cappedCube_le _ k z)) ω

/-- Where the cube of `𝒫_stat^k` is the cube of the planar partition, the anchors agree. -/
theorem statAnchor_eq_planarCoarseAnchor {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {k : ℕ} {z : Vertex 2} (h : TriadicCube.cappedCube (planarGoodCubes ω) k z = planarPartCube ω z) :
    statAnchor k ω z = planarCoarseAnchor ω z := by
  unfold statAnchor statAnchorOf
  rw [h, if_pos ⟨planarPartCube_mem_good hP z, infinite_planarCoarseAnchor hP z⟩]
  rfl

/-- The anchor of a fixed cube is measurable. -/
theorem measurable_planarAnchor (Q : TriadicCube 2) :
    Measurable fun ω : Configuration 2 => Q.planarAnchor ω := by
  by_cases hs : 1000 ≤ 3 ^ Q.scale
  · have h7 : 7 ≤ Q.scale := by
      by_contra h
      have : 3 ^ Q.scale ≤ 3 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
    let φ : Configuration 2 → Prop × Finset (Vertex 2) := fun ω =>
      (Q ∈ planarMeshedFamily ω, Q.displacements.filter fun e => Q.IsPlanarAnchor ω (Q.center + e))
    have hφ : ∀ t, MeasurableSet (φ ⁻¹' {t}) := by
      rintro ⟨P, F⟩
      have e : φ ⁻¹' {(P, F)} = {ω | (Q ∈ planarMeshedFamily ω ↔ P)} ∩
          {ω | Q.displacements.filter (fun e => Q.IsPlanarAnchor ω (Q.center + e)) = F} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff,
          Set.mem_setOf_eq, φ, eq_iff_iff]
      rw [e]
      exact (measurableSet_setOf.2 ((measurableSet_setOf.1
        (measurableSet_mem_planarMeshedFamily Q)).iff measurable_const)).inter
        (measurableSet_filter_eq _ _ fun e => measurable_isPlanarAnchor Q (Q.center + e))
    refine measurable_of_fiber_const φ hφ fun ω ω' h => ?_
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hmesh : ∀ ω'' : Configuration 2, Q ∈ planarMeshedFamily ω'' ↔ Q.planarMeshed ω'' :=
      fun ω'' => ⟨fun hm => hm.2, fun hm => ⟨h7, hm⟩⟩
    by_cases hm : Q.planarMeshed ω
    · have hm' : Q.planarMeshed ω' := by
        rw [← hmesh, ← h1, hmesh]
        exact hm
      exact planarAnchor_eq_of_filter_eq ⟨hm, hs⟩ ⟨hm', hs⟩ h2
    · have hm' : ¬ Q.planarMeshed ω' := by
        rw [← hmesh, ← h1, hmesh]
        exact hm
      unfold TriadicCube.planarAnchor
      rw [if_neg (fun h' => hm h'.1), if_neg (fun h' => hm' h'.1)]
  · have e : (fun ω : Configuration 2 => Q.planarAnchor ω) = fun _ => Q.center := by
      funext ω
      unfold TriadicCube.planarAnchor
      rw [if_neg (fun h' => hs h'.2)]
    rw [e]
    exact measurable_const

theorem measurableSet_mem_cappedPlanar (k : ℕ) (T : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | T ∈ TriadicCube.capped (planarGoodCubes ω) k} := by
  have h : {ω : Configuration 2 | T ∈ TriadicCube.capped (planarGoodCubes ω) k} =
      {ω | T ∈ planarGoodCubes ω} ∪ {_ω | k ≤ T.scale} := rfl
  rw [h]
  exact (TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
    measurableSet_mem_planarMeshedFamily T).union (MeasurableSet.const _)

theorem measurable_statAnchorOf (Q : TriadicCube 2) :
    Measurable fun ω => statAnchorOf ω Q := by
  have hA := measurable_planarAnchor Q
  have hinf : MeasurableSet {ω : Configuration 2 |
      ω ∈ infiniteComponentEvent (Q.planarAnchor ω)} := by
    have e : {ω : Configuration 2 | ω ∈ infiniteComponentEvent (Q.planarAnchor ω)} =
        ⋃ v : Vertex 2, ((fun ω => Q.planarAnchor ω) ⁻¹' {v} ∩ infiniteComponentEvent v) := by
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
  have hgood : MeasurableSet {ω : Configuration 2 | Q ∈ planarGoodCubes ω} :=
    TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
      measurableSet_mem_planarMeshedFamily Q
  unfold statAnchorOf
  exact Measurable.ite (hgood.inter hinf) hA Q.measurable_nearestInf

/-- **The anchors of `𝒫_stat^k` are measurable.** -/
theorem measurable_statAnchor (k : ℕ) (z : Vertex 2) :
    Measurable fun ω => statAnchor k ω z := by
  refine measurable_to_countable' fun v => ?_
  have e : (fun ω => statAnchor k ω z) ⁻¹' {v} = ⋃ Q : TriadicCube 2,
      ({ω | z ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.capped (planarGoodCubes ω) k)} ∩
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
      (fun ω => TriadicCube.capped (planarGoodCubes ω) k) (measurableSet_mem_cappedPlanar k) Q)))).inter
    (measurable_statAnchorOf Q (measurableSet_singleton v))

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The gradient `χ_{e_i}(z̄_stat(y + e_j)) - χ_{e_i}(z̄_stat(y))` of the coarsened corrector
`[χ_{e_i}]_{𝒫_stat^k}`. -/
noncomputable def statGrad (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2) (ω : Configuration 2) :
    ℝ :=
  correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω (y + LatticeProb.unit j))
    (statAnchor k ω y)

theorem measurable_statGrad (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2) :
    Measurable (statGrad hG hGv i k y j) :=
  measurable_correctorDiff_comp hG hGv _ (measurable_statAnchor k _) (measurable_statAnchor k y)

/-- **Stationarity of the coarsened corrector** (Dario, (statcoarsencorrector)): for
`c ∈ 3^k ℤ²`, `∇[χ]_{𝒫_stat^k}(y + c)(τ_c ω) = ∇[χ]_{𝒫_stat^k}(y)(ω)`. -/
theorem statGrad_translation {i : Fin 2} {k : ℕ} {c : Vertex 2} (hc : ∀ i, (3 : ℤ) ^ k ∣ c i)
    {ω : Configuration 2} (hω : ω ∈ G) (hω' : configurationTranslation c ω ∈ G) {v₀ : Vertex 2}
    (h₀ : ω ∈ infiniteComponentEvent v₀) (y : Vertex 2) (j : Fin 2) :
    statGrad hG hGv i k (y + c) j (configurationTranslation c ω) = statGrad hG hGv i k y j ω := by
  unfold statGrad
  rw [show y + c + LatticeProb.unit j = (y + LatticeProb.unit j) + c by abel,
    statAnchor_translation hc, statAnchor_translation hc]
  exact correctorDiff_translate hG hGv c hω hω' (statAnchor_mem_inf k _ h₀)
    (statAnchor_mem_inf k _ h₀)

end Carrier

end Rigidity.Corrector
