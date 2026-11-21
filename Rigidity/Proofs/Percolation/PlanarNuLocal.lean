import Rigidity.Proofs.Percolation.PlanarLocality
import Rigidity.Proofs.Percolation.PlanarNuConvergence
import Rigidity.Proofs.Percolation.PlanarMuMeasurable

/-!
# The local version of `ν` in the plane

For a triadic cube `V` of scale `n`, the local data of the partition at `V` are, at each vertex of
`V`, the cube of the partition capped at scale `n` and the displacements from its centre with the
anchor property, together with the open edges inside `V`. They depend only on the bonds inside the
square of side `14 · 3ⁿ` around `V`. On the event that the partition exists and agrees with the
capped partition on `V`, the local data determine the partition cubes of the vertices of `V`,
their anchors, the cluster `C_*(V)` and hence `1{V res} ν(V, ξ)`.

The local version `ν_loc(V, ξ)` is the value of `1{P, V res} ν(V, ξ)` at any configuration of this
event with the same local data. It is measurable for the σ-algebra of the bonds near `V`, so that
local versions on cubes with disjoint neighbourhoods are independent; it agrees with
`1{P, V res} ν(V, ξ)` outside an event of probability at most `C exp (-c 3ⁿ)`. This is the planar
form of the local quantities of Armstrong and Dario, (4.39), and of Proposition 4.10 for `ν`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The type of local data at a triadic cube. -/
abbrev PlanarLocalDatum (V : TriadicCube 2) : Type :=
  (↥V.toIntegerCube.vertices → TriadicCube 2 × Finset (Vertex 2)) × Finset (Vertex 2 × Vertex 2)

/-- The displacements with the anchor property of a cube. -/
noncomputable def TriadicCube.anchorDisplacements (ω : Configuration 2) (Q : TriadicCube 2) :
    Finset (Vertex 2) :=
  Q.displacements.filter fun e => Q.IsPlanarAnchor ω (Q.center + e)

/-- The local data of the partition at a triadic cube `V`. -/
noncomputable def planarLocalData (ω : Configuration 2) (V : TriadicCube 2) : PlanarLocalDatum V :=
  (fun x => (TriadicCube.cappedCube (planarGoodCubes ω) V.scale x.1,
      (TriadicCube.cappedCube (planarGoodCubes ω) V.scale x.1).anchorDisplacements ω),
    (V.toIntegerCube.vertices ×ˢ V.toIntegerCube.vertices).filter
      fun e => (openGraph ω).Adj e.1 e.2)

/-- The partition exists and agrees with the capped partition on `V`. -/
def PlanarLocalGood (ω : Configuration 2) (V : TriadicCube 2) : Prop :=
  PlanarPartitionEvent ω ∧ ¬ PlanarCappedDiscrepancy ω V

/-- The value of `1{P, V res} ν(V, ξ)` at a configuration of the good event with given local
data. -/
noncomputable def planarNuLocOf (V : TriadicCube 2) (ξ : Fin 2 → ℝ) (t : PlanarLocalDatum V) :
    ℝ≥0∞ :=
  if h : ∃ ω, PlanarLocalGood ω V ∧ planarLocalData ω V = t then
    (if PlanarPartitionEvent h.choose ∧ PlanarResolved h.choose V then
      ENNReal.ofReal (planarNu h.choose V ξ) else 0)
  else 0

/-- **The local version of `ν`.** -/
noncomputable def planarNuLoc (V : TriadicCube 2) (ξ : Fin 2 → ℝ) (ω : Configuration 2) :
    ℝ≥0∞ :=
  planarNuLocOf V ξ (planarLocalData ω V)

variable {ω ω' : Configuration 2}

theorem planarPartCube_eq_cappedCube {V : TriadicCube 2} (h : PlanarLocalGood ω V) {x : Vertex 2}
    (hx : x ∈ V.vertices) :
    planarPartCube ω x = TriadicCube.cappedCube (planarGoodCubes ω) V.scale x := by
  by_contra hne
  exact h.2 ⟨x, hx, _, (planarPartCube_spec h.1 x).1, (planarPartCube_spec h.1 x).2, hne⟩

/-- On the good event, the local data determine `1{P, V res} ν(V, ξ)`. -/
theorem planarNu_indicator_eq_of_planarLocalData_eq {V : TriadicCube 2}
    (hω : PlanarLocalGood ω V) (hω' : PlanarLocalGood ω' V)
    (h : planarLocalData ω V = planarLocalData ω' V) (ξ : Fin 2 → ℝ) :
    (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then ENNReal.ofReal (planarNu ω V ξ)
      else 0) =
      if PlanarPartitionEvent ω' ∧ PlanarResolved ω' V then ENNReal.ofReal (planarNu ω' V ξ)
      else 0 := by
  have hcd := congrArg Prod.fst h
  have hQx : ∀ x ∈ V.vertices,
      TriadicCube.cappedCube (planarGoodCubes ω) V.scale x =
        TriadicCube.cappedCube (planarGoodCubes ω') V.scale x ∧
      (TriadicCube.cappedCube (planarGoodCubes ω) V.scale x).anchorDisplacements ω =
        (TriadicCube.cappedCube (planarGoodCubes ω') V.scale x).anchorDisplacements ω' := by
    intro x hx
    have := congrFun hcd ⟨x, (V.mem_toIntegerCube_vertices x).2 hx⟩
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hQ : ∀ x ∈ V.vertices, planarPartCube ω x = planarPartCube ω' x := fun x hx => by
    rw [planarPartCube_eq_cappedCube hω hx, planarPartCube_eq_cappedCube hω' hx]
    exact (hQx x hx).1
  have hres : PlanarResolved ω V ↔ PlanarResolved ω' V := by
    unfold PlanarResolved
    exact forall₂_congr fun z hz => by rw [hQ z hz]
  have hanc : ∀ x ∈ V.vertices,
      (planarPartCube ω' x).planarAnchor ω' = (planarPartCube ω x).planarAnchor ω := by
    intro x hx
    rw [← hQ x hx]
    have hT := (hQx x hx).2
    rw [← planarPartCube_eq_cappedCube hω hx, ← planarPartCube_eq_cappedCube hω' hx,
      ← hQ x hx] at hT
    exact (planarAnchor_eq_of_filter_eq ⟨(planarPartCube_meshed hω.1 x).1,
      planarPartCube_large hω.1 x⟩
      (by rw [hQ x hx]; exact ⟨(planarPartCube_meshed hω'.1 x).1, planarPartCube_large hω'.1 x⟩)
      hT).symm
  have hadj : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) := by
    intro x hx y hy
    have hxS : x ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices x).2 hx
    have hyS : y ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices y).2 hy
    have h2 := Finset.ext_iff.1 (congrArg Prod.snd h) (x, y)
    simp only [planarLocalData, Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
    exact h2.symm
  have hcl : ∀ x, x ∈ planarCubeCluster ω' V ↔ x ∈ planarCubeCluster ω V := by
    intro x
    unfold planarCubeCluster
    simp only [Set.mem_setOf_eq]
    refine and_congr_right fun hx => ?_
    rw [hanc x hx]
    exact reachIn_iff_of_adj_iff hadj _ _
  by_cases hr : PlanarResolved ω V
  · rw [if_pos ⟨hω.1, hr⟩, if_pos ⟨hω'.1, hres.1 hr⟩]
    congr 1
    refine (planarNu_eq_of_cluster_eq (fun x => ?_) (fun x hx y hy => ?_) ξ).symm
    · rw [mem_clusterVertices, mem_clusterVertices]
      exact hcl x
    · exact hadj x (mem_clusterVertices.1 hx).1 y (mem_clusterVertices.1 hy).1
  · rw [if_neg fun h' => hr h'.2, if_neg fun h' => hr (hres.2 h'.2)]

/-- **Agreement with `ν`.** On the good event, the local version equals
`1{P, V res} ν(V, ξ)`. -/
theorem planarNuLoc_eq_of_good {V : TriadicCube 2} (hω : PlanarLocalGood ω V)
    (ξ : Fin 2 → ℝ) :
    planarNuLoc V ξ ω = if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (planarNu ω V ξ) else 0 := by
  have hex : ∃ ω', PlanarLocalGood ω' V ∧ planarLocalData ω' V = planarLocalData ω V :=
    ⟨ω, hω, rfl⟩
  unfold planarNuLoc planarNuLocOf
  rw [dif_pos hex]
  exact planarNu_indicator_eq_of_planarLocalData_eq hex.choose_spec.1 hω hex.choose_spec.2 ξ

theorem planarNuLoc_le (V : TriadicCube 2) (ξ : Fin 2 → ℝ) (ω : Configuration 2) :
    planarNuLoc V ξ ω ≤ ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) := by
  unfold planarNuLoc planarNuLocOf
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (planarNu_le ξ)
  · exact zero_le
  · exact zero_le

/-- **Locality of the local data.** -/
theorem planarLocalData_eq_of_localBonds {V : TriadicCube 2}
    (h : ∀ e ∈ localBonds V.planarLocalRegion, ω e = ω' e) :
    planarLocalData ω' V = planarLocalData ω V := by
  have hagree := adj_iff_of_localBonds h
  have hcap : ∀ x ∈ V.vertices, TriadicCube.cappedCube (planarGoodCubes ω') V.scale x =
      TriadicCube.cappedCube (planarGoodCubes ω) V.scale x := fun x hx =>
    TriadicCube.cappedCube_eq_of_agree fun T hT hnear =>
      mem_planarGoodCubes_iff_of_adj_iff fun y hy z hz =>
        hagree y (TriadicCube.ninefold_subset_planarLocalRegion_of_near hx hT hnear hy) z
          (TriadicCube.ninefold_subset_planarLocalRegion_of_near hx hT hnear hz)
  unfold planarLocalData
  refine Prod.ext (funext fun x => ?_) ?_
  · have hx := (V.mem_toIntegerCube_vertices x.1).1 x.2
    simp only [hcap x.1 hx, TriadicCube.anchorDisplacements]
    refine Prod.ext rfl (Finset.filter_congr fun e _ => ?_)
    have hQ := TriadicCube.cappedCube_spec (planarGoodCubes ω) V.scale x.1
    exact TriadicCube.isPlanarAnchor_iff_of_adj_iff (fun y hy z hz =>
      hagree y (TriadicCube.ninefold_subset_planarLocalRegion hx hQ.1
        (TriadicCube.scale_cappedCube_le _ _ _) hy) z
      (TriadicCube.ninefold_subset_planarLocalRegion hx hQ.1
        (TriadicCube.scale_cappedCube_le _ _ _) hz)) _
  · refine Finset.filter_congr fun e he => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 he
    exact hagree e.1 (V.vertices_subset_planarLocalRegion ((V.mem_toIntegerCube_vertices _).1 h1))
      e.2 (V.vertices_subset_planarLocalRegion ((V.mem_toIntegerCube_vertices _).1 h2))

/-- The cube of the capped planar partition at a fixed vertex is a measurable function. -/
theorem measurableSet_cappedCube_eq (n : ℕ) (x : Vertex 2) (Q : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 |
      TriadicCube.cappedCube (planarGoodCubes ω) n x = Q} := by
  have heq : {ω : Configuration 2 | TriadicCube.cappedCube (planarGoodCubes ω) n x = Q} =
      {ω | x ∈ Q.vertices ∧ Q.IsMaximalStopping (TriadicCube.capped (planarGoodCubes ω) n)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact TriadicCube.cappedCube_spec _ _ _
    · rintro ⟨hx, hQ⟩
      exact TriadicCube.cappedCube_eq hx hQ
  rw [heq]
  refine (MeasurableSet.const _).inter (TriadicCube.measurableSet_isMaximalStopping
    (fun ω => TriadicCube.capped (planarGoodCubes ω) n) (fun T => ?_) Q)
  change MeasurableSet {ω : Configuration 2 | T ∈ planarGoodCubes ω ∨ n ≤ T.scale}
  exact measurableSet_setOf.2 ((measurableSet_setOf.1
    (TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
      measurableSet_mem_planarMeshedFamily T)).or measurable_const)

/-- The local data are measurable, with countably many values. -/
theorem measurableSet_planarLocalData_eq (V : TriadicCube 2) (t : PlanarLocalDatum V) :
    MeasurableSet {ω : Configuration 2 | planarLocalData ω V = t} := by
  have key : ∀ (ω : Configuration 2) (x : ↥V.toIntegerCube.vertices),
      (TriadicCube.cappedCube (planarGoodCubes ω) V.scale x.1,
        (TriadicCube.cappedCube (planarGoodCubes ω) V.scale x.1).anchorDisplacements ω) =
        t.1 x ↔
      TriadicCube.cappedCube (planarGoodCubes ω) V.scale x.1 = (t.1 x).1 ∧
        (t.1 x).1.anchorDisplacements ω = (t.1 x).2 := by
    intro ω x
    constructor
    · intro hx
      have h1 := congrArg Prod.fst hx
      have h2 := congrArg Prod.snd hx
      simp only at h1 h2
      rw [h1] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine Prod.ext h1 ?_
      simp only
      rw [h1]
      exact h2
  have heq : {ω : Configuration 2 | planarLocalData ω V = t} =
      {ω | ∀ x : ↥V.toIntegerCube.vertices,
        TriadicCube.cappedCube (planarGoodCubes ω) V.scale x.1 = (t.1 x).1 ∧
          (t.1 x).1.anchorDisplacements ω = (t.1 x).2} ∩
      {ω | (V.toIntegerCube.vertices ×ˢ V.toIntegerCube.vertices).filter
        (fun e => (openGraph ω).Adj e.1 e.2) = t.2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨fun x => (key ω x).1 (congrFun (congrArg Prod.fst h) x), congrArg Prod.snd h⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext (funext fun x => (key ω x).2 (h1 x)) h2
  rw [heq]
  refine MeasurableSet.inter (measurableSet_setOf.2 (Measurable.forall fun x =>
    (measurableSet_setOf.1 (measurableSet_cappedCube_eq V.scale x.1 (t.1 x).1)).and
      (measurableSet_setOf.1 (measurableSet_filter_eq _ _ fun e =>
        measurable_isPlanarAnchor _ _)))) ?_
  exact measurableSet_filter_eq _ _ fun e =>
    measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)

/-- The local version of `ν` is measurable. -/
theorem measurable_planarNuLoc (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Measurable (planarNuLoc V ξ) :=
  measurable_of_fiber_const (fun ω => planarLocalData ω V)
    (fun t => measurableSet_planarLocalData_eq V t) fun _ _ h =>
      congrArg (planarNuLocOf V ξ) h

/-- **Locality of `ν_loc`** (planar form of Armstrong and Dario, (4.39)). The local version of `ν`
is measurable for the σ-algebra of the bonds inside the square of side `14 · 3ⁿ` around `V`. -/
theorem measurable_planarNuLoc_localBondSigma (V : TriadicCube 2) (ξ : Fin 2 → ℝ) :
    Measurable[localBondSigma V.planarLocalRegion] (planarNuLoc V ξ) :=
  measurable_localBondSigma_of_eq _ (measurable_planarNuLoc V ξ) fun _ _ h =>
    congrArg (planarNuLocOf V ξ) (planarLocalData_eq_of_localBonds h).symm

/-- **Independence of local versions.** Local versions of `ν` on cubes with disjoint local regions
are independent. -/
theorem indepFun_planarNuLoc (p : unitInterval) {V W : TriadicCube 2}
    (hVW : Disjoint V.planarLocalRegion W.planarLocalRegion) (ξ η : Fin 2 → ℝ) :
    IndepFun (planarNuLoc V ξ) (planarNuLoc W η) (latticeBondLaw 2 p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_planarNuLoc_localBondSigma V ξ).comap_le)
    (measurable_planarNuLoc_localBondSigma W η).comap_le)

/-- **Localization of `ν`** (planar form of Armstrong and Dario, Proposition 4.10, for `ν`). The
local version differs from `1{P, V res} ν(V, ξ)` only on an event of probability at most
`C exp (-c 3ⁿ)`, and the expectations differ by at most `C |ξ|₁² exp (-c 3ⁿ)`. -/
theorem exists_planarNuLoc_localization {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube 2) (ξ : Fin 2 → ℝ),
      latticeBondLaw 2 p {ω | ¬ PlanarLocalGood ω V} ≤
          C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) ∧
      ∫⁻ ω, planarNuLoc V ξ ω ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal (9 / 4) * C *
          ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) ∧
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ∫⁻ ω, planarNuLoc V ξ ω ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal (9 / 4) * C *
          ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_planarCappedDiscrepancy_le hpc
  refine ⟨C, hC, c, hc, fun V ξ => ?_⟩
  have hPnull : latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} = 0 :=
    ae_iff.1 (ae_planarPartitionEvent hpc)
  have hbad : latticeBondLaw 2 p {ω | ¬ PlanarLocalGood ω V} ≤
      C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
    have hsub : {ω | ¬ PlanarLocalGood ω V} ⊆
        {ω | ¬ PlanarPartitionEvent ω} ∪ {ω | PlanarCappedDiscrepancy ω V} := by
      intro ω hω
      simp only [PlanarLocalGood, not_and_or, not_not, Set.mem_setOf_eq] at hω
      exact hω
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := by rw [hPnull, zero_add]; exact hD V
  set K : ℝ≥0∞ := ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) with hK
  have hKe : K * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) =
      ENNReal.ofReal (9 / 4) * C *
        ENNReal.ofReal ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
    rw [hK, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity)]
    ring
  set B := {ω : Configuration 2 | ¬ PlanarLocalGood ω V}
  have hf := measurable_planarNu_indicator V ξ
  have hl := measurable_planarNuLoc V ξ
  refine ⟨hbad, ?_, ?_⟩
  · calc ∫⁻ ω, planarNuLoc V ξ ω ∂(latticeBondLaw 2 p)
        ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) + B.indicator (fun _ => K) ω)
            ∂(latticeBondLaw 2 p) := lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            exact le_add_left (planarNuLoc_le V ξ ω)
          · rw [Set.indicator_of_notMem hω, add_zero]
            simp only [B, Set.mem_setOf_eq, not_not] at hω
            exact (planarNuLoc_eq_of_good hω ξ).le
      _ = _ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw 2 p) :=
          lintegral_add_left hf _
      _ ≤ _ := by
          rw [← hKe]
          exact add_le_add le_rfl ((lintegral_indicator_const_le _ _).trans
            (mul_le_mul' le_rfl hbad))
  · calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p)
        ≤ ∫⁻ ω, (planarNuLoc V ξ ω + B.indicator (fun _ => K) ω) ∂(latticeBondLaw 2 p) :=
          lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            refine le_add_left ?_
            split_ifs
            · exact ENNReal.ofReal_le_ofReal (planarNu_le ξ)
            · exact zero_le
          · rw [Set.indicator_of_notMem hω, add_zero]
            simp only [B, Set.mem_setOf_eq, not_not] at hω
            exact (planarNuLoc_eq_of_good hω ξ).ge
      _ = _ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw 2 p) :=
          lintegral_add_left hl _
      _ ≤ _ := by
          rw [← hKe]
          exact add_le_add le_rfl ((lintegral_indicator_const_le _ _).trans
            (mul_le_mul' le_rfl hbad))

end Rigidity.Percolation
