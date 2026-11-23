import Rigidity.Proofs.Cluster.GeneralMuLocality
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuMoment
import Rigidity.Proofs.Percolation.PlanarNuStationarity
import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Proofs.Partition.Measurability

/-!
# Localization of the partition and the local version of `μ` in every dimension

For `d ≥ 2` and `p > p_c(d)`:

* **Proposition 4.9 of Armstrong and Dario.** The partition into good cubes differs at some vertex
  of a triadic cube `A` from the partition capped at a scale `n` (every cube of scale at least `n`
  declared good, which makes it stationary under `3ⁿ ℤ^d`) with probability at most
  `C (2 · 3^{m - n} + 29)^d exp(-c 3ⁿ)`, `m` the scale of `A`
  (`exists_measure_ne_cappedCube_goodCubes_le`); for `n = m` this is `C exp(-c 3ⁿ)`.
* **The local version of `μ`** (Armstrong and Dario, (4.39) and Proposition 4.10). The local data
  of a triadic cube `V` of scale `n` are, at each vertex of `V`, the cube of the partition capped at
  scale `n` and its anchor, together with the open edges inside `V`; they depend only on the bonds
  inside the cube `V.localRegion` of side `14 · 3ⁿ + 1` around `V`. On the event that the partition
  exists and agrees with the capped partition on `V`, they determine `1{P, V res} (-μ(V, q))`. The
  local version `μ_loc(V, q)` is its value at any configuration of this event with the same local
  data. It is measurable for the σ-algebra of the bonds inside `V.localRegion`, so that local
  versions on cubes with disjoint local regions are independent, and since
  `-μ(V, q) ≤ d C₃² |q|₁² |V|²` on resolved cubes, its expectation differs from that of
  `1{P, V res} (-μ(V, q))` by at most `C |q|₁² exp(-c 3ⁿ)` (`exists_cubeMuLoc_localization`).

The quantity `ν(V, p)` uses no partition: it is measurable for the σ-algebra of the bonds inside
`V` (`measurable_cubeNu_localBondSigma`), so that `ν` itself is its local version.

As in dimension two (`PlanarNuLocal`, `PlanarMuLocal`), the local versions are built from the
partition capped at the scale of `V` rather than from the local partitions `𝒫_loc^{(n)}` of
Proposition 2.1 (iv), and the error is `exp(-c 3ⁿ)` with `n` the scale of `V`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ}

section CappedPartition

/-- The event of a cube of the partition at a vertex of `V` different from the cube of the
partition capped at the scale of `V`. -/
def CubeCappedDiscrepancy (ω : Configuration d) (V : TriadicCube d) : Prop :=
  ∃ x ∈ V.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
    Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
      Q ≠ TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x

/-- **Localization of the partition** (Armstrong and Dario, Proposition 4.9, in every dimension
`d ≥ 2`). The partition into good cubes differs at some vertex of a triadic cube `A` of scale `m`
from the partition capped at the scale `n` with probability at most
`C (2 · 3^{m - n} + 29)^d exp(-c 3ⁿ)`. -/
theorem exists_measure_ne_cappedCube_goodCubes_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (A : TriadicCube d) (n : ℕ),
      latticeBondLaw d p {ω | ∃ x ∈ A.vertices, ∃ Q : TriadicCube d, x ∈ Q.vertices ∧
          Q.IsMaximalStopping (TriadicCube.goodCubes ω) ∧
            Q ≠ TriadicCube.cappedCube (TriadicCube.goodCubes ω) n x} ≤
        (((2 * 3 ^ (A.scale - n) + 29) ^ d : ℕ) : ℝ≥0∞) * C *
          ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ n)) := by
  obtain ⟨C, c, hC, hc, hgood⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  have hgood' : ∀ T : TriadicCube d, latticeBondLaw d p {ω | T ∉ TriadicCube.goodCubes ω} ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ T.scale)) := fun T => by
    rw [← ENNReal.ofReal_mul hC]
    exact hgood T
  have hr : ENNReal.ofReal (Real.exp (-c * (3 - 1))) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.exp_lt_one_iff]
    nlinarith
  refine ⟨ENNReal.ofReal C * (1 - ENNReal.ofReal (Real.exp (-c * (3 - 1))))⁻¹,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'),
    c, hc, fun A n => ?_⟩
  have h := TriadicCube.measure_ne_cappedCube_le_stretched (latticeBondLaw d p)
    (fun ω => TriadicCube.goodCubes ω) A n (ENNReal.ofReal C) 3 c (by norm_num) hc hgood'
  rw [ENNReal.tsum_geometric] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **Localization of the partition at the scale of the cube** (Armstrong and Dario,
Proposition 4.9, with `n` the scale of `V`). -/
theorem exists_measure_cubeCappedDiscrepancy_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube d,
      latticeBondLaw d p {ω | CubeCappedDiscrepancy ω V} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_measure_ne_cappedCube_goodCubes_le hd hpc
  refine ⟨(((2 * 3 ^ 0 + 29) ^ d : ℕ) : ℝ≥0∞) * C,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hC, c, hc, fun V => ?_⟩
  have h' := h V V.scale
  rw [Nat.sub_self] at h'
  exact h'

/-- The cube of the capped partition at a fixed vertex is a measurable function. -/
theorem measurableSet_cappedCube_goodCubes_eq (n : ℕ) (x : Vertex d) (Q : TriadicCube d) :
    MeasurableSet {ω : Configuration d |
      TriadicCube.cappedCube (TriadicCube.goodCubes ω) n x = Q} := by
  have heq : {ω : Configuration d | TriadicCube.cappedCube (TriadicCube.goodCubes ω) n x = Q} =
      {ω | x ∈ Q.vertices ∧ Q.IsMaximalStopping
        (TriadicCube.capped (TriadicCube.goodCubes ω) n)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact TriadicCube.cappedCube_spec _ _ _
    · rintro ⟨hx, hQ⟩
      exact TriadicCube.cappedCube_eq hx hQ
  rw [heq]
  refine (MeasurableSet.const _).inter (TriadicCube.measurableSet_isMaximalStopping
    (fun ω => TriadicCube.capped (TriadicCube.goodCubes ω) n) (fun T => ?_) Q)
  change MeasurableSet {ω : Configuration d | T ∈ TriadicCube.goodCubes ω ∨ n ≤ T.scale}
  exact measurableSet_setOf.2 ((measurableSet_setOf.1
    (TriadicCube.measurableSet_mem_goodCubes T)).or measurable_const)

theorem measurableSet_cubeCappedDiscrepancy (V : TriadicCube d) :
    MeasurableSet {ω : Configuration d | CubeCappedDiscrepancy ω V} := by
  have hne : ∀ (x : Vertex d) (Q : TriadicCube d), Measurable fun ω : Configuration d =>
      Q ≠ TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x := by
    intro x Q
    refine measurableSet_setOf.1 ?_
    convert (measurableSet_cappedCube_goodCubes_eq V.scale x Q).compl using 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  unfold CubeCappedDiscrepancy
  exact measurableSet_setOf.2 (Measurable.exists fun x => measurable_const.and
    (Measurable.exists fun Q => measurable_const.and
      ((measurableSet_setOf.1 Q.measurableSet_isMaximalStopping_goodCubes).and (hne x Q))))

/-- The partition exists and agrees with the partition capped at the scale of `V` on `V`. -/
def CubeLocalGood (ω : Configuration d) (V : TriadicCube d) : Prop :=
  PartitionEvent ω ∧ ¬ CubeCappedDiscrepancy ω V

theorem measurableSet_cubeLocalGood (V : TriadicCube d) :
    MeasurableSet {ω : Configuration d | CubeLocalGood ω V} :=
  measurableSet_partitionEvent.inter (measurableSet_cubeCappedDiscrepancy V).compl

/-- The good event of the localization fails with probability at most `C exp(-c 3ⁿ)`. -/
theorem exists_measure_not_cubeLocalGood_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ V : TriadicCube d,
      latticeBondLaw d p {ω | ¬ CubeLocalGood ω V} ≤
        C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  obtain ⟨C, hC, c, hc, hD⟩ := exists_measure_cubeCappedDiscrepancy_le hd hpc
  refine ⟨C, hC, c, hc, fun V => ?_⟩
  have hPnull : latticeBondLaw d p {ω | ¬ PartitionEvent ω} = 0 :=
    ae_iff.1 (ae_partitionEvent hd hpc)
  have hsub : {ω | ¬ CubeLocalGood ω V} ⊆
      {ω | ¬ PartitionEvent ω} ∪ {ω | CubeCappedDiscrepancy ω V} := by
    intro ω hω
    simp only [CubeLocalGood, not_and_or, not_not, Set.mem_setOf_eq] at hω
    exact hω
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := by rw [hPnull, zero_add]; exact hD V

theorem partitionCube_eq_cappedCube {ω : Configuration d} {V : TriadicCube d}
    (h : CubeLocalGood ω V) {x : Vertex d} (hx : x ∈ V.vertices) :
    partitionCube ω x = TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x := by
  by_contra hne
  exact h.2 ⟨x, hx, _, (partitionCube_spec h.1 x).1, (partitionCube_spec h.1 x).2, hne⟩

end CappedPartition

section LocalData

/-- The type of local data at a triadic cube. -/
abbrev CubeLocalDatum (V : TriadicCube d) : Type :=
  (↥V.toIntegerCube.vertices → TriadicCube d × Vertex d) × Finset (Vertex d × Vertex d)

/-- The local data at a triadic cube `V`: at each vertex the cube of the partition capped at the
scale of `V` and its anchor, and the open edges inside `V`. -/
noncomputable def cubeLocalData (ω : Configuration d) (V : TriadicCube d) : CubeLocalDatum V :=
  (fun x => (TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x.1,
      (TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x.1).anchor ω),
    (V.toIntegerCube.vertices ×ˢ V.toIntegerCube.vertices).filter
      fun e => (openGraph ω).Adj e.1 e.2)

variable {ω ω' : Configuration d}

/-- On the good event, the local data determine resolution, the open edges inside `V` and the
anchors of the partition cubes of the vertices of `V`. -/
theorem cubeLocalData_eq_imp {V : TriadicCube d} (hω : CubeLocalGood ω V)
    (hω' : CubeLocalGood ω' V) (h : cubeLocalData ω V = cubeLocalData ω' V) :
    (PartitionResolved ω V ↔ PartitionResolved ω' V) ∧
      (∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω).Adj x y ↔ (openGraph ω').Adj x y)) ∧
      (∀ x ∈ V.vertices, partitionAnchor ω' x = partitionAnchor ω x) := by
  have hcd := congrArg Prod.fst h
  have hQx : ∀ x ∈ V.vertices,
      TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x =
        TriadicCube.cappedCube (TriadicCube.goodCubes ω') V.scale x ∧
      (TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x).anchor ω =
        (TriadicCube.cappedCube (TriadicCube.goodCubes ω') V.scale x).anchor ω' := by
    intro x hx
    have := congrFun hcd ⟨x, (V.mem_toIntegerCube_vertices x).2 hx⟩
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hQ : ∀ x ∈ V.vertices, partitionCube ω x = partitionCube ω' x := fun x hx => by
    rw [partitionCube_eq_cappedCube hω hx, partitionCube_eq_cappedCube hω' hx]
    exact (hQx x hx).1
  refine ⟨?_, ?_, ?_⟩
  · unfold PartitionResolved
    exact forall₂_congr fun z hz => by rw [hQ z hz]
  · intro x hx y hy
    have hxS : x ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices x).2 hx
    have hyS : y ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices y).2 hy
    have h2 := Finset.ext_iff.1 (congrArg Prod.snd h) (x, y)
    simp only [cubeLocalData, Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
    exact h2
  · intro x hx
    unfold partitionAnchor
    rw [partitionCube_eq_cappedCube hω hx, partitionCube_eq_cappedCube hω' hx]
    exact (hQx x hx).2.symm

/-- **Locality of the local data.** -/
theorem cubeLocalData_eq_of_localBonds {V : TriadicCube d}
    (h : ∀ e ∈ localBonds V.localRegion, ω e = ω' e) :
    cubeLocalData ω' V = cubeLocalData ω V := by
  have hagree := openGraph_adj_iff_of_localBonds h
  unfold cubeLocalData
  refine Prod.ext (funext fun x => ?_) ?_
  · have hx := (V.mem_toIntegerCube_vertices x.1).1 x.2
    exact Prod.ext (cappedCube_goodCubes_eq_of_localBonds hx h)
      (anchor_cappedCube_goodCubes_eq_of_localBonds hx h)
  · refine Finset.filter_congr fun e he => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 he
    exact hagree e.1 (V.vertices_subset_localRegion ((V.mem_toIntegerCube_vertices _).1 h1))
      e.2 (V.vertices_subset_localRegion ((V.mem_toIntegerCube_vertices _).1 h2))

/-- The local data are measurable, with countably many values. -/
theorem measurableSet_cubeLocalData_eq (V : TriadicCube d) (t : CubeLocalDatum V) :
    MeasurableSet {ω : Configuration d | cubeLocalData ω V = t} := by
  have key : ∀ (ω : Configuration d) (x : ↥V.toIntegerCube.vertices),
      (TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x.1,
        (TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x.1).anchor ω) = t.1 x ↔
      TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x.1 = (t.1 x).1 ∧
        (t.1 x).1.anchor ω = (t.1 x).2 := by
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
  have heq : {ω : Configuration d | cubeLocalData ω V = t} =
      {ω | ∀ x : ↥V.toIntegerCube.vertices,
        TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x.1 = (t.1 x).1 ∧
          (t.1 x).1.anchor ω = (t.1 x).2} ∩
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
    (measurableSet_setOf.1 (measurableSet_cappedCube_goodCubes_eq V.scale x.1 (t.1 x).1)).and
      (measurableSet_setOf.1 ((t.1 x).1.measurableSet_anchor_eq (t.1 x).2)))) ?_
  exact measurableSet_filter_eq _ _ fun e =>
    measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)

end LocalData

section MuLocal

variable {ω ω' : Configuration d}

/-- A deterministic bound for `-μ` on resolved cubes: `-μ(U, q) ≤ d C₃² |q|₁² |U|²`. -/
theorem neg_cubeMu_le_latticeVolume_sq (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    -cubeMu ω U q ≤ d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 * U.latticeVolume ^ 2 := by
  have h := neg_cubeMu_le hd hP hU q
  have hvol := U.latticeVolume_pos
  set s : ℝ := (3 : ℝ) ^ U.scale with hs
  have hs1 : 1 ≤ s := one_le_pow₀ (by norm_num)
  have hterm : ∀ z ∈ crossingClusterVertices ω U,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) ≤ s ^ (2 * (d - 1)) := by
    intro z hz
    have hzU : z ∈ U.vertices := U.crossingCluster_subset ω (mem_crossingClusterVertices.1 hz)
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (hU z hzU)) _
  have hsum : ∑ z ∈ crossingClusterVertices ω U,
      ((3 : ℝ) ^ (partitionCube ω z).scale) ^ (2 * (d - 1)) ≤
        U.latticeVolume * s ^ (2 * (d - 1)) := by
    calc _ ≤ ∑ _z ∈ crossingClusterVertices ω U, s ^ (2 * (d - 1)) := Finset.sum_le_sum hterm
      _ = ((crossingClusterVertices ω U).card : ℝ) * s ^ (2 * (d - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ U.latticeVolume * s ^ (2 * (d - 1)) :=
          mul_le_mul_of_nonneg_right (card_crossingClusterVertices_le U) (by positivity)
  have hpow : s ^ (2 * (d - 1)) ≤ U.latticeVolume ^ 2 := by
    have hv : U.latticeVolume ^ 2 = s ^ (2 * d) := by
      unfold TriadicCube.latticeVolume
      rw [← pow_mul, mul_comm d 2]
    rw [hv]
    exact pow_le_pow_right₀ hs1 (by omega)
  set K := (d : ℝ) * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  calc -cubeMu ω U q ≤ _ := h
    _ ≤ K * (U.latticeVolume * s ^ (2 * (d - 1))) / U.latticeVolume := by gcongr
    _ = K * s ^ (2 * (d - 1)) := by field_simp
    _ ≤ K * U.latticeVolume ^ 2 := mul_le_mul_of_nonneg_left hpow hK0

/-- The value of `1{P, V res} (-μ(V, q))` at a configuration of the good event with given local
data. -/
noncomputable def cubeMuLocOf (V : TriadicCube d) (q : Fin d → ℝ) (t : CubeLocalDatum V) :
    ℝ≥0∞ :=
  if h : ∃ ω, CubeLocalGood ω V ∧ cubeLocalData ω V = t then
    (if PartitionEvent h.choose ∧ PartitionResolved h.choose V then
      ENNReal.ofReal (-cubeMu h.choose V q) else 0)
  else 0

/-- **The local version of `-μ`** (Armstrong and Dario, (4.39)). -/
noncomputable def cubeMuLoc (V : TriadicCube d) (q : Fin d → ℝ) (ω : Configuration d) :
    ℝ≥0∞ :=
  cubeMuLocOf V q (cubeLocalData ω V)

/-- On the good event, the local data determine `1{P, V res} (-μ(V, q))`. -/
theorem cubeMu_indicator_eq_of_cubeLocalData_eq {V : TriadicCube d}
    (hω : CubeLocalGood ω V) (hω' : CubeLocalGood ω' V)
    (h : cubeLocalData ω V = cubeLocalData ω' V) (q : Fin d → ℝ) :
    (if PartitionEvent ω ∧ PartitionResolved ω V then ENNReal.ofReal (-cubeMu ω V q)
      else 0) =
      if PartitionEvent ω' ∧ PartitionResolved ω' V then
        ENNReal.ofReal (-cubeMu ω' V q) else 0 := by
  obtain ⟨hres, hadj, hanc⟩ := cubeLocalData_eq_imp hω hω' h
  by_cases hr : PartitionResolved ω V
  · rw [if_pos ⟨hω.1, hr⟩, if_pos ⟨hω'.1, hres.1 hr⟩,
      cubeMu_eq_of_adj_iff_of_anchor_eq hadj hanc q]
  · rw [if_neg fun h' => hr h'.2, if_neg fun h' => hr (hres.2 h'.2)]

/-- **Agreement with `μ`.** On the good event, the local version equals
`1{P, V res} (-μ(V, q))`. -/
theorem cubeMuLoc_eq_of_good {V : TriadicCube d} (hω : CubeLocalGood ω V) (q : Fin d → ℝ) :
    cubeMuLoc V q ω = if PartitionEvent ω ∧ PartitionResolved ω V then
      ENNReal.ofReal (-cubeMu ω V q) else 0 := by
  have hex : ∃ ω', CubeLocalGood ω' V ∧ cubeLocalData ω' V = cubeLocalData ω V :=
    ⟨ω, hω, rfl⟩
  unfold cubeMuLoc cubeMuLocOf
  rw [dif_pos hex]
  exact cubeMu_indicator_eq_of_cubeLocalData_eq hex.choose_spec.1 hω hex.choose_spec.2 q

theorem cubeMu_indicator_le (hd : 0 < d) (V : TriadicCube d) (q : Fin d → ℝ)
    (ω : Configuration d) :
    (if PartitionEvent ω ∧ PartitionResolved ω V then ENNReal.ofReal (-cubeMu ω V q) else 0) ≤
      ENNReal.ofReal (d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 * V.latticeVolume ^ 2) := by
  split_ifs with h
  · exact ENNReal.ofReal_le_ofReal (neg_cubeMu_le_latticeVolume_sq hd h.1 h.2 q)
  · exact zero_le

/-- **The bound (4.41) for the local version**, in the form `μ_loc(V, q) ≤ d C₃² |q|₁² |V|²`. -/
theorem cubeMuLoc_le (hd : 0 < d) (V : TriadicCube d) (q : Fin d → ℝ) (ω : Configuration d) :
    cubeMuLoc V q ω ≤
      ENNReal.ofReal (d * coarseGradConstant d ^ 2 * (∑ i, |q i|) ^ 2 * V.latticeVolume ^ 2) := by
  unfold cubeMuLoc cubeMuLocOf
  split
  · exact cubeMu_indicator_le hd V q _
  · exact zero_le

/-- The local version of `-μ` is measurable. -/
theorem measurable_cubeMuLoc (V : TriadicCube d) (q : Fin d → ℝ) :
    Measurable (cubeMuLoc V q) :=
  measurable_of_constant_on_fibres (fun ω => cubeLocalData ω V)
    (fun t => measurableSet_cubeLocalData_eq V t) fun _ _ h =>
      congrArg (cubeMuLocOf V q) h

/-- **Locality of `μ_loc`** (Armstrong and Dario, (4.39)). The local version of `-μ` is measurable
for the σ-algebra of the bonds inside the local region of `V`. -/
theorem measurable_cubeMuLoc_localBondSigma (V : TriadicCube d) (q : Fin d → ℝ) :
    Measurable[localBondSigma V.localRegion] (cubeMuLoc V q) :=
  measurable_localBondSigma_of_eq _ (measurable_cubeMuLoc V q) fun _ _ h =>
    congrArg (cubeMuLocOf V q) (cubeLocalData_eq_of_localBonds h).symm

/-- **Independence of local versions of `μ`.** -/
theorem indepFun_cubeMuLoc (p : unitInterval) {V W : TriadicCube d}
    (hVW : Disjoint V.localRegion W.localRegion) (q r : Fin d → ℝ) :
    IndepFun (cubeMuLoc V q) (cubeMuLoc W r) (latticeBondLaw d p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_cubeMuLoc_localBondSigma V q).comap_le)
    (measurable_cubeMuLoc_localBondSigma W r).comap_le)

/-- **Localization of `μ`** (Armstrong and Dario, Proposition 4.10, for `μ`, in every dimension
`d ≥ 2`). The expectations of the local version and of `1{P, V res} (-μ(V, q))` differ by at most
`C |q|₁² exp(-c 3ⁿ)`, `n` the scale of `V`. -/
theorem exists_cubeMuLoc_localization [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (V : TriadicCube d) (q : Fin d → ℝ),
      ∫⁻ ω, cubeMuLoc V q ω ∂(latticeBondLaw d p) ≤
        ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) ∧
      ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) ≤
        ∫⁻ ω, cubeMuLoc V q ω ∂(latticeBondLaw d p) +
        C * ENNReal.ofReal ((∑ i, |q i|) ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C, hC, c, hc, hbad⟩ := exists_measure_not_cubeLocalGood_le hd hpc
  set A : ℝ := d * coarseGradConstant d ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set M : ℝ := (max 1 (2 * ((2 * d : ℕ) + 1) / c)) ^ (2 * d) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨ENNReal.ofReal (A * M) * C, by finiteness, c / 2, by positivity, fun V q => ?_⟩
  set B := {ω : Configuration d | ¬ CubeLocalGood ω V} with hBdef
  have hB : MeasurableSet B := (measurableSet_cubeLocalGood V).compl
  set s := (∑ i, |q i|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  set K : ℝ≥0∞ := ENNReal.ofReal (A * s * V.latticeVolume ^ 2) with hK
  have hpoly : V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale) ≤
      M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale) := by
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
      _ ≤ M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale) := by
          rw [show -(c / 2) * (3 : ℝ) ^ V.scale = -(c / 2 * 3 ^ V.scale) by ring]
          exact h
  have hKe : K * (C * ENNReal.ofReal (Real.exp (-c * (3 : ℝ) ^ V.scale))) ≤
      ENNReal.ofReal (A * M) * C *
        ENNReal.ofReal (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
    rw [hK, mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
    have hAB : A * s * V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale) ≤
        A * M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by
      calc A * s * V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)
          = A * s * (V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale)) := by ring
        _ ≤ A * s * (M * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) :=
            mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = A * M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale)) := by ring
    calc C * ENNReal.ofReal (A * s * V.latticeVolume ^ 2 * Real.exp (-c * (3 : ℝ) ^ V.scale))
        ≤ C * ENNReal.ofReal (A * M * (s * Real.exp (-(c / 2) * (3 : ℝ) ^ V.scale))) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hAB)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
  have hind : Measurable (B.indicator fun _ => K) := measurable_const.indicator hB
  refine ⟨?_, ?_⟩
  · calc ∫⁻ ω, cubeMuLoc V q ω ∂(latticeBondLaw d p)
        ≤ ∫⁻ ω, ((if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) + B.indicator (fun _ => K) ω)
            ∂(latticeBondLaw d p) := lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            exact le_add_left (cubeMuLoc_le hd0 V q ω)
          · rw [Set.indicator_of_notMem hω, add_zero]
            simp only [B, Set.mem_setOf_eq, not_not] at hω
            exact (cubeMuLoc_eq_of_good hω q).le
      _ = _ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw d p) :=
          lintegral_add_right _ hind
      _ ≤ _ := add_le_add le_rfl (((lintegral_indicator_const_le _ _).trans
            (mul_le_mul' le_rfl (hbad V))).trans hKe)
  · calc ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
          ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p)
        ≤ ∫⁻ ω, (cubeMuLoc V q ω + B.indicator (fun _ => K) ω) ∂(latticeBondLaw d p) :=
          lintegral_mono fun ω => by
          by_cases hω : ω ∈ B
          · rw [Set.indicator_of_mem hω]
            exact le_add_left (cubeMu_indicator_le hd0 V q ω)
          · rw [Set.indicator_of_notMem hω, add_zero]
            simp only [B, Set.mem_setOf_eq, not_not] at hω
            exact (cubeMuLoc_eq_of_good hω q).ge
      _ = _ + ∫⁻ ω, B.indicator (fun _ => K) ω ∂(latticeBondLaw d p) :=
          lintegral_add_right _ hind
      _ ≤ _ := add_le_add le_rfl (((lintegral_indicator_const_le _ _).trans
            (mul_le_mul' le_rfl (hbad V))).trans hKe)

end MuLocal

section NuLocal

/-- **Locality of `ν`** (Armstrong and Dario, (4.39), for `ν`). `ν(V, p)` is measurable for the
σ-algebra of the bonds inside `V`. -/
theorem measurable_cubeNu_localBondSigma (V : TriadicCube d) (p : Fin d → ℝ) :
    Measurable[localBondSigma V.vertices] fun ω => cubeNu ω V p :=
  measurable_localBondSigma_of_eq _ (measurable_cubeNu V p) fun _ _ h =>
    cubeNu_eq_of_adj_iff p fun x hx y hy => (openGraph_adj_iff_of_localBonds h x hx y hy).symm

/-- **Independence of `ν`** on cubes with disjoint vertex sets. -/
theorem indepFun_cubeNu (prob : unitInterval) {V W : TriadicCube d}
    (hVW : Disjoint V.vertices W.vertices) (p p' : Fin d → ℝ) :
    IndepFun (fun ω => cubeNu ω V p) (fun ω => cubeNu ω W p') (latticeBondLaw d prob) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma prob hVW)
      (measurable_cubeNu_localBondSigma V p).comap_le)
    (measurable_cubeNu_localBondSigma W p').comap_le)

end NuLocal

end Rigidity.Percolation
