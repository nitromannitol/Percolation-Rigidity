import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLocal
import Rigidity.Proofs.Percolation.PlanarLocality
import Rigidity.Proofs.Partition.GoodCubesLocal

/-!
# Transport, translation covariance and locality of `μ` on triadic cubes of `ℤ^d`

The quantity `μ(U, q)` of Armstrong and Dario (Definition 4.1) depends only on the crossing
cluster `C_*(U)`, on the open edges between its vertices, on which of its vertices lie in the
lattice interior of `U`, and on the coarse pairing, which reads the anchors of the partition
cubes of the vertices of `U`. A bijection of clusters respecting the first three data and
carrying the coarse pairing to the coarse pairing preserves `μ` (`cubeMu_eq_of_equiv`). Hence:

* `μ(U, q)` is determined by the open edges inside `U` and the anchors of the partition cubes of
  the vertices of `U` (`cubeMu_eq_of_adj_iff_of_anchor_eq`);
* if the partition cubes of the vertices of a resolved cube `U` move with a translation `c` by a
  multiple of the side of `U`, then `μ(U + c, q)` at the translated configuration equals `μ(U, q)`
  (`cubeMu_shift_translation_of_partition`).

For the localization of `μ` (Armstrong and Dario, Section 4.3) we record the locality of the
ingredients: goodness of a triadic cube depends only on the open edges inside its threefold
enlargement, the anchor of a cube only on the open edges inside it, and the cube at `x` of the
partition capped at the scale `n` of a cube `V ∋ x` only on the open edges inside the cube
`V.localRegion` of side `14 · 3ⁿ + 1` around `V`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

section Transport

variable {ω ω' : Configuration d} {U U' : TriadicCube d}

/-- The Dirichlet form is invariant under a bijection of clusters respecting the open edges. -/
theorem cubeForm_comp_symm
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (u v : CubeFun ω U) :
    cubeForm ω' U' (u ∘ e.symm) (v ∘ e.symm) = cubeForm ω U u v := by
  rw [cubeForm_apply, cubeForm_apply]
  congr 1
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [cubeFormTerm, Function.comp_apply, Equiv.symm_apply_apply, hadj]

/-- Harmonicity is invariant under a bijection of clusters respecting the open edges and the
lattice interiors. -/
theorem comp_symm_mem_cubeHarmonic_iff
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1) (u : CubeFun ω U) :
    u ∘ e.symm ∈ cubeHarmonic ω' U' ↔ u ∈ cubeHarmonic ω U := by
  have hlap : ∀ x, cubeLaplacianAt ω' U' (e x) (u ∘ e.symm) = cubeLaplacianAt ω U x u := by
    intro x
    rw [cubeLaplacianAt_apply, cubeLaplacianAt_apply, ← e.sum_comp]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, hadj]
  rw [mem_cubeHarmonic, mem_cubeHarmonic]
  constructor
  · intro h x hx
    rw [← hlap]
    exact h (e x) ((hint x).2 hx)
  · intro h y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [hlap]
    exact h x ((hint x).1 hy)

/-- **Relabelling invariance of `μ`.** A bijection of clusters which respects open edges and
lattice interiors and carries the coarse pairing to the coarse pairing preserves `μ`. -/
theorem cubeMu_eq_of_equiv
    (e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsLatticeInterior (e x).1 ↔ U.IsLatticeInterior x.1)
    (hvol : U'.latticeVolume = U.latticeVolume) (q : Fin d → ℝ)
    (hcoarse : ∀ u : CubeFun ω U,
      cubeCoarsePairing ω' U' q (u ∘ e.symm) = cubeCoarsePairing ω U q u) :
    cubeMu ω' U' q = cubeMu ω U q := by
  let E : cubeHarmonic ω U ≃ cubeHarmonic ω' U' :=
    { toFun := fun w => ⟨w.1 ∘ e.symm, (comp_symm_mem_cubeHarmonic_iff e hadj hint w.1).2 w.2⟩
      invFun := fun w => ⟨w.1 ∘ e, by
        apply (comp_symm_mem_cubeHarmonic_iff e hadj hint (w.1 ∘ e)).1
        have : (w.1 ∘ e) ∘ e.symm = w.1 := by
          funext y
          simp only [Function.comp_apply, Equiv.apply_symm_apply]
        rw [this]
        exact w.2⟩
      left_inv := fun w => by
        ext y
        simp only [Function.comp_apply, Equiv.symm_apply_apply]
      right_inv := fun w => by
        ext y
        simp only [Function.comp_apply, Equiv.apply_symm_apply] }
  unfold cubeMu
  symm
  refine Equiv.iInf_congr E fun w => ?_
  change (cubeForm ω' U' (w.1 ∘ e.symm) (w.1 ∘ e.symm) / 2 -
      cubeCoarsePairing ω' U' q (w.1 ∘ e.symm)) / U'.latticeVolume = _
  rw [cubeForm_comp_symm e hadj, hcoarse, hvol]

/-- **Locality of `μ`.** `μ(U, q)` is determined by the open edges between vertices of `U` and
the anchors of the partition cubes of the vertices of `U`. -/
theorem cubeMu_eq_of_adj_iff_of_anchor_eq
    (h : ∀ x ∈ U.vertices, ∀ y ∈ U.vertices, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y)
    (hanc : ∀ x ∈ U.vertices, partitionAnchor ω' x = partitionAnchor ω x) (q : Fin d → ℝ) :
    cubeMu ω' U q = cubeMu ω U q := by
  have hC : ∀ x, x ∈ crossingClusterVertices ω U ↔ x ∈ crossingClusterVertices ω' U := by
    intro x
    rw [mem_crossingClusterVertices, mem_crossingClusterVertices,
      TriadicCube.crossingCluster_eq_of_adj_iff h]
  let e : ↥(crossingClusterVertices ω U) ≃ ↥(crossingClusterVertices ω' U) :=
    Equiv.subtypeEquivRight hC
  have hext : ∀ (u : CubeFun ω U) (y : Vertex d),
      cubeExtend ω' U (u ∘ e.symm) y = cubeExtend ω U u y := by
    intro u y
    by_cases hy : y ∈ crossingClusterVertices ω U
    · rw [cubeExtend_apply_of_mem _ ((hC y).1 hy), cubeExtend_apply_of_mem _ hy]
      rfl
    · have hy' : y ∉ crossingClusterVertices ω' U := fun h' => hy ((hC y).2 h')
      change (if h : y ∈ crossingClusterVertices ω' U then (u ∘ e.symm) ⟨y, h⟩ else 0) =
        if h : y ∈ crossingClusterVertices ω U then u ⟨y, h⟩ else 0
      rw [dif_neg hy', dif_neg hy]
  refine cubeMu_eq_of_equiv e (fun x y => ?_) (fun x => Iff.rfl) rfl q fun u => ?_
  · exact (h x.1 (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 x.2)) y.1
      (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 y.2))).symm
  · rw [cubeCoarsePairing_apply, cubeCoarsePairing_apply]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [hanc _ ((U.mem_toIntegerCube_vertices _).1 hi),
        hanc _ ((U.mem_toIntegerCube_vertices _).1 hx), hext, hext]
    · rfl

end Transport

section Translation

variable {ω : Configuration d} {V : TriadicCube d} {c : Vertex d}

/-- Sums over the vertices of a shifted cube. -/
theorem TriadicCube.sum_shift_toIntegerCube_vertices {M : Type*} [AddCommMonoid M]
    (hc : ∀ i, V.side ∣ c i) (f : Vertex d → M) :
    ∑ x ∈ (V.shift c).toIntegerCube.vertices, f x =
      ∑ x ∈ V.toIntegerCube.vertices, f (x + c) := by
  refine Finset.sum_nbij' (· - c) (· + c) (fun a ha => ?_) (fun a ha => ?_)
    (fun a _ => sub_add_cancel a c) (fun a _ => add_sub_cancel_right a c)
    (fun a _ => by rw [sub_add_cancel])
  · rw [TriadicCube.mem_toIntegerCube_vertices] at ha ⊢
    exact (TriadicCube.mem_shift_iff hc a).1 ha
  · rw [TriadicCube.mem_toIntegerCube_vertices] at ha ⊢
    exact (TriadicCube.add_mem_shift_iff hc a).2 ha

/-- **Translation covariance of `μ`.** If the anchors of the partition cubes of the vertices of
`V` move with a translation `c` by a multiple of the side of `V`, then `μ(V + c, q)` at the
translated configuration equals `μ(V, q)`. -/
theorem cubeMu_shift_translation (hc : ∀ i, V.side ∣ c i)
    (hanc : ∀ x ∈ V.vertices,
      partitionAnchor (configurationTranslation c ω) (x + c) = partitionAnchor ω x + c)
    (q : Fin d → ℝ) :
    cubeMu (configurationTranslation c ω) (V.shift c) q = cubeMu ω V q := by
  let e := crossingClusterVerticesShiftEquiv ω hc
  have hC : ∀ y, y + c ∈ crossingClusterVertices (configurationTranslation c ω) (V.shift c) ↔
      y ∈ crossingClusterVertices ω V := fun y => by
    rw [mem_crossingClusterVertices, mem_crossingClusterVertices]
    exact TriadicCube.add_mem_crossingCluster_shift_iff hc ω y
  have hext : ∀ (u : CubeFun ω V) (y : Vertex d),
      cubeExtend (configurationTranslation c ω) (V.shift c) (u ∘ e.symm) (y + c) =
        cubeExtend ω V u y := by
    intro u y
    by_cases hy : y ∈ crossingClusterVertices ω V
    · have hy' := (hC y).2 hy
      rw [cubeExtend_apply_of_mem _ hy', cubeExtend_apply_of_mem _ hy]
      change u (e.symm ⟨y + c, hy'⟩) = u ⟨y, hy⟩
      congr 1
      exact Subtype.ext (add_sub_cancel_right y c)
    · have hy' : y + c ∉ crossingClusterVertices (configurationTranslation c ω) (V.shift c) :=
        fun h => hy ((hC y).1 h)
      change (if h : y + c ∈ crossingClusterVertices (configurationTranslation c ω) (V.shift c)
          then (u ∘ e.symm) ⟨y + c, h⟩ else 0) =
        if h : y ∈ crossingClusterVertices ω V then u ⟨y, h⟩ else 0
      rw [dif_neg hy', dif_neg hy]
  refine cubeMu_eq_of_equiv e (fun x y => openGraph_adj_translation_iff c ω x.1 y.1)
    (fun x => TriadicCube.isLatticeInterior_shift_iff hc x.1) rfl q fun u => ?_
  rw [cubeCoarsePairing_apply, cubeCoarsePairing_apply,
    TriadicCube.sum_shift_toIntegerCube_vertices hc]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  have hxV : x ∈ V.vertices := (V.mem_toIntegerCube_vertices x).1 hx
  have hswap : x + c + LatticeProb.unit i = x + LatticeProb.unit i + c := by abel
  have hmem : x + c + LatticeProb.unit i ∈ (V.shift c).toIntegerCube.vertices ↔
      x + LatticeProb.unit i ∈ V.toIntegerCube.vertices := by
    rw [TriadicCube.mem_toIntegerCube_vertices, TriadicCube.mem_toIntegerCube_vertices, hswap]
    exact TriadicCube.add_mem_shift_iff hc _
  by_cases hi : x + LatticeProb.unit i ∈ V.toIntegerCube.vertices
  · rw [if_pos (hmem.2 hi), if_pos hi, hswap,
      hanc _ ((V.mem_toIntegerCube_vertices _).1 hi), hanc x hxV, hext, hext]
  · rw [if_neg fun h => hi (hmem.1 h), if_neg hi]

/-- Anchors of partition cubes move with the partition cubes. -/
theorem partitionAnchor_translation {x : Vertex d}
    (hpart : partitionCube (configurationTranslation c ω) (x + c) = (partitionCube ω x).shift c)
    (hc : ∀ i, (partitionCube ω x).side ∣ c i) :
    partitionAnchor (configurationTranslation c ω) (x + c) = partitionAnchor ω x + c := by
  unfold partitionAnchor
  rw [hpart]
  exact TriadicCube.anchor_shift hc ω

/-- Resolution moves with the partition cubes. -/
theorem partitionResolved_shift_iff (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      partitionCube (configurationTranslation c ω) (x + c) = (partitionCube ω x).shift c) :
    PartitionResolved (configurationTranslation c ω) (V.shift c) ↔ PartitionResolved ω V := by
  unfold PartitionResolved
  constructor
  · intro h x hx
    have := h (x + c) ((TriadicCube.add_mem_shift_iff hc x).2 hx)
    rwa [hpart x hx] at this
  · intro h z hz
    have hz' := (TriadicCube.mem_shift_iff hc z).1 hz
    have := hpart (z - c) hz'
    rw [sub_add_cancel] at this
    rw [this, TriadicCube.scale_shift, TriadicCube.scale_shift]
    exact h _ hz'

/-- **Translation covariance of `μ` on resolved cubes.** If the partition cubes of the vertices of
a resolved cube `V` move with a translation by a multiple of the side of `V`, so does `μ`. -/
theorem cubeMu_shift_translation_of_partition (hres : PartitionResolved ω V)
    (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      partitionCube (configurationTranslation c ω) (x + c) = (partitionCube ω x).shift c)
    (q : Fin d → ℝ) :
    cubeMu (configurationTranslation c ω) (V.shift c) q = cubeMu ω V q :=
  cubeMu_shift_translation hc (fun x hx => partitionAnchor_translation (hpart x hx)
    fun i => (pow_dvd_pow 3 (hres x hx)).trans (hc i)) q

end Translation

section Locality

variable {ω ω' : Configuration d}

/-- **Locality of goodness** (Armstrong and Dario, (2.1)), pointwise form: whether a triadic cube
is good depends only on the open edges inside its threefold enlargement. -/
theorem TriadicCube.mem_goodCubes_iff_of_adj_iff {T : TriadicCube d}
    (h : ∀ x ∈ T.centeredTriple, ∀ y ∈ T.centeredTriple,
      (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    T ∈ TriadicCube.goodCubes ω ↔ T ∈ TriadicCube.goodCubes ω' := by
  by_cases h3 : 3 ≤ T.scale
  · rw [TriadicCube.mem_goodCubes_iff_of_three_le h3, TriadicCube.mem_goodCubes_iff_of_three_le h3]
    exact T.mem_goodOfWellConnected_congr _
      (fun R => R.threeQuarterCube_subset_envelope.trans R.threeQuarterEnvelope_subset) h
  · exact ⟨fun hT => absurd (TriadicCube.three_le_scale_of_mem_goodCubes hT) h3,
      fun hT => absurd (TriadicCube.three_le_scale_of_mem_goodCubes hT) h3⟩

/-- **Locality of anchors.** The anchor of a cube depends only on the open edges inside it. -/
theorem TriadicCube.anchor_eq_of_adj_iff {Q : TriadicCube d}
    (h : ∀ x ∈ Q.vertices, ∀ y ∈ Q.vertices, (openGraph ω).Adj x y ↔ (openGraph ω').Adj x y) :
    Q.anchor ω = Q.anchor ω' := by
  have hC := TriadicCube.crossingCluster_eq_of_adj_iff h
  by_cases hne : (Q.crossingCluster ω).Nonempty
  · have hne' : (Q.crossingCluster ω').Nonempty := hC ▸ hne
    rw [eq_comm, TriadicCube.anchor_eq_iff hne']
    have h1 := TriadicCube.isAnchor_anchor hne
    unfold TriadicCube.IsAnchor at h1 ⊢
    rw [← hC]
    exact h1
  · have h0 : Q.crossingCluster ω = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    rw [TriadicCube.anchor_of_crossingCluster_eq_empty h0,
      TriadicCube.anchor_of_crossingCluster_eq_empty (hC ▸ h0)]

/-- Configurations agreeing on the bonds inside a region have the same open edges there. -/
theorem openGraph_adj_iff_of_localBonds {S : Set (Vertex d)}
    (h : ∀ e ∈ localBonds S, ω e = ω' e) :
    ∀ x ∈ S, ∀ y ∈ S, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) := by
  intro x hx y hy
  simp only [openGraph_adj_iff]
  constructor <;> rintro ⟨hxy, ho⟩ <;> refine ⟨hxy, ?_⟩
  · have he : bondOfAdjacent hxy ∈ localBonds S := fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    rw [h _ he]
    exact ho
  · have he : bondOfAdjacent hxy ∈ localBonds S := fun z hz => by
      rcases Sym2.mem_iff.mp hz with rfl | rfl <;> assumption
    rw [← h _ he]
    exact ho

/-- The cube of side `14 · 3ⁿ + 1` around a triadic cube of scale `n`. -/
def TriadicCube.localRegion (V : TriadicCube d) : Set (Vertex d) :=
  {y | ∀ i, |y i - V.center i| ≤ 7 * V.side}

/-- A cube of scale at most `n` meeting a cube `V` of scale `n` lies in the local region of
`V`. -/
theorem TriadicCube.vertices_subset_localRegion_of_mem {V Q : TriadicCube d} {x : Vertex d}
    (hxV : x ∈ V.vertices) (hxQ : x ∈ Q.vertices) (hQ : Q.scale ≤ V.scale) :
    Q.vertices ⊆ V.localRegion := by
  intro y hy i
  have h1 := (Q.mem_vertices_iff y).1 hy i
  have h2 := (Q.mem_vertices_iff x).1 hxQ i
  have h3 := (V.mem_vertices_iff x).1 hxV i
  have hQs := Q.side_eq_two_mul_radius_add_one
  have hVs := V.side_eq_two_mul_radius_add_one
  have hle : Q.side ≤ V.side := pow_le_pow_right₀ (by norm_num) hQ
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> omega

theorem TriadicCube.vertices_subset_localRegion (V : TriadicCube d) :
    V.vertices ⊆ V.localRegion :=
  V.vertices_subset_localRegion_of_mem V.center_mem V.center_mem le_rfl

/-- The threefold enlargements of the cubes of scale below `n` within twelve of their side
lengths of a vertex of `V` lie in the local region of `V`. -/
theorem TriadicCube.centeredTriple_subset_localRegion_of_near {V T : TriadicCube d}
    {x : Vertex d} (hxV : x ∈ V.vertices) (hT : T.scale < V.scale)
    (hnear : ∀ y ∈ T.vertices, ∀ i, |x i - y i| < 12 * T.side) :
    T.centeredTriple ⊆ V.localRegion := by
  intro z hz i
  have h1 := hz i
  have h2 := hnear T.center T.center_mem i
  have h3 := (V.mem_vertices_iff x).1 hxV i
  have hVs := V.side_eq_two_mul_radius_add_one
  have hpow : 3 * T.side ≤ V.side := by
    calc 3 * T.side = (3 : ℤ) ^ (T.scale + 1) := by
          rw [TriadicCube.side, pow_succ]; ring
      _ ≤ V.side := pow_le_pow_right₀ (by norm_num) hT
  rw [abs_lt] at h1 h2
  rw [abs_le] at h3 ⊢
  constructor <;> omega

/-- **Locality of the capped partition.** For `x ∈ V`, the cube at `x` of the partition into good
cubes capped at the scale of `V` depends only on the bonds inside the local region of `V`. -/
theorem cappedCube_goodCubes_eq_of_localBonds {V : TriadicCube d} {x : Vertex d}
    (hx : x ∈ V.vertices) (h : ∀ e ∈ localBonds V.localRegion, ω e = ω' e) :
    TriadicCube.cappedCube (TriadicCube.goodCubes ω') V.scale x =
      TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x := by
  have hagree := openGraph_adj_iff_of_localBonds h
  exact TriadicCube.cappedCube_eq_of_agree fun T hT hnear =>
    TriadicCube.mem_goodCubes_iff_of_adj_iff fun a ha b hb =>
      hagree a (TriadicCube.centeredTriple_subset_localRegion_of_near hx hT hnear ha) b
        (TriadicCube.centeredTriple_subset_localRegion_of_near hx hT hnear hb)

/-- **Locality of the anchors of the capped partition.** -/
theorem anchor_cappedCube_goodCubes_eq_of_localBonds {V : TriadicCube d} {x : Vertex d}
    (hx : x ∈ V.vertices) (h : ∀ e ∈ localBonds V.localRegion, ω e = ω' e) :
    (TriadicCube.cappedCube (TriadicCube.goodCubes ω') V.scale x).anchor ω' =
      (TriadicCube.cappedCube (TriadicCube.goodCubes ω) V.scale x).anchor ω := by
  have hagree := openGraph_adj_iff_of_localBonds h
  rw [cappedCube_goodCubes_eq_of_localBonds hx h]
  have hQ := TriadicCube.cappedCube_spec (TriadicCube.goodCubes ω) V.scale x
  have hsub := TriadicCube.vertices_subset_localRegion_of_mem hx hQ.1
    (TriadicCube.scale_cappedCube_le _ _ _)
  exact TriadicCube.anchor_eq_of_adj_iff fun a ha b hb => hagree a (hsub ha) b (hsub hb)

end Locality

end Rigidity.Percolation
