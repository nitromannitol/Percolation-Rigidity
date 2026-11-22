import Rigidity.Proofs.Percolation.PlanarNuStationarity
import Rigidity.Proofs.Percolation.PlanarCoarseWeights
import Rigidity.Proofs.Percolation.PlanarSubcubeCounts
import Rigidity.Proofs.Percolation.PlanarLocality
import Rigidity.Proofs.Partition.GeneralMinimalScaleMain
import Rigidity.Proofs.Cluster.GehringCubes
import Rigidity.Proofs.Partition.GoodCubesLocal

/-!
# The reach of the planar partition is dominated by a partition with local good events

The good cubes of the planar partition are determined by the open edges inside the squares of side
`9s` around them, while the general partition estimates (Armstrong and Dario, Propositions 2.1 and
2.4, in `GeneralPartition`) ask the failure events to be determined by the threefold enlargements.
Let `T` be *coarsely good* (`planarCoarseGood`) if all the triadic cubes of scale `scale T - 5`
inside `T` are good planar cubes (every cube of scale less than `5` is coarsely good). The failure
of `T` is determined by the edges inside the threefold enlargement of `T`
(`measurableSet_not_mem_planarCoarseGood_localEdge`), and has probability at most
`C exp(-c 3^{scale T})` (`exists_measure_not_mem_planarCoarseGood_le`).

A planar partition cube `Q` of positive scale has a bad planar cube `B` of scale at least
`scale Q - 1` near it, and the ancestor `T` of `B` five scales up is not coarsely good. If the
square of side `9 · 3^{scale Q}` around `Q` contains `x`, then `T` lies in the block of the `3 × 3`
triadic cubes of its scale around `x`, which is contained in the influence set of the triadic
cube of scale `scale T - 2` containing `x` (`mem_influence_scaleCube_of_index`). Hence the
stopping cube of the coarsely good cubes at `x` has scale at least `scale T - 1 ≥ scale Q`: the
reach of the planar partition is at most the stopping size of the partition into coarsely good
cubes (`planarReach_le_stoppingSize`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The coarsely good cubes: all their subcubes five scales down are good planar cubes. -/
def planarCoarseGood (ω : Configuration 2) : Set (TriadicCube 2) :=
  {T | T.scale < 5 ∨ ∀ B ∈ subcubesAt T (T.scale - 5), B ∈ planarGoodCubes ω}

/-- Goodness of a planar cube is determined by the open edges inside its square of side `9s`. -/
theorem measurableSet_not_mem_planarGoodCubes_localEdge (B : TriadicCube 2) :
    MeasurableSet[localEdgeSigma (↑B.ninefold.vertices : Set (Vertex 2))]
      {ω : Configuration 2 | B ∉ planarGoodCubes ω} := by
  refine localGraphSigma_le_localEdgeSigma _ (Finset.finite_toSet _) _ ?_
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨{G | ∃ ω, B ∉ planarGoodCubes ω ∧
    (openGraph ω).induce (↑B.ninefold.vertices : Set (Vertex 2)) = G}, trivial, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ω', hω', heq⟩
    intro hB
    apply hω'
    refine (mem_planarGoodCubes_iff_of_adj_iff fun x hx y hy => ?_).2 hB
    have hxy := congrArg (fun G : SimpleGraph {x : Vertex 2 // x ∈
        (↑B.ninefold.vertices : Set (Vertex 2))} => G.Adj ⟨x, hx⟩ ⟨y, hy⟩) heq
    exact Iff.of_eq hxy
  · intro hω
    exact ⟨ω, hω, rfl⟩

/-- The square of side `9s` of a cube two scales smaller lies in the threefold enlargement. -/
theorem TriadicCube.ninefold_subset_centeredTriple {B T : TriadicCube 2}
    (hBT : B.vertices ⊆ T.vertices) (hs : B.scale + 2 ≤ T.scale) :
    (↑B.ninefold.vertices : Set (Vertex 2)) ⊆ T.centeredTriple := by
  intro y hy
  rw [TriadicCube.mem_ninefold] at hy
  intro i
  have hc := TriadicCube.abs_sub_center_le (hBT B.center_mem) i
  have hr := B.two_mul_ninefoldRadius
  have hyi := hy i
  have hp : (3 : ℤ) ^ T.scale = 3 ^ B.scale * 3 ^ (T.scale - B.scale) := by
    rw [← pow_add]
    congr 1
    omega
  have h9 : (9 : ℤ) ≤ 3 ^ (T.scale - B.scale) := by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (T.scale - B.scale) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hb : (0 : ℤ) < 3 ^ B.scale := by positivity
  have hT : T.side = 3 ^ T.scale := rfl
  change 2 * |B.center i - T.center i| + 1 ≤ 3 ^ T.scale at hc
  change |2 * (y i - T.center i)| < 3 * T.side
  rw [hT]
  have h1 : |y i - T.center i| ≤ |y i - B.center i| + |B.center i - T.center i| := by
    have := abs_sub_le (y i) (B.center i) (T.center i)
    linarith
  rw [abs_mul, abs_two]
  nlinarith

/-- **Locality of coarse goodness.** -/
theorem measurableSet_not_mem_planarCoarseGood_localEdge (T : TriadicCube 2) :
    MeasurableSet[localEdgeSigma T.centeredTriple]
      {ω : Configuration 2 | T ∉ planarCoarseGood ω} := by
  by_cases h5 : T.scale < 5
  · have heq : {ω : Configuration 2 | T ∉ planarCoarseGood ω} = ∅ := by
      ext ω
      simp only [planarCoarseGood, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl h5
    rw [heq]
    exact @MeasurableSet.empty _ (localEdgeSigma T.centeredTriple)
  · have heq : {ω : Configuration 2 | T ∉ planarCoarseGood ω} =
        ⋃ B ∈ subcubesAt T (T.scale - 5), {ω | B ∉ planarGoodCubes ω} := by
      ext ω
      simp only [planarCoarseGood, Set.mem_setOf_eq, not_or, h5, not_false_eq_true, true_and,
        not_forall, Set.mem_iUnion, exists_prop]
    rw [heq]
    refine Finset.measurableSet_biUnion (m := localEdgeSigma T.centeredTriple) _ fun B hB => ?_
    have hBs : B.scale = T.scale - 5 := scale_of_mem_subcubesAt hB
    have hBT : B.vertices ⊆ T.vertices := subset_of_mem_subcubesAt (by omega) hB
    exact localEdgeSigma_mono (TriadicCube.ninefold_subset_centeredTriple hBT (by omega)) _
      (measurableSet_not_mem_planarGoodCubes_localEdge B)

/-- The local edge events are measurable. -/
theorem localEdgeSigma_le_measurableSpace (U : Set (Vertex 2)) :
    localEdgeSigma U ≤ (inferInstance : MeasurableSpace (Configuration 2)) := by
  apply MeasurableSpace.generateFrom_le
  rintro E ⟨x, -, y, -, rfl⟩
  exact measurableSet_openGraph_adj x y

theorem measurableSet_mem_planarCoarseGood (T : TriadicCube 2) :
    MeasurableSet {ω : Configuration 2 | T ∈ planarCoarseGood ω} := by
  have h := localEdgeSigma_le_measurableSpace _ _
    (measurableSet_not_mem_planarCoarseGood_localEdge T)
  have h' := h.compl
  simpa only [Set.compl_setOf, not_not] using h'

/-- **Coarse goodness is likely.** -/
theorem exists_measure_not_mem_planarCoarseGood_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ T : TriadicCube 2,
      latticeBondLaw 2 p {ω | T ∉ planarCoarseGood ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ (1 : ℝ))) := by
  obtain ⟨C, hC, c, hc, hbound⟩ := exists_measure_not_mem_planarGoodCubes_le hpc
  refine ⟨9 ^ 5 * C.toReal, by positivity, c / 3 ^ 5, by positivity, fun T => ?_⟩
  rw [Real.rpow_one]
  by_cases h5 : T.scale < 5
  · have heq : {ω : Configuration 2 | T ∉ planarCoarseGood ω} = ∅ := by
      ext ω
      simp only [planarCoarseGood, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl h5
    rw [heq, measure_empty]
    exact zero_le
  · have hsub : {ω : Configuration 2 | T ∉ planarCoarseGood ω} ⊆
        ⋃ B ∈ subcubesAt T (T.scale - 5), {ω | B ∉ planarGoodCubes ω} := by
      intro ω hω
      simp only [planarCoarseGood, Set.mem_setOf_eq, not_or, h5, not_false_eq_true, true_and,
        not_forall] at hω
      obtain ⟨B, hB, hBn⟩ := hω
      exact Set.mem_biUnion hB hBn
    have hcard : ((subcubesAt T (T.scale - 5)).card : ℝ) = 9 ^ 5 := by
      have h := card_subcubesAt_mul (U := T) (n := T.scale - 5) (Nat.sub_le _ _)
      rw [TriadicCube.volume] at h
      have h9 : (9 : ℝ) ^ T.scale = 9 ^ 5 * 9 ^ (T.scale - 5) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h9] at h
      have h9' : (0 : ℝ) < 9 ^ (T.scale - 5) := by positivity
      field_simp at h
      linarith
    have hexp : ∀ B ∈ subcubesAt T (T.scale - 5),
        Real.exp (-c * (3 : ℝ) ^ B.scale) ≤ Real.exp (-(c / 3 ^ 5) * (3 : ℝ) ^ T.scale) := by
      intro B hB
      rw [scale_of_mem_subcubesAt hB]
      apply Real.exp_le_exp.2
      have h3 : (3 : ℝ) ^ T.scale = 3 ^ 5 * 3 ^ (T.scale - 5) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h3]
      have : (0 : ℝ) < 3 ^ (T.scale - 5) := by positivity
      field_simp
      linarith
    calc latticeBondLaw 2 p {ω | T ∉ planarCoarseGood ω}
        ≤ latticeBondLaw 2 p (⋃ B ∈ subcubesAt T (T.scale - 5), {ω | B ∉ planarGoodCubes ω}) :=
          measure_mono hsub
      _ ≤ ∑ B ∈ subcubesAt T (T.scale - 5), latticeBondLaw 2 p {ω | B ∉ planarGoodCubes ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _B ∈ subcubesAt T (T.scale - 5),
            C * ENNReal.ofReal (Real.exp (-(c / 3 ^ 5) * (3 : ℝ) ^ T.scale)) :=
          Finset.sum_le_sum fun B hB => (hbound B).trans
            (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hexp B hB)) zero_le)
      _ = ENNReal.ofReal (9 ^ 5 * C.toReal * Real.exp (-(c / 3 ^ 5) * (3 : ℝ) ^ T.scale)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          conv_lhs => rw [← ENNReal.ofReal_toReal hC]
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
          congr 1
          ring

/-- A point of a triadic cube and a point of a cube of the same scale whose index differs by at
most one are joined by points at distance at most one. -/
theorem exists_near_of_index {A T : TriadicCube 2} (hs : A.scale = T.scale)
    (hT : ∀ i, |T.index i - A.index i| ≤ 1) :
    ∃ a ∈ A.vertices, ∃ b ∈ T.vertices, ∀ i, |a i - b i| ≤ 1 := by
  have h2 := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one A.scale
  have hh := Rigidity.Proofs.Cluster.halfSide_nonneg A.scale
  have hA : A.side = 3 ^ A.scale := rfl
  have hTs : T.side = 3 ^ A.scale := by rw [TriadicCube.side, hs]
  refine ⟨fun i => A.side * A.index i + Rigidity.Proofs.Cluster.halfSide A.scale * (T.index i - A.index i), ?_,
    fun i => T.side * T.index i - Rigidity.Proofs.Cluster.halfSide A.scale * (T.index i - A.index i), ?_, fun i => ?_⟩
  · intro i
    change |2 * (A.side * A.index i + Rigidity.Proofs.Cluster.halfSide A.scale * (T.index i - A.index i) -
      A.side * A.index i)| < A.side
    have hi := abs_le.1 (hT i)
    rw [hA]
    rw [abs_lt]
    constructor <;> nlinarith
  · intro i
    change |2 * (T.side * T.index i - Rigidity.Proofs.Cluster.halfSide A.scale * (T.index i - A.index i) -
      T.side * T.index i)| < T.side
    have hi := abs_le.1 (hT i)
    rw [hTs]
    rw [abs_lt]
    constructor <;> nlinarith
  · rw [hA, hTs]
    have hi := abs_le.1 (hT i)
    rw [abs_le]
    constructor <;> nlinarith

/-- **The influence cone.** The `3 × 3` block of triadic cubes of scale `h ≥ 2` around the cube of
scale `h` containing `x` lies in the influence set of the cube of scale `h - 2` containing `x`. -/
theorem mem_influence_scaleCube_of_index {x : Vertex 2} {h : ℕ} (hh : 2 ≤ h) {T : TriadicCube 2}
    (hTs : T.scale = h) (hT : ∀ i, |T.index i - (scaleCube h x).index i| ≤ 1) :
    T ∈ (scaleCube (h - 2) x).influence := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_near_of_index (by rw [scale_scaleCube, hTs]) hT
  set R := scaleCube (h - 1) a with hR
  have hRp : R.parent = scaleCube h x := by
    have e : R.parent = scaleCube h a := by
      rw [hR, scaleCube, scaleCube, show h = h - 1 + 1 by omega, TriadicCube.ancestor_succ]
      simp
    rw [e]
    exact scaleCube_eq_of_mem ha
  have step1 : (scaleCube (h - 2) x).InfluenceStep R := by
    refine ⟨?_, x, mem_scaleCube _ x, x, ?_, fun i => by simp⟩
    · rw [hR, scale_scaleCube, scale_scaleCube]
      omega
    · rw [hRp]
      exact mem_scaleCube h x
  have step2 : R.InfluenceStep T := by
    refine ⟨?_, a, mem_scaleCube _ a, b, T.vertices_subset_parent hb, hab⟩
    rw [hR, scale_scaleCube, hTs]
    omega
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single step1) step2

/-- **The reach of the planar partition is at most the stopping size of the partition into coarsely
good cubes.** -/
theorem planarReach_le_stoppingSize (hH : ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω))
    (x : Vertex 2) :
    planarReach ω x ≤ ENNReal.ofReal (TriadicCube.stoppingSize (planarCoarseGood ω) x) := by
  obtain ⟨S, ⟨hxS, hS⟩, -⟩ := hH x
  rw [TriadicCube.stoppingSize_eq_of_mem hxS hS, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
  unfold planarReach
  refine iSup₂_le fun Q ⟨hQ, hxQ⟩ => ?_
  refine pow_le_pow_right₀ (by norm_num) ?_
  rcases Nat.eq_zero_or_pos Q.scale with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨B, hB, hQB, hnear⟩ := hQ.exists_bad_near Q.center_mem hpos
  set h := B.scale + 5 with hhdef
  set T := B.ancestor 5 with hTdef
  have hTs : T.scale = h := TriadicCube.scale_ancestor B 5
  have hBT : B.vertices ⊆ T.vertices := B.vertices_subset_ancestor 5
  have hTbad : T ∉ planarCoarseGood ω := by
    rintro (h5 | hall)
    · omega
    refine hB (hall B ?_)
    rw [hTs, show h - 5 = B.scale by omega]
    have hc : B.center ∈ B.vertices := B.center_mem
    have hcT := hBT hc
    rw [subcubesAt, Finset.mem_image]
    refine ⟨B.center, (T.mem_toIntegerCube_vertices _).2 hcT, ?_⟩
    exact TriadicCube.eq_of_mem_of_scale_eq (scale_scaleCube _ _) (mem_scaleCube _ _) hc
  -- `T` lies in the block around `x`
  have hindex : ∀ i, |T.index i - (scaleCube h x).index i| ≤ 1 := by
    intro i
    have hxQ' := TriadicCube.mem_ninefold.1 hxQ i
    have hr := Q.two_mul_ninefoldRadius
    have hn := hnear i
    have hTc := TriadicCube.abs_sub_center_le (hBT B.center_mem) i
    have hAc := TriadicCube.abs_sub_center_le (mem_scaleCube h x) i
    change 2 * |B.center i - T.center i| + 1 ≤ 3 ^ T.scale at hTc
    rw [hTs] at hTc
    rw [scale_scaleCube] at hAc
    have hQs : (3 : ℤ) ^ Q.scale ≤ 3 * 3 ^ B.scale := by
      calc (3 : ℤ) ^ Q.scale ≤ 3 ^ (B.scale + 1) := pow_le_pow_right₀ (by norm_num) hQB
        _ = 3 * 3 ^ B.scale := by ring
    have hBs : B.side = 3 ^ B.scale := rfl
    have hh : (3 : ℤ) ^ h = 243 * 3 ^ B.scale := by rw [hhdef, pow_add]; ring
    have hTcen : T.center i = 3 ^ h * T.index i := by
      change T.side * T.index i = _
      rw [TriadicCube.side, hTs]
    have hAcen : (scaleCube h x).center i = 3 ^ h * (scaleCube h x).index i := by
      change (scaleCube h x).side * (scaleCube h x).index i = _
      rw [TriadicCube.side, scale_scaleCube]
    have hdist : |T.center i - (scaleCube h x).center i| < 2 * 3 ^ h := by
      have hn' : |Q.center i - B.center i| ≤ 11 * 3 ^ B.scale := hn
      have e1 := abs_sub_le (T.center i) (B.center i) (Q.center i)
      have e2 := abs_sub_le (T.center i) (Q.center i) (x i)
      have e3 := abs_sub_le (T.center i) (x i) ((scaleCube h x).center i)
      have q1 := abs_sub_comm (T.center i) (B.center i)
      have q2 := abs_sub_comm (B.center i) (Q.center i)
      have q3 := abs_sub_comm (Q.center i) (x i)
      have hb0 : (0 : ℤ) < 3 ^ B.scale := by positivity
      rw [hh] at hTc hAc ⊢
      have hQs' : (3 : ℤ) ^ Q.scale ≤ 3 * 3 ^ B.scale := hQs
      linarith
    rw [hTcen, hAcen, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ h)] at hdist
    have hpos3 : (0 : ℤ) < 3 ^ h := by positivity
    have hlt : |T.index i - (scaleCube h x).index i| < 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    omega
  have hinf := mem_influence_scaleCube_of_index (by omega : 2 ≤ h) hTs hindex
  -- the stopping cube at `x` has scale at least `h - 1`
  by_contra hlt
  push Not at hlt
  have hSle : S.scale ≤ h - 2 := by omega
  have hstable : scaleCube (h - 2) x ∈ TriadicCube.stableGood (planarCoarseGood ω) := by
    have hanc := TriadicCube.ancestor_mem_stableGood hS.1.1 (h - 2 - S.scale)
    have he : S.ancestor (h - 2 - S.scale) = scaleCube (h - 2) x :=
      TriadicCube.eq_of_mem_of_scale_eq (by rw [TriadicCube.scale_ancestor, scale_scaleCube]; omega)
        (S.vertices_subset_ancestor _ hxS) (mem_scaleCube _ x)
    rw [← he]
    exact hanc
  exact hTbad (hstable hinf)

end Rigidity.Percolation
