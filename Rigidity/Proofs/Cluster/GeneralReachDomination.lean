import Rigidity.Proofs.Cluster.PartitionReachMoments
import Rigidity.Proofs.Percolation.GeneralDim.CubeSubcubes
import Rigidity.Proofs.Partition.GoodCubesLocal
import Rigidity.Proofs.Partition.GeneralCount
import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuMonotone
import Rigidity.Proofs.Cluster.GehringCubes

/-!
# The reach of the partition is dominated by a partition with local good events

The reach `partitionReach ω z` of the partition into good cubes is the largest side of a partition
cube whose `3s`-neighbourhood contains `z`. Its sums over a cube concentrate, as needed for the
reverse Hölder cubes of `GeneralRHEvent`, because it is dominated by the stopping size of a second
partition with local failure events. Let `T` be *coarsely good* (`coarseGood`) if all its triadic
subcubes of scale `scale T - 5` are good (every cube of scale less than `5` is coarsely good). The
failure of `T` is determined by the edges inside the threefold enlargement of `T`
(`measurableSet_not_mem_coarseGood_localEdge`), and has probability at most `C exp(-c 3^{scale T})`
(`exists_measure_not_mem_coarseGood_le`, from Lemma 2.7 of Armstrong and Dario).

A partition cube `Q` of positive scale has a bad cube `B` of scale at least `scale Q - 1` near it
(`TriadicCube.IsMaximalStopping.exists_bad_near`), and the ancestor `T` of `B` five scales up is not
coarsely good. If the `3s`-neighbourhood of `Q` contains `x`, then `T` lies in the block of the
`3^d` triadic cubes of its scale around `x`, which is contained in the influence set of the
triadic cube of scale `scale T - 2` containing `x` (`mem_influence_triadicCubeAt_of_index`). Hence
the stopping cube of the coarsely good cubes at `x` has scale at least `scale T - 1 ≥ scale Q`:
the reach is at most the stopping size of the partition into coarsely good cubes
(`partitionReach_le_stoppingSize_coarseGood`). The planar case is `PlanarReachDomination`.
-/

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- The coarsely good cubes: all their subcubes five scales down are good. -/
def coarseGood (ω : Configuration d) : Set (TriadicCube d) :=
  {T | T.scale < 5 ∨ ∀ B ∈ T.subcubesAt (T.scale - 5), B ∈ TriadicCube.goodCubes ω}

/-- The threefold enlargement of a cube lies in that of each of its ancestors. -/
theorem TriadicCube.centeredTriple_subset_ancestor_centeredTriple (Q : TriadicCube d) (n : ℕ) :
    Q.centeredTriple ⊆ (Q.ancestor n).centeredTriple := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [TriadicCube.ancestor_succ]
    exact ih.trans (Q.ancestor n).centeredTriple_subset_parent_centeredTriple

/-- **Locality of coarse goodness.** -/
theorem measurableSet_not_mem_coarseGood_localEdge (T : TriadicCube d) :
    MeasurableSet[localEdgeSigma T.centeredTriple] {ω : Configuration d | T ∉ coarseGood ω} := by
  by_cases h5 : T.scale < 5
  · have heq : {ω : Configuration d | T ∉ coarseGood ω} = ∅ := by
      ext ω
      simp only [coarseGood, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl h5
    rw [heq]
    exact @MeasurableSet.empty _ (localEdgeSigma T.centeredTriple)
  · have heq : {ω : Configuration d | T ∉ coarseGood ω} =
        ⋃ B ∈ T.subcubesAt (T.scale - 5), {ω | B ∉ TriadicCube.goodCubes ω} := by
      ext ω
      simp only [coarseGood, Set.mem_setOf_eq, not_or, h5, not_false_eq_true, true_and,
        not_forall, Set.mem_iUnion, exists_prop]
    rw [heq]
    refine Finset.measurableSet_biUnion (m := localEdgeSigma T.centeredTriple) _ fun B hB => ?_
    have hBs : B.scale = T.scale - 5 := TriadicCube.scale_of_mem_subcubesAt hB
    have hBT : B.vertices ⊆ T.vertices := TriadicCube.subset_of_mem_subcubesAt (by omega) hB
    have hanc : B.ancestor 5 = T :=
      TriadicCube.eq_of_mem_of_scale_eq (by rw [TriadicCube.scale_ancestor]; omega)
        (B.vertices_subset_ancestor 5 B.center_mem) (hBT B.center_mem)
    have hsub : B.centeredTriple ⊆ T.centeredTriple := by
      rw [← hanc]
      exact B.centeredTriple_subset_ancestor_centeredTriple 5
    exact localEdgeSigma_mono hsub _ (TriadicCube.measurableSet_not_mem_goodCubes_localEdge B)

/-- The local edge events are measurable. -/
theorem localEdgeSigma_le_measurableSpace' (U : Set (Vertex d)) :
    localEdgeSigma U ≤ (inferInstance : MeasurableSpace (Configuration d)) := by
  apply MeasurableSpace.generateFrom_le
  rintro E ⟨x, -, y, -, rfl⟩
  exact measurableSet_openGraph_adj x y

theorem measurableSet_mem_coarseGood (T : TriadicCube d) :
    MeasurableSet {ω : Configuration d | T ∈ coarseGood ω} := by
  have h := localEdgeSigma_le_measurableSpace' _ _ (measurableSet_not_mem_coarseGood_localEdge T)
  have h' := h.compl
  simpa only [Set.compl_setOf, not_not] using h'

/-- **Coarse goodness is likely.** -/
theorem exists_measure_not_mem_coarseGood_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ T : TriadicCube d,
      latticeBondLaw d p {ω | T ∉ coarseGood ω} ≤
        ENNReal.ofReal (C * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ (1 : ℝ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_measure_not_mem_goodCubes_le hd hpc
  refine ⟨(3 ^ d) ^ 5 * C, by positivity, c / 3 ^ 5, by positivity, fun T => ?_⟩
  rw [Real.rpow_one]
  by_cases h5 : T.scale < 5
  · have heq : {ω : Configuration d | T ∉ coarseGood ω} = ∅ := by
      ext ω
      simp only [coarseGood, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Or.inl h5
    rw [heq, measure_empty]
    exact zero_le
  · have hsub : {ω : Configuration d | T ∉ coarseGood ω} ⊆
        ⋃ B ∈ T.subcubesAt (T.scale - 5), {ω | B ∉ TriadicCube.goodCubes ω} := by
      intro ω hω
      simp only [coarseGood, Set.mem_setOf_eq, not_or, h5, not_false_eq_true, true_and,
        not_forall] at hω
      obtain ⟨B, hB, hBn⟩ := hω
      exact Set.mem_biUnion hB hBn
    have hcard : ((T.subcubesAt (T.scale - 5)).card : ℝ) = (3 ^ d) ^ 5 := by
      have h := card_subcubesAt_mul_general T (n := T.scale - 5) (Nat.sub_le _ _)
      rw [TriadicCube.latticeVolume] at h
      have h3 : ((3 : ℝ) ^ T.scale) ^ d = (3 ^ d) ^ 5 * ((3 : ℝ) ^ (T.scale - 5)) ^ d := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 1
        have : T.scale = 5 + (T.scale - 5) := by omega
        rw [this, add_mul, Nat.add_sub_cancel_left]
        ring
      rw [h3] at h
      have h9' : (0 : ℝ) < ((3 : ℝ) ^ (T.scale - 5)) ^ d := by positivity
      field_simp at h
      linarith
    have hexp : ∀ B ∈ T.subcubesAt (T.scale - 5),
        Real.exp (-c * (3 : ℝ) ^ B.scale) ≤ Real.exp (-(c / 3 ^ 5) * (3 : ℝ) ^ T.scale) := by
      intro B hB
      rw [TriadicCube.scale_of_mem_subcubesAt hB]
      apply Real.exp_le_exp.2
      have h3 : (3 : ℝ) ^ T.scale = 3 ^ 5 * 3 ^ (T.scale - 5) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h3]
      have : (0 : ℝ) < 3 ^ (T.scale - 5) := by positivity
      field_simp
      linarith
    calc latticeBondLaw d p {ω | T ∉ coarseGood ω}
        ≤ latticeBondLaw d p (⋃ B ∈ T.subcubesAt (T.scale - 5),
            {ω | B ∉ TriadicCube.goodCubes ω}) := measure_mono hsub
      _ ≤ ∑ B ∈ T.subcubesAt (T.scale - 5),
            latticeBondLaw d p {ω | B ∉ TriadicCube.goodCubes ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _B ∈ T.subcubesAt (T.scale - 5),
            ENNReal.ofReal (C * Real.exp (-(c / 3 ^ 5) * (3 : ℝ) ^ T.scale)) :=
          Finset.sum_le_sum fun B hB => (hbound B).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hexp B hB) hC))
      _ = ENNReal.ofReal ((3 ^ d) ^ 5 * C * Real.exp (-(c / 3 ^ 5) * (3 : ℝ) ^ T.scale)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
          congr 1
          ring

/-- Twice the distance of a vertex of a triadic cube to its centre is less than the side. -/
theorem TriadicCube.two_mul_abs_sub_center_add_one_le {Q : TriadicCube d} {x : Vertex d}
    (hx : x ∈ Q.vertices) (i : Fin d) : 2 * |x i - Q.center i| + 1 ≤ 3 ^ Q.scale := by
  have h := hx i
  have hs : Q.side = 3 ^ Q.scale := rfl
  change |2 * (x i - Q.side * Q.index i)| < Q.side at h
  change 2 * |x i - Q.side * Q.index i| + 1 ≤ 3 ^ Q.scale
  rw [abs_mul, abs_two] at h
  have ho : Q.side % 2 = 1 := by
    have : Odd Q.side := by
      rw [hs]; exact (show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow
    exact Int.odd_iff.mp this
  omega

/-- The centre of a triadic cube whose `3s`-neighbourhood contains `x` is within `4 · 3^s` of
`x`. -/
theorem TriadicCube.abs_center_sub_le_of_mem_thicken {Q : TriadicCube d} {x : Vertex d}
    (hx : x ∈ (Q.thicken 3).vertices) (i : Fin d) : |Q.center i - x i| ≤ 4 * 3 ^ Q.scale := by
  have hsub := TriadicCube.subset_boxAround hx
    ((Q.mem_toIntegerCube_vertices _).2 Q.center_mem)
  rw [IntegerCube.mem_vertices] at hsub
  obtain ⟨h1, h2⟩ := hsub i
  change x i - (((3 + 1) * 3 ^ Q.scale : ℕ) : ℤ) ≤ Q.center i at h1
  change Q.center i < x i - (((3 + 1) * 3 ^ Q.scale : ℕ) : ℤ) +
    (((2 * 3 + 2) * 3 ^ Q.scale : ℕ) : ℤ) at h2
  push_cast at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- A point of a triadic cube and a point of a cube of the same scale whose index differs by at
most one are joined by points at distance at most one. -/
theorem exists_near_of_index_general {A T : TriadicCube d} (hs : A.scale = T.scale)
    (hT : ∀ i, |T.index i - A.index i| ≤ 1) :
    ∃ a ∈ A.vertices, ∃ b ∈ T.vertices, ∀ i, |a i - b i| ≤ 1 := by
  have h2 := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one A.scale
  have hh := Rigidity.Proofs.Cluster.halfSide_nonneg A.scale
  have hA : A.side = 3 ^ A.scale := rfl
  have hTs : T.side = 3 ^ A.scale := by rw [TriadicCube.side, hs]
  refine ⟨fun i => A.side * A.index i +
      Rigidity.Proofs.Cluster.halfSide A.scale * (T.index i - A.index i), ?_,
    fun i => T.side * T.index i -
      Rigidity.Proofs.Cluster.halfSide A.scale * (T.index i - A.index i), ?_, fun i => ?_⟩
  · intro i
    change |2 * (A.side * A.index i + Rigidity.Proofs.Cluster.halfSide A.scale *
      (T.index i - A.index i) - A.side * A.index i)| < A.side
    have hi := abs_le.1 (hT i)
    rw [hA]
    rw [abs_lt]
    constructor <;> nlinarith
  · intro i
    change |2 * (T.side * T.index i - Rigidity.Proofs.Cluster.halfSide A.scale *
      (T.index i - A.index i) - T.side * T.index i)| < T.side
    have hi := abs_le.1 (hT i)
    rw [hTs]
    rw [abs_lt]
    constructor <;> nlinarith
  · rw [hA, hTs]
    have hi := abs_le.1 (hT i)
    rw [abs_le]
    constructor <;> nlinarith

/-- **The influence cone.** The block of the triadic cubes of scale `h ≥ 2` with index within one
of the cube of scale `h` containing `x` lies in the influence set of the cube of scale `h - 2`
containing `x`. -/
theorem mem_influence_triadicCubeAt_of_index {x : Vertex d} {h : ℕ} (hh : 2 ≤ h)
    {T : TriadicCube d} (hTs : T.scale = h)
    (hT : ∀ i, |T.index i - (triadicCubeAt h x).index i| ≤ 1) :
    T ∈ (triadicCubeAt (h - 2) x).influence := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_near_of_index_general (by rw [scale_triadicCubeAt, hTs]) hT
  set R := triadicCubeAt (h - 1) a with hR
  have hRp : R.parent = triadicCubeAt h x := by
    have e : R.parent = triadicCubeAt h a := by
      rw [hR, triadicCubeAt, triadicCubeAt, show h = h - 1 + 1 by omega, TriadicCube.ancestor_succ]
      simp
    rw [e]
    exact triadicCubeAt_eq_of_mem ha
  have step1 : (triadicCubeAt (h - 2) x).InfluenceStep R := by
    refine ⟨?_, x, mem_triadicCubeAt _ x, x, ?_, fun i => by simp⟩
    · rw [hR, scale_triadicCubeAt, scale_triadicCubeAt]
      omega
    · rw [hRp]
      exact mem_triadicCubeAt h x
  have step2 : R.InfluenceStep T := by
    refine ⟨?_, a, mem_triadicCubeAt _ a, b, T.vertices_subset_parent hb, hab⟩
    rw [hR, scale_triadicCubeAt, hTs]
    omega
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single step1) step2

/-- **The reach of the partition is at most the stopping size of the partition into coarsely good
cubes.** -/
theorem partitionReach_le_stoppingSize_coarseGood (hH : ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (coarseGood ω))
    (x : Vertex d) :
    partitionReach ω x ≤ ENNReal.ofReal (TriadicCube.stoppingSize (coarseGood ω) x) := by
  obtain ⟨S, ⟨hxS, hS⟩, -⟩ := hH x
  rw [TriadicCube.stoppingSize_eq_of_mem hxS hS, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
  unfold partitionReach
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
  have hTbad : T ∉ coarseGood ω := by
    rintro (h5 | hall)
    · omega
    refine hB (hall B ?_)
    rw [hTs, show h - 5 = B.scale by omega]
    have hc : B.center ∈ B.vertices := B.center_mem
    have hcT := hBT hc
    have he : triadicCubeAt B.scale B.center = B :=
      TriadicCube.eq_of_mem_of_scale_eq (scale_triadicCubeAt _ _) (mem_triadicCubeAt _ _) hc
    have hmem := TriadicCube.triadicCubeAt_mem_subcubesAt (U := T) B.scale hcT
    rwa [he] at hmem
  -- `T` lies in the block around `x`
  have hindex : ∀ i, |T.index i - (triadicCubeAt h x).index i| ≤ 1 := by
    intro i
    have hxQ' := TriadicCube.abs_center_sub_le_of_mem_thicken hxQ i
    have hn := hnear i
    have hTc : 2 * |B.center i - T.center i| + 1 ≤ 3 ^ T.scale :=
      TriadicCube.two_mul_abs_sub_center_add_one_le (hBT B.center_mem) i
    have hAc := TriadicCube.two_mul_abs_sub_center_add_one_le (mem_triadicCubeAt h x) i
    rw [hTs] at hTc
    rw [scale_triadicCubeAt] at hAc
    have hQs : (3 : ℤ) ^ Q.scale ≤ 3 * 3 ^ B.scale := by
      calc (3 : ℤ) ^ Q.scale ≤ 3 ^ (B.scale + 1) := pow_le_pow_right₀ (by norm_num) hQB
        _ = 3 * 3 ^ B.scale := by ring
    have hBs : B.side = 3 ^ B.scale := rfl
    have hh : (3 : ℤ) ^ h = 243 * 3 ^ B.scale := by rw [hhdef, pow_add]; ring
    have hTcen : T.center i = 3 ^ h * T.index i := by
      change T.side * T.index i = _
      rw [TriadicCube.side, hTs]
    have hAcen : (triadicCubeAt h x).center i = 3 ^ h * (triadicCubeAt h x).index i := by
      change (triadicCubeAt h x).side * (triadicCubeAt h x).index i = _
      rw [TriadicCube.side, scale_triadicCubeAt]
    have hdist : |T.center i - (triadicCubeAt h x).center i| < 2 * 3 ^ h := by
      have hn' : |Q.center i - B.center i| ≤ 11 * 3 ^ B.scale := hn
      have e1 := abs_sub_le (T.center i) (B.center i) (Q.center i)
      have e2 := abs_sub_le (T.center i) (Q.center i) (x i)
      have e3 := abs_sub_le (T.center i) (x i) ((triadicCubeAt h x).center i)
      have q1 := abs_sub_comm (T.center i) (B.center i)
      have q2 := abs_sub_comm (B.center i) (Q.center i)
      have q3 := abs_sub_comm (x i) ((triadicCubeAt h x).center i)
      have hb0 : (0 : ℤ) < 3 ^ B.scale := by positivity
      rw [hh] at hTc hAc ⊢
      linarith
    rw [hTcen, hAcen, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ h)] at hdist
    have hpos3 : (0 : ℤ) < 3 ^ h := by positivity
    have hlt : |T.index i - (triadicCubeAt h x).index i| < 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    omega
  have hinf := mem_influence_triadicCubeAt_of_index (by omega : 2 ≤ h) hTs hindex
  -- the stopping cube at `x` has scale at least `h - 1`
  by_contra hlt
  push Not at hlt
  have hSle : S.scale ≤ h - 2 := by omega
  have hstable : triadicCubeAt (h - 2) x ∈ TriadicCube.stableGood (coarseGood ω) := by
    have hanc := TriadicCube.ancestor_mem_stableGood hS.1.1 (h - 2 - S.scale)
    have he : S.ancestor (h - 2 - S.scale) = triadicCubeAt (h - 2) x :=
      TriadicCube.eq_of_mem_of_scale_eq
        (by rw [TriadicCube.scale_ancestor, scale_triadicCubeAt]; omega)
        (S.vertices_subset_ancestor _ hxS) (mem_triadicCubeAt _ x)
    rw [← he]
    exact hanc
  exact hTbad (hstable hinf)

end Rigidity.Percolation
