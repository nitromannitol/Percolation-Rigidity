import Rigidity.Proofs.Cluster.GeneralMuMeasurable
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuMonotone

/-!
# The error in the subadditivity of `μ` on triadic cubes of `ℤ^d`

The subadditivity of `μ` (Armstrong and Dario, Lemma 4.8, (4.32); `sum_cubeMu_subcubes_le`) holds
up to the coarse pairing of the minimizer `u` of `μ(U, q)` over the *exceptional* lattice edges
`(x, x + e_i)` of `U`: those leaving the subcube `V(x)` of scale `n` of `x`, or lying in an
unresolved subcube. For lattice neighbours `x, y` the anchors of their partition cubes are joined
by an open path inside the union of the two partition cubes (`partitionCoarseData`), so

`|[u]_𝒫(y) - [u]_𝒫(x)| ≤ ∑_{z ∈ C_*(U) ∩ (□_𝒫(x) ∪ □_𝒫(y))} |∇u|₁(z)`,

`|∇u|₁(z)` the sum of the open increments of `u` at `z`. Exchanging the sums, the error is at most
`|q|₁ ∑_z |∇u|₁(z) N(z)`, where `N(z) ≤ d 3^d size(□_𝒫(z))^d` counts the exceptional edges with an
endpoint in `□_𝒫(z)`, and `N(z) = 0` unless `z` is exceptional in the sense of
`ExceptionalMajorant` (its subcube is unresolved, or `□_𝒫(z)` reaches a face of its subcube). By the
Cauchy–Schwarz inequality, the energy bound of the minimizer (Armstrong and Dario, (4.20)) and
Young's inequality with a parameter `t > 0`, the error is at most

`K |q|₁² (t ∑_{z ∈ U} size(z)^{2d-2} + t⁻¹ ∑_{z ∈ U} size(z)^{2d} 1{z exceptional}) / 2`

(`sum_cubeMu_subcubes_sub_le`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **Coarse increments along a lattice edge.** -/
theorem abs_cubeCoarsen_sub_le_sum (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (u : CubeFun ω U) {x y : Vertex d}
    (hx : x ∈ U.toIntegerCube.vertices) (hy : y ∈ U.toIntegerCube.vertices)
    (hxy : (nearestNeighborGraph d).Adj x y) :
    |cubeCoarsen ω U u y - cubeCoarsen ω U u x| ≤
      ∑ z ∈ crossingClusterVertices ω U,
        (if z ∈ (partitionCube ω x).vertices ∨ z ∈ (partitionCube ω y).vertices then
          vertexVariation ω (crossingClusterVertices ω U) (cubeExtend ω U u) z else 0) := by
  have hnn : 0 ≤ ∑ z ∈ crossingClusterVertices ω U,
      (if z ∈ (partitionCube ω x).vertices ∨ z ∈ (partitionCube ω y).vertices then
        vertexVariation ω (crossingClusterVertices ω U) (cubeExtend ω U u) z else 0) :=
    Finset.sum_nonneg fun z _ => by
      split_ifs
      · exact vertexVariation_nonneg _ _ _ _
      · exact le_rfl
  by_cases hpart : partitionCube ω x = partitionCube ω y
  · have h : cubeCoarsen ω U u y = cubeCoarsen ω U u x := by
      unfold cubeCoarsen partitionAnchor
      rw [hpart]
    rw [h, sub_self, abs_zero]
    exact hnn
  set P := partitionCoarseData hd hP U hU with hPdef
  set w := cubeExtend ω U u
  have hjoin := P.joinedWithin_pairRegion x hx y hy hxy hpart
  have h1 := abs_sub_le_sum_vertexVariation (P.pairRegion x y ∩ P.cluster) w hjoin
  have h2 : ∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω (P.pairRegion x y ∩ P.cluster) w z
      ≤ ∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω P.cluster w z :=
    Finset.sum_le_sum fun z _ => vertexVariation_mono ω Finset.inter_subset_right w z
  have h3 : ∑ z ∈ P.pairRegion x y ∩ P.cluster, vertexVariation ω P.cluster w z ≤
      ∑ z ∈ crossingClusterVertices ω U,
        (if z ∈ (partitionCube ω x).vertices ∨ z ∈ (partitionCube ω y).vertices then
          vertexVariation ω (crossingClusterVertices ω U) w z else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun z _ _ =>
      vertexVariation_nonneg _ _ _ _
    obtain ⟨hzR, hzC⟩ := Finset.mem_inter.1 hz
    exact Finset.mem_filter.2 ⟨hzC, (Finset.mem_filter.1 hzR).2⟩
  have e : cubeCoarsen ω U u y - cubeCoarsen ω U u x = -(w (P.anchor x) - w (P.anchor y)) := by
    change w (partitionAnchor ω y) - w (partitionAnchor ω x) =
      -(w (partitionAnchor ω x) - w (partitionAnchor ω y))
    ring
  rw [e, abs_neg]
  exact h1.trans (h2.trans h3)

/-- The lattice edge `(x, x + e_i)` of `U` is exceptional at scale `n`: it leaves the subcube of
scale `n` of `x`, or this subcube is not resolved. -/
def IsExceptionalEdge (ω : Configuration d) (U : TriadicCube d) (n : ℕ) (x : Vertex d)
    (i : Fin d) : Prop :=
  x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
    ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
      x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices)

/-- The number of exceptional edges of `U` with an endpoint whose partition cube contains `z`. -/
noncomputable def exceptionalEdgeCount (ω : Configuration d) (U : TriadicCube d) (n : ℕ)
    (z : Vertex d) : ℝ :=
  ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
    if IsExceptionalEdge ω U n x i ∧ (z ∈ (partitionCube ω x).vertices ∨
        z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices) then 1 else 0

theorem exceptionalEdgeCount_nonneg (U : TriadicCube d) (n : ℕ) (z : Vertex d) :
    0 ≤ exceptionalEdgeCount ω U n z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- **The error is carried by the exceptional edges.** The coarse pairing of `u` over the
exceptional edges is at most `|q|₁ ∑_{z ∈ C_*(U)} |∇u|₁(z) N(z)`. -/
theorem exceptional_error_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (n : ℕ) (q : Fin d → ℝ) (u : CubeFun ω U) :
    ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
          ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
            x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
        q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0) ≤
      (∑ i, |q i|) * ∑ z ∈ crossingClusterVertices ω U,
        vertexVariation ω (crossingClusterVertices ω U) (cubeExtend ω U u) z *
          exceptionalEdgeCount ω U n z := by
  set C := crossingClusterVertices ω U with hC
  set v : Vertex d → ℝ := fun z => vertexVariation ω C (cubeExtend ω U u) z with hv
  set Q := ∑ i, |q i| with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hq : ∀ i, |q i| ≤ Q := fun i =>
    Finset.single_le_sum (f := fun j => |q j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  set a : Vertex d → Fin d → Vertex d → ℝ := fun x i z =>
    if IsExceptionalEdge ω U n x i ∧ (z ∈ (partitionCube ω x).vertices ∨
        z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices) then 1 else 0 with ha
  have hterm : ∀ x ∈ U.toIntegerCube.vertices, ∀ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
          ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
            x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
        q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0) ≤
      Q * ∑ z ∈ C, a x i z * v z := by
    intro x hx i
    split_ifs with hc
    · have hΔ := abs_cubeCoarsen_sub_le_sum hd hP hU u hx hc.1 (y := x + LatticeProb.unit i)
        ⟨i, Or.inl rfl⟩
      have hsum : ∑ z ∈ C, (if z ∈ (partitionCube ω x).vertices ∨
          z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices then v z else 0) =
          ∑ z ∈ C, a x i z * v z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have hc' : IsExceptionalEdge ω U n x i := hc
        by_cases hz : z ∈ (partitionCube ω x).vertices ∨
            z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices
        · rw [if_pos hz, ha]
          simp only
          rw [if_pos ⟨hc', hz⟩, one_mul]
        · rw [if_neg hz, ha]
          simp only
          rw [if_neg (fun h => hz h.2), zero_mul]
      calc q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x)
          ≤ |q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x)| :=
            le_abs_self _
        _ = |q i| * |cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x| :=
            abs_mul _ _
        _ ≤ Q * |cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x| :=
            mul_le_mul_of_nonneg_right (hq i) (abs_nonneg _)
        _ ≤ Q * ∑ z ∈ C, (if z ∈ (partitionCube ω x).vertices ∨
            z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices then v z else 0) :=
            mul_le_mul_of_nonneg_left hΔ hQ0
        _ = Q * ∑ z ∈ C, a x i z * v z := by rw [hsum]
    · exact mul_nonneg hQ0 (Finset.sum_nonneg fun z _ => mul_nonneg
        (by simp only [ha]; split_ifs <;> norm_num) (vertexVariation_nonneg _ _ _ _))
  calc _ ≤ ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d, Q * ∑ z ∈ C, a x i z * v z :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun i _ => hterm x hx i
    _ = Q * ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d, ∑ z ∈ C, a x i z * v z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = Q * ∑ z ∈ C, ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d, a x i z * v z := by
        congr 1
        calc ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d, ∑ z ∈ C, a x i z * v z
            = ∑ x ∈ U.toIntegerCube.vertices, ∑ z ∈ C, ∑ i : Fin d, a x i z * v z :=
              Finset.sum_congr rfl fun x _ => Finset.sum_comm
          _ = ∑ z ∈ C, ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d, a x i z * v z :=
              Finset.sum_comm
    _ = Q * ∑ z ∈ C, v z * exceptionalEdgeCount ω U n z := by
        congr 1
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [exceptionalEdgeCount, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Exceptional edges near `z` make `z` exceptional.** If an exceptional edge has an endpoint in
the partition cube of `z`, then either the subcube of `z` contains a partition cube larger than
itself, or the partition cube of `z` reaches a face of the subcube. -/
theorem exceptionalMajorant_of_isExceptionalEdge (hP : PartitionEvent ω) {U : TriadicCube d}
    {n : ℕ} {x z : Vertex d} {i : Fin d} (hexc : IsExceptionalEdge ω U n x i)
    (hz : z ∈ (partitionCube ω x).vertices ∨
      z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices) :
    ExceptionalMajorant ω n z := by
  set V := triadicCubeAt n z with hVdef
  set Q := partitionCube ω z with hQdef
  have hVs : V.scale = n := scale_triadicCubeAt n z
  have hsize : ∀ y, TriadicCube.stoppingSize (TriadicCube.goodCubes ω) y =
      (3 : ℝ) ^ (partitionCube ω y).scale := stoppingSize_goodCubes_eq hP
  -- an unresolved subcube of `z`
  have hunres : ¬ PartitionResolved ω V → ExceptionalMajorant ω n z := by
    intro hres
    unfold PartitionResolved at hres
    push Not at hres
    obtain ⟨y, hyV, hy⟩ := hres
    refine Or.inl ⟨y, (V.mem_toIntegerCube_vertices y).2 hyV, ?_⟩
    rw [hsize]
    rw [hVs] at hy
    exact pow_lt_pow_right₀ (by norm_num) hy
  by_cases hs : n < Q.scale
  · refine Or.inl ⟨z, (V.mem_toIntegerCube_vertices z).2 (mem_triadicCubeAt n z), ?_⟩
    rw [hsize]
    exact pow_lt_pow_right₀ (by norm_num) hs
  push Not at hs
  have hzV : z ∈ V.vertices := mem_triadicCubeAt n z
  have hzQ : z ∈ Q.vertices := mem_partitionCube hP z
  have hQV : Q.vertices ⊆ V.vertices :=
    TriadicCube.vertices_subset_of_mem_of_scale_le hzQ hzV (by rw [hVs]; exact hs)
  have hQs := Q.side_eq_two_mul_radius_add_one
  have hQside : Q.side = (3 : ℤ) ^ Q.scale := rfl
  -- the bound on the margin from a point of `Q` on a face of `V`
  have hmargin : ∀ y ∈ Q.vertices, ∀ j : Fin d,
      (y j = V.toIntegerCube.corner j ∨
        y j = V.toIntegerCube.corner j + (V.toIntegerCube.size : ℤ) - 1) →
      ExceptionalMajorant ω n z := by
    intro y hy j hface
    refine Or.inr ⟨j, ?_⟩
    rw [hsize]
    have h1 := (Q.mem_vertices_iff_coord y).1 hy j
    have h2 := (Q.mem_vertices_iff_coord z).1 hzQ j
    have hm : V.margin z j ≤ Q.side - 1 := by
      unfold TriadicCube.margin
      have hsz : (V.toIntegerCube.size : ℤ) = (3 : ℤ) ^ V.scale := by
        change ((3 ^ V.scale : ℕ) : ℤ) = _
        push_cast
        rfl
      rw [hsz] at hface
      rcases hface with h | h <;> [exact (min_le_left _ _).trans (by omega);
        exact (min_le_right _ _).trans (by omega)]
    have hm' : (V.margin z j : ℝ) ≤ ((3 : ℤ) ^ Q.scale : ℤ) - 1 := by
      rw [← hQside]
      exact_mod_cast hm
    push_cast at hm'
    have h3 : (0 : ℝ) < 3 ^ Q.scale := by positivity
    linarith
  have hunit : ∀ j, (x + LatticeProb.unit i) j = x j + if j = i then 1 else 0 := by
    intro j
    rw [Pi.add_apply]
    by_cases hj : j = i
    · rw [if_pos hj, hj, unit_apply_self]
    · rw [if_neg hj, unit_apply_ne hj]
  have hVmem : ∀ y, y ∈ V.vertices ↔ ∀ j, V.toIntegerCube.corner j ≤ y j ∧
      y j < V.toIntegerCube.corner j + (V.toIntegerCube.size : ℤ) := fun y => by
    rw [← V.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
  rcases hz with hz | hz
  · -- `x` lies in the partition cube of `z`
    have hPx : partitionCube ω z = partitionCube ω x := partitionCube_eq_of_mem hP hz
    have hxQ : x ∈ Q.vertices := by rw [hQdef, hPx]; exact mem_partitionCube hP x
    have hxV : x ∈ V.vertices := hQV hxQ
    have hVx : triadicCubeAt n x = V := triadicCubeAt_eq_of_mem hxV
    have hexc' := hexc.2
    rw [hVx] at hexc'
    by_cases hres : PartitionResolved ω V
    · have hout : x + LatticeProb.unit i ∉ V.vertices := fun h =>
        hexc' ⟨hres, (V.mem_toIntegerCube_vertices _).2 h⟩
      rw [hVmem] at hout
      push Not at hout
      obtain ⟨j, hj⟩ := hout
      have hx := (hVmem x).1 hxV j
      have hu := hunit j
      by_cases hji : j = i
      · rw [if_pos hji] at hu
        refine hmargin x hxQ j (Or.inr ?_)
        have := hj (by omega)
        omega
      · rw [if_neg hji] at hu
        have := hj (by omega)
        omega
    · exact hunres hres
  · -- `x + e_i` lies in the partition cube of `z`
    have hPx : partitionCube ω z = partitionCube ω (x + LatticeProb.unit i) :=
      partitionCube_eq_of_mem hP hz
    have hyQ : x + LatticeProb.unit i ∈ Q.vertices := by
      rw [hQdef, hPx]; exact mem_partitionCube hP _
    have hyV : x + LatticeProb.unit i ∈ V.vertices := hQV hyQ
    by_cases hxV : x ∈ V.vertices
    · have hVx : triadicCubeAt n x = V := triadicCubeAt_eq_of_mem hxV
      have hexc' := hexc.2
      rw [hVx] at hexc'
      by_cases hres : PartitionResolved ω V
      · exact absurd ⟨hres, (V.mem_toIntegerCube_vertices _).2 hyV⟩ hexc'
      · exact hunres hres
    · rw [hVmem] at hxV
      push Not at hxV
      obtain ⟨j, hj⟩ := hxV
      have hy := (hVmem _).1 hyV j
      have hu := hunit j
      by_cases hji : j = i
      · rw [if_pos hji] at hu
        refine hmargin _ hyQ j (Or.inl ?_)
        by_contra hne
        have := hj (by omega)
        omega
      · rw [if_neg hji] at hu
        have := hj (by omega)
        omega

/-- **Counting the exceptional edges near `z`.** `N(z) ≤ d 3^d size(□_𝒫(z))^d`, and `N(z) = 0`
unless `z` is exceptional. -/
theorem exceptionalEdgeCount_le (hP : PartitionEvent ω) (U : TriadicCube d) (n : ℕ)
    (z : Vertex d) :
    exceptionalEdgeCount ω U n z ≤ d * 3 ^ d * ((3 : ℝ) ^ (partitionCube ω z).scale) ^ d *
      (if ExceptionalMajorant ω n z then 1 else 0) := by
  by_cases hEM : ExceptionalMajorant ω n z
  · rw [if_pos hEM, mul_one]
    set Q := partitionCube ω z with hQdef
    set B : IntegerCube d := ⟨fun j => Q.toIntegerCube.corner j - 1, 3 ^ Q.scale + 2⟩ with hB
    have hQmem : ∀ y, y ∈ Q.vertices ↔ ∀ j, Q.toIntegerCube.corner j ≤ y j ∧
        y j < Q.toIntegerCube.corner j + ((3 ^ Q.scale : ℕ) : ℤ) := fun y => by
      rw [← Q.mem_toIntegerCube_vertices, IntegerCube.mem_vertices]
      rfl
    have hmemB : ∀ x : Vertex d, ∀ i : Fin d, (z ∈ (partitionCube ω x).vertices ∨
        z ∈ (partitionCube ω (x + LatticeProb.unit i)).vertices) → x ∈ B.vertices := by
      intro x i hz
      rw [IntegerCube.mem_vertices]
      intro j
      change Q.toIntegerCube.corner j - 1 ≤ x j ∧
        x j < Q.toIntegerCube.corner j - 1 + ((3 ^ Q.scale + 2 : ℕ) : ℤ)
      push_cast
      rcases hz with hz | hz
      · have hPx : partitionCube ω z = partitionCube ω x := partitionCube_eq_of_mem hP hz
        have hxQ : x ∈ Q.vertices := by rw [hQdef, hPx]; exact mem_partitionCube hP x
        have := (hQmem x).1 hxQ j
        push_cast at this
        constructor <;> omega
      · have hPx : partitionCube ω z = partitionCube ω (x + LatticeProb.unit i) :=
          partitionCube_eq_of_mem hP hz
        have hyQ : x + LatticeProb.unit i ∈ Q.vertices := by
          rw [hQdef, hPx]; exact mem_partitionCube hP _
        have := (hQmem _).1 hyQ j
        push_cast at this
        rw [Pi.add_apply] at this
        have hu : LatticeProb.unit i j = 0 ∨ LatticeProb.unit i j = 1 := by
          by_cases hji : j = i
          · rw [hji, unit_apply_self]; exact Or.inr rfl
          · rw [unit_apply_ne hji]; exact Or.inl rfl
        rcases hu with hu | hu <;> rw [hu] at this <;> constructor <;> omega
    have hcount : exceptionalEdgeCount ω U n z ≤
        ∑ x ∈ U.toIntegerCube.vertices, ∑ _i : Fin d, (if x ∈ B.vertices then (1 : ℝ) else 0) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (hmemB x i h1.2) h2
      · norm_num
      · exact le_rfl
    have hcard : ∑ x ∈ U.toIntegerCube.vertices, ∑ _i : Fin d,
        (if x ∈ B.vertices then (1 : ℝ) else 0) ≤ d * ((3 ^ Q.scale + 2 : ℕ) : ℝ) ^ d := by
      rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.sum_boole]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
      have h1 : (U.toIntegerCube.vertices.filter fun x => x ∈ B.vertices).card ≤
          B.vertices.card := Finset.card_le_card fun x hx => (Finset.mem_filter.1 hx).2
      rw [IntegerCube.card_vertices_eq] at h1
      have h2 : ((U.toIntegerCube.vertices.filter fun x => x ∈ B.vertices).card : ℝ) ≤
          ((B.size ^ d : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_pow] at h2
      exact h2
    have hpow : ((3 ^ Q.scale + 2 : ℕ) : ℝ) ^ d ≤ 3 ^ d * ((3 : ℝ) ^ Q.scale) ^ d := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      have h1 : (1 : ℝ) ≤ 3 ^ Q.scale := one_le_pow₀ (by norm_num)
      push_cast
      linarith
    calc exceptionalEdgeCount ω U n z ≤ _ := hcount
      _ ≤ _ := hcard
      _ ≤ d * (3 ^ d * ((3 : ℝ) ^ Q.scale) ^ d) :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg d)
      _ = _ := by ring
  · rw [if_neg hEM, mul_zero]
    refine le_of_eq (Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun i _ => ?_)
    rw [if_neg]
    rintro ⟨hexc, hz⟩
    exact hEM (exceptionalMajorant_of_isExceptionalEdge hP hexc hz)

end Rigidity.Percolation
