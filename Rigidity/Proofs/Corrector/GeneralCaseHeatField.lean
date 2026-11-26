import Rigidity.Proofs.Corrector.GeneralClusterGreen
import Rigidity.Proofs.Corrector.GeneralShiftedAnchor
import Rigidity.Proofs.Corrector.GeneralPropThreeOne

/-!
# The heat average of a coarsened gradient on `ℤᵈ` as a pairing with an edge field (Dario, (3.26)-(3.27))

In the proof of Lemma 3.3, Step 2, Dario writes `(Φ_{r²} * ∇[u]_𝒫)(0) = ⟨γ_r, ∇u⟩_{𝒞_∞}` for every
`u` of finite energy, with the field `γ_r(e') = Σ_z Φ_{r²}(z) 1{e' ∈ p_{z,z+e_i}}` built from paths
`p_{z,z'}` joining the anchors of the partition cubes of neighbouring points inside the union of the
two cubes (3.26), and bounds `|γ_r(e')|` by the heat kernel near the cube of `e'` (3.27). Here the
partition is the partition into good cubes of `ℤᵈ`, whose anchors of neighbouring cubes are joined
by open paths inside the union of the two cubes (Armstrong and Dario, Corollary 2.10,
`reachable_partitionAnchor_of_adj`); the walks are made paths by `bypass`. With `stepRegion ω z j`
that union for the step from `z` to `z + e_j` (the argument of the planar file
`DarioCoarseHeatField`):

* `coarseStepWalk`: the path from the anchor of `z` to the anchor of `z + e_j`, inside
  `stepRegion ω z j`;
* `dartField`, `pathField`: the unit field of a step and the field of a walk, with
  `⟨η, pathField p⟩ = Σ_{steps} η` (`inner_pathField`);
* `coarseHeatField`: `γ = Σ_z Φ(r², x, z) pathField(p_{z,j})`;
* `heatComp_coarse_eq_inner` ((3.26)): `Φ_{r²} * ∇_j[u]_𝒫(x) = ⟨∇u, γ⟩` for `∇u ∈ ℓ²`, when
  `Σ_z Φ(r², x, z) |stepRegion ω z j| < ∞`;
* `abs_coarseHeatField_apply_le` ((3.27)): `|γ(a)| ≤ Σ_z Φ(r², x, z) |stepRegion ω z j|`, the sum
  over the `z` whose region contains the tail of `a`.
-/

namespace Rigidity.Corrector.GeneralDim

open Filter Topology LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Section5
open scoped InnerProductSpace Classical ENNReal
open Rigidity.Poincare.GeneralDim (zdHeat zdHeat_nonneg)

variable {d : ℕ} (ω : Configuration d)

/-! ### Fields of steps and walks -/

/-- The unit field of the step from `x` to `y`: `1_{(x,i)}` if `y = x + e_i`, `-1_{(y,i)}` if
`x = y + e_i`. -/
noncomputable def dartField (x y : Vertex d) : EdgeField d :=
  ∑ i : Fin d, ((if y = x + LatticeProb.unit i then lp.single 2 (x, i) (1 : ℝ) else 0) -
    (if x = y + LatticeProb.unit i then lp.single 2 (y, i) (1 : ℝ) else 0))

theorem inner_dartField (η : EdgeField d) (x y : Vertex d) :
    ⟪η, dartField x y⟫_ℝ = signedVal η x y := by
  unfold dartField signedVal
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right]
  split_ifs <;> simp [lp.inner_single_right]

theorem dartField_add_unit (x : Vertex d) (i : Fin d) :
    dartField x (x + LatticeProb.unit i) = lp.single 2 (x, i) (1 : ℝ) := by
  unfold dartField
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, if_neg (fun e => add_unit_add_unit_ne x i i e.symm), sub_zero]
  · intro j _ hj
    rw [if_neg (fun e => add_unit_ne_add_unit (Ne.symm hj) e),
      if_neg (fun e => add_unit_add_unit_ne x i j e.symm), sub_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem dartField_unit_add (y : Vertex d) (i : Fin d) :
    dartField (y + LatticeProb.unit i) y = -lp.single 2 (y, i) (1 : ℝ) := by
  unfold dartField
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, if_neg (fun e => add_unit_add_unit_ne y i i e.symm), zero_sub]
  · intro j _ hj
    rw [if_neg (fun e => add_unit_add_unit_ne y i j e.symm),
      if_neg (fun e => add_unit_ne_add_unit (Ne.symm hj) e), sub_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The field of a step between lattice neighbours has norm one and is supported on the edge, whose
tail is one of the two endpoints. -/
theorem dartField_spec {x y : Vertex d} (h : (LatticeProb.lattice d).Adj x y) :
    ‖dartField x y‖ ≤ 1 ∧
      ∀ a : LatticeEdge d, |dartField x y a| ≤ if a.1 = x ∨ a.1 = y then 1 else 0 := by
  obtain ⟨i, hi | hi⟩ := LatticeProb.Graph.Zd.adj_iff.1 h
  · rw [hi, dartField_add_unit]
    refine ⟨by rw [lp.norm_single (by norm_num)]; simp, fun a => ?_⟩
    rw [lp.single_apply]
    by_cases ha : a = (x, i)
    · subst ha
      simp
    · rw [Pi.single_eq_of_ne ha]
      simp only [abs_zero]
      split_ifs <;> norm_num
  · have hx : x = y + LatticeProb.unit i := by rw [hi]; abel
    rw [hx, dartField_unit_add]
    refine ⟨by rw [norm_neg, lp.norm_single (by norm_num)]; simp, fun a => ?_⟩
    rw [lp.coeFn_neg, Pi.neg_apply, abs_neg, lp.single_apply]
    by_cases ha : a = (y, i)
    · subst ha
      simp
    · rw [Pi.single_eq_of_ne ha]
      simp only [abs_zero]
      split_ifs <;> norm_num

/-- The field `Σ_{steps (x, y) of p} dartField x y` of a walk. -/
noncomputable def pathField {x y : Vertex d} (p : (openGraph ω).Walk x y) : EdgeField d :=
  (p.darts.map fun d => dartField d.fst d.snd).sum

theorem inner_pathField (η : EdgeField d) {x y : Vertex d} (p : (openGraph ω).Walk x y) :
    ⟪η, pathField ω p⟫_ℝ = walkSum ω η p := by
  induction p with
  | nil => simp [pathField, walkSum]
  | cons hadj p ih =>
    unfold pathField walkSum at *
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    rw [inner_add_right, inner_dartField, ih]

theorem pathField_spec {x y : Vertex d} (p : (openGraph ω).Walk x y) :
    ‖pathField ω p‖ ≤ p.length ∧
      ∀ a : LatticeEdge d, |pathField ω p a| ≤ if a.1 ∈ p.support then (p.length : ℝ) else 0 := by
  induction p with
  | nil => simp [pathField]
  | @cons u v w hadj p ih =>
    obtain ⟨ihn, iha⟩ := ih
    have hd := dartField_spec (openGraph_le ω hadj)
    have hv : v ∈ p.support := p.start_mem_support
    have hlen : (0 : ℝ) ≤ p.length := Nat.cast_nonneg _
    unfold pathField at ihn iha ⊢
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons,
      SimpleGraph.Walk.length_cons, SimpleGraph.Walk.support_cons, List.mem_cons]
    refine ⟨(norm_add_le _ _).trans ?_, fun a => ?_⟩
    · rw [Nat.cast_add, Nat.cast_one]
      linarith [hd.1]
    · rw [lp.coeFn_add, Pi.add_apply]
      refine (abs_add_le _ _).trans ?_
      have h1 := hd.2 a
      have h2 := iha a
      by_cases hA : a.1 = u ∨ a.1 ∈ p.support
      · rw [if_pos hA]
        have h1' : |dartField u v a| ≤ 1 := by
          split_ifs at h1 <;> linarith
        have h2' : |(List.map (fun d => dartField d.fst d.snd) p.darts).sum a| ≤ p.length := by
          split_ifs at h2 <;> linarith
        rw [Nat.cast_add, Nat.cast_one]
        linarith
      · rw [if_neg hA]
        obtain ⟨hu, hp⟩ := not_or.1 hA
        have hav : a.1 ≠ v := fun e => hp (e ▸ hv)
        rw [if_neg (by tauto)] at h1
        rw [if_neg hp] at h2
        linarith

/-! ### The paths between the anchors of neighbouring partition cubes -/

theorem abs_sub_add_unit_le (z : Vertex d) (j i : Fin d) :
    |z i - (z + LatticeProb.unit j) i| ≤ 1 ∧ |(z + LatticeProb.unit j) i - z i| ≤ 1 := by
  simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
  split_ifs <;> simp

/-- The union of the partition cubes of `z` and `z + e_j`. -/
noncomputable def stepRegion (z : Vertex d) (j : Fin d) : Finset (Vertex d) :=
  (partitionCube ω z).toIntegerCube.vertices ∪
    (partitionCube ω (z + LatticeProb.unit j)).toIntegerCube.vertices

theorem mem_stepRegion_iff {z w : Vertex d} {j : Fin d} :
    w ∈ stepRegion ω z j ↔ w ∈ (partitionCube ω z).vertices ∨
      w ∈ (partitionCube ω (z + LatticeProb.unit j)).vertices := by
  rw [stepRegion, Finset.mem_union, TriadicCube.mem_toIntegerCube_vertices,
    TriadicCube.mem_toIntegerCube_vertices]

/-- The vertices of a walk inside a set lie in the set. -/
theorem mem_of_mem_support_openIn {B : Set (Vertex d)} {a b : Vertex d}
    (q : (Rigidity.External.openIn ω B).Walk a b) : a ∈ B → ∀ w ∈ q.support, w ∈ B := by
  induction q with
  | nil =>
    intro ha w hw
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
    rw [hw]
    exact ha
  | cons h q ih =>
    intro ha w hw
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    exacts [ha, ih h.2.2 w hw]

theorem exists_coarseStepWalk [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) (j : Fin d) :
    ∃ q : (openGraph ω).Walk (partitionAnchor ω z) (partitionAnchor ω (z + LatticeProb.unit j)),
      ∀ w ∈ q.support, w ∈ stepRegion ω z j := by
  have hadj : (nearestNeighborGraph d).Adj z (z + LatticeProb.unit j) :=
    LatticeProb.Graph.Zd.adj_iff.2 ⟨j, Or.inl rfl⟩
  obtain ⟨q⟩ := reachable_partitionAnchor_of_adj (Nat.pos_of_ne_zero (NeZero.ne d)) hP hadj
  have hle : Rigidity.External.openIn ω ((partitionCube ω z).vertices ∪
      (partitionCube ω (z + LatticeProb.unit j)).vertices) ≤ openGraph ω := fun _ _ h => h.1
  refine ⟨q.mapLe hle, fun w hw => (mem_stepRegion_iff ω).2 ?_⟩
  rw [SimpleGraph.Walk.support_mapLe] at hw
  exact mem_of_mem_support_openIn ω q (Or.inl (partitionAnchor_mem hP z)) w hw

/-- The path from the anchor of `z` to the anchor of `z + e_j`, inside `stepRegion ω z j`. -/
noncomputable def coarseStepWalk [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) (j : Fin d) :
    (openGraph ω).Walk (partitionAnchor ω z) (partitionAnchor ω (z + LatticeProb.unit j)) :=
  (Classical.choose (exists_coarseStepWalk hP z j)).bypass

theorem coarseStepWalk_support [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) (j : Fin d) : ∀ w ∈ (coarseStepWalk hP z j).support, w ∈ stepRegion ω z j :=
  fun w hw => Classical.choose_spec (exists_coarseStepWalk hP z j) w
    (SimpleGraph.Walk.support_bypass_subset_support _ hw)

theorem length_coarseStepWalk_le [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    (z : Vertex d) (j : Fin d) : (coarseStepWalk hP z j).length ≤ (stepRegion ω z j).card := by
  set p := coarseStepWalk hP z j
  have hnd : p.support.Nodup := (SimpleGraph.Walk.bypass_isPath _).support_nodup
  have hsub : p.support.toFinset ⊆ stepRegion ω z j := fun w hw =>
    coarseStepWalk_support hP z j w (List.mem_toFinset.1 hw)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, SimpleGraph.Walk.length_support] at hcard
  omega

/-! ### The field `γ` and the identity (3.26) -/

/-- **Dario's field `γ_r`**: `Σ_z Φ(r², x, z) pathField(p_{z,j})`. -/
noncomputable def coarseHeatField [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) (r : ℝ)
    (x : Vertex d) (j : Fin d) : EdgeField d :=
  ∑' z, zdHeat d (r ^ 2) x z • pathField ω (coarseStepWalk hP z j)

theorem norm_heat_smul_pathField_le [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) (r : ℝ)
    (x z : Vertex d) (j : Fin d) :
    ‖zdHeat d (r ^ 2) x z • pathField ω (coarseStepWalk hP z j)‖ ≤
      zdHeat d (r ^ 2) x z * (stepRegion ω z j).card := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zdHeat_nonneg (sq_nonneg r) x z)]
  refine mul_le_mul_of_nonneg_left ?_ (zdHeat_nonneg (sq_nonneg r) x z)
  exact (pathField_spec ω _).1.trans (by exact_mod_cast length_coarseStepWalk_le hP z j)

theorem summable_heat_smul_pathField [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    {r : ℝ} {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card) :
    Summable fun z => zdHeat d (r ^ 2) x z • pathField ω (coarseStepWalk hP z j) :=
  Summable.of_norm_bounded hS fun z => norm_heat_smul_pathField_le hP r x z j

theorem isGradOf_edgeGrad (u : Vertex d → ℝ) : IsGradOf ω (edgeGrad ω u) u := fun a ha => by
  simp [edgeGrad, ha]

/-- **Dario, (3.26)**: for `u` with `∇u ∈ ℓ²`, `Φ_{r²} * ∇_j[u]_𝒫(x) = ⟨∇u, γ⟩`. -/
theorem heatComp_coarse_eq_inner [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω)
    {u : Vertex d → ℝ} (hu : Memℓp (edgeGrad ω u) 2) {r : ℝ} {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card) :
    heatComp (fun z => u (partitionAnchor ω z)) r x j =
      ⟪(⟨edgeGrad ω u, hu⟩ : EdgeField d), coarseHeatField hP r x j⟫_ℝ := by
  set g : EdgeField d := ⟨edgeGrad ω u, hu⟩ with hg
  unfold coarseHeatField heatComp
  have hmap := (innerSL ℝ g).map_tsum (summable_heat_smul_pathField hP hS)
  simp only [innerSL_apply_apply] at hmap
  rw [hmap]
  refine tsum_congr fun z => ?_
  rw [real_inner_smul_right, inner_pathField]
  have hw := walkSum_eq_of_isGradOf ω (isGradOf_edgeGrad ω u) (coarseStepWalk hP z j)
  rw [show ((g : LatticeEdge d → ℝ)) = edgeGrad ω u from rfl, hw]

theorem coarseHeatField_apply [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) {r : ℝ}
    {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card) (a : LatticeEdge d) :
    coarseHeatField hP r x j a =
      ∑' z, zdHeat d (r ^ 2) x z * pathField ω (coarseStepWalk hP z j) a := by
  have hmap := (innerSL ℝ (lp.single 2 a (1 : ℝ) : EdgeField d)).map_tsum
    (summable_heat_smul_pathField hP hS)
  simp only [innerSL_apply_apply] at hmap
  rw [real_inner_comm, lp.inner_single_right, Real.inner_apply, mul_one] at hmap
  unfold coarseHeatField
  rw [hmap]
  refine tsum_congr fun z => ?_
  rw [real_inner_comm, lp.inner_single_right, Real.inner_apply, mul_one, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]

/-- **Dario, (3.27)**: `|γ(a)| ≤ Σ_z Φ(r², x, z) |stepRegion ω z j|` over the `z` whose region
contains the tail of `a`. -/
theorem abs_coarseHeatField_apply_le [NeZero d] {ω : Configuration d} (hP : PartitionEvent ω) {r : ℝ}
    {x : Vertex d} {j : Fin d}
    (hS : Summable fun z => zdHeat d (r ^ 2) x z * (stepRegion ω z j).card) (a : LatticeEdge d) :
    |coarseHeatField hP r x j a| ≤
      ∑' z, zdHeat d (r ^ 2) x z *
        (if a.1 ∈ stepRegion ω z j then ((stepRegion ω z j).card : ℝ) else 0) := by
  have hb : ∀ z, |zdHeat d (r ^ 2) x z * pathField ω (coarseStepWalk hP z j) a| ≤
      zdHeat d (r ^ 2) x z *
        (if a.1 ∈ stepRegion ω z j then ((stepRegion ω z j).card : ℝ) else 0) := by
    intro z
    rw [abs_mul, abs_of_nonneg (zdHeat_nonneg (sq_nonneg r) x z)]
    refine mul_le_mul_of_nonneg_left ?_ (zdHeat_nonneg (sq_nonneg r) x z)
    refine ((pathField_spec ω _).2 a).trans ?_
    split_ifs with h1 h2 h2
    · exact Nat.cast_le.mpr (length_coarseStepWalk_le hP z j)
    · exact absurd (coarseStepWalk_support hP z j _ h1) h2
    · positivity
    · exact le_rfl
  have hS' : Summable fun z => zdHeat d (r ^ 2) x z *
      (if a.1 ∈ stepRegion ω z j then ((stepRegion ω z j).card : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) hS
    · exact mul_nonneg (zdHeat_nonneg (sq_nonneg r) x z) (by split_ifs <;> positivity)
    · refine mul_le_mul_of_nonneg_left ?_ (zdHeat_nonneg (sq_nonneg r) x z)
      split_ifs <;> simp
  rw [coarseHeatField_apply hP hS a, ← Real.norm_eq_abs]
  have hsn : Summable fun z =>
      ‖zdHeat d (r ^ 2) x z * pathField ω (coarseStepWalk hP z j) a‖ :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg _)
      (fun z => by rw [Real.norm_eq_abs]; exact hb z) hS'
  refine (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum (fun z => ?_) hsn hS')
  rw [Real.norm_eq_abs]
  exact hb z

end Rigidity.Corrector.GeneralDim
