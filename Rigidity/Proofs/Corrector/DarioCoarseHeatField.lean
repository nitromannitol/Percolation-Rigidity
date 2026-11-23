import Rigidity.Proofs.Corrector.DarioClusterGreen

/-!
# The heat average of a coarsened gradient as a pairing with an edge field (Dario, (3.26)-(3.27))

In the proof of Lemma 3.3, Step 2, Dario writes `(Φ_{r²} * ∇[u]_𝒫)(0) = ⟨γ_r, ∇u⟩_{𝒞_∞}` for every
`u` of finite energy, with the field `γ_r(e') = Σ_z Φ_{r²}(z) 1{e' ∈ p_{z,z+e_i}}` built from paths
`p_{z,z'}` joining the anchors of the partition cubes of neighbouring points inside the union of the
two cubes (3.26), and bounds `|γ_r(e')|` by the heat kernel near the cube of `e'` (3.27). Here the
partition is main's planar partition, whose anchors of neighbouring cubes are joined by open walks
inside the square of side `9s` around the smaller cube (`reachIn_planarAnchor_of_near`); the walks
are made paths by `bypass`. With `stepRegion ω z j` that square for the step from `z` to `z + e_j`:

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

namespace Rigidity.Corrector

open Filter Topology LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Section5
open scoped InnerProductSpace Classical ENNReal

variable (ω : Configuration 2)

/-! ### Fields of steps and walks -/

/-- The unit field of the step from `x` to `y`: `1_{(x,i)}` if `y = x + e_i`, `-1_{(y,i)}` if
`x = y + e_i`. -/
noncomputable def dartField (x y : Vertex 2) : EdgeField :=
  ∑ i : Fin 2, ((if y = x + LatticeProb.unit i then lp.single 2 (x, i) (1 : ℝ) else 0) -
    (if x = y + LatticeProb.unit i then lp.single 2 (y, i) (1 : ℝ) else 0))

theorem inner_dartField (η : EdgeField) (x y : Vertex 2) :
    ⟪η, dartField x y⟫_ℝ = signedVal η x y := by
  unfold dartField signedVal
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right]
  split_ifs <;> simp [lp.inner_single_right]

theorem dartField_add_unit (x : Vertex 2) (i : Fin 2) :
    dartField x (x + LatticeProb.unit i) = lp.single 2 (x, i) (1 : ℝ) := by
  unfold dartField
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, if_neg (fun e => add_unit_add_unit_ne x i i e.symm), sub_zero]
  · intro j _ hj
    rw [if_neg (fun e => add_unit_ne_add_unit (Ne.symm hj) e),
      if_neg (fun e => add_unit_add_unit_ne x i j e.symm), sub_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem dartField_unit_add (y : Vertex 2) (i : Fin 2) :
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
theorem dartField_spec {x y : Vertex 2} (h : (LatticeProb.lattice 2).Adj x y) :
    ‖dartField x y‖ ≤ 1 ∧
      ∀ a : LatticeEdge, |dartField x y a| ≤ if a.1 = x ∨ a.1 = y then 1 else 0 := by
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
noncomputable def pathField {x y : Vertex 2} (p : (openGraph ω).Walk x y) : EdgeField :=
  (p.darts.map fun d => dartField d.fst d.snd).sum

theorem inner_pathField (η : EdgeField) {x y : Vertex 2} (p : (openGraph ω).Walk x y) :
    ⟪η, pathField ω p⟫_ℝ = walkSum ω η p := by
  induction p with
  | nil => simp [pathField, walkSum]
  | cons hadj p ih =>
    unfold pathField walkSum at *
    simp only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons]
    rw [inner_add_right, inner_dartField, ih]

theorem pathField_spec {x y : Vertex 2} (p : (openGraph ω).Walk x y) :
    ‖pathField ω p‖ ≤ p.length ∧
      ∀ a : LatticeEdge, |pathField ω p a| ≤ if a.1 ∈ p.support then (p.length : ℝ) else 0 := by
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

/-- The square of side `9s` around the smaller of the partition cubes of `z` and `z + e_j`. -/
noncomputable def stepRegion (z : Vertex 2) (j : Fin 2) : Finset (Vertex 2) :=
  if (planarPartCube ω z).scale ≤ (planarPartCube ω (z + LatticeProb.unit j)).scale then
    (planarPartCube ω z).ninefold.vertices
  else (planarPartCube ω (z + LatticeProb.unit j)).ninefold.vertices

theorem abs_sub_add_unit_le (z : Vertex 2) (j : Fin 2) (i : Fin 2) :
    |z i - (z + LatticeProb.unit j) i| ≤ 1 ∧ |(z + LatticeProb.unit j) i - z i| ≤ 1 := by
  simp only [Pi.add_apply, LatticeProb.unit, Pi.single_apply]
  split_ifs <;> simp

theorem reachIn_coarseStep {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (z : Vertex 2)
    (j : Fin 2) :
    ReachIn ω ↑(stepRegion ω z j) (planarCoarseAnchor ω z)
      (planarCoarseAnchor ω (z + LatticeProb.unit j)) := by
  have hnear := fun i => (abs_sub_add_unit_le z j i).1
  have hnear' := fun i => (abs_sub_add_unit_le z j i).2
  obtain ⟨h1, h2⟩ := planarPartCube_scales_close hP hnear
  unfold stepRegion planarCoarseAnchor
  split_ifs with hle
  · exact TriadicCube.reachIn_planarAnchor_of_near (planarPartCube_meshed hP z).1
      (planarPartCube_meshed hP _).1 (planarPartCube_large hP z) hle h2
      (planarPartCube_spec hP z).1 (planarPartCube_spec hP _).1 hnear
  · exact (TriadicCube.reachIn_planarAnchor_of_near (planarPartCube_meshed hP _).1
      (planarPartCube_meshed hP z).1 (planarPartCube_large hP _) (le_of_lt (not_le.1 hle)) h1
      (planarPartCube_spec hP _).1 (planarPartCube_spec hP z).1 hnear').symm

/-- The path from the anchor of `z` to the anchor of `z + e_j`, inside `stepRegion ω z j`. -/
noncomputable def coarseStepWalk {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (z : Vertex 2) (j : Fin 2) :
    (openGraph ω).Walk (planarCoarseAnchor ω z) (planarCoarseAnchor ω (z + LatticeProb.unit j)) :=
  (Classical.choose (reachIn_coarseStep hP z j)).bypass

theorem coarseStepWalk_support {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (z : Vertex 2)
    (j : Fin 2) : ∀ w ∈ (coarseStepWalk hP z j).support, w ∈ stepRegion ω z j := fun w hw =>
  Finset.mem_coe.1 (Classical.choose_spec (reachIn_coarseStep hP z j) w
    (SimpleGraph.Walk.support_bypass_subset_support _ hw))

theorem length_coarseStepWalk_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    (z : Vertex 2) (j : Fin 2) : (coarseStepWalk hP z j).length ≤ (stepRegion ω z j).card := by
  set p := coarseStepWalk hP z j
  have hnd : p.support.Nodup := (SimpleGraph.Walk.bypass_isPath _).support_nodup
  have hsub : p.support.toFinset ⊆ stepRegion ω z j := fun w hw =>
    coarseStepWalk_support hP z j w (List.mem_toFinset.1 hw)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, SimpleGraph.Walk.length_support] at hcard
  omega

/-! ### The field `γ` and the identity (3.26) -/

/-- **Dario's field `γ_r`**: `Σ_z Φ(r², x, z) pathField(p_{z,j})`. -/
noncomputable def coarseHeatField {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (r : ℝ)
    (x : Vertex 2) (j : Fin 2) : EdgeField :=
  ∑' z, latticeHeat (r ^ 2) x z • pathField ω (coarseStepWalk hP z j)

theorem norm_heat_smul_pathField_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) (r : ℝ)
    (x z : Vertex 2) (j : Fin 2) :
    ‖latticeHeat (r ^ 2) x z • pathField ω (coarseStepWalk hP z j)‖ ≤
      latticeHeat (r ^ 2) x z * (stepRegion ω z j).card := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x z)]
  refine mul_le_mul_of_nonneg_left ?_ (latticeHeat_nonneg (sq_nonneg r) x z)
  exact (pathField_spec ω _).1.trans (by exact_mod_cast length_coarseStepWalk_le hP z j)

theorem summable_heat_smul_pathField {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {r : ℝ} {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card) :
    Summable fun z => latticeHeat (r ^ 2) x z • pathField ω (coarseStepWalk hP z j) :=
  Summable.of_norm_bounded hS fun z => norm_heat_smul_pathField_le hP r x z j

theorem isGradOf_edgeGrad (u : Vertex 2 → ℝ) : IsGradOf ω (edgeGrad ω u) u := fun a ha => by
  simp [edgeGrad, ha]

/-- **Dario, (3.26)**: for `u` with `∇u ∈ ℓ²`, `Φ_{r²} * ∇_j[u]_𝒫(x) = ⟨∇u, γ⟩`. -/
theorem heatComp_coarse_eq_inner {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {u : Vertex 2 → ℝ} (hu : Memℓp (edgeGrad ω u) 2) {r : ℝ} {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card) :
    heatComp (fun z => u (planarCoarseAnchor ω z)) r x j =
      ⟪(⟨edgeGrad ω u, hu⟩ : EdgeField), coarseHeatField hP r x j⟫_ℝ := by
  set g : EdgeField := ⟨edgeGrad ω u, hu⟩ with hg
  unfold coarseHeatField heatComp
  have hmap := (innerSL ℝ g).map_tsum (summable_heat_smul_pathField hP hS)
  simp only [innerSL_apply_apply] at hmap
  rw [hmap]
  refine tsum_congr fun z => ?_
  rw [real_inner_smul_right, inner_pathField]
  have hw := walkSum_eq_of_isGradOf ω (isGradOf_edgeGrad ω u) (coarseStepWalk hP z j)
  rw [show ((g : LatticeEdge → ℝ)) = edgeGrad ω u from rfl, hw]

theorem coarseHeatField_apply {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {r : ℝ}
    {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card) (a : LatticeEdge) :
    coarseHeatField hP r x j a =
      ∑' z, latticeHeat (r ^ 2) x z * pathField ω (coarseStepWalk hP z j) a := by
  have hmap := (innerSL ℝ (lp.single 2 a (1 : ℝ) : EdgeField)).map_tsum
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
theorem abs_coarseHeatField_apply_le {ω : Configuration 2} (hP : PlanarPartitionEvent ω) {r : ℝ}
    {x : Vertex 2} {j : Fin 2}
    (hS : Summable fun z => latticeHeat (r ^ 2) x z * (stepRegion ω z j).card) (a : LatticeEdge) :
    |coarseHeatField hP r x j a| ≤
      ∑' z, latticeHeat (r ^ 2) x z *
        (if a.1 ∈ stepRegion ω z j then ((stepRegion ω z j).card : ℝ) else 0) := by
  have hb : ∀ z, |latticeHeat (r ^ 2) x z * pathField ω (coarseStepWalk hP z j) a| ≤
      latticeHeat (r ^ 2) x z *
        (if a.1 ∈ stepRegion ω z j then ((stepRegion ω z j).card : ℝ) else 0) := by
    intro z
    rw [abs_mul, abs_of_nonneg (latticeHeat_nonneg (sq_nonneg r) x z)]
    refine mul_le_mul_of_nonneg_left ?_ (latticeHeat_nonneg (sq_nonneg r) x z)
    refine ((pathField_spec ω _).2 a).trans ?_
    split_ifs with h1 h2 h2
    · exact Nat.cast_le.mpr (length_coarseStepWalk_le hP z j)
    · exact absurd (coarseStepWalk_support hP z j _ h1) h2
    · positivity
    · exact le_rfl
  have hS' : Summable fun z => latticeHeat (r ^ 2) x z *
      (if a.1 ∈ stepRegion ω z j then ((stepRegion ω z j).card : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) hS
    · exact mul_nonneg (latticeHeat_nonneg (sq_nonneg r) x z) (by split_ifs <;> positivity)
    · refine mul_le_mul_of_nonneg_left ?_ (latticeHeat_nonneg (sq_nonneg r) x z)
      split_ifs <;> simp
  rw [coarseHeatField_apply hP hS a, ← Real.norm_eq_abs]
  have hsn : Summable fun z =>
      ‖latticeHeat (r ^ 2) x z * pathField ω (coarseStepWalk hP z j) a‖ :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg _)
      (fun z => by rw [Real.norm_eq_abs]; exact hb z) hS'
  refine (norm_tsum_le_tsum_norm hsn).trans (Summable.tsum_le_tsum (fun z => ?_) hsn hS')
  rw [Real.norm_eq_abs]
  exact hb z

end Rigidity.Corrector
