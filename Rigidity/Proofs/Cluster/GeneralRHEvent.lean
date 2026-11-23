import Rigidity.Proofs.Cluster.GeneralRHMeyers
import Rigidity.Proofs.Cluster.GeneralRHExit
import Rigidity.Proofs.Cluster.MeyersPartitionBox

/-!
# The reverse Hölder inequality on a cube whose partition cubes are small, in every dimension

Lemma 3.6 of Armstrong and Dario in the form of the local family of `GeneralRHLocal`: if the
partition cubes of the vertices of the triple `3□` of `□ = cube k x` have scale at most `k - 2` and
`∑_{3□} partitionReach^{2d(d+2)} ≤ C_G |3□|`, then `RHCube A₀ ω k x` holds with a deterministic
constant (`rhCube_of_scales`).

The cluster `𝒞(3□)` of the integer cube of the triple carries the Sobolev inequality of
`exists_clusterSobolevTwo_box` with the weight `3^ρ` of the reach scale (`exists_box_rh_cube`), and
the reverse Hölder inequality holds for the functions harmonic on it
(`reverse_holder_clusterEnergy_local`). A set `C ⊆ 3□` closed under the open edges inside `3□`
contains `𝒞(3□)` as soon as it meets it, since `𝒞(3□)` is connected inside `3□`. A vertex of
`C ∩ □` outside `𝒞(3□)` lies in a part of `C` from which no open edge leaves `3□`: otherwise an open
path from it leaves the box of its partition cube, which lies inside `3□`, and
`reachable_partitionAnchor_of_exit` joins it to its anchor inside `3□`
(`mem_partitionBoxCluster_of_exit`). On such a part every open edge stays in the part and the
harmonic function has zero energy there, by the Caccioppoli inequality
(`clusterGradSq_eq_zero_of_closed`). The planar case is `PlanarRHEvent`.
-/

namespace Rigidity.Proofs.Cluster.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal

variable {d : ℕ} {ω : Configuration d}

/-- **The cluster of the triple with its Sobolev weight.** -/
theorem exists_box_rh_cube (hd : 2 ≤ d) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {CG : ℝ}, 0 ≤ CG → ∀ (ω : Configuration d), PartitionEvent ω →
      ∀ (k : ℕ) (y : Vertex d),
      (∀ z ∈ enl 1 k y, (partitionCube ω z).scale + 1 ≤ k) →
      ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) ≤
        ENNReal.ofReal CG * 3 ^ ((k + 1) * d) →
      ∃ size : Vertex d → ℝ, (∀ x, 0 ≤ size x) ∧
        partitionBoxCluster ω (enlSquare k y) ⊆ enl 1 k y ∧
        (∀ z ∈ partitionBoxCluster ω (enlSquare k y), ∀ w, (openGraph ω).Adj z w →
          w ∈ enl 1 k y → w ∈ partitionBoxCluster ω (enlSquare k y)) ∧
        ClusterSobolevTwo ω (partitionBoxCluster ω (enlSquare k y)) size CS ∧
        ∑ x ∈ partitionBoxCluster ω (enlSquare k y), size x ^ (2 * (d : ℝ) * ((d : ℝ) + 2)) ≤
          CG * (3 : ℝ) ^ ((k + 1) * d) := by
  have hd0 : 0 < d := by omega
  obtain ⟨K₀, hK₀, hSobK⟩ := exists_clusterSobolevTwo_box hd
  refine ⟨K₀, hK₀, fun {CG} hCG ω hP k y hres hreach => ?_⟩
  have hBr := partitionBoxResolved_enlSquare hP hres
  set B := enlSquare k y with hBdef
  have hBpos : 0 < B.size := by
    change 0 < 3 ^ (k + 1)
    positivity
  set U' := partitionBoxCluster ω B with hU'def
  set P := partitionBoxCoarseData hd0 hP B hBr with hPdef
  set size : Vertex d → ℝ := fun z => (3 : ℝ) ^ P.reachScale z with hsizedef
  have hU'E : ∀ z ∈ U', z ∈ enl 1 k y := fun z hz =>
    mem_enlSquare_vertices.1 (Finset.mem_filter.1 hz).1
  have hN : (2 * (d : ℝ) * ((d : ℝ) + 2)) = ((2 * d * (d + 2) : ℕ) : ℝ) := by push_cast; ring
  have hmomR : ∑ z ∈ U', size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2)) ≤
      CG * (3 : ℝ) ^ ((k + 1) * d) := by
    have hterm : ∀ z ∈ U', ENNReal.ofReal (size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2))) ≤
        partitionReach ω z ^ (2 * d * (d + 2)) := by
      intro z hz
      rw [hN, Real.rpow_natCast, hsizedef, ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      exact pow_le_pow_left₀ zero_le (three_pow_reachScale_le_partitionReach_box hd0 hP hBr hz) _
    have hsum : ENNReal.ofReal (∑ z ∈ U', size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2))) ≤
        ENNReal.ofReal (CG * (3 : ℝ) ^ ((k + 1) * d)) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun z _ => Real.rpow_nonneg (by positivity) _]
      calc ∑ z ∈ U', ENNReal.ofReal (size z ^ (2 * (d : ℝ) * ((d : ℝ) + 2)))
          ≤ ∑ z ∈ U', partitionReach ω z ^ (2 * d * (d + 2)) := Finset.sum_le_sum hterm
        _ ≤ ∑ z ∈ enl 1 k y, partitionReach ω z ^ (2 * d * (d + 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hU'E fun _ _ _ => zero_le
        _ ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * d) := hreach
        _ = ENNReal.ofReal (CG * (3 : ℝ) ^ ((k + 1) * d)) := by
            rw [ENNReal.ofReal_mul hCG, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hsum
  refine ⟨size, fun z => by positivity, hU'E, ?_, hSobK ω hP B hBpos hBr, hmomR⟩
  intro z hz w hadj hw
  exact mem_partitionBoxCluster_of_adj hd0 hP hBr hz hadj (mem_enlSquare_vertices.2 hw)

/-- The points within `r + 1` of a vertex of `□ = cube k x₀`, `r` the radius of its partition
cube, lie in the triple `3□` when the partition cube has scale at most `k - 2`. -/
theorem mem_enl_of_near_partitionCube {k : ℕ} {x₀ z y : Vertex d}
    (hz : z ∈ cube k x₀) (hQ : (partitionCube ω z).scale + 2 ≤ k)
    (hy : ∀ i, |y i - z i| ≤ (partitionCube ω z).radius + 1) : y ∈ enl 1 k x₀ := by
  have hsr := (partitionCube ω z).side_eq_two_mul_radius_add_one
  have hN := (partitionCube ω z).natCast_three_pow_scale
  have h3 : (3 : ℤ) ^ ((partitionCube ω z).scale + 2) ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hQ
  have h4 := two_mul_halfSide_add_one k
  have h5 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have h6 : (3 : ℤ) ^ ((partitionCube ω z).scale + 2) = 9 * 3 ^ (partitionCube ω z).scale := by
    ring
  push_cast at hN
  rw [enl, mem_box]
  rw [cube, mem_box] at hz
  intro i
  have h1 := hy i
  have h2 := hz i
  calc |y i - center k x₀ i| ≤ |y i - z i| + |z i - center k x₀ i| := abs_sub_le _ _ _
    _ ≤ halfSide (k + 1) := by
      rw [h5]
      have h7 : (0 : ℤ) < 3 ^ (partitionCube ω z).scale := by positivity
      linarith

/-- **A vertex of `□` joined inside `3□` to a point with an open edge leaving `3□` is in the cluster
of the triple.** -/
theorem mem_partitionBoxCluster_of_exit (hd : 0 < d) (hP : PartitionEvent ω) {k : ℕ}
    {x₀ z a w : Vertex d} (hz : z ∈ cube k x₀) (hQ : (partitionCube ω z).scale + 2 ≤ k)
    (hza : (openIn ω ↑(enl 1 k x₀)).Reachable z a) (haw : (openGraph ω).Adj a w)
    (hw : w ∉ enl 1 k x₀) :
    z ∈ partitionBoxCluster ω (enlSquare k x₀) := by
  set Q := partitionCube ω z with hQdef
  set box : Set (Vertex d) := {y | ∀ i, |y i - z i| ≤ Q.radius} with hboxdef
  have hzbox : z ∈ box := by
    rw [hboxdef, Set.mem_setOf_eq]
    intro i
    rw [sub_self, abs_zero]
    have := Q.side_eq_two_mul_radius_add_one
    have := Q.natCast_three_pow_scale
    have : (0 : ℤ) < 3 ^ Q.scale := by positivity
    push_cast at *
    omega
  have hboxE : box ⊆ ↑(enl 1 k x₀) := fun y hy =>
    mem_enl_of_near_partitionCube hz hQ fun i =>
      (hy i).trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨u, hzu, hu⟩ := exists_reachable_inter_of_reachable_openIn hza hzbox
  have hex : ∃ v, v ∉ box ∧ (openGraph ω).Adj u v := by
    rcases hu with rfl | ⟨v, hv, huv⟩
    · exfalso
      have hu' : u ∈ box := (mem_of_reachable_openIn_of_mem (⟨by
        exact hboxE hzbox, hzbox⟩ : z ∈ ↑(enl 1 k x₀) ∩ box) hzu).2
      exact hw (mem_enl_of_near_partitionCube hz hQ fun i => by
        have h1 := abs_sub_le_one_of_openGraph_adj haw i
        have h2 := hu' i
        have h3 := abs_sub_le (w i) (u i) (z i)
        rw [abs_sub_comm (w i) (u i)] at h3
        linarith)
    · exact ⟨v, hv, huv.1⟩
  obtain ⟨v, hv, huv⟩ := hex
  have hzu' : (openIn ω box).Reachable z u :=
    reachable_openIn_mono (fun y hy => hy.2) hzu
  have h := reachable_partitionAnchor_of_exit hd hP hzu' huv hv
  have hsub : (Q.parent.vertices : Set (Vertex d)) ∪ box ⊆ ↑(enlSquare k x₀).vertices := by
    rintro y (hy | hy)
    · have hsub := TriadicCube.vertices_subset_of_mem_of_scale_le (R := ⟨k, idx k x₀⟩)
        (Q.vertices_subset_parent (mem_partitionCube hP z)) (mem_triadicCube_idx_iff.2 hz)
        (show Q.scale + 1 ≤ k by omega) hy
      exact mem_enlSquare_vertices.2 (cube_subset_enl 1 k x₀ (mem_triadicCube_idx_iff.1 hsub))
    · exact mem_enlSquare_vertices.2 (hboxE hy)
  exact mem_partitionBoxCluster.2 ⟨mem_enlSquare_vertices.2 (cube_subset_enl 1 k x₀ hz),
    reachable_openIn_mono hsub h⟩

/-- A set closed under the open edges inside `S` contains every point joined inside `S` to one of
its points. -/
theorem mem_of_reachable_openIn_of_closed {S : Set (Vertex d)} {C : Finset (Vertex d)}
    (hcl : ∀ z ∈ C, ∀ w, (openGraph ω).Adj z w → w ∈ S → w ∈ C) {a b : Vertex d}
    (h : (openIn ω S).Reachable a b) (ha : a ∈ C) : b ∈ C := by
  obtain ⟨W⟩ := h
  induction W with
  | nil => exact ha
  | cons hadj _ ih => exact ih (hcl _ ha _ hadj.1 hadj.2.2)

/-- **Zero energy on a closed set.** On a finite set closed under all open edges, a function
harmonic at every point has zero energy, by the Caccioppoli inequality with an arbitrary radius. -/
theorem clusterGradSq_eq_zero_of_closed (hd : 0 < d) (D : Finset (Vertex d))
    (hD : ∀ z ∈ D, ∀ w, (openGraph ω).Adj z w → w ∈ D) (u : Vertex d → ℝ)
    (hu : ∀ z ∈ D, openLaplacian ω u z = 0) {z : Vertex d} (hz : z ∈ D) :
    clusterGradSq ω D u z = 0 := by
  set S := ∑ x ∈ D, clusterGradSq ω D u x with hS
  set M := ∑ x ∈ D.filter (fun x => ¬ (x ∈ D ∧ ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ D)),
    u x ^ 2 with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hcac : ∀ r : ℝ, 0 < r → S ≤ 8 * d / r ^ 2 * M := fun r hr =>
    caccioppoli_cluster ω D D subset_rfl hr (fun x _ z hz hex => by
      obtain ⟨y, hadj, hy⟩ := hex
      exact absurd (hD z hz y hadj) hy) u (fun x hx _ => hu x hx)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hS0 : S ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set r : ℝ := Real.sqrt (16 * d * (M + 1) / S) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = 16 * d * (M + 1) / S := Real.sq_sqrt (by positivity)
    have h := hcac r hr0
    rw [hr2] at h
    have e : 8 * (d : ℝ) / (16 * d * (M + 1) / S) * M = S * (M / (2 * (M + 1))) := by
      field_simp
      ring
    rw [e] at h
    have : M / (2 * (M + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    nlinarith
  have hnn : ∀ x ∈ D, 0 ≤ clusterGradSq ω D u x := fun x _ => clusterGradSq_nonneg ω D u x
  have hS' : S = 0 := le_antisymm hS0 (Finset.sum_nonneg hnn)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hS' z hz

/-- The constant of the reverse Hölder inequality on the cubes of the triple with small partition
cubes. -/
noncomputable def rhConst (d : ℕ) (CS CG : ℝ) : ℝ :=
  8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2)

/-- **The reverse Hölder inequality on a cube with small partition cubes** (Lemma 3.6 of Armstrong
and Dario, deterministic part, for every set of the triple closed under its open edges). -/
theorem rhCube_of_scales (hd : 2 ≤ d) :
    ∃ CS : ℝ, 0 ≤ CS ∧ ∀ {CG : ℝ}, 0 ≤ CG → ∀ (ω : Configuration d), PartitionEvent ω →
      ∀ (k : ℕ) (x₀ : Vertex d), (∀ z ∈ enl 1 k x₀, (partitionCube ω z).scale + 2 ≤ k) →
      ∑ z ∈ enl 1 k x₀, partitionReach ω z ^ (2 * d * (d + 2)) ≤
        ENNReal.ofReal CG * 3 ^ ((k + 1) * d) →
      RHCube (rhConst d CS CG) ω k x₀ := by
  have hd0 : 0 < d := by omega
  obtain ⟨CS, hCS, hbox⟩ := exists_box_rh_cube hd
  refine ⟨CS, hCS, fun {CG} hCG ω hP k x₀ hres hreach => ?_⟩
  have hres' : ∀ z ∈ enl 1 k x₀, (partitionCube ω z).scale + 1 ≤ k := fun z hz => by
    have := hres z hz; omega
  obtain ⟨size, hsize, hU'E, hclosed, hSob, hmom⟩ := hbox hCG ω hP k x₀ hres' hreach
  set B := enlSquare k x₀ with hB
  set U' := partitionBoxCluster ω B with hU'
  have hBr := partitionBoxResolved_enlSquare hP hres'
  intro C hC hcl u hu
  -- vertices of `C ∩ □` outside `U'` carry no energy
  have hZ : ∀ z ∈ C, z ∈ cube k x₀ → z ∉ U' → clusterEnergy ω C u z = 0 := by
    intro z hzC hzc hzU
    set D := C.filter (fun a => (openIn ω ↑C).Reachable z a) with hD
    have hzD : z ∈ D := Finset.mem_filter.2 ⟨hzC, SimpleGraph.Reachable.refl _⟩
    have hDC : D ⊆ C := Finset.filter_subset _ _
    have hDcl : ∀ a ∈ D, ∀ w, (openGraph ω).Adj a w → w ∈ D := by
      intro a ha w hadj
      obtain ⟨haC, hza⟩ := Finset.mem_filter.1 ha
      by_cases hw : w ∈ enl 1 k x₀
      · have hwC := hcl a haC w hadj hw
        exact Finset.mem_filter.2 ⟨hwC, hza.trans (SimpleGraph.Adj.reachable
          (G := openIn ω ↑C) ⟨hadj, haC, hwC⟩)⟩
      · exfalso
        have hza' : (openIn ω ↑(enl 1 k x₀)).Reachable z a :=
          reachable_openIn_mono (fun b hb => hC hb) hza
        exact hzU (mem_partitionBoxCluster_of_exit hd0 hP hzc
          (hres z (cube_subset_enl 1 k x₀ hzc)) hza' hadj hw)
    have hharm : ∀ a ∈ D, openLaplacian ω u a = 0 := fun a ha =>
      hu a (hDC ha) fun w hw => hDC (hDcl a ha w hw)
    have h0 := clusterGradSq_eq_zero_of_closed hd0 D hDcl u hharm hzD
    unfold clusterEnergy
    rw [if_pos hzC, ← h0]
    unfold clusterGradSq
    congr 2
    refine Finset.filter_congr fun w hw => ?_
    have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hw
    exact ⟨fun _ => hDcl z hzD w hadj, fun hwD => hDC hwD⟩
  have hA0 : 0 ≤ rhConst d CS CG := by unfold rhConst; positivity
  have hRHS0 : 0 ≤ rhConst d CS CG * avg (enl 1 k x₀) (fun z =>
      clusterEnergy ω C u z ^ ((d : ℝ) / (d + 1))) ^ (((d : ℝ) + 1) / d) :=
    mul_nonneg hA0 (Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun z _ =>
      Real.rpow_nonneg (clusterEnergy_nonneg _ _ _ z) _) (Nat.cast_nonneg _)) _)
  by_cases hmeet : ∃ a ∈ C, a ∈ U'
  · obtain ⟨a, haC, haU⟩ := hmeet
    -- `U' ⊆ C`
    have hU'C : U' ⊆ C := by
      intro b hb
      have ha' := mem_partitionBoxCluster.1 haU
      have hb' := mem_partitionBoxCluster.1 hb
      have hab : (openIn ω ↑B.vertices).Reachable a b :=
        ha'.2.trans ((reachable_partitionAnchor_of_boxResolved hd0 hP hBr ha'.1 hb'.1).trans
          hb'.2.symm)
      exact mem_of_reachable_openIn_of_closed (S := ↑B.vertices) (fun z hz w hadj hw => hcl z hz w
        hadj (mem_enlSquare_vertices.1 hw)) hab haC
    have hrh := reverse_holder_clusterEnergy_local ω hd0 U' u k x₀
      (fun z hz _ hall => hu z (hU'C hz) fun w hw => hU'C (hall w hw)) U' hU'E subset_rfl hclosed
      (fun z hz _ => hz) size hsize hCS hCG hSob hmom
    have hnum : avg (cube k x₀) (clusterEnergy ω C u) ≤ avg (cube k x₀) (clusterEnergy ω U' u) := by
      unfold avg
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun z hz => ?_) (Nat.cast_nonneg _)
      by_cases hzU : z ∈ U'
      · apply le_of_eq
        unfold clusterEnergy
        rw [if_pos (hU'C hzU), if_pos hzU]
        unfold clusterGradSq
        congr 2
        refine Finset.filter_congr fun w hw => ?_
        have hadj := (SimpleGraph.mem_neighborFinset _ _ _).1 hw
        have hwE : w ∈ enl 1 k x₀ := mem_enl_of_near_cube hz fun i => by
          rw [abs_sub_comm]; exact abs_sub_le_one_of_openGraph_adj hadj i
        exact ⟨fun _ => hclosed z hzU w hadj hwE, fun hwU => hU'C hwU⟩
      · by_cases hzC : z ∈ C
        · rw [hZ z hzC hz hzU]
          exact clusterEnergy_nonneg _ _ _ z
        · unfold clusterEnergy
          rw [if_neg hzC]
          exact clusterEnergy_nonneg _ _ _ z
    have hden : avg (enl 1 k x₀) (fun z => clusterEnergy ω U' u z ^ ((d : ℝ) / (d + 1))) ≤
        avg (enl 1 k x₀) (fun z => clusterEnergy ω C u z ^ ((d : ℝ) / (d + 1))) := by
      unfold avg
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun z _ => ?_) (Nat.cast_nonneg _)
      refine Real.rpow_le_rpow (clusterEnergy_nonneg _ _ _ z) ?_ (by positivity)
      unfold clusterEnergy
      by_cases hzU : z ∈ U'
      · rw [if_pos hzU, if_pos (hU'C hzU)]
        exact clusterGradSq_le_of_subset ω hU'C u z
      · rw [if_neg hzU]
        split_ifs
        · exact clusterGradSq_nonneg _ _ _ _
        · exact le_rfl
    refine hnum.trans (hrh.trans ?_)
    change rhConst d CS CG * _ ≤ _
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg
      fun z _ => Real.rpow_nonneg (clusterEnergy_nonneg _ _ _ z) _) (Nat.cast_nonneg _)) hden
      (by positivity)) hA0
  · push Not at hmeet
    have h0 : avg (cube k x₀) (clusterEnergy ω C u) = 0 := by
      unfold avg
      rw [Finset.sum_eq_zero fun z hz => ?_, zero_div]
      by_cases hzC : z ∈ C
      · exact hZ z hzC hz (hmeet z hzC)
      · unfold clusterEnergy; rw [if_neg hzC]
    rw [h0]
    exact hRHS0

end Rigidity.Proofs.Cluster.GeneralDim
