import Rigidity.Proofs.Percolation.PlanarSubcubes

/-!
# Subadditivity of `μ` on the planar cluster

Let `U` be a resolved triadic cube of scale `m` and `n ≤ m`. Testing the definition of `μ(V, q)`,
for every resolved subcube `V` of scale `n`, with the restriction of the minimizer `u` of
`μ(U, q)`, the energies add up to at most the energy of `u` (the clusters of distinct subcubes are
disjoint subsets of the cluster of `U`), and the coarse pairings add up to the coarse pairing of
`u` except for the lattice edges of `U` leaving their subcube of scale `n` or lying in an
unresolved one:

`∑_{x ∈ U} 1{V(x) resolved} μ(V(x), q) ≤ |U| μ(U, q) + ∑_{e ∈ E'} q · ∇[u](e)`,

where `V(x)` is the subcube of scale `n` containing `x` and `E'` the set of these exceptional
edges (Armstrong and Dario, Lemma 4.8, (4.17)).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The subcubes of scale `n` of a triadic cube. -/
noncomputable def subcubesAt (U : TriadicCube 2) (n : ℕ) : Finset (TriadicCube 2) :=
  U.toIntegerCube.vertices.image (scaleCube n)

theorem subset_of_mem_subcubesAt {U V : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (hV : V ∈ subcubesAt U n) : V.vertices ⊆ U.vertices := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hV
  exact scaleCube_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)

theorem scale_of_mem_subcubesAt {U V : TriadicCube 2} {n : ℕ} (hV : V ∈ subcubesAt U n) :
    V.scale = n := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hV
  exact scale_scaleCube n x

/-- **Fibres of the subcube map.** -/
theorem sum_scaleCube_eq {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (g : TriadicCube 2 → Vertex 2 → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices, g (scaleCube n x) x =
      ∑ V ∈ subcubesAt U n, ∑ x ∈ V.toIntegerCube.vertices, g V x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := scaleCube n) (t := subcubesAt U n)
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun V hV => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hV
  have hfib : U.toIntegerCube.vertices.filter (fun x => scaleCube n x = scaleCube n x₀) =
      (scaleCube n x₀).toIntegerCube.vertices := by
    ext x
    rw [Finset.mem_filter, (scaleCube n x₀).mem_toIntegerCube_vertices,
      U.mem_toIntegerCube_vertices]
    constructor
    · rintro ⟨_, hx⟩
      rw [← hx]
      exact mem_scaleCube n x
    · intro hx
      exact ⟨scaleCube_subset hn ((U.mem_toIntegerCube_vertices x₀).1 hx₀) hx,
        scaleCube_eq_of_mem hx⟩
  rw [hfib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [scaleCube_eq_of_mem (((scaleCube n x₀).mem_toIntegerCube_vertices x).1 hx)]

/-- Distinct subcubes of the same scale have disjoint clusters. -/
theorem pairwiseDisjoint_clusterVertices (U : TriadicCube 2) (n : ℕ)
    (T : Finset (TriadicCube 2)) (hT : T ⊆ subcubesAt U n) :
    (↑T : Set (TriadicCube 2)).PairwiseDisjoint (fun V => clusterVertices ω V) := by
  intro V hV V' hV' hne
  refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
  exact TriadicCube.eq_of_mem_of_scale_eq
    (by rw [scale_of_mem_subcubesAt (hT hV), scale_of_mem_subcubesAt (hT hV')])
    (mem_clusterVertices.1 hx).1 (mem_clusterVertices.1 hx').1

/-- The restriction of a function on the cluster of `U` to the cluster of any cube, through the
extension by zero. -/
noncomputable def clusterRestrictExt (V : TriadicCube 2) {U : TriadicCube 2}
    (u : ClusterFun ω U) : ClusterFun ω V :=
  fun y => clusterExtend ω U u y.1

theorem clusterRestrictExt_eq {U V : TriadicCube 2} (hVU : V.vertices ⊆ U.vertices)
    (u : ClusterFun ω U) : clusterRestrictExt V u = clusterRestrict hVU u := by
  funext y
  exact clusterExtend_apply_of_mem u (clusterVertices_subset hVU y.2)

/-- The energy of a function on the cluster, as a sum over the cluster as a finite set. -/
theorem clusterForm_self_eq_sum {U : TriadicCube 2} (u : ClusterFun ω U) :
    clusterForm ω U u u = (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U,
      (if (openGraph ω).Adj x y then (clusterExtend ω U u x - clusterExtend ω U u y) *
        (clusterExtend ω U u x - clusterExtend ω U u y) else 0) := by
  rw [clusterForm_apply]
  congr 1
  rw [← Finset.sum_coe_sort (clusterVertices ω U)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort (clusterVertices ω U)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [clusterFormTerm]
  rw [clusterExtend_apply_of_mem u x.2, clusterExtend_apply_of_mem u y.2]

/-- **Energies of restrictions add up to at most the energy.** -/
theorem sum_clusterForm_restrict_le {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (T : Finset (TriadicCube 2)) (hT : T ⊆ subcubesAt U n) (u : ClusterFun ω U) :
    ∑ V ∈ T, clusterForm ω V (clusterRestrictExt V u) (clusterRestrictExt V u) ≤
      clusterForm ω U u u := by
  set G : Vertex 2 → Vertex 2 → ℝ := fun x y => if (openGraph ω).Adj x y then
    (clusterExtend ω U u x - clusterExtend ω U u y) *
      (clusterExtend ω U u x - clusterExtend ω U u y) else 0 with hG
  have hG0 : ∀ x y, 0 ≤ G x y := fun x y => by
    simp only [hG]
    split_ifs
    · exact mul_self_nonneg _
    · exact le_rfl
  have hV : ∀ V ∈ T, clusterForm ω V (clusterRestrictExt V u) (clusterRestrictExt V u) =
      (1 / 2 : ℝ) * ∑ x ∈ clusterVertices ω V, ∑ y ∈ clusterVertices ω V, G x y := by
    intro V _
    rw [clusterForm_apply]
    congr 1
    rw [← Finset.sum_coe_sort (clusterVertices ω V)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_coe_sort (clusterVertices ω V)]
    rfl
  rw [Finset.sum_congr rfl hV, ← Finset.mul_sum, clusterForm_self_eq_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hsubU : ∀ V ∈ T, clusterVertices ω V ⊆ clusterVertices ω U := fun V hV =>
    clusterVertices_subset (subset_of_mem_subcubesAt hn (hT hV))
  calc ∑ V ∈ T, ∑ x ∈ clusterVertices ω V, ∑ y ∈ clusterVertices ω V, G x y
      ≤ ∑ V ∈ T, ∑ x ∈ clusterVertices ω V, ∑ y ∈ clusterVertices ω U, G x y :=
        Finset.sum_le_sum fun V hV => Finset.sum_le_sum fun x _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (hsubU V hV) fun y _ _ => hG0 x y
    _ = ∑ x ∈ T.biUnion (fun V => clusterVertices ω V), ∑ y ∈ clusterVertices ω U, G x y :=
        (Finset.sum_biUnion (pairwiseDisjoint_clusterVertices U n T hT)).symm
    _ ≤ ∑ x ∈ clusterVertices ω U, ∑ y ∈ clusterVertices ω U, G x y := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ =>
          Finset.sum_nonneg fun y _ => hG0 x y
        intro x hx
        obtain ⟨V, hV, hxV⟩ := Finset.mem_biUnion.1 hx
        exact hsubU V hV hxV

/-- The coarse pairing of a restriction, in terms of the coarsening on `U`. -/
theorem coarsePairing_restrict (hP : PlanarPartitionEvent ω) {U V : TriadicCube 2}
    (hV : PlanarResolved ω V) (hVU : V.vertices ⊆ U.vertices) (q : Fin 2 → ℝ)
    (u : ClusterFun ω U) :
    coarsePairing ω V q (clusterRestrictExt V u) = ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin 2,
      if x + unitVertex i ∈ V.toIntegerCube.vertices then
        q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) else 0 := by
  rw [coarsePairing_apply, clusterRestrictExt_eq hVU]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hxi
  · have h1 := coarsen_restrict hP hV hVU u ((V.mem_toIntegerCube_vertices _).1 hxi)
    have h2 := coarsen_restrict hP hV hVU u ((V.mem_toIntegerCube_vertices _).1 hx)
    unfold coarsen at h1 h2
    rw [h1, h2]
    rfl
  · rfl

theorem volume_eq_card (V : TriadicCube 2) :
    V.volume = (V.toIntegerCube.vertices.card : ℝ) := by
  rw [IntegerCube.card_vertices]
  change (9 : ℝ) ^ V.scale = (((3 ^ V.scale) ^ 2 : ℕ) : ℝ)
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **Subadditivity of `μ`** (planar form of Armstrong and Dario, Lemma 4.8, (4.17)). -/
theorem sum_planarMu_subcubes_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ) :
    ∃ u ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w u = coarsePairing ω U q w) ∧
      ∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) ≤
        planarMu ω U q * U.volume + ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
          (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
              ¬ (PlanarResolved ω (scaleCube n x) ∧
                x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then
            q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) else 0) := by
  obtain ⟨u, hu, hvar, hμ⟩ := exists_planarMu_minimizer hP hU q
  refine ⟨u, hu, hvar, ?_⟩
  set S := subcubesAt U n
  set T := S.filter (fun V => PlanarResolved ω V)
  set D : Vertex 2 → Fin 2 → ℝ := fun x i =>
    q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) with hD
  -- the left side as a sum over subcubes
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) =
      ∑ V ∈ T, V.volume * planarMu ω V q := by
    rw [sum_scaleCube_eq hn (fun V _ => if PlanarResolved ω V then planarMu ω V q else 0),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun V _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← volume_eq_card]
    split_ifs <;> simp
  -- testing `μ(V, q)` with the restriction of `u`
  have hV : ∀ V ∈ T, V.volume * planarMu ω V q ≤
      clusterForm ω V (clusterRestrictExt V u) (clusterRestrictExt V u) / 2 -
        coarsePairing ω V q (clusterRestrictExt V u) := by
    intro V hVT
    obtain ⟨hVS, hVres⟩ := Finset.mem_filter.1 hVT
    have hVU := subset_of_mem_subcubesAt hn hVS
    have hmem : clusterRestrictExt V u ∈ clusterHarmonic ω V := by
      rw [clusterRestrictExt_eq hVU]
      exact clusterRestrict_mem_clusterHarmonic hP hVres hVU hu
    have h := planarMu_le hP hVres q hmem
    rw [le_div_iff₀ V.volume_pos] at h
    linarith
  -- the coarse pairings of the restrictions
  have hpair : ∑ V ∈ T, coarsePairing ω V q (clusterRestrictExt V u) =
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
        (if PlanarResolved ω (scaleCube n x) ∧
          x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices then D x i else 0) := by
    rw [Finset.sum_filter]
    have e1 : ∀ V ∈ S, (if PlanarResolved ω V then
        coarsePairing ω V q (clusterRestrictExt V u) else 0) =
        ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin 2,
          (if PlanarResolved ω V ∧ x + unitVertex i ∈ V.toIntegerCube.vertices then D x i
            else 0) := by
      intro V hVS
      split_ifs with hres
      · rw [coarsePairing_restrict hP hres (subset_of_mem_subcubesAt hn hVS)]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [hres, true_and, hD]
      · simp [hres]
    rw [Finset.sum_congr rfl e1,
      ← sum_scaleCube_eq hn (fun V x => ∑ i : Fin 2,
        (if PlanarResolved ω V ∧ x + unitVertex i ∈ V.toIntegerCube.vertices then D x i
          else 0))]
  have hBU := sum_clusterForm_restrict_le hn T (Finset.filter_subset _ _) u
  have hℓU : coarsePairing ω U q u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
      (if x + unitVertex i ∈ U.toIntegerCube.vertices then D x i else 0) := by
    rw [coarsePairing_apply]
    rfl
  have hsplit : ∀ x ∈ U.toIntegerCube.vertices, ∀ i : Fin 2,
      (if x + unitVertex i ∈ U.toIntegerCube.vertices then D x i else 0) =
      (if PlanarResolved ω (scaleCube n x) ∧
        x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices then D x i else 0) +
      (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
        ¬ (PlanarResolved ω (scaleCube n x) ∧
          x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then D x i else 0) := by
    intro x hx i
    have hsub := scaleCube_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)
    by_cases h1 : PlanarResolved ω (scaleCube n x) ∧
        x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices
    · have h2 : x + unitVertex i ∈ U.toIntegerCube.vertices :=
        (U.mem_toIntegerCube_vertices _).2
          (hsub (((scaleCube n x).mem_toIntegerCube_vertices _).1 h1.2))
      simp [h1, h2]
    · by_cases h2 : x + unitVertex i ∈ U.toIntegerCube.vertices <;> simp [h1, h2]
  have hℓsplit : coarsePairing ω U q u =
      ∑ V ∈ T, coarsePairing ω V q (clusterRestrictExt V u) +
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
        (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
          ¬ (PlanarResolved ω (scaleCube n x) ∧
            x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then D x i else 0) := by
    rw [hℓU, hpair, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsplit x hx i
  have hμU : planarMu ω U q * U.volume = clusterForm ω U u u / 2 - coarsePairing ω U q u := by
    rw [hμ, div_mul_cancel₀ _ U.volume_pos.ne']
  rw [hL]
  have hsumV := Finset.sum_le_sum hV
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hsumV
  linarith

end Rigidity.Percolation
