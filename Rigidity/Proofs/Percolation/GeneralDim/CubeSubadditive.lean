import Rigidity.Proofs.Percolation.GeneralDim.CubeSubcubes

/-!
# Subadditivity of `μ` and `ν` on triadic cubes of `ℤ^d`

Let `U` be a triadic cube of `ℤ^d` of scale `m` and `n ≤ m`, on the partition event. Write
`V(x)` for the subcube of scale `n` containing `x`.

For `μ` (with `U` resolved), testing the definition of `μ(V, q)`, for every resolved subcube `V`
of scale `n`, with the restriction of the minimizer `u` of `μ(U, q)`: the energies of the
restrictions add up to at most the energy of `u` (the clusters of distinct subcubes are disjoint
subsets of `C_*(U)`), and the coarse pairings add up to the coarse pairing of `u` except for the
lattice edges of `U` leaving their subcube of scale `n` or lying in an unresolved one:

`∑_{x ∈ U} 1{V(x) resolved} μ(V(x), q) ≤ |U| μ(U, q) + ∑_{e ∈ E'} q · ∇[u]_𝒫(e)`.

For `ν`, testing `ν(V, p)` with the restriction of the maximizer `v` of `ν(U, p)`, the flux
pairings add up to the flux pairing of `v` except for the open edges of `C_*(U)` which do not lie
in the cluster of a resolved subcube:

`|U| ν(U, p) ≤ ∑_{x ∈ U} 1{V(x) resolved} ν(V(x), p) + F_p^{exc}(v)`.

These are the deterministic parts of Lemma 4.8 of Armstrong and Dario, (4.32) and (4.33), with
the error terms kept explicit.
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

theorem mem_resolvedSubcubesAt {U V : TriadicCube d} {n : ℕ} :
    V ∈ U.resolvedSubcubesAt ω n ↔ V ∈ U.subcubesAt n ∧ PartitionResolved ω V :=
  Finset.mem_filter

theorem sum_resolvedSubcubesAt {U : TriadicCube d} {n : ℕ} (f : TriadicCube d → ℝ) :
    ∑ V ∈ U.resolvedSubcubesAt ω n, f V =
      ∑ V ∈ U.subcubesAt n, if PartitionResolved ω V then f V else 0 :=
  Finset.sum_filter _ _

/-- The coarse pairing of a restriction to a resolved cube, in terms of the coarsening on `U`. -/
theorem cubeCoarsePairing_restrictExt (hd : 0 < d) (hP : PartitionEvent ω) {U V : TriadicCube d}
    (hV : PartitionResolved ω V) (q : Fin d → ℝ) (u : CubeFun ω U) :
    cubeCoarsePairing ω V q (cubeRestrictExt V u) =
      ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin d,
        if x + LatticeProb.unit i ∈ V.toIntegerCube.vertices then
          q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0 := by
  rw [cubeCoarsePairing_apply]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hxi
  · have h1 := cubeCoarsen_cubeRestrictExt hd hP hV u ((V.mem_toIntegerCube_vertices _).1 hxi)
    have h2 := cubeCoarsen_cubeRestrictExt hd hP hV u ((V.mem_toIntegerCube_vertices _).1 hx)
    unfold cubeCoarsen at h1 h2
    rw [h1, h2]
    rfl
  · rfl

/-- **Subadditivity of `μ`** (Armstrong and Dario, Lemma 4.8, (4.32), with the error term over the
exceptional lattice edges). -/
theorem sum_cubeMu_subcubes_le (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin d → ℝ) :
    ∃ u ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w u = cubeCoarsePairing ω U q w) ∧
      ∑ x ∈ U.toIntegerCube.vertices,
          (if PartitionResolved ω (triadicCubeAt n x) then cubeMu ω (triadicCubeAt n x) q
            else 0) ≤
        cubeMu ω U q * U.latticeVolume + ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
          (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
              ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
                x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then
            q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) else 0) := by
  obtain ⟨u, hu, hvar, hμ⟩ := exists_cubeMu_minimizer hd hP hU q
  refine ⟨u, hu, hvar, ?_⟩
  set S := U.subcubesAt n
  set T := U.resolvedSubcubesAt ω n
  set D : Vertex d → Fin d → ℝ := fun x i =>
    q i * (cubeCoarsen ω U u (x + LatticeProb.unit i) - cubeCoarsen ω U u x) with hD
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PartitionResolved ω (triadicCubeAt n x) then cubeMu ω (triadicCubeAt n x) q else 0) =
      ∑ V ∈ T, V.latticeVolume * cubeMu ω V q :=
    sum_vertices_ite_triadicCubeAt_eq hn (fun V => cubeMu ω V q)
  -- testing `μ(V, q)` with the restriction of `u`
  have hV : ∀ V ∈ T, V.latticeVolume * cubeMu ω V q ≤
      cubeForm ω V (cubeRestrictExt V u) (cubeRestrictExt V u) / 2 -
        cubeCoarsePairing ω V q (cubeRestrictExt V u) := by
    intro V hVT
    obtain ⟨hVS, hVres⟩ := mem_resolvedSubcubesAt.1 hVT
    have hVU := TriadicCube.subset_of_mem_subcubesAt hn hVS
    have hmem : cubeRestrictExt V u ∈ cubeHarmonic ω V :=
      cubeRestrictExt_mem_cubeHarmonic hVU
        (crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hVT) hu
    have h := cubeMu_le hd hP hVres q hmem
    rw [le_div_iff₀ V.latticeVolume_pos] at h
    linarith
  -- the coarse pairings of the restrictions
  have hpair : ∑ V ∈ T, cubeCoarsePairing ω V q (cubeRestrictExt V u) =
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        (if PartitionResolved ω (triadicCubeAt n x) ∧
          x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices then D x i
          else 0) := by
    rw [sum_resolvedSubcubesAt]
    have e1 : ∀ V ∈ S, (if PartitionResolved ω V then
        cubeCoarsePairing ω V q (cubeRestrictExt V u) else 0) =
        ∑ x ∈ V.toIntegerCube.vertices, ∑ i : Fin d,
          (if PartitionResolved ω V ∧ x + LatticeProb.unit i ∈ V.toIntegerCube.vertices then
            D x i else 0) := by
      intro V _
      split_ifs with hres
      · rw [cubeCoarsePairing_restrictExt hd hP hres]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [hres, true_and, hD]
      · simp [hres]
    rw [Finset.sum_congr rfl e1,
      ← sum_triadicCubeAt_eq hn (fun V x => ∑ i : Fin d,
        (if PartitionResolved ω V ∧ x + LatticeProb.unit i ∈ V.toIntegerCube.vertices then D x i
          else 0))]
  have hBU := sum_cubeForm_restrictExt_le T (Finset.filter_subset _ _)
    (fun V hV => crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hV) u
  have hℓU : cubeCoarsePairing ω U q u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then D x i else 0) := by
    rw [cubeCoarsePairing_apply]
    rfl
  have hsplit : ∀ x ∈ U.toIntegerCube.vertices, ∀ i : Fin d,
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then D x i else 0) =
      (if PartitionResolved ω (triadicCubeAt n x) ∧
        x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices then D x i else 0) +
      (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
        ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
          x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then D x i
        else 0) := by
    intro x hx i
    have hsub := triadicCubeAt_subset hn ((U.mem_toIntegerCube_vertices x).1 hx)
    by_cases h1 : PartitionResolved ω (triadicCubeAt n x) ∧
        x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices
    · have h2 : x + LatticeProb.unit i ∈ U.toIntegerCube.vertices :=
        (U.mem_toIntegerCube_vertices _).2
          (hsub (((triadicCubeAt n x).mem_toIntegerCube_vertices _).1 h1.2))
      simp [h1, h2]
    · by_cases h2 : x + LatticeProb.unit i ∈ U.toIntegerCube.vertices <;> simp [h1, h2]
  have hℓsplit : cubeCoarsePairing ω U q u =
      ∑ V ∈ T, cubeCoarsePairing ω V q (cubeRestrictExt V u) +
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
        (if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices ∧
          ¬ (PartitionResolved ω (triadicCubeAt n x) ∧
            x + LatticeProb.unit i ∈ (triadicCubeAt n x).toIntegerCube.vertices) then D x i
          else 0) := by
    rw [hℓU, hpair, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsplit x hx i
  have hμU : cubeMu ω U q * U.latticeVolume =
      cubeForm ω U u u / 2 - cubeCoarsePairing ω U q u := by
    rw [hμ, div_mul_cancel₀ _ U.latticeVolume_pos.ne']
  rw [hL]
  have hsumV := Finset.sum_le_sum hV
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hsumV
  linarith

/-- The flux pairing as a sum over the cluster as a finite set. -/
theorem cubeFluxPairing_eq_sum {U : TriadicCube d} (p : Fin d → ℝ) (u : CubeFun ω U) :
    cubeFluxPairing ω U p u = (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U,
      ∑ y ∈ crossingClusterVertices ω U,
      (if (openGraph ω).Adj x y then (∑ i, p i * ((y i : ℝ) - x i)) *
        (cubeExtend ω U u y - cubeExtend ω U u x) else 0) := by
  rw [cubeFluxPairing_apply]
  congr 1
  rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort (crossingClusterVertices ω U)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cubeExtend_apply_of_mem u x.2, cubeExtend_apply_of_mem u y.2]

/-- Sums over the clusters of subcubes, indexed by the first vertex. -/
theorem sum_subcubes_crossingCluster_eq {U : TriadicCube d} {n : ℕ}
    (T : Finset (TriadicCube d)) (hT : T ⊆ U.subcubesAt n)
    (hsubU : ∀ V ∈ T, crossingClusterVertices ω V ⊆ crossingClusterVertices ω U)
    (H : TriadicCube d → Vertex d → ℝ) :
    ∑ V ∈ T, ∑ x ∈ crossingClusterVertices ω V, H V x =
      ∑ x ∈ crossingClusterVertices ω U, (if triadicCubeAt n x ∈ T ∧
        x ∈ crossingClusterVertices ω (triadicCubeAt n x) then H (triadicCubeAt n x) x
        else 0) := by
  have hVx : ∀ V ∈ T, ∀ x ∈ crossingClusterVertices ω V, triadicCubeAt n x = V := by
    intro V hV x hx
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.1 (hT hV)
    exact triadicCubeAt_eq_of_mem
      ((triadicCubeAt n x₀).crossingCluster_subset ω (mem_crossingClusterVertices.1 hx))
  calc ∑ V ∈ T, ∑ x ∈ crossingClusterVertices ω V, H V x
      = ∑ V ∈ T, ∑ x ∈ crossingClusterVertices ω V, H (triadicCubeAt n x) x :=
        Finset.sum_congr rfl fun V hV => Finset.sum_congr rfl fun x hx => by
          rw [hVx V hV x hx]
    _ = ∑ x ∈ T.biUnion (fun V => crossingClusterVertices ω V), H (triadicCubeAt n x) x :=
        (Finset.sum_biUnion (pairwiseDisjoint_crossingClusterVertices U n T hT)).symm
    _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨V, hV, hx⟩
          rw [hVx V hV x hx]
          exact ⟨hsubU V hV hx, hV, hx⟩
        · rintro ⟨_, hT', hx⟩
          exact ⟨_, hT', hx⟩

/-- The flux term of an ordered pair of open neighbours. -/
noncomputable def cubeFluxTerm (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ)
    (v : CubeFun ω U) (x y : Vertex d) : ℝ :=
  if (openGraph ω).Adj x y then
    (∑ i, p i * ((y i : ℝ) - x i)) * (cubeExtend ω U v y - cubeExtend ω U v x)
  else 0

/-- The flux pairing of a restriction. -/
theorem cubeFluxPairing_restrictExt (V : TriadicCube d) {U : TriadicCube d} (p : Fin d → ℝ)
    (v : CubeFun ω U) :
    cubeFluxPairing ω V p (cubeRestrictExt V v) = (1 / 2 : ℝ) *
      ∑ x ∈ crossingClusterVertices ω V, ∑ y ∈ crossingClusterVertices ω V,
        cubeFluxTerm ω U p v x y := by
  rw [cubeFluxPairing_eq_sum]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun x hx =>
    Finset.sum_congr rfl fun y hy => ?_)
  simp only [cubeFluxTerm]
  rw [cubeExtend_cubeRestrictExt V v hy, cubeExtend_cubeRestrictExt V v hx]

/-- The pairs of vertices lying in the cluster of the resolved subcube of scale `n` of the first
vertex. -/
def IsResolvedSubcubePair (ω : Configuration d) (n : ℕ) (x y : Vertex d) : Prop :=
  PartitionResolved ω (triadicCubeAt n x) ∧ x ∈ crossingClusterVertices ω (triadicCubeAt n x) ∧
    y ∈ crossingClusterVertices ω (triadicCubeAt n x)

/-- The flux pairings of the restrictions to resolved subcubes. -/
theorem sum_cubeFluxPairing_restrictExt (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n : ℕ} (hn : n ≤ U.scale) (p : Fin d → ℝ) (v : CubeFun ω U) :
    ∑ V ∈ U.resolvedSubcubesAt ω n, cubeFluxPairing ω V p (cubeRestrictExt V v) =
      (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
        (if IsResolvedSubcubePair ω n x y then cubeFluxTerm ω U p v x y else 0) := by
  set T := U.resolvedSubcubesAt ω n
  have hTS : T ⊆ U.subcubesAt n := Finset.filter_subset _ _
  have hsubU : ∀ V ∈ T, crossingClusterVertices ω V ⊆ crossingClusterVertices ω U :=
    fun V hV => crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hV
  have hSx : ∀ x ∈ crossingClusterVertices ω U, triadicCubeAt n x ∈ U.subcubesAt n :=
    fun x hx => TriadicCube.triadicCubeAt_mem_subcubesAt n
      (U.crossingCluster_subset ω (mem_crossingClusterVertices.1 hx))
  rw [Finset.sum_congr rfl fun V _ => cubeFluxPairing_restrictExt V p v, ← Finset.mul_sum]
  refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
  rw [sum_subcubes_crossingCluster_eq T hTS hsubU
    (fun V x => ∑ y ∈ crossingClusterVertices ω V, cubeFluxTerm ω U p v x y)]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hT : triadicCubeAt n x ∈ T ↔ PartitionResolved ω (triadicCubeAt n x) := by
    rw [mem_resolvedSubcubesAt]
    exact ⟨fun h => h.2, fun h => ⟨hSx x hx, h⟩⟩
  by_cases hc : PartitionResolved ω (triadicCubeAt n x) ∧
      x ∈ crossingClusterVertices ω (triadicCubeAt n x)
  · have hc' : triadicCubeAt n x ∈ T ∧ x ∈ crossingClusterVertices ω (triadicCubeAt n x) :=
      ⟨hT.2 hc.1, hc.2⟩
    rw [if_pos hc', ← Finset.sum_filter]
    have hsub := hsubU _ hc'.1
    congr 1
    ext y
    simp only [Finset.mem_filter, IsResolvedSubcubePair]
    exact ⟨fun h => ⟨hsub h, hc.1, hc.2, h⟩, fun h => h.2.2.2⟩
  · have hc' : ¬ (triadicCubeAt n x ∈ T ∧ x ∈ crossingClusterVertices ω (triadicCubeAt n x)) :=
      fun h => hc ⟨hT.1 h.1, h.2⟩
    rw [if_neg hc']
    symm
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    exact fun h => hc ⟨h.1, h.2.1⟩

/-- **Subadditivity of `ν`** (Armstrong and Dario, Lemma 4.8, (4.33), with the error term over the
exceptional open edges). -/
theorem cubeNu_le_sum_subcubes (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    {n : ℕ} (hn : n ≤ U.scale) (p : Fin d → ℝ) :
    ∃ v ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w v = cubeFluxPairing ω U p w) ∧
      cubeNu ω U p * U.latticeVolume ≤
        ∑ x ∈ U.toIntegerCube.vertices,
          (if PartitionResolved ω (triadicCubeAt n x) then cubeNu ω (triadicCubeAt n x) p
            else 0) +
        (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
          (if IsResolvedSubcubePair ω n x y then 0 else cubeFluxTerm ω U p v x y) := by
  obtain ⟨v, hv, hvar, hν⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  refine ⟨v, hv, hvar, ?_⟩
  set T := U.resolvedSubcubesAt ω n
  have hTS : T ⊆ U.subcubesAt n := Finset.filter_subset _ _
  have hL : ∑ x ∈ U.toIntegerCube.vertices,
      (if PartitionResolved ω (triadicCubeAt n x) then cubeNu ω (triadicCubeAt n x) p else 0) =
      ∑ V ∈ T, V.latticeVolume * cubeNu ω V p :=
    sum_vertices_ite_triadicCubeAt_eq hn (fun V => cubeNu ω V p)
  have hV : ∀ V ∈ T, cubeFluxPairing ω V p (cubeRestrictExt V v) -
      cubeForm ω V (cubeRestrictExt V v) (cubeRestrictExt V v) / 2 ≤
      V.latticeVolume * cubeNu ω V p := by
    intro V hVT
    obtain ⟨hVS, -⟩ := mem_resolvedSubcubesAt.1 hVT
    have hVU := TriadicCube.subset_of_mem_subcubesAt hn hVS
    have hmem : cubeRestrictExt V v ∈ cubeHarmonic ω V :=
      cubeRestrictExt_mem_cubeHarmonic hVU
        (crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hVT) hv
    have h := le_cubeNu p hmem
    rw [div_le_iff₀ V.latticeVolume_pos] at h
    linarith
  have hFU : cubeFluxPairing ω U p v =
      ∑ V ∈ T, cubeFluxPairing ω V p (cubeRestrictExt V v) +
      (1 / 2 : ℝ) * ∑ x ∈ crossingClusterVertices ω U, ∑ y ∈ crossingClusterVertices ω U,
        (if IsResolvedSubcubePair ω n x y then 0 else cubeFluxTerm ω U p v x y) := by
    rw [sum_cubeFluxPairing_restrictExt hd hP hn p v, cubeFluxPairing_eq_sum, ← mul_add,
      ← Finset.sum_add_distrib]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) (Finset.sum_congr rfl fun x _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [cubeFluxTerm]
    split_ifs <;> simp
  have hBU := sum_cubeForm_restrictExt_le T hTS
    (fun V hV => crossingClusterVertices_subset_of_mem_resolvedSubcubesAt hd hP hn hV) v
  have hνU : cubeNu ω U p * U.latticeVolume =
      cubeFluxPairing ω U p v - cubeForm ω U v v / 2 := by
    rw [hν, div_mul_cancel₀ _ U.latticeVolume_pos.ne']
  rw [hL, hνU, hFU]
  have hsumV := Finset.sum_le_sum hV
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hsumV
  linarith

end Rigidity.Percolation
