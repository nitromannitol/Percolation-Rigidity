import Rigidity.Proofs.Percolation.PlanarMuMeasurable

/-!
# Quadratic minimization against a field pairing and a flux pairing

For a lattice edge field `g`, let `ℓ_g u = ∑_{x ∈ U} ∑_i 1{x + e_i ∈ U} g(x, i) ([u](x + e_i) - [u](x))`
be the pairing of `g` with the gradient of the coarsening of `u` (for a constant field `q` this is
the coarse pairing `ℓ_q` of `μ`), and for a slope `p` let `F_p` be the flux pairing of `ν`. Set
`μ_{g,p}(U) = inf_{w ∈ A_*(U)} |U|⁻¹ (B(w, w)/2 - ℓ_g w - F_p w)`.

* On the partition event and for a resolved cube, `ℓ_g` vanishes on the null space of `B`, the
  first variation `B(w, u) = ℓ_g w + F_p w` (`w ∈ A_*(U)`) has a solution, and the infimum is
  attained at every solution (`planarMuGen_eq_of_variation`).
* **Polarization.** If `u` solves the first variation of `μ_{g',p'}`, then for every field `g`,
  `ℓ_g u = -|U| (μ_{g+g',p'} - μ_{g,0} - μ_{g',p'})` (`fieldPairing_eq_planarMuGen`). With `g'` a
  constant field `q` and `p' = 0`, `u` is a minimizer of `μ(U, q)`; with `g' = 0`, `u` is a maximizer
  of `ν(U, p')`.
* `μ_{g,p}(U)` depends only on the cluster `C_*(U)`, the open edges between its vertices and the
  coarse anchors of the vertices of `U`, so `1{partition event, U resolved} μ_{g,p}(U)` is
  measurable (`measurable_planarMuGen_indicator`). Hence the pairings of the minimizers of `μ` and
  the maximizers of `ν` with any fixed field are measurable functions of the configuration, whatever
  minimizer or maximizer is chosen.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- The pairing `ℓ_g u = ∑_{x ∈ U} ∑_i 1{x + e_i ∈ U} g(x, i) ([u](x + e_i) - [u](x))` of a lattice
edge field with the gradient of the coarsening. -/
noncomputable def fieldPairing (ω : Configuration 2) (U : TriadicCube 2)
    (g : Vertex 2 → Fin 2 → ℝ) : Module.Dual ℝ (ClusterFun ω U) :=
  ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
    if x + unitVertex i ∈ U.toIntegerCube.vertices then
      g x i • (clusterEval ω U (planarCoarseAnchor ω (x + unitVertex i)) -
        clusterEval ω U (planarCoarseAnchor ω x))
    else 0

theorem fieldPairing_apply {U : TriadicCube 2} (g : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω U) :
    fieldPairing ω U g u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
      if x + unitVertex i ∈ U.toIntegerCube.vertices then
        g x i * (clusterExtend ω U u (planarCoarseAnchor ω (x + unitVertex i)) -
          clusterExtend ω U u (planarCoarseAnchor ω x))
      else 0 := by
  simp only [fieldPairing, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, clusterEval_apply, smul_eq_mul]
  · simp

/-- For a constant field the field pairing is the coarse pairing. -/
theorem fieldPairing_const {U : TriadicCube 2} (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    fieldPairing ω U (fun _ => q) u = coarsePairing ω U q u := by
  rw [fieldPairing_apply, coarsePairing_apply]

theorem fieldPairing_add {U : TriadicCube 2} (g h : Vertex 2 → Fin 2 → ℝ) (u : ClusterFun ω U) :
    fieldPairing ω U (g + h) u = fieldPairing ω U g u + fieldPairing ω U h u := by
  simp only [fieldPairing_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · simp

theorem fluxPairing_zero {U : TriadicCube 2} (u : ClusterFun ω U) : fluxPairing ω U 0 u = 0 := by
  rw [fluxPairing_apply]
  simp

/-- The field pairing vanishes on the null space of the Dirichlet form. -/
theorem fieldPairing_eq_zero_of_clusterForm (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (g : Vertex 2 → Fin 2 → ℝ) {u : ClusterFun ω U}
    (h : clusterForm ω U u u = 0) : fieldPairing ω U g u = 0 := by
  rw [fieldPairing_apply]
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hxi
  · have hxU : x ∈ U.vertices := (U.mem_toIntegerCube_vertices x).1 hx
    have hxiU : x + unitVertex i ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hxi
    rw [planarCoarseAnchor, planarCoarseAnchor, clusterExtend_eq_of_clusterForm_self_eq_zero hP hU h
      (planarAnchor_mem_planarCubeCluster hP hU hxiU)
      (planarAnchor_mem_planarCubeCluster hP hU hxU)]
    ring
  · rfl

/-- The quantity `μ_{g,p}(U) = inf_{w ∈ A_*(U)} |U|⁻¹ (B(w, w)/2 - ℓ_g w - F_p w)`. -/
noncomputable def planarMuGen (ω : Configuration 2) (U : TriadicCube 2)
    (g : Vertex 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) : ℝ :=
  ⨅ u : clusterHarmonic ω U,
    (clusterForm ω U u u / 2 - (fieldPairing ω U g u + fluxPairing ω U p u)) / U.volume

/-- **The infimum is attained at every solution of the first variation.** -/
theorem planarMuGen_eq_of_variation {U : TriadicCube 2} (g : Vertex 2 → Fin 2 → ℝ)
    (p : Fin 2 → ℝ) {u : ClusterFun ω U} (hu : u ∈ clusterHarmonic ω U)
    (hfv : ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w u = fieldPairing ω U g w + fluxPairing ω U p w) :
    planarMuGen ω U g p =
      (clusterForm ω U u u / 2 - (fieldPairing ω U g u + fluxPairing ω U p u)) / U.volume := by
  set Λ : Module.Dual ℝ (ClusterFun ω U) := fieldPairing ω U g + fluxPairing ω U p with hΛ
  have hmin : ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U u u / 2 - Λ u ≤ clusterForm ω U w w / 2 - Λ w := fun w hw =>
    LinearMap.BilinForm.quadratic_le_of_apply_eq (clusterFormOn ω U)
      (fun u w => clusterForm_symm (u : ClusterFun ω U) w)
      (fun v => clusterForm_self_nonneg (v : ClusterFun ω U)) (Λ.comp (clusterHarmonic ω U).subtype)
      (u := ⟨u, hu⟩) (fun w' => hfv w'.1 w'.2) ⟨w, hw⟩
  have hvol := U.volume_pos
  set f : clusterHarmonic ω U → ℝ := fun w =>
    (clusterForm ω U w w / 2 - (fieldPairing ω U g w + fluxPairing ω U p w)) / U.volume with hf
  have hμ : planarMuGen ω U g p = ⨅ w, f w := rfl
  have hle : ∀ w, (clusterForm ω U u u / 2 - (fieldPairing ω U g u + fluxPairing ω U p u)) /
      U.volume ≤ f w :=
    fun w => div_le_div_of_nonneg_right (hmin w.1 w.2) hvol.le
  have hfu : f ⟨u, hu⟩ =
      (clusterForm ω U u u / 2 - (fieldPairing ω U g u + fluxPairing ω U p u)) / U.volume := rfl
  rw [hμ]
  apply le_antisymm
  · rw [← hfu]
    exact ciInf_le ⟨f ⟨u, hu⟩, by rintro _ ⟨w, rfl⟩; rw [hfu]; exact hle w⟩ _
  · exact le_ciInf hle

/-- On the partition event and for a resolved cube, the first variation of `μ_{g,p}` has a
solution. -/
theorem exists_planarMuGen_variation (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (g : Vertex 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) :
    ∃ u ∈ clusterHarmonic ω U, ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w u = fieldPairing ω U g w + fluxPairing ω U p w := by
  obtain ⟨u, hu, hmin⟩ := exists_clusterHarmonic_minimizer U
    (fieldPairing ω U g + fluxPairing ω U p) (fun v hv => by
      rw [LinearMap.add_apply, fieldPairing_eq_zero_of_clusterForm hP hU g hv,
        fluxPairing_eq_zero_of_clusterForm p hv, add_zero])
  exact ⟨u, hu, fun w hw => (hmin w hw).1⟩

/-- **Polarization.** If `u ∈ A_*(U)` solves the first variation of `μ_{g',p'}`, then for every
field `g`, `ℓ_g u = -|U| (μ_{g+g',p'} - μ_{g,0} - μ_{g',p'})`. -/
theorem fieldPairing_eq_planarMuGen (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {g' : Vertex 2 → Fin 2 → ℝ} {p' : Fin 2 → ℝ}
    {u : ClusterFun ω U} (hu : u ∈ clusterHarmonic ω U)
    (hfv : ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w u = fieldPairing ω U g' w + fluxPairing ω U p' w)
    (g : Vertex 2 → Fin 2 → ℝ) :
    fieldPairing ω U g u = -U.volume *
      (planarMuGen ω U (g + g') p' - planarMuGen ω U g 0 - planarMuGen ω U g' p') := by
  obtain ⟨v, hv, hfvv⟩ := exists_planarMuGen_variation hP hU g 0
  have hvu : v + u ∈ clusterHarmonic ω U := add_mem hv hu
  have hfvs : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w (v + u) =
      fieldPairing ω U (g + g') w + fluxPairing ω U p' w := by
    intro w hw
    rw [map_add, hfvv w hw, hfv w hw, fieldPairing_add, fluxPairing_zero]
    ring
  have h1 := planarMuGen_eq_of_variation g 0 hv hfvv
  have h2 := planarMuGen_eq_of_variation g' p' hu hfv
  have h3 := planarMuGen_eq_of_variation (g + g') p' hvu hfvs
  have hvuB := hfv v hv
  have hsymm := clusterForm_symm (ω := ω) (U := U) u v
  have hexp : clusterForm ω U (v + u) (v + u) = clusterForm ω U v v + clusterForm ω U v u +
      (clusterForm ω U u v + clusterForm ω U u u) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [fluxPairing_zero] at h1
  rw [h1, h2, h3, hexp, fieldPairing_add, map_add, map_add, map_add]
  have hvol := U.volume_pos.ne'
  have key : ∀ A B C : ℝ, -U.volume * (A / U.volume - B / U.volume - C / U.volume) =
      -(A - B - C) := by
    intro A B C
    field_simp
  rw [key]
  linear_combination (1 / 2 : ℝ) * hsymm + hvuB

section Transport

variable {U U' : TriadicCube 2} (e : ↥(clusterVertices ω U) ≃ ↥(clusterVertices ω' U'))

/-- **Relabelling invariance of `μ_{g,p}`.** A bijection of clusters which respects open edges,
their displacements and interior vertices and carries the field pairing to the field pairing
preserves `μ_{g,p}`. -/
theorem planarMuGen_eq_of_equiv
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hdisp : ∀ x y i, ((e y).1 i : ℝ) - (e x).1 i = (y.1 i : ℝ) - x.1 i)
    (hint : ∀ x, U'.IsInterior (e x).1 ↔ U.IsInterior x.1) (hvol : U'.volume = U.volume)
    (g : Vertex 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ)
    (hfield : ∀ u : ClusterFun ω U, fieldPairing ω' U' g (u ∘ e.symm) = fieldPairing ω U g u) :
    planarMuGen ω' U' g p = planarMuGen ω U g p := by
  let E : clusterHarmonic ω U ≃ clusterHarmonic ω' U' :=
    { toFun := fun w => ⟨w.1 ∘ e.symm, (comp_symm_mem_clusterHarmonic_iff e hadj hint w.1).2 w.2⟩
      invFun := fun w => ⟨w.1 ∘ e, by
        have h := (comp_symm_mem_clusterHarmonic_iff e hadj hint (w.1 ∘ e)).1
        apply h
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
  unfold planarMuGen
  symm
  refine Equiv.iInf_congr E fun w => ?_
  change (clusterForm ω' U' (w.1 ∘ e.symm) (w.1 ∘ e.symm) / 2 -
      (fieldPairing ω' U' g (w.1 ∘ e.symm) + fluxPairing ω' U' p (w.1 ∘ e.symm))) / U'.volume = _
  rw [clusterForm_comp_symm e hadj, hfield, fluxPairing_comp_symm e hadj hdisp, hvol]

end Transport

/-- `μ_{g,p}` depends only on the cluster, the open edges between its vertices and the coarse
anchors. -/
theorem planarMuGen_eq_of_cluster_anchor_eq {U : TriadicCube 2}
    (hC : ∀ x, x ∈ clusterVertices ω' U ↔ x ∈ clusterVertices ω U)
    (hadj : ∀ x ∈ clusterVertices ω U, ∀ y ∈ clusterVertices ω U,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (hanc : ∀ x ∈ U.vertices, planarCoarseAnchor ω' x = planarCoarseAnchor ω x)
    (g : Vertex 2 → Fin 2 → ℝ) (p : Fin 2 → ℝ) :
    planarMuGen ω' U g p = planarMuGen ω U g p := by
  let e : ↥(clusterVertices ω U) ≃ ↥(clusterVertices ω' U) :=
    Equiv.subtypeEquivRight fun x => (hC x).symm
  have hext : ∀ (u : ClusterFun ω U) (y : Vertex 2),
      clusterExtend ω' U (u ∘ e.symm) y = clusterExtend ω U u y := by
    intro u y
    by_cases hy : y ∈ clusterVertices ω U
    · have hy' := (hC y).2 hy
      rw [clusterExtend_apply_of_mem _ hy', clusterExtend_apply_of_mem _ hy]
      rfl
    · have hy' : y ∉ clusterVertices ω' U := fun h => hy ((hC y).1 h)
      change (if h : y ∈ clusterVertices ω' U then (u ∘ e.symm) ⟨y, h⟩ else 0) =
        if h : y ∈ clusterVertices ω U then u ⟨y, h⟩ else 0
      rw [dif_neg hy', dif_neg hy]
  refine planarMuGen_eq_of_equiv e (fun x y => by
      simp only [e, Equiv.subtypeEquivRight_apply_coe]
      exact hadj x.1 x.2 y.1 y.2)
    (fun x y i => by simp only [e, Equiv.subtypeEquivRight_apply_coe])
    (fun x => by simp only [e, Equiv.subtypeEquivRight_apply_coe]) rfl g p fun u => ?_
  rw [fieldPairing_apply, fieldPairing_apply]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [hanc _ ((U.mem_toIntegerCube_vertices _).1 hi),
      hanc _ ((U.mem_toIntegerCube_vertices _).1 hx), hext, hext]
  · rfl

/-- **Measurability of `μ_{g,p}`.** The quantity `1{partition event, U resolved} μ_{g,p}(U)` is
measurable. -/
theorem measurable_planarMuGen_indicator (V : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ)
    (p : Fin 2 → ℝ) :
    Measurable fun ω : Configuration 2 =>
      if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarMuGen ω V g p else 0 := by
  set S := V.toIntegerCube.vertices
  let anc : Configuration 2 → ↥S → TriadicCube 2 × Finset (Vertex 2) := fun ω x =>
    (planarPartCube ω x.1, (planarPartCube ω x.1).displacements.filter fun e =>
      (planarPartCube ω x.1).IsPlanarAnchor ω ((planarPartCube ω x.1).center + e))
  let φ : Configuration 2 →
      Option (Finset (Vertex 2) × Finset (Vertex 2 × Vertex 2) ×
        (↥S → TriadicCube 2 × Finset (Vertex 2))) :=
    fun ω => if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      some (S.filter (PlanarClusterLink ω V),
        (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2), anc ω)
    else none
  have hE := measurableSet_planarPartitionEvent_resolved V
  have key : ∀ ω, PlanarPartitionEvent ω → ∀ (t : ↥S → TriadicCube 2 × Finset (Vertex 2))
      (x : ↥S), (anc ω x = t x ↔ (x.1 ∈ (t x).1.vertices ∧
        (t x).1.IsMaximalStopping (planarGoodCubes ω)) ∧
        (t x).1.displacements.filter (fun e => (t x).1.IsPlanarAnchor ω ((t x).1.center + e)) =
          (t x).2) := by
    intro ω hP t x
    constructor
    · intro hx
      have h1 : planarPartCube ω x.1 = (t x).1 := congrArg Prod.fst hx
      have h2 := congrArg Prod.snd hx
      rw [← h1]
      exact ⟨planarPartCube_spec hP x.1, h2⟩
    · rintro ⟨⟨hxQ, hQ⟩, hT⟩
      have h1 := planarPartCube_eq hP hxQ hQ
      refine Prod.ext h1 ?_
      change (planarPartCube ω x.1).displacements.filter (fun e =>
        (planarPartCube ω x.1).IsPlanarAnchor ω ((planarPartCube ω x.1).center + e)) = (t x).2
      rw [h1]
      exact hT
  refine measurable_of_fiber_const φ (fun t => ?_) (fun ω ω' h => ?_)
  · rcases t with _ | ⟨C, E, t⟩
    · have heq : φ ⁻¹' {none} =
          {ω | PlanarPartitionEvent ω ∧ PlanarResolved ω V}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h <;> simp [h]
      rw [heq]
      exact hE.compl
    · have heq : φ ⁻¹' {some (C, E, t)} =
          {ω | PlanarPartitionEvent ω ∧ PlanarResolved ω V} ∩
            ({ω | S.filter (PlanarClusterLink ω V) = C} ∩
              ({ω | (S ×ˢ S).filter (fun e => (openGraph ω).Adj e.1 e.2) = E} ∩
                {ω | ∀ x : ↥S, (x.1 ∈ (t x).1.vertices ∧
                  (t x).1.IsMaximalStopping (planarGoodCubes ω)) ∧
                  (t x).1.displacements.filter
                    (fun e => (t x).1.IsPlanarAnchor ω ((t x).1.center + e)) = (t x).2})) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          φ]
        split_ifs with h
        · simp only [Option.some.injEq, Prod.mk.injEq, h, true_and, funext_iff, key ω h.1 t]
        · simp only [h, false_and]
      rw [heq]
      refine hE.inter ((measurableSet_filter_eq S C (measurable_planarClusterLink V)).inter
        ((measurableSet_filter_eq (S ×ˢ S) E fun e =>
          measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)).inter ?_))
      exact measurableSet_setOf.2 (Measurable.forall fun x =>
        (measurable_const.and (measurable_isMaximalStopping_planarGoodCubes _)).and
          (measurableSet_setOf.1 (measurableSet_filter_eq _ _ fun e =>
            measurable_isPlanarAnchor _ _)))
  · by_cases hω : PlanarPartitionEvent ω ∧ PlanarResolved ω V
    · have hω' : PlanarPartitionEvent ω' ∧ PlanarResolved ω' V := by
        by_contra hn
        simp only [φ, if_pos hω, if_neg hn, reduceCtorEq] at h
      simp only [φ, if_pos hω, if_pos hω', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hCl, hAdj, hAnc⟩ := h
      rw [if_pos hω, if_pos hω']
      refine (planarMuGen_eq_of_cluster_anchor_eq (fun x => ?_) (fun x hx y hy => ?_)
        (fun x hx => ?_) g p).symm
      · rw [mem_clusterVertices, mem_clusterVertices, mem_planarCubeCluster_iff_link hω'.1 hω'.2,
          mem_planarCubeCluster_iff_link hω.1 hω.2, ← V.mem_toIntegerCube_vertices]
        have h1 := Finset.ext_iff.1 hCl x
        simp only [Finset.mem_filter] at h1
        exact h1.symm
      · have hx' := (mem_planarCubeCluster_iff_link hω.1 hω.2 x).1 (mem_clusterVertices.1 hx)
        have hy' := (mem_planarCubeCluster_iff_link hω.1 hω.2 y).1 (mem_clusterVertices.1 hy)
        have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx'.1
        have hyS : y ∈ S := (V.mem_toIntegerCube_vertices y).2 hy'.1
        have h2 := Finset.ext_iff.1 hAdj (x, y)
        simp only [Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
        exact h2.symm
      · have hxS : x ∈ S := (V.mem_toIntegerCube_vertices x).2 hx
        have hx' := congrFun hAnc ⟨x, hxS⟩
        have hQ : planarPartCube ω x = planarPartCube ω' x := congrArg Prod.fst hx'
        have hT := congrArg Prod.snd hx'
        unfold planarCoarseAnchor
        rw [← hQ]
        refine (planarAnchor_eq_of_filter_eq ⟨(planarPartCube_meshed hω.1 x).1,
          planarPartCube_large hω.1 x⟩ ?_ ?_).symm
        · rw [hQ]
          exact ⟨(planarPartCube_meshed hω'.1 x).1, planarPartCube_large hω'.1 x⟩
        · change (planarPartCube ω x).displacements.filter (fun e =>
            (planarPartCube ω x).IsPlanarAnchor ω ((planarPartCube ω x).center + e)) =
            (planarPartCube ω' x).displacements.filter (fun e =>
              (planarPartCube ω' x).IsPlanarAnchor ω' ((planarPartCube ω' x).center + e)) at hT
          rw [← hQ] at hT
          exact hT
    · have hω' : ¬ (PlanarPartitionEvent ω' ∧ PlanarResolved ω' V) := by
        intro hn
        simp only [φ, if_neg hω, if_pos hn, reduceCtorEq] at h
      rw [if_neg hω, if_neg hω']

end Rigidity.Percolation
