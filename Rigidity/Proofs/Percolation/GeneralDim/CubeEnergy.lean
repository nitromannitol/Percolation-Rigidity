import Rigidity.Proofs.Cluster.PartitionCoarseData
import Rigidity.Proofs.Percolation.QuadraticVariation

/-!
# The subadditive energy quantities on the cluster of a triadic cube of `ℤ^d`

Let `U` be a triadic cube of `ℤ^d` containing the partition cubes of its vertices (a resolved
cube), on the partition event. Then the closure `cl_𝒫(U)` is `U` and the cluster `C_*(U)` of
Armstrong and Dario (beginning of Section 3) is the crossing cluster of `U`
(`setCluster_eq_crossingCluster`). Functions on `C_*(U)` form a finite-dimensional space; on it we
consider

* the Dirichlet form `B u v = (1/2) ∑ (u x - u y) (v x - v y)` over ordered pairs of open
  neighbours in `C_*(U)`, which is `⟨∇u, a∇v⟩_{C_*(U)}` of Armstrong and Dario;
* the coarse pairing `ℓ_q u = ∑ q_i ([u]_𝒫(x + e_i) - [u]_𝒫(x))` over the lattice edges inside `U`,
  each counted once, where `[u]_𝒫(x)` is the value of `u` at the anchor of the partition cube
  of `x`;
* the flux pairing `F_p u = (1/2) ∑ p · (y - x) (u y - u x)` over ordered pairs of open neighbours
  in `C_*(U)`, which is `⟨p, a∇u⟩_{C_*(U)}`;
* the space `A_*(U)` of functions on `C_*(U)` harmonic at the vertices of `C_*(U)` all of whose
  lattice neighbours lie in `U`, that is at the vertices of `C_*(U) \ ∂U`.

The quantities of Armstrong and Dario (Definition 4.1) are
`μ(U, q) = inf_{u ∈ A_*(U)} (B u u / 2 - ℓ_q u) / |U|` and
`ν(U, p) = sup_{v ∈ A_*(U)} (F_p v - B v v / 2) / |U|`. On a resolved cube the functions of zero
energy are the constants on `C_*(U)`, on which both pairings vanish; hence both optimization
problems have optimizers, characterized by the first variation (Lemma 4.2).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- An open neighbour inside `U` of a vertex of the crossing cluster of `U` lies in it. -/
theorem mem_crossingCluster_of_adj {U : TriadicCube d} {x y : Vertex d}
    (hx : x ∈ U.crossingCluster ω) (hy : y ∈ U.vertices) (hxy : (openGraph ω).Adj x y) :
    y ∈ U.crossingCluster ω := by
  obtain ⟨r, hr, hrx⟩ := hx
  exact ⟨r, hr, hrx.trans (SimpleGraph.Adj.reachable (G := openIn ω U.vertices)
    ⟨hxy, U.crossingCluster_subset ω ⟨r, hr, hrx⟩, hy⟩)⟩

/-- **Connectivity of `C_*(U)`.** On the partition event, any two vertices of the crossing
cluster of a resolved cube are joined by an open path inside the crossing cluster. -/
theorem joinedWithin_crossingClusterVertices (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {x y : Vertex d}
    (hx : x ∈ U.crossingCluster ω) (hy : y ∈ U.crossingCluster ω) :
    JoinedWithin ω ↑(crossingClusterVertices ω U) x y := by
  have hz := U.center_mem
  have hG := mem_goodCubes_of_partitionCube_le hP hz (hU _ hz)
  obtain ⟨root, hroot⟩ := (U.wellConnectedIn_threeQuarter_iff ω).1 hG.2.1.2
  have h := hroot.reachable_of_mem_crossingCluster hd hG.2.1.1 hx hy
  have h2 : (openIn ω (U.vertices ∩ Set.univ)).Reachable x y := by
    rwa [Set.inter_univ]
  have h' := TriadicCube.reachable_crossingCluster_inter hx h2
  refine (joinedWithin_of_reachable_openIn h' ⟨hx, Set.mem_univ _⟩).mono ?_
  rintro z ⟨hz, -⟩
  exact Finset.mem_coe.2 (mem_crossingClusterVertices.2 hz)

/-- The anchors of the partition cubes of the vertices of a resolved cube lie in its crossing
cluster. -/
theorem partitionAnchor_mem_crossingCluster_of_resolved (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {x : Vertex d} (hx : x ∈ U.vertices) :
    partitionAnchor ω x ∈ U.crossingCluster ω :=
  crossingCluster_partitionCube_subset hd hP hx (hU x hx) (partitionAnchor_mem_crossingCluster hP x)

/-- Functions on the cluster `C_*(U)` of a triadic cube. -/
abbrev CubeFun (ω : Configuration d) (U : TriadicCube d) : Type :=
  ↥(crossingClusterVertices ω U) → ℝ

/-- The extension by zero of a function on the cluster. -/
noncomputable def cubeExtend (ω : Configuration d) (U : TriadicCube d) :
    CubeFun ω U →ₗ[ℝ] (Vertex d → ℝ) where
  toFun u x := if h : x ∈ crossingClusterVertices ω U then u ⟨x, h⟩ else 0
  map_add' u v := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem cubeExtend_apply_of_mem {U : TriadicCube d} (u : CubeFun ω U) {x : Vertex d}
    (hx : x ∈ crossingClusterVertices ω U) : cubeExtend ω U u x = u ⟨x, hx⟩ := by
  change (if h : x ∈ crossingClusterVertices ω U then u ⟨x, h⟩ else 0) = _
  rw [dif_pos hx]

/-- The summand of the Dirichlet form. -/
noncomputable def cubeFormTerm (ω : Configuration d) {U : TriadicCube d}
    (u v : CubeFun ω U) (x y : ↥(crossingClusterVertices ω U)) : ℝ :=
  if (openGraph ω).Adj x.1 y.1 then (u x - u y) * (v x - v y) else 0

theorem cubeFormTerm_add_left {U : TriadicCube d} (u₁ u₂ v : CubeFun ω U)
    (x y : ↥(crossingClusterVertices ω U)) :
    cubeFormTerm ω (u₁ + u₂) v x y = cubeFormTerm ω u₁ v x y + cubeFormTerm ω u₂ v x y := by
  simp only [cubeFormTerm, Pi.add_apply]
  split_ifs <;> ring

theorem cubeFormTerm_add_right {U : TriadicCube d} (u v₁ v₂ : CubeFun ω U)
    (x y : ↥(crossingClusterVertices ω U)) :
    cubeFormTerm ω u (v₁ + v₂) x y = cubeFormTerm ω u v₁ x y + cubeFormTerm ω u v₂ x y := by
  simp only [cubeFormTerm, Pi.add_apply]
  split_ifs <;> ring

theorem cubeFormTerm_smul_left {U : TriadicCube d} (c : ℝ) (u v : CubeFun ω U)
    (x y : ↥(crossingClusterVertices ω U)) :
    cubeFormTerm ω (c • u) v x y = c * cubeFormTerm ω u v x y := by
  simp only [cubeFormTerm, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem cubeFormTerm_smul_right {U : TriadicCube d} (c : ℝ) (u v : CubeFun ω U)
    (x y : ↥(crossingClusterVertices ω U)) :
    cubeFormTerm ω u (c • v) x y = c * cubeFormTerm ω u v x y := by
  simp only [cubeFormTerm, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The Dirichlet form `⟨∇u, a∇v⟩_{C_*(U)}` of the open edges of the cluster. -/
noncomputable def cubeForm (ω : Configuration d) (U : TriadicCube d) :
    LinearMap.BilinForm ℝ (CubeFun ω U) :=
  LinearMap.mk₂ ℝ (fun u v => (1 / 2 : ℝ) * ∑ x, ∑ y, cubeFormTerm ω u v x y)
    (fun u₁ u₂ v => by
      simp only [cubeFormTerm_add_left, Finset.sum_add_distrib, mul_add])
    (fun c u v => by
      simp only [cubeFormTerm_smul_left, ← Finset.mul_sum, smul_eq_mul]
      ring)
    (fun u v₁ v₂ => by
      simp only [cubeFormTerm_add_right, Finset.sum_add_distrib, mul_add])
    (fun c u v => by
      simp only [cubeFormTerm_smul_right, ← Finset.mul_sum, smul_eq_mul]
      ring)

theorem cubeForm_apply {U : TriadicCube d} (u v : CubeFun ω U) :
    cubeForm ω U u v = (1 / 2 : ℝ) * ∑ x, ∑ y, cubeFormTerm ω u v x y := rfl

theorem cubeForm_symm {U : TriadicCube d} (u v : CubeFun ω U) :
    cubeForm ω U u v = cubeForm ω U v u := by
  rw [cubeForm_apply, cubeForm_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [cubeFormTerm]
  split_ifs <;> ring

theorem cubeFormTerm_self_nonneg {U : TriadicCube d} (u : CubeFun ω U)
    (x y : ↥(crossingClusterVertices ω U)) : 0 ≤ cubeFormTerm ω u u x y := by
  simp only [cubeFormTerm]
  split_ifs
  · exact mul_self_nonneg _
  · exact le_rfl

theorem cubeForm_self_nonneg {U : TriadicCube d} (u : CubeFun ω U) :
    0 ≤ cubeForm ω U u u := by
  rw [cubeForm_apply]
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => cubeFormTerm_self_nonneg u x y)

/-- A function of zero energy is constant across the open edges of the cluster. -/
theorem eq_of_cubeForm_self_eq_zero {U : TriadicCube d} {u : CubeFun ω U}
    (h : cubeForm ω U u u = 0) {x y : ↥(crossingClusterVertices ω U)}
    (hxy : (openGraph ω).Adj x.1 y.1) : u x = u y := by
  rw [cubeForm_apply] at h
  have hsum : ∑ x, ∑ y, cubeFormTerm ω u u x y = 0 := by linarith
  have hx := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => cubeFormTerm_self_nonneg u x y).1 hsum x (Finset.mem_univ x)
  have hxy' := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => cubeFormTerm_self_nonneg u x y).1 hx y
    (Finset.mem_univ y)
  simp only [cubeFormTerm, hxy, if_true] at hxy'
  have := mul_self_eq_zero.1 hxy'
  linarith

/-- A function constant across the open edges inside a set is constant along open paths inside
the set. -/
theorem eq_of_joinedWithin_of_adj_eq {f : Vertex d → ℝ} {S : Set (Vertex d)}
    (hf : ∀ a ∈ S, ∀ b ∈ S, (openGraph ω).Adj a b → f a = f b) {x y : Vertex d}
    (h : JoinedWithin ω S x y) : f x = f y := by
  obtain ⟨W, hW⟩ := h
  induction W with
  | nil => rfl
  | @cons a b c hab W ih =>
    have ha : a ∈ S := hW a (SimpleGraph.Walk.start_mem_support _)
    have hb : b ∈ S := hW b (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ W.start_mem_support)
    rw [hf a ha b hb hab]
    exact ih fun z hz => hW z (List.mem_cons_of_mem _ hz)

/-- **Null space of the Dirichlet form.** On the partition event and the cluster of a resolved
cube, a function of zero energy is constant. -/
theorem cubeExtend_eq_of_cubeForm_self_eq_zero (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) {u : CubeFun ω U}
    (h : cubeForm ω U u u = 0) {x y : Vertex d} (hx : x ∈ U.crossingCluster ω)
    (hy : y ∈ U.crossingCluster ω) :
    cubeExtend ω U u x = cubeExtend ω U u y := by
  refine eq_of_joinedWithin_of_adj_eq (S := ↑(crossingClusterVertices ω U))
    (fun a ha b hb hab => ?_) (joinedWithin_crossingClusterVertices hd hP hU hx hy)
  rw [cubeExtend_apply_of_mem u ha, cubeExtend_apply_of_mem u hb]
  exact eq_of_cubeForm_self_eq_zero h (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) hab

/-- Evaluation of the extension at a vertex. -/
noncomputable def cubeEval (ω : Configuration d) (U : TriadicCube d) (x : Vertex d) :
    Module.Dual ℝ (CubeFun ω U) :=
  (LinearMap.proj x).comp (cubeExtend ω U)

theorem cubeEval_apply {U : TriadicCube d} (x : Vertex d) (u : CubeFun ω U) :
    cubeEval ω U x u = cubeExtend ω U u x := rfl

/-- Evaluation of a function on the cluster at a vertex of the cluster. -/
noncomputable def cubeProj {U : TriadicCube d} (y : ↥(crossingClusterVertices ω U)) :
    Module.Dual ℝ (CubeFun ω U) :=
  LinearMap.proj (R := ℝ) (φ := fun _ : ↥(crossingClusterVertices ω U) => ℝ) y

theorem cubeProj_apply {U : TriadicCube d} (y : ↥(crossingClusterVertices ω U))
    (u : CubeFun ω U) : cubeProj y u = u y := rfl

/-- **Coarse pairing.** `ℓ_q u = ∑ q_i ([u]_𝒫(x + e_i) - [u]_𝒫(x))` over the lattice edges inside
`U`, which is `⟨q, ∇[u]_𝒫⟩_U` with each edge counted once. -/
noncomputable def cubeCoarsePairing (ω : Configuration d) (U : TriadicCube d) (q : Fin d → ℝ) :
    Module.Dual ℝ (CubeFun ω U) :=
  ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
    if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
      q i • (cubeEval ω U (partitionAnchor ω (x + LatticeProb.unit i)) -
        cubeEval ω U (partitionAnchor ω x))
    else 0

theorem cubeCoarsePairing_apply {U : TriadicCube d} (q : Fin d → ℝ) (u : CubeFun ω U) :
    cubeCoarsePairing ω U q u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin d,
      if x + LatticeProb.unit i ∈ U.toIntegerCube.vertices then
        q i * (cubeExtend ω U u (partitionAnchor ω (x + LatticeProb.unit i)) -
          cubeExtend ω U u (partitionAnchor ω x))
      else 0 := by
  simp only [cubeCoarsePairing, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, cubeEval_apply, smul_eq_mul]
  · simp

/-- **Flux pairing.** `F_p u = (1/2) ∑ p · (y - x) (u y - u x)` over ordered pairs of open
neighbours in `C_*(U)`, which is `⟨p, a∇u⟩_{C_*(U)}`. -/
noncomputable def cubeFluxPairing (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ) :
    Module.Dual ℝ (CubeFun ω U) :=
  (1 / 2 : ℝ) • ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
    if (openGraph ω).Adj x.1 y.1 then
      (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) • (cubeProj y - cubeProj x)
    else 0

theorem cubeFluxPairing_apply {U : TriadicCube d} (p : Fin d → ℝ) (u : CubeFun ω U) :
    cubeFluxPairing ω U p u = (1 / 2 : ℝ) * ∑ x, ∑ y,
      if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (u y - u x)
      else 0 := by
  simp only [cubeFluxPairing, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, cubeProj_apply, smul_eq_mul]
  · simp

/-- A vertex lies in the lattice interior `int(U)` of a triadic cube when all its lattice
neighbours lie in the cube (Armstrong and Dario, Section 1.2). -/
def TriadicCube.IsLatticeInterior (U : TriadicCube d) (x : Vertex d) : Prop :=
  ∀ y : Vertex d, (nearestNeighborGraph d).Adj x y → y ∈ U.vertices

/-- The Laplacian of a function on the cluster at a vertex. -/
noncomputable def cubeLaplacianAt (ω : Configuration d) (U : TriadicCube d)
    (x : ↥(crossingClusterVertices ω U)) : Module.Dual ℝ (CubeFun ω U) :=
  ∑ y : ↥(crossingClusterVertices ω U),
    if (openGraph ω).Adj x.1 y.1 then cubeProj y - cubeProj x else 0

theorem cubeLaplacianAt_apply {U : TriadicCube d} (x : ↥(crossingClusterVertices ω U))
    (u : CubeFun ω U) :
    cubeLaplacianAt ω U x u = ∑ y, if (openGraph ω).Adj x.1 y.1 then u y - u x else 0 := by
  simp only [cubeLaplacianAt, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp only [LinearMap.sub_apply, cubeProj_apply]
  · simp

/-- The space `A_*(U)` of functions on the cluster harmonic at its vertices in `int(U)`. -/
noncomputable def cubeHarmonic (ω : Configuration d) (U : TriadicCube d) :
    Submodule ℝ (CubeFun ω U) :=
  ⨅ (x : ↥(crossingClusterVertices ω U)) (_ : U.IsLatticeInterior x.1),
    LinearMap.ker (cubeLaplacianAt ω U x)

theorem mem_cubeHarmonic {U : TriadicCube d} {u : CubeFun ω U} :
    u ∈ cubeHarmonic ω U ↔
      ∀ x : ↥(crossingClusterVertices ω U), U.IsLatticeInterior x.1 →
        cubeLaplacianAt ω U x u = 0 := by
  simp only [cubeHarmonic, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Constant functions are harmonic. -/
theorem const_mem_cubeHarmonic {U : TriadicCube d} (c : ℝ) :
    (fun _ => c : CubeFun ω U) ∈ cubeHarmonic ω U := by
  rw [mem_cubeHarmonic]
  intro x _
  rw [cubeLaplacianAt_apply]
  exact Finset.sum_eq_zero fun y _ => by split_ifs <;> simp

/-- The coarse pairing vanishes on the null space of the Dirichlet form. -/
theorem cubeCoarsePairing_eq_zero_of_cubeForm (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (q : Fin d → ℝ) {u : CubeFun ω U}
    (h : cubeForm ω U u u = 0) : cubeCoarsePairing ω U q u = 0 := by
  rw [cubeCoarsePairing_apply]
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hxi
  · have hxU : x ∈ U.vertices := (U.mem_toIntegerCube_vertices x).1 hx
    have hxiU : x + LatticeProb.unit i ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hxi
    rw [cubeExtend_eq_of_cubeForm_self_eq_zero hd hP hU h
      (partitionAnchor_mem_crossingCluster_of_resolved hd hP hU hxiU)
      (partitionAnchor_mem_crossingCluster_of_resolved hd hP hU hxU)]
    ring
  · rfl

/-- The flux pairing vanishes on the null space of the Dirichlet form. -/
theorem cubeFluxPairing_eq_zero_of_cubeForm {U : TriadicCube d} (p : Fin d → ℝ)
    {u : CubeFun ω U} (h : cubeForm ω U u u = 0) : cubeFluxPairing ω U p u = 0 := by
  rw [cubeFluxPairing_apply]
  have hsum : ∑ x : ↥(crossingClusterVertices ω U), ∑ y : ↥(crossingClusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (u y - u x)
        else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by
      split_ifs with hxy
      · rw [eq_of_cubeForm_self_eq_zero h hxy]
        ring
      · rfl
  rw [hsum, mul_zero]

/-- The restriction of the Dirichlet form to `A_*(U)`. -/
noncomputable def cubeFormOn (ω : Configuration d) (U : TriadicCube d) :
    LinearMap.BilinForm ℝ (cubeHarmonic ω U) :=
  (cubeForm ω U).compl₁₂ (cubeHarmonic ω U).subtype (cubeHarmonic ω U).subtype

/-- **Optimizers.** For every linear functional on functions on the cluster vanishing on the
functions of zero energy, the first-variation equation has a solution in `A_*(U)`, which minimizes
`B u u / 2 - ℓ u` over `A_*(U)`. -/
theorem exists_cubeHarmonic_minimizer (U : TriadicCube d) (ℓ : Module.Dual ℝ (CubeFun ω U))
    (hℓ : ∀ u, cubeForm ω U u u = 0 → ℓ u = 0) :
    ∃ u ∈ cubeHarmonic ω U, ∀ w ∈ cubeHarmonic ω U,
      cubeForm ω U w u = ℓ w ∧
      cubeForm ω U u u / 2 - ℓ u ≤ cubeForm ω U w w / 2 - ℓ w := by
  set A := cubeHarmonic ω U
  obtain ⟨u, hu⟩ := LinearMap.BilinForm.exists_apply_eq_of_symm (cubeFormOn ω U)
    (fun u w => cubeForm_symm (u : CubeFun ω U) w) (ℓ.comp A.subtype)
    (fun u hu => hℓ u (hu u))
  refine ⟨u, u.2, fun w hw => ⟨hu ⟨w, hw⟩, ?_⟩⟩
  exact LinearMap.BilinForm.quadratic_le_of_apply_eq (cubeFormOn ω U)
    (fun u w => cubeForm_symm (u : CubeFun ω U) w)
    (fun v => cubeForm_self_nonneg (v : CubeFun ω U)) (ℓ.comp A.subtype) hu ⟨w, hw⟩

/-- The number `|U| = 3^{d n}` of vertices of a triadic cube of scale `n`, as a real number. -/
noncomputable def TriadicCube.latticeVolume (U : TriadicCube d) : ℝ := ((3 : ℝ) ^ U.scale) ^ d

theorem TriadicCube.latticeVolume_pos (U : TriadicCube d) : 0 < U.latticeVolume := by
  unfold TriadicCube.latticeVolume
  positivity

theorem TriadicCube.card_toIntegerCube_vertices (U : TriadicCube d) :
    (U.toIntegerCube.vertices.card : ℝ) = U.latticeVolume := by
  rw [IntegerCube.card_vertices_eq]
  unfold TriadicCube.latticeVolume
  change (((3 ^ U.scale) ^ d : ℕ) : ℝ) = _
  push_cast
  rfl

/-- The quantity `μ(U, q)` of Armstrong and Dario (Definition 4.1). -/
noncomputable def cubeMu (ω : Configuration d) (U : TriadicCube d) (q : Fin d → ℝ) : ℝ :=
  ⨅ u : cubeHarmonic ω U, (cubeForm ω U u u / 2 - cubeCoarsePairing ω U q u) / U.latticeVolume

/-- The quantity `ν(U, p)` of Armstrong and Dario (Definition 4.1). -/
noncomputable def cubeNu (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ) : ℝ :=
  ⨆ v : cubeHarmonic ω U, (cubeFluxPairing ω U p v - cubeForm ω U v v / 2) / U.latticeVolume

/-- **First variation for `μ`** (Armstrong and Dario, Lemma 4.2). On the partition event and for
a resolved cube, `μ(U, q)` is attained at a function `u ∈ A_*(U)` solving `B w u = ℓ_q w` for all
`w ∈ A_*(U)`. -/
theorem exists_cubeMu_minimizer (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    ∃ u ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w u = cubeCoarsePairing ω U q w) ∧
      cubeMu ω U q = (cubeForm ω U u u / 2 - cubeCoarsePairing ω U q u) / U.latticeVolume := by
  obtain ⟨u, hu, hmin⟩ := exists_cubeHarmonic_minimizer U (cubeCoarsePairing ω U q)
    (fun v hv => cubeCoarsePairing_eq_zero_of_cubeForm hd hP hU q hv)
  refine ⟨u, hu, fun w hw => (hmin w hw).1, ?_⟩
  have hvol := U.latticeVolume_pos
  set f : cubeHarmonic ω U → ℝ := fun w =>
    (cubeForm ω U w w / 2 - cubeCoarsePairing ω U q w) / U.latticeVolume with hf
  have hμ : cubeMu ω U q = ⨅ w, f w := rfl
  have hle : ∀ w, (cubeForm ω U u u / 2 - cubeCoarsePairing ω U q u) / U.latticeVolume ≤ f w :=
    fun w => div_le_div_of_nonneg_right ((hmin w.1 w.2).2) hvol.le
  have hfu : f ⟨u, hu⟩ =
      (cubeForm ω U u u / 2 - cubeCoarsePairing ω U q u) / U.latticeVolume := rfl
  rw [hμ]
  apply le_antisymm
  · rw [← hfu]
    exact ciInf_le ⟨f ⟨u, hu⟩, by rintro _ ⟨w, rfl⟩; rw [hfu]; exact hle w⟩ _
  · exact le_ciInf hle

/-- **First variation for `ν`** (Armstrong and Dario, Lemma 4.2). For every triadic cube, `ν(U, p)`
is attained at a function `v ∈ A_*(U)` solving `B w v = F_p w` for all `w ∈ A_*(U)`. -/
theorem exists_cubeNu_maximizer {U : TriadicCube d} (p : Fin d → ℝ) :
    ∃ v ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w v = cubeFluxPairing ω U p w) ∧
      cubeNu ω U p = (cubeFluxPairing ω U p v - cubeForm ω U v v / 2) / U.latticeVolume := by
  obtain ⟨v, hv, hmin⟩ := exists_cubeHarmonic_minimizer U (cubeFluxPairing ω U p)
    (fun w hw => cubeFluxPairing_eq_zero_of_cubeForm p hw)
  refine ⟨v, hv, fun w hw => (hmin w hw).1, ?_⟩
  have hvol := U.latticeVolume_pos
  set f : cubeHarmonic ω U → ℝ := fun w =>
    (cubeFluxPairing ω U p w - cubeForm ω U w w / 2) / U.latticeVolume with hf
  have hν : cubeNu ω U p = ⨆ w, f w := rfl
  have hle : ∀ w, f w ≤ (cubeFluxPairing ω U p v - cubeForm ω U v v / 2) / U.latticeVolume := by
    intro w
    refine div_le_div_of_nonneg_right ?_ hvol.le
    linarith [(hmin w.1 w.2).2]
  have hfv : f ⟨v, hv⟩ =
      (cubeFluxPairing ω U p v - cubeForm ω U v v / 2) / U.latticeVolume := rfl
  rw [hν]
  apply le_antisymm
  · exact ciSup_le hle
  · rw [← hfv]
    exact le_ciSup ⟨f ⟨v, hv⟩, by rintro _ ⟨w, rfl⟩; rw [hfv]; exact hle w⟩ _

end Rigidity.Percolation
