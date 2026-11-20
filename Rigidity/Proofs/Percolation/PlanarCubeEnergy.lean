import Rigidity.Proofs.Percolation.PlanarCubeCluster
import Rigidity.Proofs.Percolation.QuadraticVariation

/-!
# Subadditive energy quantities on the cluster of a resolved planar cube

For a resolved triadic cube `U`, functions on the cluster `C_*(U)` form a finite-dimensional space.
On it we consider

* the Dirichlet form `B u v = (1/2) ∑ (u x - u y) (v x - v y)` over ordered pairs of open
  neighbours in `C_*(U)`, so that `B u u / 2` is half the sum over open edges of the squared
  increments;
* the coarse pairing `ℓ_q u = ∑ q_i ([u](x + e_i) - [u](x))` over the lattice edges inside `U`,
  where `[u]` is the coarsening of `u` by the anchors of the partition cubes;
* the flux pairing `F_p u = ∑ p · (y - x) (u y - u x)` over open edges `{x, y}` of `C_*(U)`;
* the space `A_*(U)` of functions harmonic at the vertices of `C_*(U)` whose lattice neighbours all
  lie in `U`.

The quantities of Armstrong and Dario (Section 4.1) are
`μ(U, q) = inf_{u ∈ A_*(U)} (B u u / 2 - ℓ_q u) / |U|` and
`ν(U, p) = sup_{v ∈ A_*(U)} (F_p v - B v v / 2) / |U|`. The null space of `B` consists of the
functions constant on `C_*(U)`, on which both pairings vanish; hence both optimization problems
have optimizers, characterized by the first variation, with the second variation identity.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- The vertices of the cluster of a triadic cube, as a finite set. -/
noncomputable def clusterVertices (ω : Configuration 2) (U : TriadicCube 2) :
    Finset (Vertex 2) :=
  U.toIntegerCube.vertices.filter (· ∈ planarCubeCluster ω U)

theorem mem_clusterVertices {U : TriadicCube 2} {x : Vertex 2} :
    x ∈ clusterVertices ω U ↔ x ∈ planarCubeCluster ω U := by
  unfold clusterVertices
  rw [Finset.mem_filter, U.mem_toIntegerCube_vertices]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Functions on the cluster of a triadic cube. -/
abbrev ClusterFun (ω : Configuration 2) (U : TriadicCube 2) : Type :=
  ↥(clusterVertices ω U) → ℝ

/-- The extension by zero of a function on the cluster. -/
noncomputable def clusterExtend (ω : Configuration 2) (U : TriadicCube 2) :
    ClusterFun ω U →ₗ[ℝ] (Vertex 2 → ℝ) where
  toFun u x := if h : x ∈ clusterVertices ω U then u ⟨x, h⟩ else 0
  map_add' u v := by
    funext x
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem clusterExtend_apply_of_mem {U : TriadicCube 2} (u : ClusterFun ω U) {x : Vertex 2}
    (hx : x ∈ clusterVertices ω U) : clusterExtend ω U u x = u ⟨x, hx⟩ := by
  change (if h : x ∈ clusterVertices ω U then u ⟨x, h⟩ else 0) = _
  rw [dif_pos hx]

/-- The summand of the Dirichlet form. -/
noncomputable def clusterFormTerm (ω : Configuration 2) {U : TriadicCube 2}
    (u v : ClusterFun ω U) (x y : ↥(clusterVertices ω U)) : ℝ :=
  if (openGraph ω).Adj x.1 y.1 then (u x - u y) * (v x - v y) else 0

theorem clusterFormTerm_add_left {U : TriadicCube 2} (u₁ u₂ v : ClusterFun ω U)
    (x y : ↥(clusterVertices ω U)) :
    clusterFormTerm ω (u₁ + u₂) v x y =
      clusterFormTerm ω u₁ v x y + clusterFormTerm ω u₂ v x y := by
  simp only [clusterFormTerm, Pi.add_apply]
  split_ifs <;> ring

theorem clusterFormTerm_add_right {U : TriadicCube 2} (u v₁ v₂ : ClusterFun ω U)
    (x y : ↥(clusterVertices ω U)) :
    clusterFormTerm ω u (v₁ + v₂) x y =
      clusterFormTerm ω u v₁ x y + clusterFormTerm ω u v₂ x y := by
  simp only [clusterFormTerm, Pi.add_apply]
  split_ifs <;> ring

theorem clusterFormTerm_smul_left {U : TriadicCube 2} (c : ℝ) (u v : ClusterFun ω U)
    (x y : ↥(clusterVertices ω U)) :
    clusterFormTerm ω (c • u) v x y = c * clusterFormTerm ω u v x y := by
  simp only [clusterFormTerm, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem clusterFormTerm_smul_right {U : TriadicCube 2} (c : ℝ) (u v : ClusterFun ω U)
    (x y : ↥(clusterVertices ω U)) :
    clusterFormTerm ω u (c • v) x y = c * clusterFormTerm ω u v x y := by
  simp only [clusterFormTerm, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The Dirichlet form of the open edges of the cluster. -/
noncomputable def clusterForm (ω : Configuration 2) (U : TriadicCube 2) :
    LinearMap.BilinForm ℝ (ClusterFun ω U) :=
  LinearMap.mk₂ ℝ (fun u v => (1 / 2 : ℝ) * ∑ x, ∑ y, clusterFormTerm ω u v x y)
    (fun u₁ u₂ v => by
      simp only [clusterFormTerm_add_left, Finset.sum_add_distrib, mul_add])
    (fun c u v => by
      simp only [clusterFormTerm_smul_left, ← Finset.mul_sum, smul_eq_mul]
      ring)
    (fun u v₁ v₂ => by
      simp only [clusterFormTerm_add_right, Finset.sum_add_distrib, mul_add])
    (fun c u v => by
      simp only [clusterFormTerm_smul_right, ← Finset.mul_sum, smul_eq_mul]
      ring)

theorem clusterForm_apply {U : TriadicCube 2} (u v : ClusterFun ω U) :
    clusterForm ω U u v = (1 / 2 : ℝ) * ∑ x, ∑ y, clusterFormTerm ω u v x y := rfl

theorem clusterForm_symm {U : TriadicCube 2} (u v : ClusterFun ω U) :
    clusterForm ω U u v = clusterForm ω U v u := by
  rw [clusterForm_apply, clusterForm_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [clusterFormTerm]
  split_ifs <;> ring

theorem clusterForm_self_nonneg {U : TriadicCube 2} (u : ClusterFun ω U) :
    0 ≤ clusterForm ω U u u := by
  rw [clusterForm_apply]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
  simp only [clusterFormTerm]
  split_ifs
  · exact mul_self_nonneg _
  · exact le_rfl

/-- A function of zero energy is constant across the open edges of the cluster. -/
theorem eq_of_clusterForm_self_eq_zero {U : TriadicCube 2} {u : ClusterFun ω U}
    (h : clusterForm ω U u u = 0) {x y : ↥(clusterVertices ω U)}
    (hxy : (openGraph ω).Adj x.1 y.1) : u x = u y := by
  rw [clusterForm_apply] at h
  have hsum : ∑ x, ∑ y, clusterFormTerm ω u u x y = 0 := by linarith
  have hnn : ∀ x y, 0 ≤ clusterFormTerm ω u u x y := fun x y => by
    simp only [clusterFormTerm]
    split_ifs
    · exact mul_self_nonneg _
    · exact le_rfl
  have hx := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => hnn x y).1 hsum x (Finset.mem_univ x)
  have hxy' := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hnn x y).1 hx y (Finset.mem_univ y)
  simp only [clusterFormTerm, hxy, if_true] at hxy'
  have := mul_self_eq_zero.1 hxy'
  linarith

/-- A function constant across the open edges inside a set is constant along open paths inside
the set. -/
theorem eq_of_reachIn_of_adj_eq {f : Vertex 2 → ℝ} {S : Set (Vertex 2)}
    (hf : ∀ a ∈ S, ∀ b ∈ S, (openGraph ω).Adj a b → f a = f b) {x y : Vertex 2}
    (h : ReachIn ω S x y) : f x = f y := by
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

/-- Any two vertices of the cluster of a resolved cube are joined by an open path inside the
cluster. -/
theorem reachIn_clusterVertices (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {x y : Vertex 2} (hx : x ∈ planarCubeCluster ω U)
    (hy : y ∈ planarCubeCluster ω U) :
    ReachIn ω (↑(clusterVertices ω U)) x y := by
  have h : ReachIn ω U.vertices x y :=
    (hx.2.trans (reachIn_planarAnchor_of_resolved hP hU hx.1 hy.1)).trans hy.2.symm
  have h' := reachIn_planarCubeCluster hP hU le_rfl hx h
  refine h'.mono fun z hz => ?_
  rw [Finset.mem_coe, mem_clusterVertices]
  exact hz.2

/-- **Null space of the Dirichlet form.** On the cluster of a resolved cube, a function of zero
energy is constant. -/
theorem clusterExtend_eq_of_clusterForm_self_eq_zero (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) {u : ClusterFun ω U}
    (h : clusterForm ω U u u = 0) {x y : Vertex 2} (hx : x ∈ planarCubeCluster ω U)
    (hy : y ∈ planarCubeCluster ω U) :
    clusterExtend ω U u x = clusterExtend ω U u y := by
  refine eq_of_reachIn_of_adj_eq (S := ↑(clusterVertices ω U)) (fun a ha b hb hab => ?_)
    (reachIn_clusterVertices hP hU hx hy)
  rw [clusterExtend_apply_of_mem u ha, clusterExtend_apply_of_mem u hb]
  exact eq_of_clusterForm_self_eq_zero h (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) hab

/-- Evaluation of the extension at a vertex. -/
noncomputable def clusterEval (ω : Configuration 2) (U : TriadicCube 2) (x : Vertex 2) :
    Module.Dual ℝ (ClusterFun ω U) :=
  (LinearMap.proj x).comp (clusterExtend ω U)

theorem clusterEval_apply {U : TriadicCube 2} (x : Vertex 2) (u : ClusterFun ω U) :
    clusterEval ω U x u = clusterExtend ω U u x := rfl

/-- Evaluation of a function on the cluster at a vertex of the cluster. -/
noncomputable def clusterProj {U : TriadicCube 2} (y : ↥(clusterVertices ω U)) :
    Module.Dual ℝ (ClusterFun ω U) :=
  LinearMap.proj (R := ℝ) (φ := fun _ : ↥(clusterVertices ω U) => ℝ) y

theorem clusterProj_apply {U : TriadicCube 2} (y : ↥(clusterVertices ω U)) (u : ClusterFun ω U) :
    clusterProj y u = u y := rfl

/-- The unit vector in direction `i`. -/
def unitVertex (i : Fin 2) : Vertex 2 := Pi.single i 1

/-- **Coarse pairing.** `ℓ_q u = ∑ q_i ([u](x + e_i) - [u](x))` over lattice edges inside `U`. -/
noncomputable def coarsePairing (ω : Configuration 2) (U : TriadicCube 2) (q : Fin 2 → ℝ) :
    Module.Dual ℝ (ClusterFun ω U) :=
  ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
    if x + unitVertex i ∈ U.toIntegerCube.vertices then
      q i • (clusterEval ω U (planarCoarseAnchor ω (x + unitVertex i)) -
        clusterEval ω U (planarCoarseAnchor ω x))
    else 0

theorem coarsePairing_apply {U : TriadicCube 2} (q : Fin 2 → ℝ) (u : ClusterFun ω U) :
    coarsePairing ω U q u = ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
      if x + unitVertex i ∈ U.toIntegerCube.vertices then
        q i * (clusterExtend ω U u (planarCoarseAnchor ω (x + unitVertex i)) -
          clusterExtend ω U u (planarCoarseAnchor ω x))
      else 0 := by
  simp only [coarsePairing, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, clusterEval_apply, smul_eq_mul]
  · simp

/-- **Flux pairing.** `F_p u = (1/2) ∑ p · (y - x) (u y - u x)` over ordered pairs of open
neighbours in `C_*(U)`. -/
noncomputable def fluxPairing (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ) :
    Module.Dual ℝ (ClusterFun ω U) :=
  (1 / 2 : ℝ) • ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
    if (openGraph ω).Adj x.1 y.1 then
      (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) • (clusterProj y - clusterProj x)
    else 0

theorem fluxPairing_apply {U : TriadicCube 2} (p : Fin 2 → ℝ) (u : ClusterFun ω U) :
    fluxPairing ω U p u = (1 / 2 : ℝ) * ∑ x, ∑ y,
      if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (u y - u x)
      else 0 := by
  simp only [fluxPairing, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, clusterProj_apply, smul_eq_mul]
  · simp

/-- A vertex is interior to a triadic cube when its lattice neighbourhood lies in the cube. -/
def TriadicCube.IsInterior (U : TriadicCube 2) (x : Vertex 2) : Prop :=
  ∀ y : Vertex 2, (∀ i, |x i - y i| ≤ 1) → y ∈ U.vertices

/-- The Laplacian of a function on the cluster at a vertex. -/
noncomputable def clusterLaplacianAt (ω : Configuration 2) (U : TriadicCube 2)
    (x : ↥(clusterVertices ω U)) : Module.Dual ℝ (ClusterFun ω U) :=
  ∑ y : ↥(clusterVertices ω U),
    if (openGraph ω).Adj x.1 y.1 then clusterProj y - clusterProj x else 0

theorem clusterLaplacianAt_apply {U : TriadicCube 2} (x : ↥(clusterVertices ω U))
    (u : ClusterFun ω U) :
    clusterLaplacianAt ω U x u = ∑ y, if (openGraph ω).Adj x.1 y.1 then u y - u x else 0 := by
  simp only [clusterLaplacianAt, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp only [LinearMap.sub_apply, clusterProj_apply]
  · simp

/-- The space `A_*(U)` of functions on the cluster harmonic at its interior vertices. -/
noncomputable def clusterHarmonic (ω : Configuration 2) (U : TriadicCube 2) :
    Submodule ℝ (ClusterFun ω U) :=
  ⨅ (x : ↥(clusterVertices ω U)) (_ : U.IsInterior x.1),
    LinearMap.ker (clusterLaplacianAt ω U x)

theorem mem_clusterHarmonic {U : TriadicCube 2} {u : ClusterFun ω U} :
    u ∈ clusterHarmonic ω U ↔
      ∀ x : ↥(clusterVertices ω U), U.IsInterior x.1 → clusterLaplacianAt ω U x u = 0 := by
  simp only [clusterHarmonic, Submodule.mem_iInf, LinearMap.mem_ker]

/-- Constant functions are harmonic. -/
theorem const_mem_clusterHarmonic {U : TriadicCube 2} (c : ℝ) :
    (fun _ => c : ClusterFun ω U) ∈ clusterHarmonic ω U := by
  rw [mem_clusterHarmonic]
  intro x _
  rw [clusterLaplacianAt_apply]
  exact Finset.sum_eq_zero fun y _ => by split_ifs <;> simp

/-- Both pairings vanish on the null space of the Dirichlet form. -/
theorem coarsePairing_eq_zero_of_clusterForm (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) {u : ClusterFun ω U}
    (h : clusterForm ω U u u = 0) : coarsePairing ω U q u = 0 := by
  rw [coarsePairing_apply]
  refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hxi
  · have hxU : x ∈ U.vertices := (U.mem_toIntegerCube_vertices x).1 hx
    have hxiU : x + unitVertex i ∈ U.vertices := (U.mem_toIntegerCube_vertices _).1 hxi
    rw [planarCoarseAnchor, planarCoarseAnchor, clusterExtend_eq_of_clusterForm_self_eq_zero hP hU h
      (planarAnchor_mem_planarCubeCluster hP hU hxiU)
      (planarAnchor_mem_planarCubeCluster hP hU hxU)]
    ring
  · rfl

theorem fluxPairing_eq_zero_of_clusterForm {U : TriadicCube 2} (p : Fin 2 → ℝ)
    {u : ClusterFun ω U} (h : clusterForm ω U u u = 0) : fluxPairing ω U p u = 0 := by
  rw [fluxPairing_apply]
  have hsum : ∑ x : ↥(clusterVertices ω U), ∑ y : ↥(clusterVertices ω U),
      (if (openGraph ω).Adj x.1 y.1 then (∑ i, p i * ((y.1 i : ℝ) - x.1 i)) * (u y - u x)
        else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by
      split_ifs with hxy
      · rw [eq_of_clusterForm_self_eq_zero h hxy]
        ring
      · rfl
  rw [hsum, mul_zero]

/-- The restriction of a bilinear form to a submodule. -/
noncomputable def clusterFormOn (ω : Configuration 2) (U : TriadicCube 2) :
    LinearMap.BilinForm ℝ (clusterHarmonic ω U) :=
  (clusterForm ω U).compl₁₂ (clusterHarmonic ω U).subtype (clusterHarmonic ω U).subtype

/-- **Optimizers.** For every linear functional on functions on the cluster vanishing on the
functions of zero energy, the first-variation equation has a solution in `A_*(U)`, which minimizes
`B u u / 2 - ℓ u` over `A_*(U)`. -/
theorem exists_clusterHarmonic_minimizer (U : TriadicCube 2) (ℓ : Module.Dual ℝ (ClusterFun ω U))
    (hℓ : ∀ u, clusterForm ω U u u = 0 → ℓ u = 0) :
    ∃ u ∈ clusterHarmonic ω U, ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w u = ℓ w ∧
      clusterForm ω U u u / 2 - ℓ u ≤ clusterForm ω U w w / 2 - ℓ w := by
  set A := clusterHarmonic ω U
  obtain ⟨u, hu⟩ := LinearMap.BilinForm.exists_apply_eq_of_symm (clusterFormOn ω U)
    (fun u w => clusterForm_symm (u : ClusterFun ω U) w) (ℓ.comp A.subtype)
    (fun u hu => hℓ u (hu u))
  refine ⟨u, u.2, fun w hw => ⟨hu ⟨w, hw⟩, ?_⟩⟩
  exact LinearMap.BilinForm.quadratic_le_of_apply_eq (clusterFormOn ω U)
    (fun u w => clusterForm_symm (u : ClusterFun ω U) w)
    (fun v => clusterForm_self_nonneg (v : ClusterFun ω U)) (ℓ.comp A.subtype) hu ⟨w, hw⟩

/-- The number of vertices of a triadic cube. -/
def TriadicCube.volume (U : TriadicCube 2) : ℝ := (9 : ℝ) ^ U.scale

/-- The quantity `μ(U, q)` of Armstrong and Dario. -/
noncomputable def planarMu (ω : Configuration 2) (U : TriadicCube 2) (q : Fin 2 → ℝ) : ℝ :=
  ⨅ u : clusterHarmonic ω U,
    (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume

/-- The quantity `ν(U, p)` of Armstrong and Dario. -/
noncomputable def planarNu (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ) : ℝ :=
  ⨆ v : clusterHarmonic ω U,
    (fluxPairing ω U p v - clusterForm ω U v v / 2) / U.volume

theorem TriadicCube.volume_pos (U : TriadicCube 2) : 0 < U.volume := by
  unfold TriadicCube.volume
  positivity

/-- **First and second variations for `μ`** (Armstrong and Dario, Lemma 4.1). On the partition
event and for a resolved cube, `μ(U, q)` is attained at a function `u ∈ A_*(U)` solving
`B w u = ℓ_q w` for all `w ∈ A_*(U)`. -/
theorem exists_planarMu_minimizer (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    ∃ u ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w u = coarsePairing ω U q w) ∧
      planarMu ω U q = (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume := by
  obtain ⟨u, hu, hmin⟩ := exists_clusterHarmonic_minimizer U (coarsePairing ω U q)
    (fun v hv => coarsePairing_eq_zero_of_clusterForm hP hU q hv)
  refine ⟨u, hu, fun w hw => (hmin w hw).1, ?_⟩
  have hvol := U.volume_pos
  set f : clusterHarmonic ω U → ℝ := fun w =>
    (clusterForm ω U w w / 2 - coarsePairing ω U q w) / U.volume with hf
  have hμ : planarMu ω U q = ⨅ w, f w := rfl
  have hle : ∀ w, (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume ≤ f w :=
    fun w => div_le_div_of_nonneg_right ((hmin w.1 w.2).2) hvol.le
  have hfu : f ⟨u, hu⟩ = (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume := rfl
  rw [hμ]
  apply le_antisymm
  · rw [← hfu]
    exact ciInf_le ⟨f ⟨u, hu⟩, by rintro _ ⟨w, rfl⟩; rw [hfu]; exact hle w⟩ _
  · exact le_ciInf hle

/-- **First and second variations for `ν`** (Armstrong and Dario, Lemma 4.1). On the partition
event and for a resolved cube, `ν(U, p)` is attained at a function `v ∈ A_*(U)` solving
`B w v = F_p w` for all `w ∈ A_*(U)`. -/
theorem exists_planarNu_maximizer {U : TriadicCube 2} (p : Fin 2 → ℝ) :
    ∃ v ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w v = fluxPairing ω U p w) ∧
      planarNu ω U p = (fluxPairing ω U p v - clusterForm ω U v v / 2) / U.volume := by
  obtain ⟨v, hv, hmin⟩ := exists_clusterHarmonic_minimizer U (fluxPairing ω U p)
    (fun w hw => fluxPairing_eq_zero_of_clusterForm p hw)
  refine ⟨v, hv, fun w hw => (hmin w hw).1, ?_⟩
  have hvol := U.volume_pos
  set f : clusterHarmonic ω U → ℝ := fun w =>
    (fluxPairing ω U p w - clusterForm ω U w w / 2) / U.volume with hf
  have hν : planarNu ω U p = ⨆ w, f w := rfl
  have hle : ∀ w, f w ≤ (fluxPairing ω U p v - clusterForm ω U v v / 2) / U.volume := by
    intro w
    refine div_le_div_of_nonneg_right ?_ hvol.le
    linarith [(hmin w.1 w.2).2]
  have hfv : f ⟨v, hv⟩ = (fluxPairing ω U p v - clusterForm ω U v v / 2) / U.volume := rfl
  rw [hν]
  apply le_antisymm
  · exact ciSup_le hle
  · rw [← hfv]
    exact le_ciSup ⟨f ⟨v, hv⟩, by rintro _ ⟨w, rfl⟩; rw [hfv]; exact hle w⟩ _

end Rigidity.Percolation
