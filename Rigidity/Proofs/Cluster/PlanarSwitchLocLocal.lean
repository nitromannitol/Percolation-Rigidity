import Rigidity.Proofs.Cluster.PlanarSwitchLocGeom
import Rigidity.Proofs.Percolation.PlanarNuLocal

/-!
# The localized pairing of display (5.31) of Armstrong and Dario

Let `V` be a triadic cube, `k` a scale and `D` the interior square of `V` at distance `6 · 3^k`
from its complement. On the event `PlanarCapGood k V` that the partition exists and agrees on `V`
with the partition capped at scale `k`, the partition cubes of the vertices of `D`, their squares of
side `9s` and the cubes deciding the capped partition there lie inside `V`. Hence two
configurations of this event with the same open edges inside `V` have the same coarse anchors on
`D` (`planarCoarseAnchor_eq_of_capGood`) and the same cluster `C_*(V)` (the vertices of `V`
joined inside `V` to the anchor of the centre, `clusterVertices_iff_of_capGood`).

The localized pairing `switchLocValue` is `|V|⁻¹ ℓ_{g|D}(u_loc)`, where `u_loc` solves the first
variation with the field `q|D` (the local minimizer of Armstrong and Dario, Proposition 4.10, whose
coarse pairing is taken only inside `V^{(k)}`); by polarization it is a combination of the
quantities `μ_{g,0}` for fields supported on the edges inside `D`. It is therefore the same for two
configurations of the event with the same open edges inside `V` (`switchLocValue_eq_of_capGood`).
Its value at a configuration of the event with the given open edges inside `V`, clamped to
`[-M, M]`, is measurable for the bonds inside `V` (`switchLoc`), and these are independent for
disjoint cubes (`indepFun_switchLoc`), as in display (e.munuloc).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω ω' : Configuration 2}

/-- The partition exists and agrees on `V` with the partition capped at scale `k`. -/
def PlanarCapGood (k : ℕ) (V : TriadicCube 2) (ω : Configuration 2) : Prop :=
  PlanarPartitionEvent ω ∧
    ∀ x ∈ V.vertices, planarPartCube ω x = TriadicCube.cappedCube (planarGoodCubes ω) k x

theorem PlanarCapGood.scale_le {k : ℕ} {V : TriadicCube 2} (h : PlanarCapGood k V ω) :
    ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ k := fun x hx => by
  rw [h.2 x hx]
  exact TriadicCube.scale_cappedCube_le _ _ _

theorem PlanarCapGood.resolved {k : ℕ} {V : TriadicCube 2} (h : PlanarCapGood k V ω)
    (hk : k ≤ V.scale) : PlanarResolved ω V := fun x hx => (h.scale_le x hx).trans hk

/-- The open edges inside `V`. -/
noncomputable def adjData (V : TriadicCube 2) (ω : Configuration 2) :
    Finset (Vertex 2 × Vertex 2) :=
  (V.toIntegerCube.vertices ×ˢ V.toIntegerCube.vertices).filter
    fun e => (openGraph ω).Adj e.1 e.2

theorem adj_iff_of_adjData_eq {V : TriadicCube 2} (h : adjData V ω = adjData V ω') :
    ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) := by
  intro x hx y hy
  have hxS : x ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices x).2 hx
  have hyS : y ∈ V.toIntegerCube.vertices := (V.mem_toIntegerCube_vertices y).2 hy
  have h2 := Finset.ext_iff.1 h (x, y)
  simp only [adjData, Finset.mem_filter, Finset.mem_product, hxS, hyS, true_and] at h2
  exact h2.symm

/-- The interior vertices used by the localized pairing. -/
noncomputable def switchInterior (k : ℕ) (V : TriadicCube 2) : Finset (Vertex 2) :=
  (interiorCube V (6 * 3 ^ k)).vertices

theorem mem_vertices_of_near_switchInterior {k : ℕ} {V : TriadicCube 2}
    (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale) {x y : Vertex 2} (hx : x ∈ switchInterior k V)
    (hy : ∀ i, |y i - x i| ≤ 6 * 3 ^ k) : y ∈ V.vertices :=
  (V.mem_toIntegerCube_vertices y).1
    (mem_toIntegerCube_vertices_of_near_interiorCube h2r hx fun i => by exact_mod_cast hy i)

theorem switchInterior_subset {k : ℕ} {V : TriadicCube 2} (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale) :
    switchInterior k V ⊆ V.toIntegerCube.vertices :=
  interiorCube_subset h2r

/-- **Locality of the capped partition in the interior.** -/
theorem cappedCube_eq_of_adj_iff {k : ℕ} {V : TriadicCube 2}
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale) {x : Vertex 2} (hx : x ∈ switchInterior k V) :
    TriadicCube.cappedCube (planarGoodCubes ω') k x =
      TriadicCube.cappedCube (planarGoodCubes ω) k x := by
  refine TriadicCube.cappedCube_eq_of_agree fun T hT hnear => ?_
  have hsub : ∀ y ∈ (↑T.ninefold.vertices : Set (Vertex 2)), y ∈ V.vertices := by
    intro y hy
    refine mem_vertices_of_near_switchInterior h2r hx fun i => ?_
    rw [TriadicCube.mem_ninefold] at hy
    have h1 := hy i
    have h2 := hnear T.center T.center_mem i
    have h4 := T.two_mul_ninefoldRadius
    have hsT : T.side = 3 ^ T.scale := rfl
    have hpow : 3 * (3 : ℤ) ^ T.scale ≤ 3 ^ k := by
      calc 3 * (3 : ℤ) ^ T.scale = 3 ^ (T.scale + 1) := by ring
        _ ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) hT
    have h5 := abs_sub_le (y i) (T.center i) (x i)
    rw [abs_sub_comm (T.center i) (x i)] at h5
    rw [hsT] at h2
    have h6 : (0 : ℤ) < 3 ^ T.scale := by positivity
    linarith
  exact mem_planarGoodCubes_iff_of_adj_iff fun y hy z hz => hagree y (hsub y hy) z (hsub z hz)

/-- **Locality of the coarse anchors in the interior.** -/
theorem planarCoarseAnchor_eq_of_capGood {k : ℕ} {V : TriadicCube 2} (hω : PlanarCapGood k V ω)
    (hω' : PlanarCapGood k V ω')
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale) {x : Vertex 2} (hx : x ∈ switchInterior k V) :
    planarCoarseAnchor ω' x = planarCoarseAnchor ω x := by
  have hxV : x ∈ V.vertices := (V.mem_toIntegerCube_vertices x).1 (switchInterior_subset h2r hx)
  have hQ : planarPartCube ω' x = planarPartCube ω x := by
    rw [hω'.2 x hxV, hω.2 x hxV]
    exact cappedCube_eq_of_adj_iff hagree h2r hx
  have hsub : ∀ y ∈ (↑(planarPartCube ω x).ninefold.vertices : Set (Vertex 2)), y ∈ V.vertices := by
    intro y hy
    refine mem_vertices_of_near_switchInterior h2r hx fun i => ?_
    have h1 := abs_sub_le_of_mem_ninefold (planarPartCube_spec hω.1 x).1 hy i
    have h2 : (3 : ℤ) ^ (planarPartCube ω x).scale ≤ 3 ^ k :=
      pow_le_pow_right₀ (by norm_num) (hω.scale_le x hxV)
    have h6 : (0 : ℤ) < 3 ^ k := by positivity
    linarith
  unfold planarCoarseAnchor
  rw [hQ]
  refine (planarAnchor_eq_of_filter_eq ⟨(planarPartCube_meshed hω.1 x).1,
    planarPartCube_large hω.1 x⟩ (by rw [← hQ]; exact ⟨(planarPartCube_meshed hω'.1 x).1,
      planarPartCube_large hω'.1 x⟩) ?_).symm
  refine Finset.filter_congr fun e _ => ?_
  exact (TriadicCube.isPlanarAnchor_iff_of_adj_iff (fun y hy z hz =>
    hagree y (hsub y hy) z (hsub z hz)) _).symm

/-- On a resolved cube the cluster consists of the vertices joined inside the cube to the anchor
of any of its vertices. -/
theorem mem_planarCubeCluster_iff_reachIn (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) {z : Vertex 2} (hz : z ∈ V.vertices) (x : Vertex 2) :
    x ∈ planarCubeCluster ω V ↔ x ∈ V.vertices ∧ ReachIn ω V.vertices x (planarCoarseAnchor ω z) :=
  ⟨fun h => ⟨h.1, h.2.trans (reachIn_planarAnchor_of_resolved hP hV h.1 hz)⟩,
    fun h => mem_planarCubeCluster_of_reachIn hP hV h.1 hz h.2⟩

/-- **Locality of the cluster.** -/
theorem clusterVertices_iff_of_capGood {k : ℕ} {V : TriadicCube 2} (hω : PlanarCapGood k V ω)
    (hω' : PlanarCapGood k V ω') (hk : k ≤ V.scale)
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (hc : planarCoarseAnchor ω' V.center = planarCoarseAnchor ω V.center) (x : Vertex 2) :
    x ∈ clusterVertices ω' V ↔ x ∈ clusterVertices ω V := by
  rw [mem_clusterVertices, mem_clusterVertices,
    mem_planarCubeCluster_iff_reachIn hω'.1 (hω'.resolved hk) V.center_mem,
    mem_planarCubeCluster_iff_reachIn hω.1 (hω.resolved hk) V.center_mem]
  have hc' : planarCoarseAnchor ω' (fun i => V.side * V.index i) =
      planarCoarseAnchor ω (fun i => V.side * V.index i) := hc
  rw [hc']
  exact and_congr_right fun _ => reachIn_iff_of_adj_iff hagree _ _

/-- `μ_{g,p}` depends only on the cluster, the open edges between its vertices and the coarse
anchors on `D`, for a field supported on the edges inside `D`. -/
theorem planarMuGen_eq_of_cluster_anchor_eq_on {U : TriadicCube 2}
    (hC : ∀ x, x ∈ clusterVertices ω' U ↔ x ∈ clusterVertices ω U)
    (hadj : ∀ x ∈ clusterVertices ω U, ∀ y ∈ clusterVertices ω U,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    {D : Finset (Vertex 2)} (hanc : ∀ x ∈ D, planarCoarseAnchor ω' x = planarCoarseAnchor ω x)
    (g : Vertex 2 → Fin 2 → ℝ) (hg : ∀ x i, ¬(x ∈ D ∧ x + unitVertex i ∈ D) → g x i = 0)
    (p : Fin 2 → ℝ) :
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
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · by_cases hD : x ∈ D ∧ x + unitVertex i ∈ D
    · rw [hanc _ hD.2, hanc _ hD.1, hext, hext]
    · rw [hg x i hD, zero_mul, zero_mul]
  · rfl

/-- The fields of the localized pairing are supported on the edges inside `D`. -/
theorem restrictField_eq_zero {D : Finset (Vertex 2)} (g : Vertex 2 → Fin 2 → ℝ) {x : Vertex 2}
    {i : Fin 2} (h : ¬(x ∈ D ∧ x + unitVertex i ∈ D)) : restrictField D g x i = 0 := by
  simp only [restrictField, if_neg h]

/-- **The localized pairing** `|V|⁻¹ ℓ_{g|D}(u_loc)`, written through polarization: minus the
combination `μ_{g|D + q|D, 0} - μ_{g|D, 0} - μ_{q|D, 0}`. -/
noncomputable def switchLocValue (k : ℕ) (V : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ)
    (q : Fin 2 → ℝ) (ω : Configuration 2) : ℝ :=
  if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
    -(planarMuGen ω V (restrictField (switchInterior k V) g +
          restrictField (switchInterior k V) (fun _ => q)) 0 -
        planarMuGen ω V (restrictField (switchInterior k V) g) 0 -
        planarMuGen ω V (restrictField (switchInterior k V) (fun _ => q)) 0)
  else 0

/-- **Locality of the localized pairing.** -/
theorem switchLocValue_eq_of_capGood {k : ℕ} {V : TriadicCube 2} (hω : PlanarCapGood k V ω)
    (hω' : PlanarCapGood k V ω') (hk : k ≤ V.scale) (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale)
    (hagree : ∀ x ∈ V.vertices, ∀ y ∈ V.vertices, ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y))
    (hcI : V.center ∈ switchInterior k V) (g : Vertex 2 → Fin 2 → ℝ) (q : Fin 2 → ℝ) :
    switchLocValue k V g q ω' = switchLocValue k V g q ω := by
  have hanc : ∀ x ∈ switchInterior k V, planarCoarseAnchor ω' x = planarCoarseAnchor ω x :=
    fun x hx => planarCoarseAnchor_eq_of_capGood hω hω' hagree h2r hx
  have hC := clusterVertices_iff_of_capGood hω hω' hk hagree (hanc _ hcI)
  have hadj : ∀ x ∈ clusterVertices ω V, ∀ y ∈ clusterVertices ω V,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y) := fun x hx y hy =>
    hagree x ((mem_clusterVertices.1 hx).1)
      y ((mem_clusterVertices.1 hy).1)
  have hsupp : ∀ f : Vertex 2 → Fin 2 → ℝ, ∀ x i,
      ¬(x ∈ switchInterior k V ∧ x + unitVertex i ∈ switchInterior k V) →
        restrictField (switchInterior k V) f x i = 0 := fun f x i h => restrictField_eq_zero f h
  have e := fun f hf => planarMuGen_eq_of_cluster_anchor_eq_on (U := V) hC hadj hanc f hf 0
  unfold switchLocValue
  rw [if_pos ⟨hω'.1, hω'.resolved hk⟩, if_pos ⟨hω.1, hω.resolved hk⟩,
    e _ (hsupp _), e _ (hsupp _),
    e _ fun x i h => by rw [Pi.add_apply, Pi.add_apply, hsupp _ x i h, hsupp _ x i h, add_zero]]

/-- The value of the localized pairing at a configuration of the event with the given open edges
inside `V`. -/
noncomputable def switchLocOf (k : ℕ) (V : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ)
    (q : Fin 2 → ℝ) (t : Finset (Vertex 2 × Vertex 2)) : ℝ :=
  if h : ∃ ω, PlanarCapGood k V ω ∧ adjData V ω = t then switchLocValue k V g q h.choose else 0

/-- **The local version of the pairing**, clamped to `[-M, M]`. -/
noncomputable def switchLoc (k : ℕ) (V : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ)
    (q : Fin 2 → ℝ) (M : ℝ) (ω : Configuration 2) : ℝ :=
  max (-M) (min M (switchLocOf k V g q (adjData V ω)))

theorem switchLocOf_eq_of_capGood {k : ℕ} {V : TriadicCube 2} (hω : PlanarCapGood k V ω)
    (hk : k ≤ V.scale) (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale)
    (hcI : V.center ∈ switchInterior k V) (g : Vertex 2 → Fin 2 → ℝ) (q : Fin 2 → ℝ) :
    switchLocOf k V g q (adjData V ω) = switchLocValue k V g q ω := by
  have h : ∃ ω', PlanarCapGood k V ω' ∧ adjData V ω' = adjData V ω := ⟨ω, hω, rfl⟩
  rw [switchLocOf, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact switchLocValue_eq_of_capGood hω h1 hk h2r (adj_iff_of_adjData_eq h2.symm) hcI g q

theorem abs_switchLoc_le {k : ℕ} {V : TriadicCube 2} (g : Vertex 2 → Fin 2 → ℝ)
    (q : Fin 2 → ℝ) {M : ℝ} (hM : 0 ≤ M) (ω : Configuration 2) :
    |switchLoc k V g q M ω| ≤ M := by
  unfold switchLoc
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Clamping to `[-M, M]` does not increase the distance to a point of `[-M, M]`. -/
theorem abs_sub_clamp_le {X Y M : ℝ} (hX : |X| ≤ M) : |X - max (-M) (min M Y)| ≤ |X - Y| := by
  obtain ⟨h1, h2⟩ := abs_le.1 hX
  rcases le_total Y M with hYM | hYM
  · rw [min_eq_right hYM]
    rcases le_total (-M) Y with hY | hY
    · rw [max_eq_right hY]
    · rw [max_eq_left hY, abs_of_nonneg (by linarith : 0 ≤ X - -M),
        abs_of_nonneg (by linarith : 0 ≤ X - Y)]
      linarith
  · rw [min_eq_left hYM, max_eq_right (by linarith : -M ≤ M),
      abs_of_nonpos (by linarith : X - M ≤ 0), abs_of_nonpos (by linarith : X - Y ≤ 0)]
    linarith

theorem switchLoc_eq_of_capGood {k : ℕ} {V : TriadicCube 2} (hω : PlanarCapGood k V ω)
    (hk : k ≤ V.scale) (h2r : 2 * (6 * 3 ^ k) ≤ 3 ^ V.scale)
    (hcI : V.center ∈ switchInterior k V) (g : Vertex 2 → Fin 2 → ℝ) (q : Fin 2 → ℝ) (M : ℝ) :
    switchLoc k V g q M ω = max (-M) (min M (switchLocValue k V g q ω)) := by
  rw [switchLoc, switchLocOf_eq_of_capGood hω hk h2r hcI]

theorem measurableSet_adjData_eq (V : TriadicCube 2) (t : Finset (Vertex 2 × Vertex 2)) :
    MeasurableSet (adjData V ⁻¹' {t}) :=
  measurableSet_filter_eq _ _ fun e => measurableSet_setOf.1 (measurableSet_openGraph_adj e.1 e.2)

theorem measurable_switchLoc (k : ℕ) (V : TriadicCube 2) (g : Vertex 2 → Fin 2 → ℝ)
    (q : Fin 2 → ℝ) (M : ℝ) : Measurable (switchLoc k V g q M) :=
  measurable_of_fiber_const (adjData V) (measurableSet_adjData_eq V) fun _ _ h => by
    simp only [switchLoc, h]

/-- **Locality of the local version** (display (e.munuloc)): it is measurable for the bonds inside
`V`. -/
theorem measurable_switchLoc_localBondSigma (k : ℕ) (V : TriadicCube 2)
    (g : Vertex 2 → Fin 2 → ℝ) (q : Fin 2 → ℝ) (M : ℝ) :
    Measurable[localBondSigma V.vertices] (switchLoc k V g q M) :=
  measurable_localBondSigma_of_eq _ (measurable_switchLoc k V g q M) fun ω ω' h => by
    have hagree := adj_iff_of_localBonds h
    have hD : adjData V ω' = adjData V ω := by
      refine Finset.filter_congr fun e he => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 he
      exact hagree e.1 ((V.mem_toIntegerCube_vertices _).1 h1) e.2
        ((V.mem_toIntegerCube_vertices _).1 h2)
    simp only [switchLoc, hD]

/-- **Independence of the local versions** on disjoint cubes. -/
theorem indepFun_switchLoc (p : unitInterval) {k : ℕ} {V W : TriadicCube 2}
    (hVW : Disjoint V.vertices W.vertices) (g g' : Vertex 2 → Fin 2 → ℝ) (q : Fin 2 → ℝ)
    (M : ℝ) :
    IndepFun (switchLoc k V g q M) (switchLoc k W g' q M) (latticeBondLaw 2 p) :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hVW)
      (measurable_switchLoc_localBondSigma k V g q M).comap_le)
    (measurable_switchLoc_localBondSigma k W g' q M).comap_le)

end Rigidity.Proofs.Cluster
