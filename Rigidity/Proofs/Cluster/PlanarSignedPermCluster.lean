import Rigidity.Proofs.Cluster.PlanarSignedPermMesh
import Rigidity.Proofs.Percolation.PlanarClusterTransport
import Rigidity.Proofs.Percolation.PlanarNuQuadratic

/-!
# Symmetries of the planar cluster and of `ν`

Let `φ` be a signed permutation of `ℤ²` under which the strip meshes of the squares are carried to
those of their images (`hmesh`). On the partition event, for a resolved triadic cube `U`:

* any anchor of the image `φ(Q)` of a meshed cube `Q` in the transported configuration is, moved
  back, joined inside `Q` to the anchor of `Q`, since both are joined to every long open path;
* hence the cluster `C_*(φ(U))` of the transported configuration is the image of `C_*(U)`, the
  interior vertices correspond, and `ν(φ(U), φ(p)) = ν(U, p)` for the transported slope
  `φ(p)ᵢ = sᵢ p_{π i}`, which keeps the displacement pairing `p · (y − x)` of every edge.

Since the bond law is invariant under `φ` and `φ(□_m) = □_m`, the expectations of `ν(□_m, ·)` on
the partition event, hence their limits, are invariant: `ν̄(φ(ξ)) = ν̄(ξ)`. With the reflection
`x ↦ (-x₀, x₁)` and the transposition `x ↦ (x₁, x₀)` this gives
`ā = σ I` (`planarAhom_eq_smul_one`), the remark of Armstrong and Dario before (5.20) that `ā` is a
multiple of the identity by the symmetries of the model.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Proofs.S3 Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

section Relabel

variable {ω ω' : Configuration 2} {U U' : TriadicCube 2}
  (e : ↥(clusterVertices ω U) ≃ ↥(clusterVertices ω' U'))

theorem fluxPairing_comp_symm_slope
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (p p' : Fin 2 → ℝ)
    (hdisp : ∀ x y, ∑ i, p' i * (((e y).1 i : ℝ) - (e x).1 i) = ∑ i, p i * ((y.1 i : ℝ) - x.1 i))
    (u : ClusterFun ω U) :
    fluxPairing ω' U' p' (u ∘ e.symm) = fluxPairing ω U p u := by
  rw [fluxPairing_apply, fluxPairing_apply]
  congr 1
  refine (Fintype.sum_equiv e.symm _ _ fun x => ?_)
  refine (Fintype.sum_equiv e.symm _ _ fun y => ?_)
  have h := hadj (e.symm x) (e.symm y)
  have hd := hdisp (e.symm x) (e.symm y)
  simp only [Equiv.apply_symm_apply] at h hd
  simp only [Function.comp_apply, h, hd]

/-- **Relabelling invariance of `ν` with a change of slope.** A bijection of clusters which
respects open edges and interior vertices and carries the displacement pairing with `p` to the
displacement pairing with `p'` gives `ν(U', p') = ν(U, p)`. -/
theorem planarNu_eq_of_equiv_slope
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (p p' : Fin 2 → ℝ)
    (hdisp : ∀ x y, ∑ i, p' i * (((e y).1 i : ℝ) - (e x).1 i) = ∑ i, p i * ((y.1 i : ℝ) - x.1 i))
    (hint : ∀ x, U'.IsInterior (e x).1 ↔ U.IsInterior x.1) (hvol : U'.volume = U.volume) :
    planarNu ω' U' p' = planarNu ω U p := by
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
  unfold planarNu
  symm
  refine Equiv.iSup_congr E fun w => ?_
  change (fluxPairing ω' U' p' (w.1 ∘ e.symm) -
      clusterForm ω' U' (w.1 ∘ e.symm) (w.1 ∘ e.symm) / 2) / U'.volume = _
  rw [fluxPairing_comp_symm_slope e hadj p p' hdisp, clusterForm_comp_symm e hadj, hvol]

end Relabel

variable (π : Equiv.Perm (Fin 2)) (s : Fin 2 → ℤˣ)

/-- The hypothesis that the strip meshes of the squares are carried to those of their images. -/
def MeshInvariant : Prop :=
  ∀ (ω : Configuration 2) (R : IntegerCube 2) (w : ℕ),
    PlanarMesh (configurationMap (signedPermIso π s) ω) (R.signedPerm π s) w ↔ PlanarMesh ω R w

variable {π s}

theorem signedPermIso_apply (x : Vertex 2) : signedPermIso π s x = signedPermVertex π s x := rfl

/-- **Anchors of image cubes.** -/
theorem TriadicCube.reachIn_planarAnchor_signedPerm {ω : Configuration 2} (hmesh : MeshInvariant π s)
    {Q : TriadicCube 2} (hQ : Q.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale) :
    ReachIn ω Q.vertices
      ((signedPermVertex π s).symm ((Q.signedPerm π s).planarAnchor
        (configurationMap (signedPermIso π s) ω))) (Q.planarAnchor ω) := by
  set φ := signedPermIso π s
  set A' := (Q.signedPerm π s).planarAnchor (configurationMap φ ω) with hA'
  have hQ' : (Q.signedPerm π s).planarMeshed (configurationMap φ ω) :=
    (TriadicCube.signedPerm_planarMeshed_iff π s hmesh ω Q).2 hQ
  have hs' : 1000 ≤ 3 ^ (Q.signedPerm π s).scale := hs
  obtain ⟨a, b, k, hab, hlong⟩ := Q.exists_long_reachIn hQ hs
  have hS : ∀ v, φ v ∈ (Q.signedPerm π s).vertices ↔ v ∈ Q.vertices :=
    fun v => Q.signedPermVertex_mem_vertices_iff π s v
  have hab' := (reachIn_configurationMap_iff φ ω hS a b).2 hab
  have hpull : ∀ c, ReachIn (configurationMap φ ω) (Q.signedPerm π s).vertices A' (φ c) →
      ReachIn ω Q.vertices ((signedPermVertex π s).symm A') c := by
    intro c hc
    rw [← reachIn_configurationMap_iff φ ω hS]
    have e : φ ((signedPermVertex π s).symm A') = A' := (signedPermVertex π s).apply_symm_apply A'
    rw [e]
    exact hc
  have hanchor := (TriadicCube.planarAnchor_spec hQ hs).2.1 a b k hab hlong
  set k' := π.symm k with hk'
  have hdiff : φ b k' - φ a k' = (s k' : ℤ) * (b k - a k) := by
    change (s k' : ℤ) * b (π k') - (s k' : ℤ) * a (π k') = _
    rw [hk', Equiv.apply_symm_apply]
    ring
  rcases units_int_eq_one_or (s k') with hsk | hsk
  · have hl : φ a k' + ((3 ^ (Q.signedPerm π s).scale / 100 : ℕ) : ℤ) ≤ φ b k' := by
      rw [hsk, one_mul] at hdiff
      change φ a k' + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ φ b k'
      linarith
    have h1 := (TriadicCube.planarAnchor_spec hQ' hs').2.1 (φ a) (φ b) k' hab' hl
    exact (hpull a h1).trans hanchor.symm
  · have hl : φ b k' + ((3 ^ (Q.signedPerm π s).scale / 100 : ℕ) : ℤ) ≤ φ a k' := by
      rw [hsk] at hdiff
      change φ b k' + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ φ a k'
      linarith
    have h1 := (TriadicCube.planarAnchor_spec hQ' hs').2.1 (φ b) (φ a) k' hab'.symm hl
    exact ((hpull b h1).trans hab.symm).trans hanchor.symm

/-- **Resolution of image cubes.** -/
theorem planarResolved_signedPerm_iff (hmesh : MeshInvariant π s) {ω : Configuration 2}
    (hP : PlanarPartitionEvent ω) (V : TriadicCube 2) :
    PlanarResolved (configurationMap (signedPermIso π s) ω) (V.signedPerm π s) ↔
      PlanarResolved ω V := by
  unfold PlanarResolved
  constructor
  · intro h x hx
    have := h (signedPermVertex π s x) ((V.signedPermVertex_mem_vertices_iff π s x).2 hx)
    rwa [planarPartCube_configurationMap π s hmesh hP x] at this
  · intro h z hz
    obtain ⟨x, rfl⟩ := (signedPermVertex π s).surjective z
    rw [planarPartCube_configurationMap π s hmesh hP x]
    exact h x ((V.signedPermVertex_mem_vertices_iff π s x).1 hz)

/-- **Transport of the cluster.** -/
theorem signedPerm_mem_planarCubeCluster_iff (hmesh : MeshInvariant π s) {ω : Configuration 2}
    (hP : PlanarPartitionEvent ω) {V : TriadicCube 2} (hres : PlanarResolved ω V) (x : Vertex 2) :
    signedPermVertex π s x ∈
        planarCubeCluster (configurationMap (signedPermIso π s) ω) (V.signedPerm π s) ↔
      x ∈ planarCubeCluster ω V := by
  set φ := signedPermIso π s
  unfold planarCubeCluster
  simp only [Set.mem_setOf_eq]
  rw [V.signedPermVertex_mem_vertices_iff π s x]
  refine and_congr_right fun hx => ?_
  have hQV := planarPartCube_subset_of_resolved hP hres hx
  rw [planarPartCube_configurationMap π s hmesh hP x]
  have hjoin := (TriadicCube.reachIn_planarAnchor_signedPerm hmesh (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x)).mono hQV
  set A' := ((planarPartCube ω x).signedPerm π s).planarAnchor (configurationMap φ ω)
  have hS : ∀ v, φ v ∈ (V.signedPerm π s).vertices ↔ v ∈ V.vertices :=
    fun v => V.signedPermVertex_mem_vertices_iff π s v
  have key : ReachIn (configurationMap φ ω) (V.signedPerm π s).vertices (signedPermVertex π s x) A' ↔
      ReachIn ω V.vertices x ((signedPermVertex π s).symm A') := by
    rw [← reachIn_configurationMap_iff φ ω hS]
    have e : φ ((signedPermVertex π s).symm A') = A' := (signedPermVertex π s).apply_symm_apply A'
    rw [e]
    rfl
  rw [key]
  exact ⟨fun h => h.trans hjoin, fun h => h.trans hjoin.symm⟩

/-- Interior vertices are carried to interior vertices. -/
theorem TriadicCube.isInterior_signedPerm_iff (V : TriadicCube 2) (x : Vertex 2) :
    (V.signedPerm π s).IsInterior (signedPermVertex π s x) ↔ V.IsInterior x := by
  unfold TriadicCube.IsInterior
  have hd : ∀ y : Vertex 2, (∀ i, |signedPermVertex π s x i - signedPermVertex π s y i| ≤ 1) ↔
      ∀ i, |x i - y i| ≤ 1 := by
    intro y
    have h : ∀ i, |signedPermVertex π s x i - signedPermVertex π s y i| = |x (π i) - y (π i)| := by
      intro i
      rw [signedPermVertex_apply, signedPermVertex_apply, ← mul_sub, abs_mul, abs_units_int,
        one_mul]
    simp only [h]
    exact forall_perm_iff π (fun i => |x i - y i| ≤ 1)
  constructor
  · intro h y hy
    rw [← V.signedPermVertex_mem_vertices_iff π s]
    exact h _ ((hd y).2 hy)
  · intro h y' hy'
    obtain ⟨y, rfl⟩ := (signedPermVertex π s).surjective y'
    rw [V.signedPermVertex_mem_vertices_iff π s]
    exact h y ((hd y).1 hy')

/-- The transported slope keeps the displacement pairing. -/
theorem sum_signedPermSlope_mul_sub (p : Fin 2 → ℝ) (x y : Vertex 2) :
    ∑ i, signedPermSlope π s p i *
        ((signedPermVertex π s y i : ℝ) - signedPermVertex π s x i) =
      ∑ i, p i * ((y i : ℝ) - x i) := by
  have h1 := sum_signedPermSlope_mul π s p y
  have h2 := sum_signedPermSlope_mul π s p x
  have e : ∀ z : Vertex 2, signedPermIso π s z = signedPermVertex π s z := fun _ => rfl
  simp only [e] at h1 h2
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]

/-- **Covariance of `ν` under the symmetry.** -/
theorem planarNu_signedPerm (hmesh : MeshInvariant π s) {ω : Configuration 2}
    (hP : PlanarPartitionEvent ω) {V : TriadicCube 2} (hres : PlanarResolved ω V)
    (p : Fin 2 → ℝ) :
    planarNu (configurationMap (signedPermIso π s) ω) (V.signedPerm π s) (signedPermSlope π s p) =
      planarNu ω V p := by
  have hC := signedPerm_mem_planarCubeCluster_iff hmesh hP hres
  let e : ↥(clusterVertices ω V) ≃
      ↥(clusterVertices (configurationMap (signedPermIso π s) ω) (V.signedPerm π s)) :=
    { toFun := fun x => ⟨signedPermVertex π s x.1,
        mem_clusterVertices.2 ((hC x.1).2 (mem_clusterVertices.1 x.2))⟩
      invFun := fun y => ⟨(signedPermVertex π s).symm y.1,
        mem_clusterVertices.2 ((hC _).1 (by
          rw [Equiv.apply_symm_apply]
          exact mem_clusterVertices.1 y.2))⟩
      left_inv := fun x => Subtype.ext ((signedPermVertex π s).symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext ((signedPermVertex π s).apply_symm_apply y.1) }
  refine planarNu_eq_of_equiv_slope e
    (fun x y => openGraph_adj_configurationMap_iff (signedPermIso π s) ω x.1 y.1) p
    (signedPermSlope π s p) (fun x y => sum_signedPermSlope_mul_sub p x.1 y.1)
    (fun x => V.isInterior_signedPerm_iff x.1) rfl

/-- The centred triadic cube is fixed by the symmetries. -/
theorem TriadicCube.origin_signedPerm (m : ℕ) :
    (⟨m, 0⟩ : TriadicCube 2).signedPerm π s = ⟨m, 0⟩ := by
  apply TriadicCube.ext
  · rfl
  · exact signedPermIso_zero π s

/-- **Invariance of the expectations of `ν(□_m, ·)` on the partition event.** -/
theorem planarNuMean_signedPermSlope (hmesh : MeshInvariant π s) (p : unitInterval) (m : ℕ)
    (ξ : Fin 2 → ℝ) : planarNuMean p m (signedPermSlope π s ξ) = planarNuMean p m ξ := by
  set φ := signedPermIso π s
  set f : Configuration 2 → ENNReal := fun ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (planarNu ω ⟨m, 0⟩ (signedPermSlope π s ξ)) else 0 with hf
  have hcomp : ∀ ω, f (configurationMap φ ω) =
      if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        ENNReal.ofReal (planarNu ω ⟨m, 0⟩ ξ) else 0 := by
    intro ω
    simp only [hf]
    by_cases hP : PlanarPartitionEvent ω
    · have hP' := (planarPartitionEvent_configurationMap_iff π s hmesh ω).2 hP
      have hres := planarResolved_signedPerm_iff hmesh hP ⟨m, 0⟩
      rw [TriadicCube.origin_signedPerm] at hres
      by_cases hr : PlanarResolved ω ⟨m, 0⟩
      · rw [if_pos ⟨hP', hres.2 hr⟩, if_pos ⟨hP, hr⟩]
        have h := planarNu_signedPerm hmesh hP hr ξ
        rw [TriadicCube.origin_signedPerm] at h
        rw [h]
      · rw [if_neg (fun h => hr (hres.1 h.2)), if_neg (fun h => hr h.2)]
    · have hP' : ¬PlanarPartitionEvent (configurationMap φ ω) :=
        fun h => hP ((planarPartitionEvent_configurationMap_iff π s hmesh ω).1 h)
      rw [if_neg (fun h => hP' h.1), if_neg (fun h => hP h.1)]
  have hmp := measurePreserving_configurationMap φ p
  have hint := hmp.lintegral_comp_emb (configurationMap φ).measurableEmbedding f
  unfold planarNuMean
  rw [← hint]
  simp only [hcomp]

/-- **Invariance of the limit of the expectations of `ν(□_m, ·)`.** -/
theorem planarNuLimit_signedPermSlope (hmesh : MeshInvariant π s) (p : unitInterval)
    (ξ : Fin 2 → ℝ) : planarNuLimit p (signedPermSlope π s ξ) = planarNuLimit p ξ := by
  unfold planarNuLimit
  simp only [planarNuMean_signedPermSlope hmesh p]

end Rigidity.Percolation
