import Rigidity.Proofs.Percolation.PlanarTranslation
import Rigidity.Proofs.Percolation.PlanarCubeEnergy

/-!
# Transport of the cluster of a resolved planar cube

The quantity `ν(U, p)` depends only on the vertices of the cluster `C_*(U)`, on the open edges
between them, on the displacements along these edges and on which vertices are interior to `U`: a
bijection of clusters respecting these data carries the harmonic functions of one cluster to those
of the other and preserves the Dirichlet form and the flux pairing.

For a translation by `c`, where the side of `U` divides `c`, the cluster of the translated
configuration in the translated cube is the translated cluster as soon as the partition cubes of the
vertices of `U` move with the translation: any two anchors of a meshed cube are joined inside it,
since each of them is joined to every long open path of the cube. Hence `ν` is translation
covariant on resolved cubes, which is the deterministic part of the stationarity of
Armstrong and Dario, (4.21).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

section Relabel

variable {U U' : TriadicCube 2} (e : ↥(clusterVertices ω U) ≃ ↥(clusterVertices ω' U'))

theorem clusterForm_comp_symm
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (u v : ClusterFun ω U) :
    clusterForm ω' U' (u ∘ e.symm) (v ∘ e.symm) = clusterForm ω U u v := by
  rw [clusterForm_apply, clusterForm_apply]
  congr 1
  refine (Fintype.sum_equiv e.symm _ _ fun x => ?_)
  refine (Fintype.sum_equiv e.symm _ _ fun y => ?_)
  have h := hadj (e.symm x) (e.symm y)
  simp only [Equiv.apply_symm_apply] at h
  simp only [clusterFormTerm, Function.comp_apply, h]

theorem fluxPairing_comp_symm
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hdisp : ∀ x y i, ((e y).1 i : ℝ) - (e x).1 i = (y.1 i : ℝ) - x.1 i)
    (p : Fin 2 → ℝ) (u : ClusterFun ω U) :
    fluxPairing ω' U' p (u ∘ e.symm) = fluxPairing ω U p u := by
  rw [fluxPairing_apply, fluxPairing_apply]
  congr 1
  refine (Fintype.sum_equiv e.symm _ _ fun x => ?_)
  refine (Fintype.sum_equiv e.symm _ _ fun y => ?_)
  have h := hadj (e.symm x) (e.symm y)
  have hd := hdisp (e.symm x) (e.symm y)
  simp only [Equiv.apply_symm_apply] at h hd
  simp only [Function.comp_apply, h, hd]

theorem clusterLaplacianAt_comp_symm
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (x : ↥(clusterVertices ω U)) (u : ClusterFun ω U) :
    clusterLaplacianAt ω' U' (e x) (u ∘ e.symm) = clusterLaplacianAt ω U x u := by
  rw [clusterLaplacianAt_apply, clusterLaplacianAt_apply]
  refine (Fintype.sum_equiv e.symm _ _ fun y => ?_)
  have h := hadj x (e.symm y)
  simp only [Equiv.apply_symm_apply] at h
  simp only [Function.comp_apply, h, Equiv.symm_apply_apply]

theorem comp_symm_mem_clusterHarmonic_iff
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsInterior (e x).1 ↔ U.IsInterior x.1) (u : ClusterFun ω U) :
    u ∘ e.symm ∈ clusterHarmonic ω' U' ↔ u ∈ clusterHarmonic ω U := by
  rw [mem_clusterHarmonic, mem_clusterHarmonic]
  constructor
  · intro h x hx
    rw [← clusterLaplacianAt_comp_symm e hadj]
    exact h (e x) ((hint x).2 hx)
  · intro h x' hx'
    have hx := (hint (e.symm x')).1 (by simpa only [Equiv.apply_symm_apply] using hx')
    have := clusterLaplacianAt_comp_symm e hadj (e.symm x') u
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact h _ hx

/-- **Relabelling invariance of `ν`.** A bijection of clusters which respects open edges, their
displacements and interior vertices preserves `ν`. -/
theorem planarNu_eq_of_equiv
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hdisp : ∀ x y i, ((e y).1 i : ℝ) - (e x).1 i = (y.1 i : ℝ) - x.1 i)
    (hint : ∀ x, U'.IsInterior (e x).1 ↔ U.IsInterior x.1) (hvol : U'.volume = U.volume)
    (p : Fin 2 → ℝ) : planarNu ω' U' p = planarNu ω U p := by
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
  change (fluxPairing ω' U' p (w.1 ∘ e.symm) -
      clusterForm ω' U' (w.1 ∘ e.symm) (w.1 ∘ e.symm) / 2) / U'.volume = _
  rw [fluxPairing_comp_symm e hadj hdisp, clusterForm_comp_symm e hadj, hvol]

end Relabel

/-- `ν` depends only on the cluster and on the open edges between its vertices. -/
theorem planarNu_eq_of_cluster_eq {U : TriadicCube 2}
    (hC : ∀ x, x ∈ clusterVertices ω' U ↔ x ∈ clusterVertices ω U)
    (hadj : ∀ x ∈ clusterVertices ω U, ∀ y ∈ clusterVertices ω U,
      ((openGraph ω').Adj x y ↔ (openGraph ω).Adj x y)) (p : Fin 2 → ℝ) :
    planarNu ω' U p = planarNu ω U p :=
  planarNu_eq_of_equiv (Equiv.subtypeEquivRight fun x => (hC x).symm)
    (fun x y => by
      simp only [Equiv.subtypeEquivRight_apply_coe]
      exact hadj x.1 x.2 y.1 y.2)
    (fun x y i => by simp only [Equiv.subtypeEquivRight_apply_coe])
    (fun x => by simp only [Equiv.subtypeEquivRight_apply_coe]) rfl p

/-- A meshed cube carries an open path inside it whose endpoints differ by at least a hundredth of
its side in some coordinate. -/
theorem TriadicCube.exists_long_reachIn {Q : TriadicCube 2} (hQ : Q.planarMeshed ω)
    (hs : 1000 ≤ 3 ^ Q.scale) :
    ∃ a b : Vertex 2, ∃ k : Fin 2, ReachIn ω Q.vertices a b ∧
      a k + ((3 ^ Q.scale / 100 : ℕ) : ℤ) ≤ b k := by
  have hm := hQ _ Q.toIntegerCube_mem_planarSquares
  have hsize : Q.toIntegerCube.size = 3 ^ Q.scale := rfl
  obtain ⟨a, b, hab, ha, hb⟩ := hm.1 (Q.toIntegerCube.corner 1) le_rfl (by
    rw [hsize]; omega)
  refine ⟨a, b, 0, hab.mono ((IntegerCube.hStrip_subset le_rfl (by
    rw [hsize]; omega)).trans Q.coe_toIntegerCube_vertices.le), ?_⟩
  rw [ha, hb, hsize]
  omega

/-- The anchor of the translated cube in the translated configuration, moved back, is joined to
the anchor of the cube inside the cube. -/
theorem TriadicCube.reachIn_planarAnchor_shift {Q : TriadicCube 2} {c : Vertex 2}
    (hQ : Q.planarMeshed ω) (hs : 1000 ≤ 3 ^ Q.scale) (hc : ∀ i, Q.side ∣ c i) :
    ReachIn ω Q.vertices ((Q.shift c).planarAnchor (configurationTranslation c ω) - c)
      (Q.planarAnchor ω) := by
  have hQ' : (Q.shift c).planarMeshed (configurationTranslation c ω) :=
    (shift_planarMeshed_translation_iff hc ω).2 hQ
  obtain ⟨a, b, k, hab, hlong⟩ := Q.exists_long_reachIn hQ hs
  have hS := add_mem_shift_iff hc
  have hab' := (reachIn_translation_iff c ω hS a b).2 hab
  have h1 := (planarAnchor_spec hQ' hs).2.1 (a + c) (b + c) k hab' (by
    simp only [Pi.add_apply, scale_shift]
    omega)
  have h1' : ReachIn ω Q.vertices
      ((Q.shift c).planarAnchor (configurationTranslation c ω) - c) a := by
    rw [← reachIn_translation_iff c ω hS, sub_add_cancel]
    exact h1
  exact h1'.trans ((planarAnchor_spec hQ hs).2.1 a b k hab hlong).symm

/-- Interior vertices move with translations. -/
theorem TriadicCube.isInterior_shift_iff {U : TriadicCube 2} {c : Vertex 2}
    (hc : ∀ i, U.side ∣ c i) (x : Vertex 2) :
    (U.shift c).IsInterior (x + c) ↔ U.IsInterior x := by
  unfold IsInterior
  constructor
  · intro h y hy
    rw [← add_mem_shift_iff hc]
    exact h (y + c) fun i => by simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using hy i
  · intro h y hy
    rw [mem_shift_iff hc]
    exact h (y - c) fun i => by
      have := hy i
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      rwa [show x i - (y i - c i) = x i + c i - y i by ring]

section Translation

variable {V : TriadicCube 2} {c : Vertex 2}

/-- Resolution moves with the partition. -/
theorem planarResolved_shift_iff (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      planarPartCube (configurationTranslation c ω) (x + c) = (planarPartCube ω x).shift c) :
    PlanarResolved (configurationTranslation c ω) (V.shift c) ↔ PlanarResolved ω V := by
  unfold PlanarResolved
  constructor
  · intro h x hx
    have := h (x + c) ((TriadicCube.add_mem_shift_iff hc x).2 hx)
    rwa [hpart x hx] at this
  · intro h z hz
    have hz' := (TriadicCube.mem_shift_iff hc z).1 hz
    have := hpart (z - c) hz'
    rw [sub_add_cancel] at this
    rw [this, TriadicCube.scale_shift, TriadicCube.scale_shift]
    exact h _ hz'

/-- **Transport of the cluster.** If the partition cubes of the vertices of a resolved cube move
with a translation, so does its cluster. -/
theorem add_mem_planarCubeCluster_shift_iff (hP : PlanarPartitionEvent ω)
    (hres : PlanarResolved ω V) (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      planarPartCube (configurationTranslation c ω) (x + c) = (planarPartCube ω x).shift c)
    (x : Vertex 2) :
    x + c ∈ planarCubeCluster (configurationTranslation c ω) (V.shift c) ↔
      x ∈ planarCubeCluster ω V := by
  unfold planarCubeCluster
  simp only [Set.mem_setOf_eq]
  rw [TriadicCube.add_mem_shift_iff hc]
  refine and_congr_right fun hx => ?_
  have hQV := planarPartCube_subset_of_resolved hP hres hx
  have hQc : ∀ i, (planarPartCube ω x).side ∣ c i := fun i =>
    (pow_dvd_pow 3 (hres x hx)).trans (hc i)
  rw [hpart x hx]
  have hjoin := (TriadicCube.reachIn_planarAnchor_shift (planarPartCube_meshed hP x).1
    (planarPartCube_large hP x) hQc).mono hQV
  have key : ReachIn (configurationTranslation c ω) (V.shift c).vertices (x + c)
      (((planarPartCube ω x).shift c).planarAnchor (configurationTranslation c ω)) ↔
      ReachIn ω V.vertices x
        (((planarPartCube ω x).shift c).planarAnchor (configurationTranslation c ω) - c) := by
    rw [← reachIn_translation_iff c ω (TriadicCube.add_mem_shift_iff hc), sub_add_cancel]
  rw [key]
  exact ⟨fun h => h.trans hjoin, fun h => h.trans hjoin.symm⟩

/-- **Translation covariance of `ν`.** -/
theorem planarNu_shift_translation (hP : PlanarPartitionEvent ω) (hres : PlanarResolved ω V)
    (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      planarPartCube (configurationTranslation c ω) (x + c) = (planarPartCube ω x).shift c)
    (p : Fin 2 → ℝ) :
    planarNu (configurationTranslation c ω) (V.shift c) p = planarNu ω V p := by
  have hC := add_mem_planarCubeCluster_shift_iff hP hres hc hpart
  let e : ↥(clusterVertices ω V) ≃ ↥(clusterVertices (configurationTranslation c ω) (V.shift c)) :=
    { toFun := fun x => ⟨x.1 + c, mem_clusterVertices.2 ((hC x.1).2 (mem_clusterVertices.1 x.2))⟩
      invFun := fun y => ⟨y.1 - c, mem_clusterVertices.2 ((hC (y.1 - c)).1 (by
        rw [sub_add_cancel]
        exact mem_clusterVertices.1 y.2))⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel_right x.1 c)
      right_inv := fun y => Subtype.ext (sub_add_cancel y.1 c) }
  refine planarNu_eq_of_equiv e (fun x y => openGraph_adj_translation_iff c ω x.1 y.1)
    (fun x y i => ?_) (fun x => TriadicCube.isInterior_shift_iff hc x.1) rfl p
  change (((y.1 + c) i : ℤ) : ℝ) - (((x.1 + c) i : ℤ) : ℝ) = _
  simp only [Pi.add_apply, Int.cast_add]
  ring

end Translation

end Rigidity.Percolation
