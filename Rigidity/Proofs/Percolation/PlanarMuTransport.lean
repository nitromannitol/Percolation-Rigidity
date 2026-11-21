import Rigidity.Proofs.Percolation.PlanarAnchorTranslation
import Rigidity.Proofs.Percolation.PlanarClusterTransport

/-!
# Transport of `μ` in the plane

The quantity `μ(U, q)` depends only on the cluster `C_*(U)`, on the open edges between its
vertices, on which vertices are interior to `U` and on the coarse pairing: a bijection of clusters
respecting the first three data and carrying the coarse pairing to the coarse pairing preserves
`μ`. For a translation by `c`, where the side of `U` divides `c`, the coarse anchors of the
vertices of a resolved cube move with the translation as soon as the partition cubes do, since
anchors move with translations. Hence `μ` is translation covariant on resolved cubes, which is the
deterministic part of the stationarity of Armstrong and Dario, (4.40), for `μ`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω ω' : Configuration 2}

/-- **Relabelling invariance of `μ`.** A bijection of clusters which respects open edges and
interior vertices and carries the coarse pairing to the coarse pairing preserves `μ`. -/
theorem planarMu_eq_of_equiv {U U' : TriadicCube 2}
    (e : ↥(clusterVertices ω U) ≃ ↥(clusterVertices ω' U'))
    (hadj : ∀ x y, (openGraph ω').Adj (e x).1 (e y).1 ↔ (openGraph ω).Adj x.1 y.1)
    (hint : ∀ x, U'.IsInterior (e x).1 ↔ U.IsInterior x.1) (hvol : U'.volume = U.volume)
    (q : Fin 2 → ℝ)
    (hcoarse : ∀ u : ClusterFun ω U,
      coarsePairing ω' U' q (u ∘ e.symm) = coarsePairing ω U q u) :
    planarMu ω' U' q = planarMu ω U q := by
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
  unfold planarMu
  symm
  refine Equiv.iInf_congr E fun w => ?_
  change (clusterForm ω' U' (w.1 ∘ e.symm) (w.1 ∘ e.symm) / 2 -
      coarsePairing ω' U' q (w.1 ∘ e.symm)) / U'.volume = _
  rw [clusterForm_comp_symm e hadj, hcoarse, hvol]

/-- Sums over the vertices of a shifted cube. -/
theorem TriadicCube.sum_toIntegerCube_vertices_shift {M : Type*} [AddCommMonoid M]
    {V : TriadicCube 2} {c : Vertex 2} (hc : ∀ i, V.side ∣ c i) (f : Vertex 2 → M) :
    ∑ x ∈ (V.shift c).toIntegerCube.vertices, f x =
      ∑ x ∈ V.toIntegerCube.vertices, f (x + c) := by
  refine Finset.sum_nbij' (· - c) (· + c) (fun a ha => ?_) (fun a ha => ?_)
    (fun a _ => sub_add_cancel a c) (fun a _ => add_sub_cancel_right a c)
    (fun a _ => by rw [sub_add_cancel])
  · rw [TriadicCube.mem_toIntegerCube_vertices] at ha ⊢
    exact (TriadicCube.mem_shift_iff hc a).1 ha
  · rw [TriadicCube.mem_toIntegerCube_vertices] at ha ⊢
    exact (TriadicCube.add_mem_shift_iff hc a).2 ha

section Translation

variable {V : TriadicCube 2} {c : Vertex 2}

/-- Coarse anchors move with the partition. -/
theorem planarCoarseAnchor_translation (hres : PlanarResolved ω V) (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      planarPartCube (configurationTranslation c ω) (x + c) = (planarPartCube ω x).shift c)
    {x : Vertex 2} (hx : x ∈ V.vertices) :
    planarCoarseAnchor (configurationTranslation c ω) (x + c) = planarCoarseAnchor ω x + c := by
  unfold planarCoarseAnchor
  rw [hpart x hx]
  exact TriadicCube.planarAnchor_shift (fun i => (pow_dvd_pow 3 (hres x hx)).trans (hc i)) ω

/-- **Translation covariance of `μ`.** -/
theorem planarMu_shift_translation (hP : PlanarPartitionEvent ω) (hres : PlanarResolved ω V)
    (hc : ∀ i, V.side ∣ c i)
    (hpart : ∀ x ∈ V.vertices,
      planarPartCube (configurationTranslation c ω) (x + c) = (planarPartCube ω x).shift c)
    (q : Fin 2 → ℝ) :
    planarMu (configurationTranslation c ω) (V.shift c) q = planarMu ω V q := by
  have hC := add_mem_planarCubeCluster_shift_iff hP hres hc hpart
  let e : ↥(clusterVertices ω V) ≃ ↥(clusterVertices (configurationTranslation c ω) (V.shift c)) :=
    { toFun := fun x => ⟨x.1 + c, mem_clusterVertices.2 ((hC x.1).2 (mem_clusterVertices.1 x.2))⟩
      invFun := fun y => ⟨y.1 - c, mem_clusterVertices.2 ((hC (y.1 - c)).1 (by
        rw [sub_add_cancel]
        exact mem_clusterVertices.1 y.2))⟩
      left_inv := fun x => Subtype.ext (add_sub_cancel_right x.1 c)
      right_inv := fun y => Subtype.ext (sub_add_cancel y.1 c) }
  have hext : ∀ (u : ClusterFun ω V) (y : Vertex 2),
      clusterExtend (configurationTranslation c ω) (V.shift c) (u ∘ e.symm) (y + c) =
        clusterExtend ω V u y := by
    intro u y
    by_cases hy : y ∈ clusterVertices ω V
    · have hy' : y + c ∈ clusterVertices (configurationTranslation c ω) (V.shift c) :=
        mem_clusterVertices.2 ((hC y).2 (mem_clusterVertices.1 hy))
      rw [clusterExtend_apply_of_mem _ hy', clusterExtend_apply_of_mem _ hy]
      change u (e.symm ⟨y + c, hy'⟩) = u ⟨y, hy⟩
      congr 1
      exact Subtype.ext (add_sub_cancel_right y c)
    · have hy' : y + c ∉ clusterVertices (configurationTranslation c ω) (V.shift c) :=
        fun h => hy (mem_clusterVertices.2 ((hC y).1 (mem_clusterVertices.1 h)))
      change (if h : y + c ∈ clusterVertices (configurationTranslation c ω) (V.shift c) then
          (u ∘ e.symm) ⟨y + c, h⟩ else 0) = if h : y ∈ clusterVertices ω V then u ⟨y, h⟩ else 0
      rw [dif_neg hy', dif_neg hy]
  refine planarMu_eq_of_equiv e (fun x y => openGraph_adj_translation_iff c ω x.1 y.1)
    (fun x => TriadicCube.isInterior_shift_iff hc x.1) rfl q fun u => ?_
  rw [coarsePairing_apply, coarsePairing_apply, TriadicCube.sum_toIntegerCube_vertices_shift hc]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_
  have hxV : x ∈ V.vertices := (V.mem_toIntegerCube_vertices x).1 hx
  have hswap : x + c + unitVertex i = x + unitVertex i + c := by abel
  have hmem : x + c + unitVertex i ∈ (V.shift c).toIntegerCube.vertices ↔
      x + unitVertex i ∈ V.toIntegerCube.vertices := by
    rw [TriadicCube.mem_toIntegerCube_vertices, TriadicCube.mem_toIntegerCube_vertices, hswap]
    exact TriadicCube.add_mem_shift_iff hc _
  by_cases hi : x + unitVertex i ∈ V.toIntegerCube.vertices
  · rw [if_pos (hmem.2 hi), if_pos hi, hswap,
      planarCoarseAnchor_translation hres hc hpart ((V.mem_toIntegerCube_vertices _).1 hi),
      planarCoarseAnchor_translation hres hc hpart hxV, hext, hext]
  · rw [if_neg fun h => hi (hmem.1 h), if_neg hi]

end Translation

end Rigidity.Percolation
