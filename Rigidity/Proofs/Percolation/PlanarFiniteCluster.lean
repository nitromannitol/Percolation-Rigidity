import Rigidity.Proofs.Section5.ManyPaths
import Rigidity.Proofs.Percolation.PlanarAnnulusTail
import Rigidity.Proofs.S3.ChemicalDistance

/-!
# Planar finite clusters and annulus crossings

A loop in the infinite cluster separates any finite cluster intersecting the inner cube from the
outside of the enclosing cube. Supercritical annulus crossings supply such loops at each scale.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5
open Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- A finite cluster touching the inner cube stays inside a surrounding infinite-cluster loop. -/
theorem finite_component_subset_cube_of_loop {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {R n : ℕ}
    (γ : Fin (n + 1) → uniqueInfiniteComponent h)
    (hγa : ∀ i, (componentGraph _).Adj (γ i) (γ (i + 1)))
    (hγm : ∀ i, (γ i).val ∈ cube (2 * R) \ cube R)
    (hγw : windingNumber (fun i => (γ i).val) ≠ 0)
    {x : Vertex 2} (hx : x ∈ cube R)
    (hf : ((openGraph ω).connectedComponentMk x).supp.Finite) :
    ((openGraph ω).connectedComponentMk x).supp ⊆ cube (2 * R) := by
  intro y hy
  by_contra hyout
  have hxy : (openGraph ω).Reachable x y := by
    apply SimpleGraph.ConnectedComponent.exact
    exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hy).symm
  obtain ⟨W⟩ := hxy
  have hβa : ∀ i, latticeL1Dist (γ i).val (γ (i + 1)).val = 1 :=
    fun i => latticeL1Dist_eq_one_of_adj (hγa i)
  have hβw : windAt (fun i => (γ i).val) 0 ≠ 0 := by
    intro hz
    apply hγw
    rw [windingNumber_eq_windAt, hz, zero_div]
  obtain ⟨i, hi, t, hit⟩ := exists_eq_of_crossing hβa hγm hβw
    (P := W.getVert) (L := W.length)
    (fun i hi => lattice_adj_iff_l1Dist.1 (W.adj_getVert_succ hi).1)
    (by simpa using hx) (by simpa using hyout)
  have hxγ : (openGraph ω).Reachable x (γ t).val := by
    rw [hit]
    exact (W.takeUntil (W.getVert i) (W.getVert_mem_support i)).reachable
  have hinf := (mem_uniqueInfiniteComponent_iff h (γ t).val).1 (γ t).property
  change ((openGraph ω).connectedComponentMk (γ t).val).supp.Infinite at hinf
  have heq := SimpleGraph.ConnectedComponent.sound hxγ
  rw [← heq] at hinf
  exact hinf hf

/-- Uniform annulus crossings confine finite clusters touching the inner cube. -/
theorem finite_component_subset_cube_of_crossings {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {M R : ℕ}
    (hM : ∀ r : ℕ, M ≤ r → AnnulusCrossings ω r) (hR : M + 1 ≤ R)
    {x : Vertex 2} (hx : x ∈ cube R)
    (hf : ((openGraph ω).connectedComponentMk x).supp.Finite) :
    ((openGraph ω).connectedComponentMk x).supp ⊆ cube (2 * R) := by
  obtain ⟨n, γ, hγa, hγm, hγw⟩ := loop_at_scale_of_crossings ω h M hM R hR
  exact finite_component_subset_cube_of_loop h γ hγa hγm hγw hx hf

end Rigidity.Percolation
