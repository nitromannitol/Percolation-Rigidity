import Rigidity.Proofs.Section5.ManyPaths
import Rigidity.Proofs.Percolation.PlanarAnnulusTail
import Rigidity.Proofs.Percolation.SupercriticalUniqueness
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

/-- Crossings confine a finite component to at most the volume of the enclosing square. -/
theorem finite_component_card_le_of_crossings {ω : Configuration 2}
    (h : HasUniqueInfiniteOpenComponent ω) {M R : ℕ}
    (hM : ∀ r : ℕ, M ≤ r → AnnulusCrossings ω r) (hR : M + 1 ≤ R)
    {x : Vertex 2} (hx : x ∈ cube R)
    (hf : ((openGraph ω).connectedComponentMk x).supp.Finite) :
    ((openGraph ω).connectedComponentMk x).supp.ncard ≤ (4 * R + 1) ^ 2 := by
  have heq : cube (2 * R) = Rigidity.External.cubeAt (0 : Vertex 2) (2 * R) := by
    ext v
    simp [cube, Rigidity.External.cubeAt]
  have hsub := finite_component_subset_cube_of_crossings h hM hR hx hf
  rw [heq] at hsub
  have hcard := Set.ncard_le_ncard hsub (Rigidity.Proofs.S3.finite_cubeAt 0 (2 * R))
  have hset : Rigidity.External.cubeAt (0 : Vertex 2) (2 * R) =
      ↑(Rigidity.Proofs.S3.cubeFinset (0 : Vertex 2) (2 * R)) := by
    ext v
    exact Rigidity.Proofs.S3.mem_cubeFinset.symm
  rw [hset, Set.ncard_coe_finset, Rigidity.Proofs.S3.card_cubeFinset] at hcard
  convert hcard using 1; ring

/-- The origin's finite cluster exceeds the enclosing square only if a crossing fails. -/
theorem finite_cluster_exceeds_square_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ R : ℕ, 1 ≤ R →
      latticeBondLaw 2 p {ω |
        ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
        (4 * R + 1) ^ 2 < ((openGraph ω).connectedComponentMk 0).supp.ncard} ≤
      ENNReal.ofReal (C * Real.exp (-(c * (R - 1 : ℕ)))) := by
  obtain ⟨C, c, hC, hc, hcross⟩ := annulusCrossings_tail p hp
  refine ⟨C, c, hC, hc, fun R hR => ?_⟩
  have hU : ∀ᵐ ω ∂latticeBondLaw 2 p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).2
      (uniqueInfiniteComponentEvent_eq_one_of_criticalProbability_lt 2 p hp)
  have hsub : ∀ᵐ ω ∂latticeBondLaw 2 p,
      ω ∈ {ω | ((openGraph ω).connectedComponentMk 0).supp.Finite ∧
        (4 * R + 1) ^ 2 < ((openGraph ω).connectedComponentMk 0).supp.ncard} →
      ω ∈ {ω | ∃ n : ℕ, R - 1 ≤ n ∧ ¬ AnnulusCrossings ω n} := by
    filter_upwards [hU] with ω hω ⟨hfin, hsize⟩
    by_contra hbad
    have hM : ∀ n : ℕ, R - 1 ≤ n → AnnulusCrossings ω n := by
      intro n hn
      by_contra hn'
      exact hbad ⟨n, hn, hn'⟩
    have hle := finite_component_card_le_of_crossings hω (M := R - 1) (R := R) hM (by omega)
      (x := 0) (by simp [cube]) hfin
    omega
  exact (measure_mono_ae hsub).trans (hcross (R - 1))

end Rigidity.Percolation
