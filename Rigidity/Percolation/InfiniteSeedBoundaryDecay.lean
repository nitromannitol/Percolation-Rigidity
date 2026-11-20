import Rigidity.Percolation.CubeBoundaryContactDecay
import Rigidity.Percolation.SlabInfiniteConnectivity

/-!
# Infinite seed clusters and cube boundaries

An infinite open component meeting a finite seed reaches every surrounding
cube boundary. The probability that it reaches fewer than a fixed number of
boundary vertices therefore tends to zero.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped Topology

/-- Some seed vertex belongs to an infinite open component. -/
def seedInfiniteOpenEvent {d : ℕ} (roots : Finset (Vertex d)) : Set (Configuration d) :=
  ⋃ z ∈ roots, infiniteOpenInEvent Set.univ z

/-- An infinite open component meeting the seed reaches the boundary of
every finite region containing the seed. -/
theorem seedReachableContacts_nonempty_of_infinite {d : ℕ} {ω : Configuration d}
    {P : Set (Vertex d)} {roots face : Finset (Vertex d)} (hP : P.Finite)
    (hroots : ∀ z ∈ roots, z ∈ P)
    (hface : ∀ x ∈ P, ∀ y, y ∉ P →
      (nearestNeighborGraph d).Adj x y → x ∈ face)
    (hinf : ω ∈ seedInfiniteOpenEvent roots) :
    (seedReachableContacts P roots face ω).Nonempty := by
  classical
  obtain ⟨z, hz, hinf⟩ := Set.mem_iUnion.mp hinf |>.imp fun _ h => Set.mem_iUnion.mp h
  obtain ⟨w, _, hw, hzw⟩ := (mem_infiniteOpenInEvent_iff Set.univ z ω).mp hinf hP.toFinset
  have hwout : w ∉ P := by simpa only [Set.Finite.mem_toFinset] using hw
  have hdisj : Disjoint P Pᶜ := by
    rw [Set.disjoint_left]
    intro x hx hxnot
    exact hxnot hx
  have hcover : Set.univ ⊆ P ∪ Pᶜ := by simp only [Set.union_compl_self, Set.subset_univ]
  obtain ⟨x, hx, y, hy, hxy, hzx, _⟩ :=
    exists_slab_attachment_of_reachable hdisj hcover (hroots z hz) hwout hzw
  exact ⟨x, (mem_seedReachableContacts P roots face ω x).mpr ⟨hface x hx y hy hxy, z, hz, hzx⟩⟩

/-- If a finite seed meets an infinite open component, the probability of
fewer than `m` reached vertices on a centered cube boundary tends to zero. -/
theorem tendsto_measure_infinite_seed_few_cube_contacts {d : ℕ} (p : unitInterval)
    (hp : (p : ℝ) < 1) (roots : Finset (Vertex d)) (M m : ℕ)
    (hroots : ∀ z ∈ roots, z ∈ centeredBondCube M) :
    Tendsto (fun n => latticeBondLaw d p (seedInfiniteOpenEvent roots ∩ {ω |
      (seedReachableContacts (centeredBondCube (M + n)) roots
        (centeredBondCubeBoundary (M + n)) ω).card < m})) atTop (𝓝 0) := by
  have hlim := tendsto_measure_bounded_centeredCube_contacts p hp roots M m hroots
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  rintro ω ⟨hinf, hcard⟩
  have hroots' : ∀ z ∈ roots, z ∈ centeredBondCube (M + n) := by
    intro z hz
    apply (mem_centeredBondCube _ z).mpr
    intro i
    have h := (mem_centeredBondCube M z).mp (hroots z hz) i
    exact h.trans (by exact_mod_cast Nat.le_add_right M n)
  have hne := seedReachableContacts_nonempty_of_infinite (finite_centeredBondCube _)
    hroots' (fun _ hx _ hy hxy => mem_centeredBondCubeBoundary_of_exit hx hy hxy) hinf
  exact ⟨Finset.card_pos.mpr hne, Nat.le_of_lt hcard⟩

end Rigidity.Percolation
