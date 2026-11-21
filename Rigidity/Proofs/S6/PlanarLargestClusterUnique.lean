import Rigidity.Proofs.S6.PlanarLargestCluster
import Rigidity.Proofs.Section5.PlanarBoxRadius

/-!
# Eventual uniqueness of the largest planar box cluster

Every largest cluster of a sufficiently large box contains any fixed vertex of the infinite
cluster, so two such largest clusters coincide.
-/

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Section6

namespace Rigidity.Proofs.S6

/-- Two box clusters with a common vertex coincide. -/
theorem largestBoxCluster_eq_of_mem {d : ℕ} {ω : Configuration d} {n : ℕ}
    {V W : Finset (Vertex d)} (hV : IsLargestBoxCluster ω n V)
    (hW : IsLargestBoxCluster ω n W) {z : Vertex d} (hzV : z ∈ V) (hzW : z ∈ W) :
    V = W := by
  obtain ⟨⟨a, ha, hVa⟩, _⟩ := hV
  obtain ⟨⟨b, hb, hWb⟩, _⟩ := hW
  have haz : (boxOpenGraph ω n).Reachable a z := by
    have : z ∈ (V : Set (Vertex d)) := hzV
    rw [hVa] at this
    exact this
  have hbz : (boxOpenGraph ω n).Reachable b z := by
    have : z ∈ (W : Set (Vertex d)) := hzW
    rw [hWb] at this
    exact this
  apply Finset.coe_injective
  rw [hVa, hWb]
  ext x
  change (boxOpenGraph ω n).Reachable a x ↔ (boxOpenGraph ω n).Reachable b x
  exact ⟨fun h => (hbz.trans haz.symm).trans h,
    fun h => (haz.trans hbz.symm).trans h⟩

/-- Almost surely the largest planar box cluster is unique for every sufficiently large box. -/
theorem ae_eventually_planar_largestBoxCluster_unique (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ᶠ n : ℕ in atTop,
      ∀ V W : Finset (Vertex 2), IsLargestBoxCluster ω n V →
        IsLargestBoxCluster ω n W → V = W := by
  filter_upwards [planar_largestBox_absorbs_infiniteCluster p hpc hp1,
    ae_planar_infiniteCluster_mem_largestBox p hpc hp1] with ω hcomponent hinner
  obtain ⟨h, _⟩ := hcomponent
  obtain ⟨z, hz⟩ := (uniqueInfiniteComponent_infinite h).nonempty
  obtain ⟨B, hB, hchoose⟩ := Rigidity.Proofs.Section5.exists_box_radius z 0
  obtain ⟨n₀, _, _, hz₀, _, _⟩ := hchoose z
  filter_upwards [hinner, eventually_ge_atTop n₀] with n hn hn₀
  have hzinner : ∀ i, 2 * |z i| ≤ (n : ℤ) := by
    intro i
    have hcast : (n₀ : ℤ) ≤ n := by exact_mod_cast hn₀
    exact (hz₀ i).trans hcast
  have hzinf : ω ∈ infiniteComponentEvent z := (mem_uniqueInfiniteComponent_iff h z).mp hz
  intro V W hV hW
  exact largestBoxCluster_eq_of_mem hV hW (hn V hV z hzinner hzinf)
    (hn W hW z hzinner hzinf)

end Rigidity.Proofs.S6
