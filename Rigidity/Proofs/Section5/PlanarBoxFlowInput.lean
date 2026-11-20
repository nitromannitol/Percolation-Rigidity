import Rigidity.Proofs.Section5.PlanarBoxFlowGreen
import Rigidity.Proofs.Section5.PlanarGreenUniqueness
import Rigidity.Proofs.S6.PlanarLargestCluster

/-!
# Planar Green existence from box-cluster flows

The almost-sure box-cluster comparison turns logarithmic finite-box flow bounds into
existence of planar Green columns.
-/

open MeasureTheory Filter LatticeProb.Percolation LatticeProb.Network Rigidity.Section6
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- Almost-sure logarithmic flow bounds on largest planar box clusters give Green columns. -/
theorem greenColumnExistsTwo_of_largestBox_flows
    (hflow : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop,
        ∀ V : Finset (Vertex 2), IsLargestBoxCluster ω n V →
          ∀ a b : V, ∃ θ : V → V → ℝ,
            IsFlow ((openGraph ω).induce (V : Set (Vertex 2))) θ ∧
            (∀ z : V, divergence ((openGraph ω).induce (V : Set (Vertex 2))) θ z =
              (if z = a then 1 else 0) - (if z = b then 1 else 0)) ∧
            flowEnergyOn ((openGraph ω).induce (V : Set (Vertex 2)))
              (unitCond ((openGraph ω).induce (V : Set (Vertex 2)))) Finset.univ θ ≤
                2 * (A * Real.log n)) :
    Rigidity.External.SupercriticalBondGreenColumnExistsTwo := by
  intro p hp hp1 y
  filter_upwards [hflow p hp hp1, Rigidity.Proofs.S6.planar_largestBox_absorbs_infiniteCluster
    p hp hp1] with ω hflows hboxes h hy
  obtain ⟨A, hA, hflows⟩ := hflows
  obtain ⟨h', hboxes⟩ := hboxes
  have hh : h = h' := Subsingleton.elim _ _
  subst h'
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hflows
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hboxes
  apply exists_greenColumn_of_box_flows (uniqueInfiniteComponent h)
    (uniqueInfiniteComponent_infinite h) ⟨y, hy⟩ A hA (max N₁ N₂)
  intro n hn hn1
  obtain ⟨V, hV, hsubset, hinner⟩ := hN₂ n ((le_max_right _ _).trans hn)
  refine ⟨V, hsubset, ?_, hN₁ n ((le_max_left _ _).trans hn) V hV⟩
  intro z hz
  exact hinner z.val hz z.property

end Rigidity.Proofs.Section5
