import Rigidity.Proofs.Section5.PlanarPotentialLogBound
import Rigidity.Proofs.Section5.ComponentFiniteFlow

/-!
# Green columns from sublinear potential bounds

A bound `o(|x|)` on the truncated potential kernels, uniform in the truncation time, gives a
planar Green column. Finite unit flows from the pole whose energies grow sublinearly supply such
a bound.
-/

open Filter Topology LatticeProb.Percolation LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

open Rigidity.Section5

/-- Truncated potentials bounded by `ε |x|` far from the origin, uniformly in the truncation time
and for every `ε > 0`, give a planar Green column. -/
theorem exists_greenColumn_of_truncatedPotential_sublinear {ω : Configuration 2}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n (x : C), R ≤ eucl x.val →
      |truncatedComponentPotential C n y x| ≤ ε * eucl x.val) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  choose B hB using exists_bound_truncatedComponentPotential C hC y
  let S : Set (C → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-B x) (B x))
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, truncatedComponentPotential C n y ∈ S := by
    intro n x _
    exact abs_le.mp (hB x n)
  obtain ⟨v, _, φ, hφ, hv⟩ := hS.tendsto_subseq hmem
  have hφ' : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hv' : ∀ x, Tendsto (fun n => truncatedComponentPotential C (φ n) y x)
      atTop (nhds (v x)) := fun x => (tendsto_pi_nhds.mp hv) x
  have hΔ : ∀ x, componentLaplacian C v x = if x = y then 1 else 0 := by
    apply componentLaplacian_eq_of_tendsto C
      (fun n => truncatedComponentPotential C (φ n) y) v (fun x => if x = y then 1 else 0) hv'
    intro x
    have h := (tendsto_const_nhds (x := (if x = y then (1 : ℝ) else 0))).sub
      (((tendsto_componentHeat_zero C hC x y).comp hφ').const_mul
        (((componentGraph C).degree x : ℝ) / (componentGraph C).degree y))
    simp_rw [componentLaplacian_truncatedPotential C hC]
    simpa only [Function.comp_apply, mul_zero, sub_zero] using h
  have hsub : IsSublinearOn C v := by
    intro ε hε
    obtain ⟨R, hR⟩ := hbound ε hε
    exact ⟨R, fun x hx => le_of_tendsto ((hv' x).abs)
      (Filter.Eventually.of_forall fun n => hR (φ n) x hx)⟩
  exact ⟨fun x => v y - v x, isGreenColumn_of_potentialKernel C y v hΔ hsub⟩

/-- Finite unit flows from the pole, inside the component, whose energies are at most `ε |x|`
far from the origin for every `ε > 0`, give a planar Green column. -/
theorem exists_greenColumn_of_sublinear_finite_flows {ω : Configuration 2}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C)
    (hflow : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val →
      ∃ V : Finset (Vertex 2), (∀ z ∈ V, z ∈ C.supp) ∧
        ∃ (hy : y.val ∈ V) (hx : x.val ∈ V) (θ : V → V → ℝ),
        IsFlow ((openGraph ω).induce (V : Set (Vertex 2))) θ ∧
        (∀ z : V, divergence ((openGraph ω).induce (V : Set (Vertex 2))) θ z =
          (if z = ⟨y.val, hy⟩ then 1 else 0) - (if z = ⟨x.val, hx⟩ then 1 else 0)) ∧
        flowEnergyOn ((openGraph ω).induce (V : Set (Vertex 2)))
          (unitCond ((openGraph ω).induce (V : Set (Vertex 2)))) Finset.univ θ ≤
            2 * (ε * eucl x.val)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  apply exists_greenColumn_of_truncatedPotential_sublinear C hC y
  intro ε hε
  obtain ⟨R, hR⟩ := hflow ε hε
  refine ⟨R, fun n x hx => ?_⟩
  obtain ⟨V, hV, hy, hxV, θ, hθ, hdiv, henergy⟩ := hR x hx
  rw [abs_of_nonneg (truncatedComponentPotential_nonneg C n y x)]
  exact truncatedComponentPotential_le_lattice_flow_energy C hC y x V hV hy hxV θ _ hθ hdiv
    henergy n

end Rigidity.Proofs.Section5
