/- Adapted from Lattice-Probability revision c21955f, module Summary.
   Based on Leonardo Bonanno, https://github.com/leobon12/lean-formalizations, and
   R. Kirov, https://github.com/rkirov/jordan_pick, revision b3c9b7cf (Apache-2.0). -/
import Rigidity.Proofs.Topology.PlanarJordan.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Planar Jordan curve theorem: Summary

The topology follows H. Maehara, *The Jordan curve theorem via the Brouwer fixed point
theorem*, Amer. Math. Monthly 91 (1984), 641–643.
-/

namespace MatedCRTHarmonic.Planar.Jordan

open Metric Set Function Bornology

/-- **Jordan curve theorem (full form).** The complement of a Jordan curve `J = range r` in
`ℝ²` is the disjoint union of the bounded component of `x₁` and the unbounded component of
`x₀`, and both components have frontier `J`. -/
theorem jordan_curve_components (r : sphere (0 : Plane) 1 → Plane)
    (hcont : Continuous r) (hinj : Injective r) :
    ∃ x₁ ∈ (range r)ᶜ, ∃ x₀ ∈ (range r)ᶜ,
      IsBounded (connectedComponentIn (range r)ᶜ x₁) ∧
      ¬ IsBounded (connectedComponentIn (range r)ᶜ x₀) ∧
      Disjoint (connectedComponentIn (range r)ᶜ x₁) (connectedComponentIn (range r)ᶜ x₀) ∧
      (range r)ᶜ = connectedComponentIn (range r)ᶜ x₁ ∪ connectedComponentIn (range r)ᶜ x₀ ∧
      frontier (connectedComponentIn (range r)ᶜ x₁) = range r ∧
      frontier (connectedComponentIn (range r)ᶜ x₀) = range r := by
  have hbr : BrouwerFPT := Brouwer.brouwerFPT
  obtain ⟨x₀, hx₀S, hx₀u⟩ := exists_unbounded_component r hcont
  obtain ⟨x₁, hx₁S, hx₁b⟩ := step_A_exists_bounded hbr hcont hinj
  have hne : connectedComponentIn (range r)ᶜ x₁ ≠ connectedComponentIn (range r)ᶜ x₀ :=
    fun h => hx₀u (h ▸ hx₁b)
  refine ⟨x₁, hx₁S, x₀, hx₀S, hx₁b, hx₀u, ?_, ?_,
    component_boundary_eq hbr hcont hinj hx₁S ⟨x₀, hx₀S, hne.symm⟩,
    component_boundary_eq hbr hcont hinj hx₀S ⟨x₁, hx₁S, hne⟩⟩
  · exact Set.disjoint_left.mpr fun z hz₁ hz₀ =>
      hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₀).symm)
  · refine Subset.antisymm (fun z hz => ?_)
      (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
    have hzz : z ∈ connectedComponentIn (range r)ᶜ z := mem_connectedComponentIn hz
    by_cases hzb : IsBounded (connectedComponentIn (range r)ᶜ z)
    · left
      rwa [step_B_bounded_unique hbr hcont hinj x₁ hx₁S z hz hx₁b hzb]
    · right
      rwa [unbounded_component_unique r hcont hx₀u hzb]

end MatedCRTHarmonic.Planar.Jordan
