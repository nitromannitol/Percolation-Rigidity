import Rigidity.Steps.Section5.Common
import LatticeProb.Network.BarrierMaximum

/-! # Section 5: the finite maximum principle on an infinite open component

A function harmonic on a finite set `Ω` of an infinite open component is bounded on `Ω` by any
upper bound on its outer boundary. The component graph is connected and `Ω` misses a vertex,
so this is the finite maximum principle of the unit-conductance network on the component. -/

open LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- The finite maximum principle on an infinite open component. -/
theorem finiteMaxPrinciple : FiniteMaxPrinciple := by
  intro ω C hC Ω hΩ g hg M hM
  obtain ⟨q, -, hq⟩ := (hC.sdiff hΩ).nonempty
  have hqΩ : q ∉ (hΩ.toFinset : Set C) := by simpa using hq
  have key := LatticeProb.Network.le_on_finset_of_outerBoundary C.connected_toSimpleGraph
    LatticeProb.Network.isCond_unitCond hΩ.toFinset hqΩ g M
    (fun x hx => by
      rw [← componentLaplacian_eq_netLaplacian]
      exact hg x (by simpa using hx))
    (fun x hx => hM x (by rwa [Set.Finite.coe_toFinset] at hx))
  exact fun x hx => key x (by simpa using hx)

end Rigidity.Proofs.Section5
