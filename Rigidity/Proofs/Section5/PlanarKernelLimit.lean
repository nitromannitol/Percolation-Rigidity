import Rigidity.Proofs.Section5.PlanarPotentialKernel

/-!
# Passing to limits of potential kernels

The local Laplacian commutes with pointwise limits, allowing a limiting potential kernel to
inherit the unit-pole equation.
-/

open Filter Topology LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

/-- The component Laplacian commutes with pointwise limits. -/
theorem tendsto_componentLaplacian {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    {α : Type*} {l : Filter α} (u : α → C → ℝ) (v : C → ℝ)
    (h : ∀ x, Tendsto (fun t => u t x) l (𝓝 (v x))) (x : C) :
    Tendsto (fun t => componentLaplacian C (u t) x) l (𝓝 (componentLaplacian C v x)) := by
  classical
  unfold componentLaplacian
  exact tendsto_finsetSum _ fun y _ => (h y).sub (h x)

/-- A pointwise kernel limit inherits its limiting Laplacian. -/
theorem componentLaplacian_eq_of_tendsto {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    {α : Type*} {l : Filter α} [NeBot l] (u : α → C → ℝ) (v q : C → ℝ)
    (hu : ∀ x, Tendsto (fun t => u t x) l (𝓝 (v x)))
    (hq : ∀ x, Tendsto (fun t => componentLaplacian C (u t) x) l (𝓝 (q x))) :
    ∀ x, componentLaplacian C v x = q x := by
  intro x
  exact tendsto_nhds_unique (tendsto_componentLaplacian C u v hu x) (hq x)

end Rigidity.Proofs.Section5
