import Rigidity.Proofs.Section5.PlanarPotentialKernel
import LatticeProb.Graph.HeatVanishing

/-!
# Passing to limits of potential kernels

The local Laplacian commutes with pointwise limits, allowing a limiting potential kernel to
inherit the unit-pole equation.
-/

open Filter Topology LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- The component Laplacian commutes with pointwise limits. -/
theorem tendsto_componentLaplacian {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    {α : Type*} {l : Filter α} (u : α → C → ℝ) (v : C → ℝ)
    (h : ∀ x, Tendsto (fun t => u t x) l (𝓝 (v x))) (x : C) :
    Tendsto (fun t => componentLaplacian C (u t) x) l (𝓝 (componentLaplacian C v x)) := by
  classical
  unfold componentLaplacian
  exact tendsto_finsetSum _ fun y _ => (h y).sub (h x)

/-- Transition probabilities on an infinite open component tend to zero. -/
theorem tendsto_componentHeat_zero {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (x y : C) :
    Tendsto (fun n : ℕ => LatticeProb.Graph.heat (componentGraph C) n x y) atTop (𝓝 0) := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  exact LatticeProb.Graph.heat_tendsto_zero C.connected_toSimpleGraph x y

/-- A pointwise kernel limit inherits its limiting Laplacian. -/
theorem componentLaplacian_eq_of_tendsto {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    {α : Type*} {l : Filter α} [NeBot l] (u : α → C → ℝ) (v q : C → ℝ)
    (hu : ∀ x, Tendsto (fun t => u t x) l (𝓝 (v x)))
    (hq : ∀ x, Tendsto (fun t => componentLaplacian C (u t) x) l (𝓝 (q x))) :
    ∀ x, componentLaplacian C v x = q x := by
  intro x
  exact tendsto_nhds_unique (tendsto_componentLaplacian C u v hu x) (hq x)


/-- A pointwise limit of truncated kernels inherits the unit-pole equation when its remainder is
    a multiple of the transition probability. -/
theorem componentLaplacian_eq_unitPole_of_heat_limit {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C) (u : ℕ → C → ℝ) (v : C → ℝ)
    (hu : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (hΔ : ∀ n x, componentLaplacian C (u n) x = (if x = y then 1 else 0) -
      ((componentGraph C).degree x : ℝ) / (componentGraph C).degree y *
        LatticeProb.Graph.heat (componentGraph C) n x y) :
    ∀ x, componentLaplacian C v x = if x = y then 1 else 0 := by
  apply componentLaplacian_eq_of_tendsto C u v (fun x => if x = y then 1 else 0) hu
  intro x
  have h := (tendsto_const_nhds (x := (if x = y then (1 : ℝ) else 0))).sub
    ((tendsto_componentHeat_zero C hC x y).const_mul
    (((componentGraph C).degree x : ℝ) / (componentGraph C).degree y))
  simpa only [hΔ, mul_zero, sub_zero] using h

/-- A logarithmically bounded limit of truncated kernels gives a planar Green column. -/
theorem exists_greenColumn_of_heat_limit {ω : Configuration 2} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (y : C) (u : ℕ → C → ℝ) (v : C → ℝ) (K R₀ : ℝ)
    (hu : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (hΔ : ∀ n x, componentLaplacian C (u n) x = (if x = y then 1 else 0) -
      ((componentGraph C).degree x : ℝ) / (componentGraph C).degree y *
        LatticeProb.Graph.heat (componentGraph C) n x y)
    (hK : 0 ≤ K) (hbound : ∀ x : C, R₀ ≤ Rigidity.Section5.eucl x.val →
      |v x| ≤ K * Real.log (Rigidity.Section5.eucl x.val)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  exact ⟨fun x => v y - v x, isGreenColumn_of_potentialKernel C y v
    (componentLaplacian_eq_unitPole_of_heat_limit C hC y u v hu hΔ)
    (isSublinearOn_of_log_bound C v K R₀ hK hbound)⟩

end Rigidity.Proofs.Section5
