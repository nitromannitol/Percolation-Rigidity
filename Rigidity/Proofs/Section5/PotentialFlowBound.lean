import Rigidity.Proofs.Section5.PotentialPathBound
import LatticeProb.Network.FiniteEnergyVoltage
import Rigidity.Proofs.Section5.PlanarPotentialLogBound

/-!
# Potential kernels and unit flows

A unit flow bounds truncated potential kernels by its energy.
-/

open Finset Filter Topology LatticeProb.Percolation LatticeProb.Graph LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- A unit flow bounds the oscillation of a voltage between its source and sink. -/
theorem exists_voltage_le_flow_energy {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [Infinite V] (hG : G.Connected) (a b : V) (θ : V → V → ℝ) (K : ℝ)
    (hθ : IsFlow G θ)
    (hdiv : ∀ z, divergence G θ z = (if z = a then 1 else 0) - (if z = b then 1 else 0))
    (henergy : ∀ S : Finset V, flowEnergyOn G (unitCond G) S θ ≤ 2 * K) :
    ∃ f : V → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ K) ∧
      ∀ x, laplacian G f x = (if x = b then 1 else 0) - (if x = a then 1 else 0) := by
  obtain ⟨p⟩ := hG.preconnected a b
  let P : Finset V := p.support.toFinset
  let u : Finset V → V → ℝ := fun S x => dipole G S a b x - dipole G S a b b
  have haP : a ∈ P := List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support p)
  have hbP : b ∈ P := List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support p)
  have hbox : ∀ S : Finset V, P ⊆ S → ∀ x, 0 ≤ u S x ∧ u S x ≤ K := by
    intro S hPS x
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
    have ha := hPS haP
    have hb := hPS hbP
    have hth := thomson_principle (G := G) isCond_unitCond (nbhd G S) S
      (dipole G S a b) θ hθ
      (fun z hz => dipole_vanishes hG S hq hz) (subset_nbhd S)
      (fun z hz w hzw => mem_nbhd_of_adj hz hzw) (by
        intro z hz
        rw [hdiv z, netLaplacian_unitCond, laplacian_dipole hG S ha hb hq hz]
        ring)
    rw [energyOn_dipole hG S (nbhd G S) ha hb hq (subset_nbhd S)
      (fun z hz w hzw => mem_nbhd_of_adj hz hzw)] at hth
    have hbound := henergy (nbhd G S)
    have h1 := dipole_le_source hG S ha hb hq x
    refine ⟨by linarith [sink_le_dipole hG S ha hb hq x], ?_⟩
    change dipole G S a b x - dipole G S a b b ≤ K
    linarith
  let B : Set (V → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) K
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  have huB : Filter.map u atTop ≤ 𝓟 B := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    refine Filter.mem_of_superset (Filter.Ici_mem_atTop P) fun S hS => ?_
    intro x _
    exact hbox S hS x
  obtain ⟨f, hfB, hf⟩ := hBc huB
  refine ⟨f, fun x => hfB x (Set.mem_univ x), fun x => ?_⟩
  let Z : Set (V → ℝ) := {g | laplacian G g x =
    (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0)}
  have hZc : IsClosed Z := by
    refine isClosed_eq ?_ continuous_const
    show Continuous fun g : V → ℝ => ∑ y ∈ G.neighborFinset x, (g y - g x)
    exact continuous_finsetSum _ fun y _ => (continuous_apply y).sub (continuous_apply x)
  have hZF : Z ∈ Filter.map u atTop := by
    rw [Filter.mem_map]
    refine Filter.mem_of_superset (Filter.Ici_mem_atTop (insert x P)) fun S hS => ?_
    have hS' : insert x P ⊆ S := hS
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
    show laplacian G (fun v => dipole G S a b v - dipole G S a b b) x = _
    rw [laplacian_sub_const]
    exact laplacian_dipole hG S (hS' (Finset.mem_insert_of_mem haP))
      (hS' (Finset.mem_insert_of_mem hbP)) hq (hS' (Finset.mem_insert_self x P))
  have hcl : f ∈ closure Z :=
    mem_closure_iff_clusterPt.mpr (hf.mono (Filter.le_principal_iff.mpr hZF))
  rw [hZc.closure_eq] at hcl
  exact hcl

/-- A unit flow between two component vertices bounds their truncated potential. -/
theorem truncatedComponentPotential_le_flow_energy {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y x : C)
    (θ : C → C → ℝ) (K : ℝ) (hθ : IsFlow (componentGraph C) θ)
    (hdiv : ∀ z, divergence (componentGraph C) θ z =
      (if z = y then 1 else 0) - (if z = x then 1 else 0))
    (henergy : ∀ S : Finset C, flowEnergyOn (componentGraph C)
      (unitCond (componentGraph C)) S θ ≤ 2 * K) (n : ℕ) :
    truncatedComponentPotential C n y x ≤ K := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  obtain ⟨f, hf, hlap⟩ := exists_voltage_le_flow_energy (componentGraph C)
    C.connected_toSimpleGraph y x θ K hθ (fun z => by
      by_cases hy : z = y <;> by_cases hx : z = x <;> simpa [hy, hx] using hdiv z) henergy
  have ht := voltage_sub_walkOp_iterate (componentGraph C) C.connected_toSimpleGraph y x f hlap n y
  have hnonneg := walkOp_iterate_nonneg (componentGraph C) f (fun z => (hf z).1) n y
  have heq : truncatedComponentPotential C n y x =
      ∑ k ∈ Finset.range n, (heat (componentGraph C) k y y / ((componentGraph C).degree y : ℝ) -
        heat (componentGraph C) k y x / ((componentGraph C).degree x : ℝ)) := by
    simp only [truncatedComponentPotential, sub_div, heat_div_degree_symm]
  rw [heq]
  linarith [(hf y).2]

/-- Logarithmic-energy flows from the pole produce a planar Green column. -/
theorem exists_greenColumn_of_logarithmic_flow_energy {ω : Configuration 2}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C) (K R₀ : ℝ) (hK : 0 ≤ K)
    (hflow : ∀ x : C, R₀ ≤ Rigidity.Section5.eucl x.val →
      ∃ θ : C → C → ℝ, IsFlow (componentGraph C) θ ∧
        (∀ z, divergence (componentGraph C) θ z =
          (if z = y then 1 else 0) - (if z = x then 1 else 0)) ∧
        ∀ S : Finset C, flowEnergyOn (componentGraph C) (unitCond (componentGraph C)) S θ ≤
          2 * (K * Real.log (Rigidity.Section5.eucl x.val))) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  apply exists_greenColumn_of_truncatedPotential_log_bound C hC y K R₀ hK
  intro n x hx
  obtain ⟨θ, hθ, hdiv, henergy⟩ := hflow x hx
  rw [abs_of_nonneg (truncatedComponentPotential_nonneg C n y x)]
  exact truncatedComponentPotential_le_flow_energy C hC y x θ _ hθ hdiv henergy n

end Rigidity.Proofs.Section5
