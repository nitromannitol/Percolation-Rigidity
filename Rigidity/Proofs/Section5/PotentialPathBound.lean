import Rigidity.Proofs.Section5.PotentialLocalBound

/-!
# Potential kernels and graph distance

The truncated potential between two vertices is bounded by the length of any path between them.
-/

open Finset Filter Topology LatticeProb.Percolation LatticeProb.Graph LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- A voltage between two vertices can be chosen with oscillation at most the length of a walk. -/
theorem exists_voltage_le_walk_length {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [Infinite V] (hG : G.Connected) {a b : V} (p : G.Walk a b) :
    ∃ f : V → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ p.length) ∧
      ∀ x : V, laplacian G f x = (if x = b then 1 else 0) - (if x = a then 1 else 0) := by
  let P : Finset V := p.support.toFinset
  let u : Finset V → V → ℝ := fun S x => dipole G S a b x - dipole G S a b b
  have haP : a ∈ P := List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support p)
  have hbP : b ∈ P := List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support p)
  have hbox : ∀ S : Finset V, P ⊆ S → ∀ x, 0 ≤ u S x ∧ u S x ≤ p.length := by
    intro S hPS x
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
    have ha := hPS haP
    have hb := hPS hbP
    refine ⟨by linarith [sink_le_dipole hG S ha hb hq x], ?_⟩
    have h1 := dipole_le_source hG S ha hb hq x
    have h2 := dipole_walk_le hG S ha hb hq p
      (fun z hz => hPS (List.mem_toFinset.mpr hz))
    change dipole G S a b x - dipole G S a b b ≤ p.length
    linarith
  let K : Set (V → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) p.length
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have huK : Filter.map u atTop ≤ 𝓟 K := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    refine Filter.mem_of_superset (Filter.Ici_mem_atTop P) fun S hS => ?_
    intro x _
    exact hbox S hS x
  obtain ⟨f, hfK, hf⟩ := hKc huK
  refine ⟨f, fun x => hfK x (Set.mem_univ x), fun x => ?_⟩
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

/-- A walk bounds the truncated potential between its endpoints uniformly in time. -/
theorem truncatedComponentPotential_le_walk_length {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y x : C)
    (p : (componentGraph C).Walk y x) (n : ℕ) :
    truncatedComponentPotential C n y x ≤ p.length := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  obtain ⟨f, hf, hlap⟩ := exists_voltage_le_walk_length (componentGraph C)
    C.connected_toSimpleGraph p
  have ht := voltage_sub_walkOp_iterate (componentGraph C) C.connected_toSimpleGraph y x f hlap n y
  have hnonneg := walkOp_iterate_nonneg (componentGraph C) f (fun z => (hf z).1) n y
  have heq : truncatedComponentPotential C n y x =
      ∑ k ∈ Finset.range n, (heat (componentGraph C) k y y / ((componentGraph C).degree y : ℝ) -
        heat (componentGraph C) k y x / ((componentGraph C).degree x : ℝ)) := by
    simp only [truncatedComponentPotential, sub_div, heat_div_degree_symm]
  rw [heq]
  linarith [(hf y).2]

end Rigidity.Proofs.Section5
