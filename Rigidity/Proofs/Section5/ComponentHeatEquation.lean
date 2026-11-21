import Rigidity.Proofs.Section5.PlanarKernelLimit

/-!
# The heat equation on open components

The transition kernel satisfies the discrete heat equation with the component Laplacian.
-/

open Filter Topology LatticeProb.Percolation
open scoped Classical
namespace Rigidity.Proofs.Section5

/-- The heat equation on an infinite open component. -/
theorem componentLaplacian_heat {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (n : ℕ) (x y : C) :
    componentLaplacian C (fun z => LatticeProb.Graph.heat (componentGraph C) n z y) x =
      ((componentGraph C).degree x : ℝ) *
        (LatticeProb.Graph.heat (componentGraph C) (n + 1) x y -
          LatticeProb.Graph.heat (componentGraph C) n x y) := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  have hd : ((componentGraph C).degree x : ℝ) ≠ 0 := by
    exact_mod_cast (LatticeProb.Graph.degree_pos C.connected_toSimpleGraph x).ne'
  rw [LatticeProb.Graph.heat_succ, LatticeProb.Graph.walkOp]
  simp only [componentLaplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp

/-- The Laplacian of a normalized heat-kernel difference. -/
theorem componentLaplacian_heatDifference {d : ℕ} {ω : Configuration d} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (n : ℕ) (x y : C) :
    componentLaplacian C (fun z =>
      (LatticeProb.Graph.heat (componentGraph C) n y y -
        LatticeProb.Graph.heat (componentGraph C) n z y) / (componentGraph C).degree y) x =
      ((componentGraph C).degree x : ℝ) / (componentGraph C).degree y *
        (LatticeProb.Graph.heat (componentGraph C) n x y -
          LatticeProb.Graph.heat (componentGraph C) (n + 1) x y) := by
  classical
  have hh := componentLaplacian_heat C hC n x y
  have hlocal : componentLaplacian C (fun z =>
      (LatticeProb.Graph.heat (componentGraph C) n y y -
        LatticeProb.Graph.heat (componentGraph C) n z y) / (componentGraph C).degree y) x =
      -(componentLaplacian C (fun z => LatticeProb.Graph.heat (componentGraph C) n z y) x) /
        (componentGraph C).degree y := by
    simp only [componentLaplacian, ← Finset.sum_neg_distrib]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [hlocal, hh]
  ring

/-- Finite potential kernel defined by the normalized heat-kernel difference. -/
noncomputable def truncatedComponentPotential {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (n : ℕ) (y x : C) : ℝ :=
  ∑ k ∈ Finset.range n,
    (LatticeProb.Graph.heat (componentGraph C) k y y -
      LatticeProb.Graph.heat (componentGraph C) k x y) / (componentGraph C).degree y

/-- The finite potential kernel has the unit-pole equation with a heat remainder. -/
theorem componentLaplacian_truncatedPotential {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (n : ℕ) (x y : C) :
    componentLaplacian C (truncatedComponentPotential C n y) x = (if x = y then 1 else 0) -
      ((componentGraph C).degree x : ℝ) / (componentGraph C).degree y *
        LatticeProb.Graph.heat (componentGraph C) n x y := by
  classical
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  have hd : ((componentGraph C).degree y : ℝ) ≠ 0 := by
    exact_mod_cast (LatticeProb.Graph.degree_pos C.connected_toSimpleGraph y).ne'
  have hsum : componentLaplacian C (truncatedComponentPotential C n y) x =
      ∑ k ∈ Finset.range n, componentLaplacian C (fun z =>
        (LatticeProb.Graph.heat (componentGraph C) k y y -
          LatticeProb.Graph.heat (componentGraph C) k z y) / (componentGraph C).degree y) x := by
    simp only [componentLaplacian, truncatedComponentPotential, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hsum]
  simp_rw [componentLaplacian_heatDifference C hC]
  rw [← Finset.mul_sum, Finset.sum_range_sub']
  simp only [LatticeProb.Graph.heat]
  split_ifs with h
  · subst x
    field_simp
  · simp



/-- A logarithmically bounded limit of truncated potentials gives a planar Green column. -/
theorem exists_greenColumn_of_truncatedPotential_limit {ω : Configuration 2} (C : OpenComponent ω)
    (hC : C.supp.Infinite) (y : C) (v : C → ℝ) (K R₀ : ℝ)
    (hu : ∀ x, Filter.Tendsto (fun n => truncatedComponentPotential C n y x)
      Filter.atTop (nhds (v x)))
    (hK : 0 ≤ K) (hbound : ∀ x : C, R₀ ≤ Rigidity.Section5.eucl x.val →
      |v x| ≤ K * Real.log (Rigidity.Section5.eucl x.val)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g :=
  exists_greenColumn_of_heat_limit C hC y (fun n => truncatedComponentPotential C n y) v K R₀
    hu (fun n x => componentLaplacian_truncatedPotential C hC n x y) hK hbound

/-- Any diverging sequence of truncated potentials with a logarithmically bounded pointwise
limit gives a planar Green column. -/
theorem exists_greenColumn_of_truncatedPotential_subsequence_limit {ω : Configuration 2}
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (v : C → ℝ) (K R₀ : ℝ)
    (hu : ∀ x, Tendsto (fun n => truncatedComponentPotential C (φ n) y x)
      atTop (nhds (v x)))
    (hK : 0 ≤ K) (hbound : ∀ x : C, R₀ ≤ Rigidity.Section5.eucl x.val →
      |v x| ≤ K * Real.log (Rigidity.Section5.eucl x.val)) :
    ∃ g, IsGreenColumn 2 le_rfl C y g := by
  have hΔ : ∀ x, componentLaplacian C v x = if x = y then 1 else 0 := by
    apply componentLaplacian_eq_of_tendsto C
      (fun n => truncatedComponentPotential C (φ n) y) v (fun x => if x = y then 1 else 0) hu
    intro x
    have h := (tendsto_const_nhds (x := (if x = y then (1 : ℝ) else 0))).sub
      (((tendsto_componentHeat_zero C hC x y).comp hφ).const_mul
        (((componentGraph C).degree x : ℝ) / (componentGraph C).degree y))
    simp_rw [componentLaplacian_truncatedPotential C hC]
    simpa only [Function.comp_apply, mul_zero, sub_zero] using h
  exact ⟨fun x => v y - v x, isGreenColumn_of_potentialKernel C y v hΔ
    (isSublinearOn_of_log_bound C v K R₀ hK hbound)⟩

end Rigidity.Proofs.Section5
