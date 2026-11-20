import Rigidity.Proofs.Section5.PotentialFiniteFlow

/-!
# Extension of finite flows

Flows on finite induced subgraphs extend by zero to the ambient graph.
-/

open LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- Extend a flow on an induced finite subgraph by zero. -/
noncomputable def extendFiniteFlow {V : Type*} (T : Finset V) (θ : T → T → ℝ) (x y : V) : ℝ :=
  if hx : x ∈ T then if hy : y ∈ T then θ ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0

/-- The extension agrees with the original flow on the finite set. -/
theorem extendFiniteFlow_apply {V : Type*} (T : Finset V) (θ : T → T → ℝ) (x y : T) :
    extendFiniteFlow T θ x y = θ x y := by
  simp [extendFiniteFlow]

/-- The extension vanishes outside the finite set. -/
theorem extendFiniteFlow_eq_zero {V : Type*} (T : Finset V) (θ : T → T → ℝ)
    {x : V} (hx : x ∉ T) (y : V) : extendFiniteFlow T θ x y = 0 := by
  simp [extendFiniteFlow, hx]

/-- Extension by zero preserves antisymmetry and edge support. -/
theorem isFlow_extendFiniteFlow {V : Type*} (G : SimpleGraph V) (T : Finset V)
    (θ : T → T → ℝ) (hθ : IsFlow (G.induce (T : Set V)) θ) :
    IsFlow G (extendFiniteFlow T θ) := by
  refine ⟨?_, ?_⟩
  · intro x y
    by_cases hx : x ∈ T
    · by_cases hy : y ∈ T
      · simpa only [extendFiniteFlow, dif_pos hx, dif_pos hy] using
          hθ.antisymm ⟨x, hx⟩ ⟨y, hy⟩
      · simp [extendFiniteFlow, hx, hy]
    · simp [extendFiniteFlow, hx]
  · intro x y hxy
    by_cases hx : x ∈ T
    · by_cases hy : y ∈ T
      · have hnot : ¬ (G.induce (T : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
        simpa only [extendFiniteFlow, dif_pos hx, dif_pos hy] using hθ.zero_of_not_adj hnot
      · simp [extendFiniteFlow, hx, hy]
    · simp [extendFiniteFlow, hx]

/-- Divergence is preserved at vertices of the finite induced subgraph. -/
theorem divergence_extendFiniteFlow {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (T : Finset V) (θ : T → T → ℝ) (x : T) :
    divergence G (extendFiniteFlow T θ) x =
      divergence (G.induce (T : Set V)) θ x := by
  have hmap : ((G.induce (T : Set V)).neighborFinset x).map
      (Function.Embedding.subtype (fun v => v ∈ T)) = G.neighborFinset x ∩ T := by
    ext z
    simp
  rw [divergence, divergence]
  calc
    _ = ∑ z ∈ G.neighborFinset x ∩ T, extendFiniteFlow T θ x z := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro z hz hnot
      have hzT : z ∉ T := fun hzT => hnot (Finset.mem_inter.mpr ⟨hz, hzT⟩)
      simp [extendFiniteFlow, hzT]
    _ = _ := by
      rw [← hmap, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro z hz
      exact extendFiniteFlow_apply T θ x z

/-- The divergence of the extension vanishes outside its support. -/
theorem divergence_extendFiniteFlow_eq_zero {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (T : Finset V) (θ : T → T → ℝ) {x : V} (hx : x ∉ T) :
    divergence G (extendFiniteFlow T θ) x = 0 := by
  simp [divergence, extendFiniteFlow_eq_zero T θ hx]

/-- Extension by zero preserves the ordered energy of a finite induced-subgraph flow. -/
theorem flowEnergyOn_extendFiniteFlow {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (T : Finset V) (θ : T → T → ℝ) :
    flowEnergyOn G (unitCond G) T (extendFiniteFlow T θ) =
      flowEnergyOn (G.induce (T : Set V)) (unitCond (G.induce (T : Set V))) Finset.univ θ := by
  have hTmap : (Finset.univ : Finset T).map (Function.Embedding.subtype (fun v => v ∈ T)) = T := by
    ext z
    simp
  have houter (f : V → ℝ) : ∑ x ∈ T, f x = ∑ x : T, f x := by
    calc
      _ = ∑ x ∈ (Finset.univ : Finset T).map (Function.Embedding.subtype (fun v => v ∈ T)), f x := by
        rw [hTmap]
      _ = _ := by simp [Finset.sum_map]
  unfold flowEnergyOn
  rw [houter]
  apply Finset.sum_congr rfl
  intro x hx
  have hmap : ((G.induce (T : Set V)).neighborFinset x).map
      (Function.Embedding.subtype (fun v => v ∈ T)) = G.neighborFinset x ∩ T := by
    ext z
    simp
  calc
    _ = ∑ z ∈ G.neighborFinset x ∩ T,
        (extendFiniteFlow T θ x z) ^ 2 / unitCond G x z := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro z hz hnot
      have hzT : z ∉ T := fun hzT => hnot (Finset.mem_inter.mpr ⟨hz, hzT⟩)
      simp [extendFiniteFlow, hzT]
    _ = _ := by
      rw [← hmap, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro z hz
      have hadj : (G.induce (T : Set V)).Adj x z :=
        (SimpleGraph.mem_neighborFinset _ _ _).mp hz
      have hadj' : G.Adj x z := hadj
      simp only [Function.Embedding.subtype_apply, extendFiniteFlow_apply]
      simp [unitCond, hadj']

/-- A unit flow on a finite induced subgraph bounds the component potential. -/
theorem truncatedComponentPotential_le_induced_flow_energy {d : ℕ}
    {ω : LatticeProb.Percolation.Configuration d} (C : LatticeProb.Percolation.OpenComponent ω)
    (hC : C.supp.Infinite) (y x : C) (T : Finset C) (hy : y ∈ T) (hx : x ∈ T)
    (θ : T → T → ℝ) (K : ℝ)
    (hθ : IsFlow ((LatticeProb.Percolation.componentGraph C).induce (T : Set C)) θ)
    (hdiv : ∀ z : T, divergence ((LatticeProb.Percolation.componentGraph C).induce (T : Set C)) θ z =
      (if z = ⟨y, hy⟩ then 1 else 0) - (if z = ⟨x, hx⟩ then 1 else 0))
    (henergy : flowEnergyOn ((LatticeProb.Percolation.componentGraph C).induce (T : Set C))
      (unitCond ((LatticeProb.Percolation.componentGraph C).induce (T : Set C))) Finset.univ θ ≤ 2 * K)
    (n : ℕ) : truncatedComponentPotential C n y x ≤ K := by
  let G := LatticeProb.Percolation.componentGraph C
  let Θ := extendFiniteFlow T θ
  apply truncatedComponentPotential_le_finite_flow_energy C hC y x Θ T K
    (isFlow_extendFiniteFlow G T θ hθ) (fun z hz w => extendFiniteFlow_eq_zero T θ hz w)
  · intro z
    by_cases hz : z ∈ T
    · have hd := hdiv ⟨z, hz⟩
      rw [← divergence_extendFiniteFlow G T θ ⟨z, hz⟩] at hd
      by_cases hzy : z = y <;> by_cases hzx : z = x <;> simpa [hzy, hzx] using hd
    · have hzy : z ≠ y := fun h => hz (h ▸ hy)
      have hzx : z ≠ x := fun h => hz (h ▸ hx)
      simp only [if_neg hzy, if_neg hzx, sub_self]
      exact divergence_extendFiniteFlow_eq_zero _ T θ hz
  · rw [show flowEnergyOn G (unitCond G) T Θ =
        flowEnergyOn (G.induce (T : Set C)) (unitCond (G.induce (T : Set C))) Finset.univ θ from
      flowEnergyOn_extendFiniteFlow G T θ]
    exact henergy

/-- Logarithmic-energy flows on finite induced subgraphs give a planar Green column. -/
theorem exists_greenColumn_of_finite_logarithmic_flows
    {ω : LatticeProb.Percolation.Configuration 2} (C : LatticeProb.Percolation.OpenComponent ω)
    (hC : C.supp.Infinite) (y : C) (K R₀ : ℝ) (hK : 0 ≤ K)
    (hflow : ∀ x : C, R₀ ≤ Rigidity.Section5.eucl x.val →
      ∃ (T : Finset C) (hy : y ∈ T) (hx : x ∈ T) (θ : T → T → ℝ),
        IsFlow ((LatticeProb.Percolation.componentGraph C).induce (T : Set C)) θ ∧
        (∀ z : T, divergence ((LatticeProb.Percolation.componentGraph C).induce (T : Set C)) θ z =
          (if z = ⟨y, hy⟩ then 1 else 0) - (if z = ⟨x, hx⟩ then 1 else 0)) ∧
        flowEnergyOn ((LatticeProb.Percolation.componentGraph C).induce (T : Set C))
          (unitCond ((LatticeProb.Percolation.componentGraph C).induce (T : Set C))) Finset.univ θ ≤
            2 * (K * Real.log (Rigidity.Section5.eucl x.val))) :
    ∃ g, LatticeProb.Percolation.IsGreenColumn 2 le_rfl C y g := by
  apply exists_greenColumn_of_truncatedPotential_log_bound C hC y K R₀ hK
  intro n x hx
  obtain ⟨T, hy, hxT, θ, hθ, hdiv, henergy⟩ := hflow x hx
  rw [abs_of_nonneg (truncatedComponentPotential_nonneg C n y x)]
  exact truncatedComponentPotential_le_induced_flow_energy C hC y x T hy hxT θ _
    hθ hdiv henergy n

end Rigidity.Proofs.Section5
