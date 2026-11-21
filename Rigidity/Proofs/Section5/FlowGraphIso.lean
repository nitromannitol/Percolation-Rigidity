import LatticeProb.Network.Flow

/-!
# Flow transport under graph isomorphisms

Graph isomorphisms preserve flows, divergence, and unit-conductance energy.
-/

open LatticeProb.Network
open scoped Classical

namespace Rigidity.Proofs.Section5

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
  [G.LocallyFinite] [H.LocallyFinite] (e : G ≃g H)

/-- The image of a neighbor set under a graph isomorphism is the neighbor set of the image. -/
theorem map_neighborFinset_graphIso (x : V) :
    (G.neighborFinset x).map e.toEquiv.toEmbedding = H.neighborFinset (e x) := by
  ext y
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact e.map_adj_iff.mpr hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact e.map_adj_iff.mp (by simpa using hy)

omit [G.LocallyFinite] [H.LocallyFinite] in
/-- Pulling a flow back along a graph isomorphism gives a flow. -/
theorem isFlow_comp_graphIso (θ : W → W → ℝ) (hθ : IsFlow H θ) :
    IsFlow G (fun x y => θ (e x) (e y)) := by
  refine ⟨fun x y => hθ.antisymm (e x) (e y), ?_⟩
  intro x y hxy
  exact hθ.zero_of_not_adj (fun h => hxy (e.map_adj_iff.mp h))

/-- Divergence is preserved by pullback along a graph isomorphism. -/
theorem divergence_comp_graphIso (θ : W → W → ℝ) (x : V) :
    divergence G (fun x y => θ (e x) (e y)) x = divergence H θ (e x) := by
  rw [divergence, divergence, ← map_neighborFinset_graphIso G H e x, Finset.sum_map]
  rfl

/-- Ordered unit-conductance energy is preserved by pullback along a graph isomorphism. -/
theorem flowEnergyOn_comp_graphIso (θ : W → W → ℝ) (S : Finset V) :
    flowEnergyOn G (unitCond G) S (fun x y => θ (e x) (e y)) =
      flowEnergyOn H (unitCond H) (S.map e.toEquiv.toEmbedding) θ := by
  unfold flowEnergyOn
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x hx
  change (∑ y ∈ G.neighborFinset x, θ (e x) (e y) ^ 2 / unitCond G x y) =
    ∑ y ∈ H.neighborFinset (e x), θ (e x) y ^ 2 / unitCond H (e x) y
  rw [← map_neighborFinset_graphIso G H e x, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro y hy
  have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
  have hadj' : H.Adj (e x) (e y) := e.map_adj_iff.mpr hadj
  simp [unitCond, hadj, hadj']

end Rigidity.Proofs.Section5
