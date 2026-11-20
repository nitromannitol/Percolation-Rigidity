import Rigidity.Proofs.Percolation.PlanarBoxGeometry
import Rigidity.Proofs.Percolation.PlanarPathCardinality

/-!
# Long planar paths and coordinate displacement

An injective path longer than the number of vertices in a small cube has an open subpath with a
large coordinate displacement.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5

namespace Rigidity.Percolation

/-- Every vertex of a finite nearest-neighbour path is reachable from its first vertex. -/
theorem fin_path_reachable {α : Type*} (G : SimpleGraph α) {n : ℕ}
    (γ : Fin (n + 1) → α) (hγ : ∀ i : Fin n, G.Adj (γ i.castSucc) (γ i.succ))
    (i : Fin (n + 1)) : G.Reachable (γ 0) (γ i) := by
  have h : ∀ k (hk : k ≤ n), G.Reachable (γ 0) (γ ⟨k, by omega⟩) := by
    intro k hk
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      exact (ih (by omega)).trans (hγ ⟨k, by omega⟩).reachable
  exact h i.val (by omega)

/-- A sufficiently long injective open path contains a subpath with large coordinate displacement. -/
theorem exists_open_subpath_with_displacement {ω : Configuration 2} {x : Vertex 2}
    {N n r : ℕ} (γ : Fin (n + 1) → Vertex 2) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin n, (openIn ω (cubeAt x N)).Adj (γ i.castSucc) (γ i.succ))
    (hn : (2 * r + 1) ^ 2 < n + 1) :
    ∃ (b : Vertex 2) (j : Fin 2), ReachIn ω (cubeAt x N) (γ 0) b ∧
      (r : ℤ) < |b j - γ 0 j| := by
  obtain ⟨i, j, hij⟩ := exists_path_coordinate_displacement γ hinj hn
  have h1 : 0 < (2 * r + 1) ^ 2 := by positivity
  have hnpos : 0 < n := by omega
  have hstart : γ 0 ∈ cubeAt x N := (hγ ⟨0, hnpos⟩).2.1
  exact ⟨γ i, j, reachIn_of_reachable_openIn hstart (fin_path_reachable _ γ hγ i), hij⟩

end Rigidity.Percolation
