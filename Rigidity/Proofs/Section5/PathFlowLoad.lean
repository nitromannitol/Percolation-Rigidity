import Rigidity.Proofs.Section5.FlowOnConnectedSet

/-!
# Edge loads of averaged path flows

The absolute flow on an edge averaged over paths is at most the fraction of paths
that use that edge.
-/

open SimpleGraph
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- A nonzero walk flow uses the corresponding unoriented edge. -/
theorem mem_edges_of_walkFlow_ne_zero {V : Type} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {x y : V} (h : walkFlow p x y ≠ 0) : s(x, y) ∈ p.edges := by
  induction p with
  | nil => simp [walkFlow] at h
  | @cons u v w huv p ih =>
    simp only [walkFlow] at h
    by_cases h1 : x = u ∧ y = v
    · obtain ⟨rfl, rfl⟩ := h1
      simp [Walk.edges_cons]
    by_cases h2 : x = v ∧ y = u
    · obtain ⟨rfl, rfl⟩ := h2
      simp [Walk.edges_cons, Sym2.eq_swap]
    simp only [h1, h2, if_false, sub_zero, zero_add] at h
    simp only [Walk.edges_cons, List.mem_cons]
    exact Or.inr (ih h)

/-- An average of path flows is bounded edgewise by its edge-use fraction. -/
theorem abs_average_pathFlow_le_edge_fraction {V ι : Type} {G : SimpleGraph V}
    {a b : V} (s : Finset ι) (p : ι → G.Walk a b)
    (hp : ∀ i ∈ s, (p i).IsPath) (x y : V) :
    |(∑ i ∈ s, walkFlow (p i) x y) / s.card| ≤
      ((s.filter fun i => s(x, y) ∈ (p i).edges).card : ℝ) / s.card := by
  have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  rw [abs_div, abs_of_nonneg hcard]
  apply div_le_div_of_nonneg_right _ hcard
  calc
    _ ≤ ∑ i ∈ s, |walkFlow (p i) x y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (if s(x, y) ∈ (p i).edges then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases he : s(x, y) ∈ (p i).edges
      · simpa [he] using abs_walkFlow_le_one (p i) (hp i hi) x y
      · have hz : walkFlow (p i) x y = 0 := by
          by_contra hn
          exact he (mem_edges_of_walkFlow_ne_zero (p i) hn)
        simp [he, hz]
    _ = _ := by simp

end Rigidity.Proofs.Section5
