import Rigidity.Proofs.Section5.FlowOnConnectedSet
import Rigidity.Proofs.Section5.FlowSeries

/-!
# Edge loads of averaged path flows

The absolute flow on an edge averaged over paths is at most the fraction of paths
that use that edge.
-/

open SimpleGraph LatticeProb.Network
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

/-- Averaging finitely many paths gives a unit flow whose energy is bounded by the sum of
the squared fractions of paths using each edge. -/
theorem exists_flow_energy_le_path_edge_fractions {V ι : Type} [Fintype V]
    (G : SimpleGraph V) [G.LocallyFinite] {a b : V} (s : Finset ι) (hs : s.Nonempty)
    (p : ι → G.Walk a b) (hp : ∀ i ∈ s, (p i).IsPath) :
    ∃ θ : V → V → ℝ, IsFlow G θ ∧
      (∀ z, divergence G θ z = (if z = a then 1 else 0) - (if z = b then 1 else 0)) ∧
      flowEnergyOn G (unitCond G) Finset.univ θ ≤
        ∑ x : V, ∑ y ∈ G.neighborFinset x,
          (((s.filter fun i => s(x, y) ∈ (p i).edges).card : ℝ) / s.card) ^ 2 := by
  let ψ (i : ι) := walkFlow (p i)
  have hflow : ∀ i ∈ s, IsFlow G (ψ i) := by
    intro i hi
    refine ⟨fun x y => walkFlow_antisymm (p i) y x, ?_⟩
    intro x y hxy
    by_contra hn
    exact hxy (walkFlow_ne_zero (p i) hn).1
  have hdiv : ∀ i ∈ s, ∀ z, divergence G (ψ i) z =
      (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
    intro i hi z
    rw [divergence]
    calc
      _ = ∑ w : V, ψ i z w := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w hw hnot
        have hn : ¬ G.Adj z w := by simpa using hnot
        exact (hflow i hi).zero_of_not_adj hn
      _ = _ := sum_walkFlow (p i) (fun x hx => Finset.mem_univ x) z
  let θ : V → V → ℝ := fun x y => (∑ i ∈ s, ψ i x y) / s.card
  obtain ⟨hθ, hθdiv⟩ := isFlow_average_unit_divergence G s hs ψ a b hflow hdiv
  refine ⟨θ, hθ, hθdiv, ?_⟩
  unfold flowEnergyOn
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
  have hload := abs_average_pathFlow_le_edge_fraction s p hp x y
  have hnonneg : 0 ≤ ((s.filter fun i => s(x, y) ∈ (p i).edges).card : ℝ) / s.card :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsquare : θ x y ^ 2 ≤
      (((s.filter fun i => s(x, y) ∈ (p i).edges).card : ℝ) / s.card) ^ 2 := by
    change |θ x y| ≤ _ at hload
    nlinarith [sq_abs (θ x y), abs_nonneg (θ x y)]
  simpa [unitCond, hadj] using hsquare

end Rigidity.Proofs.Section5
