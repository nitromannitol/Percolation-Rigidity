import Rigidity.Steps.S3.NotLipschitz

/-!
# `step:3.2-removal`: a maximal set of removable edges

Step `step:3.2-removal` of Proposition 3.2 (corrected draft L986-1022). Among the subsets `B` of a
finite set `H` of open edges of the cluster `C` whose closing leaves the vertices of `C` connected,
pick one, `B`, of maximal cardinality (the empty set is one). If `e = {x, y} ∈ H \ B` and `x`, `y`
were still connected after closing `insert e B`, then every walk of the environment with `B` closed
could be rerouted around `e` along this connection, so `insert e B` would also leave `C` connected,
contradicting the maximality of `B`. This is the outcome of the greedy procedure of the paper,
which removes the edges of `H` one at a time whenever their removal does not disconnect the
current cluster.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Proofs.S3

open LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- A bond is open after closing `B` iff it is not in `B` and it is open. -/
theorem closeBonds_eq_true_iff (B : Finset (Bond d)) (ω : Configuration d) (e : Bond d) :
    closeBonds B ω e = true ↔ e ∉ B ∧ ω e = true := by
  unfold closeBonds
  split_ifs with h <;> simp [h]

/-- Closing no bond does not change the environment. -/
theorem closeBonds_empty (ω : Configuration d) : closeBonds ∅ ω = ω := by
  funext e
  simp [closeBonds]

/-- If `x` and `y` are joined in `G₁`, and every edge of `G₂` is an edge of `G₁` or the edge
`{x, y}`, then every pair of vertices joined in `G₂` is joined in `G₁`. -/
theorem reachable_of_reroute {V : Type*} {G₁ G₂ : SimpleGraph V} {x y : V}
    (hadj : ∀ a b, G₂.Adj a b → G₁.Adj a b ∨ s(a, b) = s(x, y)) (hxy : G₁.Reachable x y)
    {a b : V} (h : G₂.Reachable a b) : G₁.Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h' _ ih =>
    rcases hadj _ _ h' with h₁ | h₁
    · exact h₁.reachable.trans ih
    · rcases Sym2.eq_iff.mp h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy.trans ih
      · exact hxy.symm.trans ih

/-- An open edge after closing `B` is an open edge after closing `insert e B`, or the edge `e`. -/
theorem openGraph_closeBonds_insert_adj (ω : Configuration d) (B : Finset (Bond d)) (e : Bond d)
    {x y : Vertex d} (he : (e : Sym2 (Vertex d)) = s(x, y)) (a b : Vertex d)
    (hab : (openGraph (closeBonds B ω)).Adj a b) :
    (openGraph (closeBonds (insert e B) ω)).Adj a b ∨ s(a, b) = s(x, y) := by
  obtain ⟨h, ho⟩ := hab
  rw [closeBonds_eq_true_iff] at ho
  by_cases hbe : bondOfAdjacent h = e
  · right
    rw [← he, ← hbe]
    rfl
  · left
    refine ⟨h, ?_⟩
    rw [closeBonds_eq_true_iff, Finset.mem_insert, not_or]
    exact ⟨⟨hbe, ho.1⟩, ho.2⟩

/-- `step:3.2-removal`. -/
theorem removalStep : RemovalStep d := by
  intro ω C H _
  classical
  let P : Finset (Bond d) → Prop := fun B =>
    ∀ x ∈ C.supp, ∀ y ∈ C.supp, (openGraph (closeBonds B ω)).Reachable x y
  have hP0 : P ∅ := by
    intro x hx y hy
    rw [closeBonds_empty]
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx hy
    exact SimpleGraph.ConnectedComponent.exact (hx.trans hy.symm)
  obtain ⟨B, hBmem, hBmax⟩ := Finset.exists_max_image (H.powerset.filter P) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset H, hP0⟩⟩
  obtain ⟨hBH, hB⟩ := Finset.mem_filter.mp hBmem
  refine ⟨B, Finset.mem_powerset.mp hBH, hB, ?_⟩
  intro e heH heB x y he hxy
  have hP : P (insert e B) := fun a ha b hb =>
    reachable_of_reroute (openGraph_closeBonds_insert_adj ω B e he) hxy (hB a ha b hb)
  have hle := hBmax (insert e B) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset heH (Finset.mem_powerset.mp hBH)), hP⟩)
  rw [Finset.card_insert_of_notMem heB] at hle
  omega

end Rigidity.Proofs.S3
