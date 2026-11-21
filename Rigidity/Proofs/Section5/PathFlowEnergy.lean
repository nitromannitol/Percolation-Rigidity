import Rigidity.Proofs.Section5.FlowOnConnectedSet
import LatticeProb.Network.Flow
import LatticeProb.Prob.Percolation.LatticeBondGraph

/-!
# Energy of path flows

A short walk in a bounded-degree finite graph gives a unit flow of comparable energy.
-/

open LatticeProb.Network SimpleGraph
open scoped Classical

namespace Rigidity.Proofs.Section5

/-- A walk gives a unit flow whose energy is bounded by the degree bound times its length. -/
theorem exists_flow_energy_le_degree_mul_length {V : Type} [Fintype V] (G : SimpleGraph V)
    [G.LocallyFinite] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) {a b : V} (p : G.Walk a b) :
    ∃ θ : V → V → ℝ, IsFlow G θ ∧
      (∀ z, divergence G θ z = (if z = a then 1 else 0) - (if z = b then 1 else 0)) ∧
      flowEnergyOn G (unitCond G) Finset.univ θ ≤ (D : ℝ) * (p.length + 1) := by
  let q := p.bypass
  let θ := walkFlow q
  let P : Finset V := q.support.toFinset
  have hθ : IsFlow G θ := by
    refine ⟨fun x y => (walkFlow_antisymm q y x), ?_⟩
    intro x y hxy
    by_contra hn
    exact hxy (walkFlow_ne_zero q hn).1
  have hdiv : ∀ z, divergence G θ z =
      (if z = a then 1 else 0) - (if z = b then 1 else 0) := by
    intro z
    rw [divergence]
    calc
      _ = ∑ w : V, θ z w := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w hw hnot
        have hn : ¬ G.Adj z w := by simpa using hnot
        exact hθ.zero_of_not_adj hn
      _ = _ := sum_walkFlow q (fun x hx => Finset.mem_univ x) z
  have hsq (x y : V) : θ x y ^ 2 ≤ 1 := by
    have habs := abs_walkFlow_le_one q p.bypass_isPath x y
    have habs' := abs_le.mp habs
    nlinarith [habs'.1, habs'.2]
  have heq : flowEnergyOn G (unitCond G) Finset.univ θ =
      ∑ x ∈ P, ∑ y ∈ G.neighborFinset x, θ x y ^ 2 / unitCond G x y := by
    unfold flowEnergyOn
    symm
    apply Finset.sum_subset (Finset.subset_univ P)
    intro x hx hnot
    apply Finset.sum_eq_zero
    intro y hy
    have hzero : θ x y = 0 := by
      by_contra hn
      exact hnot (List.mem_toFinset.mpr (walkFlow_ne_zero q hn).2.1)
    simp [hzero]
  have hP : P.card ≤ p.length + 1 := by
    calc
      P.card ≤ q.support.length := List.toFinset_card_le _
      _ = q.length + 1 := q.length_support
      _ ≤ p.length + 1 := Nat.add_le_add_right p.length_bypass_le_length 1
  refine ⟨θ, hθ, hdiv, ?_⟩
  rw [heq]
  calc
    _ ≤ ∑ _x ∈ P, (D : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        _ ≤ ∑ _y ∈ G.neighborFinset x, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro y hy
          have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
          simpa [unitCond, hadj] using hsq x y
        _ = G.degree x := by simp [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ D := by exact_mod_cast hD x
    _ = (P.card : ℝ) * D := by simp
    _ ≤ (D : ℝ) * (p.length + 1) := by
      have hP' : (P.card : ℝ) ≤ p.length + 1 := by exact_mod_cast hP
      nlinarith

/-- A walk in a finite induced open lattice graph gives a unit flow with energy at most
`2d` times one plus its length. -/
theorem exists_lattice_flow_energy_le_walk_length {d : ℕ}
    {ω : LatticeProb.Percolation.Configuration d} (V : Finset (LatticeProb.Percolation.Vertex d))
    {a b : V} (p : ((LatticeProb.Percolation.openGraph ω).induce (V : Set _)).Walk a b) :
    ∃ θ : V → V → ℝ, IsFlow ((LatticeProb.Percolation.openGraph ω).induce (V : Set _)) θ ∧
      (∀ z, divergence ((LatticeProb.Percolation.openGraph ω).induce (V : Set _)) θ z =
        (if z = a then 1 else 0) - (if z = b then 1 else 0)) ∧
      flowEnergyOn ((LatticeProb.Percolation.openGraph ω).induce (V : Set _))
        (unitCond ((LatticeProb.Percolation.openGraph ω).induce (V : Set _))) Finset.univ θ ≤
          ((2 * d : ℕ) : ℝ) * (p.length + 1) := by
  let G := LatticeProb.Percolation.openGraph ω
  let H := G.induce (V : Set (LatticeProb.Percolation.Vertex d))
  have hdegree : ∀ v : V, H.degree v ≤ 2 * d := by
    intro v
    let e : H.neighborSet v ↪ G.neighborSet v.val :=
      ⟨fun w => ⟨w.val.val, w.property⟩, fun w w' h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : G.neighborSet v.val => z.val) h⟩
    calc
      H.degree v ≤ G.degree v.val := by
        rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
        exact Fintype.card_le_of_injective e e.injective
      _ ≤ 2 * d := LatticeProb.Percolation.openGraph_degree_le ω v.val
  obtain ⟨θ, hθ, hdiv, henergy⟩ :=
    exists_flow_energy_le_degree_mul_length H (2 * d) hdegree p
  refine ⟨θ, hθ, ?_, henergy⟩
  intro z
  by_cases hza : z = a <;> by_cases hzb : z = b <;>
    simpa [hza, hzb] using hdiv z

end Rigidity.Proofs.Section5
