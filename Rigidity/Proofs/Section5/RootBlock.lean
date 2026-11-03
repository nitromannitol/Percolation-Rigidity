import Rigidity.Proofs.Section5.ExplorationBlocks
import Rigidity.Proofs.Section5.LeafExit

/-! # Lemma 5.27, Step 2: the root block

Proof of `RootBlockStep` (Step 2, corrected draft L2496, corrected in the carving
`Rigidity/Steps/Section5/LargeGradientSensitive.lean`).

By `Δℓ(x₁) = 0` the flux of `ℓ` from `x₁` to its neighbours `y` with `ℓ(y) > ℓ(x₁)` equals minus
the flux to the others, which is at least `ℓ(x₁) - ℓ(x₀) ≥ C_χ` (the term of `x₀`; the other
terms are `≤ 0`). There are at most four such neighbours, so one of them, `y`, has
`ℓ(y) - ℓ(x₁) ≥ C_χ / 4`. If `u(y) ≠ u(x₁)` the edge `(x₁, y)` is sensitive. Otherwise `y ∈ 𝒢`,
the pair `{x₁, y}` is biconnected in `𝒢` and lies in a block `B₀`; the terms of the outgoing flux
of `x₁` into `B₀` are `≥ 0` since `ℓ ≥ ℓ(x₁)` on `𝒢`, and the term of `y` is at least `C_χ / 4`.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5 Classical

namespace Rigidity.Proofs.Section5

/-- Step 2, choice of the root (L2496, corrected): either `x₁` carries a sensitive edge, or a
block of `𝒢` containing `x₁` receives from `x₁` an outgoing flux at least `C_χ / 4`. -/
theorem rootBlockStep : RootBlockStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj hu Cχ hCχ hgap
  set N := (componentGraph C).neighborFinset x₁ with hN
  have hharm : ∑ y ∈ N, (ℓ y - ℓ x₁) = 0 := hℓ.1.1 x₁
  have hx₀N : x₀ ∈ N := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj.symm
  -- the flux to the neighbours with `ℓ ≤ ℓ(x₁)` is at most the term of `x₀`
  have hneg : ∑ y ∈ N with ¬ ℓ x₁ < ℓ y, (ℓ y - ℓ x₁) ≤ ℓ x₀ - ℓ x₁ := by
    have hx₀mem : x₀ ∈ N.filter fun y => ¬ ℓ x₁ < ℓ y :=
      Finset.mem_filter.2 ⟨hx₀N, by linarith⟩
    rw [← Finset.add_sum_erase _ _ hx₀mem]
    have hrest : ∑ y ∈ (N.filter fun y => ¬ ℓ x₁ < ℓ y).erase x₀, (ℓ y - ℓ x₁) ≤ 0 :=
      Finset.sum_nonpos fun y hy => by
        have := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hy)).2
        linarith [not_lt.1 this]
    linarith
  have hpos : Cχ ≤ ∑ y ∈ N with ℓ x₁ < ℓ y, (ℓ y - ℓ x₁) := by
    have := Finset.sum_filter_add_sum_filter_not N (fun y => ℓ x₁ < ℓ y) (fun y => ℓ y - ℓ x₁)
    linarith
  -- pigeonhole over the at most four neighbours of `x₁`
  obtain ⟨y, hyN, hy⟩ : ∃ y ∈ N.filter fun y => ℓ x₁ < ℓ y, Cχ / 4 ≤ ℓ y - ℓ x₁ := by
    by_contra! hlt
    have hcard : ((N.filter fun y => ℓ x₁ < ℓ y).card : ℝ) ≤ 4 := by
      have h1 := Finset.card_filter_le N (fun y => ℓ x₁ < ℓ y)
      have h2 : N.card ≤ 2 * 2 := by
        rw [hN, SimpleGraph.card_neighborFinset_eq_degree]
        exact componentGraph_degree_le C x₁
      exact_mod_cast h1.trans h2
    rcases (N.filter fun y => ℓ x₁ < ℓ y).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty] at hpos
      linarith
    · have := Finset.sum_lt_sum_of_nonempty hne hlt
      rw [Finset.sum_const, nsmul_eq_mul] at this
      nlinarith
  obtain ⟨hyN', hxy⟩ := Finset.mem_filter.1 hyN
  have hx₁y : (componentGraph C).Adj x₁ y := (SimpleGraph.mem_neighborFinset _ _ _).1 hyN'
  by_cases huy : u y = u x₀
  · right
    have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
    have hyV := mem_explorationSet_of_adj hx₁V hx₁y huy hxy
    obtain ⟨B, hB, hsub⟩ := exists_isBlock_superset
      (biconnectedIn_pair (G := explorationGraph C u ℓ x₀ x₁) hx₁V hyV ⟨hx₁V, hyV, hx₁y, hxy.ne⟩)
    refine ⟨⟨B, hB⟩, hsub (Set.mem_insert _ _), ?_⟩
    have hymem : y ∈ N.filter (· ∈ B) :=
      Finset.mem_filter.2 ⟨hyN', hsub (Set.mem_insert_of_mem _ rfl)⟩
    refine hy.trans (Finset.single_le_sum (f := fun w => ℓ w - ℓ x₁) (fun w hw => ?_) hymem)
    have hwV := hB.1.1 (Finset.mem_filter.1 hw).2
    linarith [le_of_mem_explorationSet C hwV]
  · left
    exact ⟨y, hx₁y, hxy.ne, fun h => huy (h.symm.trans hu)⟩

end Rigidity.Proofs.Section5
