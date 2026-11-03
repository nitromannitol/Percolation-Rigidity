import Rigidity.Proofs.Section5.LeafSensitive
import Rigidity.Proofs.Section5.ExplorationBlocks

/-! # Lemma 5.27, Step 4 (ii): growth of the corrected plane across a kept block

Proof of `FluxGrowthStep` (step:5.27-regularity (ii), eq. `increasevaluefluxcorr`, corrected draft
L2542-2561). Let `B` be a kept block with parent `x_cut,0` (or the root `B₀ ∋ x₁`, with `x₁` in
place of `x_cut,0`) and `x_cut,1 ∈ B` a child cut-vertex.

* `ℓ ≥ ℓ(x_cut,0)` on `B`. A walk of `𝒢` from `x₁` to `y ∈ B` avoiding `x_cut,0` gives a walk of
  the block-cut tree from `B₀` to `B` avoiding `x_cut,0` (`exists_blockCutWalk_avoiding`), against
  `x_cut,0` being a strict ancestor of `B`. So `x_cut,0` separates `x₁` from `y`, and every
  increasing path of `𝒢` from `x₁` to `y` passes through `x_cut,0` (`le_of_not_reachIn`). For the
  root, `ℓ ≥ ℓ(x₁)` on `𝒢`.
* Each term `ℓ(x_cut,1) - ℓ(y)` of `i_in(x_cut,1)` is then at most `ℓ(x_cut,1) - ℓ(x_cut,0) ≥ 0`,
  and `x_cut,1` has at most four neighbours, so `i_in(x_cut,1) ≤ 4 (ℓ(x_cut,1) - ℓ(x_cut,0))`.

The printed argument picks a neighbour `y` with `ℓ(x_cut,1) - ℓ(y) ≥ i_in(x_cut,1) / 4`; this
pigeonhole needs `i_in(x_cut,1) ≥ 0` when `x_cut,1` has fewer than four neighbours in `B`. The
bound above avoids it. No literature input is used.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

section Tree

variable {ω : Configuration 2} {C : OpenComponent ω} {G : SimpleGraph C} {V : Set C}

/-- A walk of `G` inside `V \ {x}` from a point carried by `a` to a point carried by `b` gives a
walk of the block-cut tree from `a` to `b` through no cut-vertex `x`. -/
theorem exists_blockCutWalk_avoiding {x p q : C} (π : G.Walk p q) :
    (∀ v ∈ π.support, v ∈ V ∧ v ≠ x) → ∀ {a b : BlockCutVertex C G V},
      p ∈ blockCutCarrier C a → q ∈ blockCutCarrier C b →
      ∃ Q : (blockCutTree C G V).Walk a b,
        ∀ c : {y // IsCutVertex C G V y}, Sum.inr c ∈ Q.support → c.val ≠ x := by
  induction π with
  | nil =>
    rename_i p
    intro hπ a b ha hb
    have hpx : p ≠ x := (hπ p (by simp)).2
    obtain ⟨Q, hQ⟩ := exists_walk_of_mem_blockCutCarrier ha hb
    refine ⟨Q, fun c hc => ?_⟩
    rcases hQ _ hc with h | h | ⟨_, h⟩
    · rw [← h] at ha
      exact fun hcx => hpx ((show p = c.val from ha).trans hcx)
    · rw [← h] at hb
      exact fun hcx => hpx ((show p = c.val from hb).trans hcx)
    · rw [show c.val = p from congrArg Subtype.val (Sum.inr_injective h)]
      exact hpx
  | @cons y z q h π ih =>
    intro hπ a b ha hb
    have hy := hπ y (by simp)
    have hz := hπ z (by simp)
    obtain ⟨B, hB, hsub⟩ := exists_isBlock_superset (biconnectedIn_pair hy.1 hz.1 h)
    obtain ⟨Q₁, hQ₁⟩ := exists_walk_of_mem_blockCutCarrier (b := .inl ⟨B, hB⟩) ha
      (hsub (Set.mem_insert _ _))
    obtain ⟨Q₂, hQ₂⟩ := ih (fun v hv => hπ v (by simp [hv])) (a := .inl ⟨B, hB⟩)
      (hsub (Set.mem_insert_of_mem _ rfl)) hb
    refine ⟨Q₁.append Q₂, fun c hc => ?_⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff Q₁ Q₂).1 hc with hc | hc
    · rcases hQ₁ _ hc with h' | h' | ⟨_, h'⟩
      · rw [← h'] at ha
        exact fun hcx => hy.2 ((show y = c.val from ha).trans hcx)
      · exact absurd h' Sum.inr_ne_inl
      · rw [show c.val = y from congrArg Subtype.val (Sum.inr_injective h')]
        exact hy.2
    · exact hQ₂ c hc

/-- A cut-vertex `c` which is a strict ancestor of a block `B` in the block-cut tree rooted at a
block `B₀ ∋ s` separates `s` from `B`. -/
theorem not_reachIn_of_isStrictAncestor {B₀ B : {S // IsBlock C G V S}}
    {c : {y // IsCutVertex C G V y}}
    (hc : IsStrictAncestor (blockCutTree C G V) (.inl B₀) (.inr c) (.inl B)) {s y : C}
    (hs : s ∈ B₀.val) (hy : y ∈ B.val) : ¬ GraphReachIn G (V \ {c.val}) s y := by
  classical
  rintro ⟨π, hπ⟩
  obtain ⟨Q, hQ⟩ := exists_blockCutWalk_avoiding π (fun v hv => ⟨(hπ v hv).1, (hπ v hv).2⟩)
    (a := .inl B₀) (b := .inl B) hs hy
  exact hQ c (Q.support_bypass_subset_support (hc.2 Q.bypass Q.bypass_isPath)) rfl

end Tree

section Exploration

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- `ℓ(c) ≤ ℓ(y)` at every point `y` of `𝒢` separated from `x₁` by `c`: the increasing paths of
`𝒢` from `x₁` to `y` pass through `c`. -/
theorem le_of_not_reachIn (hx₁ : x₁ ∈ explorationSet C u ℓ x₀ x₁) {c : C} :
    ∀ y ∈ explorationSet C u ℓ x₀ x₁, (y = c ∨ ¬ GraphReachIn (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁ \ {c}) x₁ y) → ℓ c ≤ ℓ y := by
  refine explorationSet_induction ?_ ?_
  · rintro (h | h)
    · rw [h]
    · by_cases hx : x₁ = c
      · rw [hx]
      · exact (h (.refl ⟨hx₁, hx⟩)).elim
  · intro y y' hy hy' hyy' hlt ih h'
    by_cases hy'c : y' = c
    · rw [hy'c]
    have hnr := h'.resolve_left hy'c
    by_cases hyc : y = c
    · rw [← hyc]
      exact hlt.le
    refine (ih (.inr fun hr => hnr (hr.trans ?_))).trans hlt.le
    exact GraphReachIn.of_adj ⟨hy, hyc⟩ ⟨hy', hy'c⟩ ⟨hy, hy', hyy', hlt.ne⟩

/-- If `m ≤ ℓ` on `B` and `c ∈ B`, then `m + i_in(c) / 4 ≤ ℓ(c)`: each term of `i_in(c)` is at
most `ℓ(c) - m ≥ 0`, and `c` has at most four neighbours. -/
theorem add_incomingFlux_div_four_le {B : Set C} {m : ℝ} (hm : ∀ y ∈ B, m ≤ ℓ y) {c : C}
    (hc : c ∈ B) : m + incomingFlux C ℓ B c / 4 ≤ ℓ c := by
  classical
  have h0 : 0 ≤ ℓ c - m := by linarith [hm c hc]
  have hle : incomingFlux C ℓ B c ≤
      ((componentGraph C).neighborFinset c).card * (ℓ c - m) := by
    unfold incomingFlux
    calc _ ≤ ∑ y ∈ (componentGraph C).neighborFinset c with y ∈ B, (ℓ c - m) :=
          Finset.sum_le_sum fun y hy => by linarith [hm y (Finset.mem_filter.1 hy).2]
      _ ≤ ∑ y ∈ (componentGraph C).neighborFinset c, (ℓ c - m) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => h0
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hdeg : (((componentGraph C).neighborFinset c).card : ℝ) ≤ 4 := by
    have h := componentGraph_degree_le C c
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast h
  have h4 := mul_le_mul_of_nonneg_right hdeg h0
  linarith

end Exploration

/-- step:5.27-regularity (ii) (L2542-2561, eq. `increasevaluefluxcorr`): across a kept block, from
its parent cut-vertex (or from `x₁` for the root) to a child cut-vertex `x_cut,1`, `ℓ` increases
by at least `i_in(x_cut,1) / 4`. -/
theorem fluxGrowthStep : FluxGrowthStep := by
  intro ω C u ℓ x₀ x₁ hadj _ hu B₀ hx₁B₀
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  refine ⟨fun c hc => ?_, fun B c₀ c₁ hc₀ hc₁ => ?_⟩
  · exact add_incomingFlux_div_four_le (fun y hy => le_of_mem_explorationSet _ (B₀.2.1.1 hy))
      hc.2.2.1
  · refine add_incomingFlux_div_four_le (fun y hy => ?_) hc₁.2.2.1
    exact le_of_not_reachIn hx₁V y (B.2.1.1 hy)
      (.inr (not_reachIn_of_isStrictAncestor hc₀.2.2.2 hx₁B₀ hy))

end Rigidity.Proofs.Section5
