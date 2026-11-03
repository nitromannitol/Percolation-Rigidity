import Rigidity.Steps.Section5.LargeGradientSensitive
import Rigidity.Proofs.Section5.InfiniteBranches

/-! # Lemma 5.27, Step 2: the leaves of `𝒢_tree` carry a sensitive edge

Proof of `LeafSensitiveStep` (step:5.27-tree, corrected draft L2498-2500) of the carving
`Rigidity/Steps/Section5/LargeGradientSensitive.lean`.

Block-cut tree of `(𝒢, G)`, rooted at the block `B₀ ∋ x₁`:
* it is connected (`blockCutTree_reachable`): an edge of `𝒢` lies in a block, and two vertices of
  the tree carrying a common point are joined through it;
* a block `B` has at most one parent (`eq_of_parent`): a path from the root to a cut-vertex of `B`
  avoiding `B` extends to a path from the root to `B`, and the tree is acyclic;
* a cut-vertex of a kept, non-pruning block `B` which is not its parent is a child of `B` in
  `𝒢_tree` (`isTreeChild_or_parent`).

Proof. A pruning block carries a sensitive edge by definition (`u = a` on `𝒢`). Otherwise let `z`
be a maximum of `ℓ` on the finite block `B`. Every point of `𝒢` has a neighbour with a smaller value
of `ℓ` (`x₀` for `x₁`, the previous point of an increasing path otherwise), so by harmonicity `z`
has a neighbour `p` with `ℓ(p) > ℓ(z)`. If `u(p) ≠ a`, `(z, p)` is sensitive. Otherwise
`p ∈ 𝒢 \ B`, so `z` is a cut-vertex of `B`, hence its parent since `B` has no child in `𝒢_tree`,
and `B ≠ B₀`. Then `z` is the only cut-vertex of `B`: an increasing path of `𝒢` enters `B` only
through `z` (`x₁ ∈ B₀ ∩ B` would be a second cut-vertex), so `ℓ > ℓ(z)` on `B \ {z}`, which is
nonempty since `z` lies in a second block. This contradicts the maximality of `z`.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

section Tree

variable {ω : Configuration 2} {C : OpenComponent ω} {G : SimpleGraph C} {V : Set C}

/-- A walk of `G` inside `V` from a point carried by `a` to a point carried by `b` gives a walk of
the block-cut tree from `a` to `b`. -/
theorem blockCutTree_reachable_of_walk {p q : C} (π : G.Walk p q) :
    (∀ v ∈ π.support, v ∈ V) → ∀ {a b : BlockCutVertex C G V}, p ∈ blockCutCarrier C a →
      q ∈ blockCutCarrier C b → (blockCutTree C G V).Reachable a b := by
  induction π with
  | nil =>
    intro _ a b ha hb
    obtain ⟨Q, -⟩ := exists_walk_of_mem_blockCutCarrier ha hb
    exact ⟨Q⟩
  | @cons x y z h π ih =>
    intro hπ a b ha hb
    have hx : x ∈ V := hπ x (by simp)
    have hy : y ∈ V := hπ y (by simp)
    obtain ⟨B, hB, hsub⟩ := exists_isBlock_superset (biconnectedIn_pair hx hy h)
    obtain ⟨Q, -⟩ := exists_walk_of_mem_blockCutCarrier (b := .inl ⟨B, hB⟩) ha
      (hsub (Set.mem_insert _ _))
    exact SimpleGraph.Reachable.trans ⟨Q⟩
      (ih (fun v hv => hπ v (by simp [hv])) (hsub (Set.mem_insert_of_mem _ rfl)) hb)

/-- The block-cut tree of a connected `(V, G)` is connected. -/
theorem blockCutTree_reachable (hV : ConnectedIn C G V) {a b : BlockCutVertex C G V} {p q : C}
    (hp : p ∈ blockCutCarrier C a) (hq : q ∈ blockCutCarrier C b) :
    (blockCutTree C G V).Reachable a b := by
  obtain ⟨π, hπ⟩ := connectedIn_iff.1 hV p (blockCutCarrier_subset a hp) q
    (blockCutCarrier_subset b hq)
  exact blockCutTree_reachable_of_walk π hπ hp hq

/-- A block has at most one parent: paths from the root `r` to cut-vertices `c, c'` of `B`
avoiding `B` extend to paths from `r` to `B`, which coincide. -/
theorem eq_of_parent {r : BlockCutVertex C G V} {B : {S // IsBlock C G V S}}
    {c c' : {x // IsCutVertex C G V x}} (W : (blockCutTree C G V).Walk r (.inr c))
    (hW : W.IsPath) (hBW : Sum.inl B ∉ W.support) (hc : c.val ∈ B.val)
    (W' : (blockCutTree C G V).Walk r (.inr c')) (hW' : W'.IsPath)
    (hBW' : Sum.inl B ∉ W'.support) (hc' : c'.val ∈ B.val) : c = c' := by
  have h : (blockCutTree C G V).Adj (.inr c) (.inl B) := hc
  have h' : (blockCutTree C G V).Adj (.inr c') (.inl B) := hc'
  have hP : (W.concat h).IsPath := (SimpleGraph.Walk.concat_isPath_iff h).2 ⟨hW, hBW⟩
  have hP' : (W'.concat h').IsPath := (SimpleGraph.Walk.concat_isPath_iff h').2 ⟨hW', hBW'⟩
  have heq := congrArg (fun P : (blockCutTree C G V).Path r (.inl B) => P.1.penultimate)
    (blockCutTree_isAcyclic.path_unique ⟨_, hP⟩ ⟨_, hP'⟩)
  simp only [SimpleGraph.Walk.penultimate_concat] at heq
  exact Sum.inr_injective heq

end Tree

section Exploration

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- Every point of `𝒢` has a neighbour with a smaller value of `ℓ`: `x₀` for `x₁`, the previous
point of an increasing path otherwise. -/
theorem exists_adj_lt_of_mem_explorationSet (hadj : (componentGraph C).Adj x₀ x₁)
    (hlt : ℓ x₀ < ℓ x₁) :
    ∀ y ∈ explorationSet C u ℓ x₀ x₁, ∃ w, (componentGraph C).Adj y w ∧ ℓ w < ℓ y :=
  explorationSet_induction ⟨x₀, hadj.symm, hlt⟩ fun y _ _ _ hyy' hlt' _ => ⟨y, hyy'.symm, hlt'⟩

/-- A cut-vertex `c` of a kept, non-pruning block `B` is a child of `B` in `𝒢_tree`, unless a path
from the root to `c` avoids `B` (`c` is the parent of `B`). -/
theorem isTreeChild_or_parent {B₀ B : ExplorationBlock C u ℓ x₀ x₁}
    (hx₁V : x₁ ∈ explorationSet C u ℓ x₀ x₁) (hx₁B₀ : x₁ ∈ B₀.val)
    (hBk : Sum.inl B ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀))
    (hBp : ¬ IsPruningBlock C u ℓ (u x₀) B.val) (c : ExplorationCut C u ℓ x₀ x₁)
    (hc : c.val ∈ B.val) :
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inl B) (.inr c) ∨
      ∃ W : (blockCutTree C _ _).Walk (.inl B₀) (.inr c), W.IsPath ∧ Sum.inl B ∉ W.support := by
  obtain ⟨P0⟩ := blockCutTree_reachable (connectedIn_explorationSet hx₁V)
    (a := .inl B₀) (b := .inl B) hx₁B₀ hc
  have hP : P0.bypass.IsPath := P0.bypass_isPath
  have hBc : (blockCutTree C _ _).Adj (.inl B) (.inr c) := hc
  by_cases hcP : Sum.inr c ∈ P0.bypass.support
  · exact .inr ⟨_, hP.takeUntil hcP,
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil hP hcP Sum.inl_ne_inr⟩
  · left
    have hQ : (P0.bypass.concat hBc).IsPath := (SimpleGraph.Walk.concat_isPath_iff hBc).2 ⟨hP, hcP⟩
    refine ⟨hBk, ?_, hBc, isStrictAncestor_of_mem _ hQ (by simp [SimpleGraph.Walk.support_concat])
      Sum.inl_ne_inr⟩
    show ¬ _
    rintro ⟨A, hA, -, hAall⟩
    have hAm := hAall _ hQ
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hAm
    rcases hAm with hAm | hAm
    · by_cases hAB : (Sum.inl A : BlockCutVertex C _ _) = .inl B
      · exact hBp (Sum.inl_injective hAB ▸ hA)
      · exact hBk ⟨A, hA, isStrictAncestor_of_mem _ hP hAm hAB⟩
    · exact Sum.inl_ne_inr hAm

end Exploration

/-- step:5.27-tree (L2498-2500): a finite kept block which prunes or has no child in `𝒢_tree`
carries a sensitive edge. -/
theorem leafSensitiveStep : LeafSensitiveStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj hlt hu B₀ hx₁B₀ B hBk hBfin hcase
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  have hVc := connectedIn_explorationSet hx₁V
  -- a pruning block carries a sensitive edge
  by_cases hBp : IsPruningBlock C u ℓ (u x₀) B.val
  · obtain ⟨y, hyB, z, hzy, hz, hℓzy⟩ := hBp
    have hyu : u y = u x₀ := levelSet_of_mem_explorationSet (B.2.1.1 hyB)
    exact ⟨y, hyB, z, hzy.symm, fun h => hℓzy h.symm, fun h => hz (h.symm.trans hyu)⟩
  have hnochild := hcase.resolve_left hBp
  -- every cut-vertex of `B` is its parent, which is unique
  have hpar : ∀ c : ExplorationCut C u ℓ x₀ x₁, c.val ∈ B.val →
      ∃ W : (blockCutTree C _ _).Walk (.inl B₀) (.inr c), W.IsPath ∧ Sum.inl B ∉ W.support :=
    fun c hc => (isTreeChild_or_parent hx₁V hx₁B₀ hBk hBp c hc).resolve_left (hnochild c)
  have hcut : ∀ c c' : ExplorationCut C u ℓ x₀ x₁, c.val ∈ B.val → c'.val ∈ B.val → c = c' := by
    intro c c' hc hc'
    obtain ⟨W, hW, hBW⟩ := hpar c hc
    obtain ⟨W', hW', hBW'⟩ := hpar c' hc'
    exact eq_of_parent W hW hBW hc W' hW' hBW' hc'
  -- `B` is nonempty, by maximality against `{x₁}`
  have hBne : B.val.Nonempty := by
    by_contra hBe
    rw [Set.not_nonempty_iff_eq_empty] at hBe
    have hbi : BiconnectedIn C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)
        {x₁} :=
      ⟨Set.singleton_subset_iff.2 hx₁V,
        connectedIn_of_reachIn (z := x₁) fun x hx => by
          rw [Set.mem_singleton_iff.1 hx]
          exact .refl rfl,
        fun x hx => connectedIn_of_reachIn (z := x₁) fun y hy =>
          (hy.2 ((Set.mem_singleton_iff.1 hy.1).trans (Set.mem_singleton_iff.1 hx).symm)).elim⟩
    have := B.2.2 {x₁} hbi (hBe ▸ Set.empty_subset _)
    rw [hBe] at this
    exact Set.singleton_ne_empty x₁ this
  -- the maximum `z` of `ℓ` on `B` has a neighbour `p` with `ℓ(p) > ℓ(z)`
  obtain ⟨z, hzB, hzmax⟩ := Set.exists_max_image B.val ℓ hBfin hBne
  have hzV := B.2.1.1 hzB
  have hzu : u z = u x₀ := levelSet_of_mem_explorationSet hzV
  obtain ⟨w, hzw, hwz⟩ := exists_adj_lt_of_mem_explorationSet hadj hlt z hzV
  obtain ⟨⟨p, hzp, hzp'⟩, -⟩ :=
    exists_above_below_of_harmonic (u := ℓ) (hℓ.1.1 z) rfl hzw hwz.ne
  by_cases hpu : u p = u x₀
  swap
  · exact ⟨z, hzB, p, hzp, hzp'.ne, fun h => hpu (h.symm.trans hzu)⟩
  -- otherwise `z` is a cut-vertex of `B`, its parent
  exfalso
  have hpV := mem_explorationSet_of_adj hzV hzp hpu hzp'
  have hpB : p ∉ B.val := fun h => absurd (hzmax p h) (not_le.2 hzp')
  have hzcut := IsBlock.isCutVertex_of_adj B.2 hzB hpV hpB ⟨hzV, hpV, hzp, hzp'.ne⟩
  obtain ⟨W, -, hBW⟩ := hpar ⟨z, hzcut⟩ hzB
  have hBB₀ : B ≠ B₀ := by
    rintro rfl
    exact hBW W.start_mem_support
  have honly : ∀ y ∈ B.val, IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁) y → y = z :=
    fun y hy hcy => congrArg Subtype.val (hcut ⟨y, hcy⟩ ⟨z, hzcut⟩ hy hzB)
  -- `ℓ > ℓ(z)` on `B \ {z}`
  have hmin : ∀ y ∈ explorationSet C u ℓ x₀ x₁, y ∈ B.val → y ≠ z → ℓ z < ℓ y := by
    refine explorationSet_induction ?_ ?_
    · intro hx₁B hx₁z
      exact absurd (honly x₁ hx₁B (IsBlock.isCutVertex B.2 B₀.2
        (fun h => hBB₀ (Subtype.ext h)) hx₁B hx₁B₀)) hx₁z
    · intro y y' hy hy' hyy' hlt' ih hy'B hy'z
      by_cases hyB : y ∈ B.val
      · by_cases hyz : y = z
        · rw [← hyz]
          exact hlt'
        · exact (ih hyB hyz).trans hlt'
      · exact absurd (honly y' hy'B (IsBlock.isCutVertex_of_adj B.2 hy'B hy hyB
          ⟨hy', hy, hyy'.symm, hlt'.ne'⟩)) hy'z
  -- `B` has a point other than `z`, since `z` lies in a second block
  obtain ⟨B', hB', hzB', hB'B⟩ := exists_isBlock_ne hVc hzcut B.2
  obtain ⟨w', hw'B, hw'z⟩ := IsBlock.exists_ne_of_ne B.2 hB' (Ne.symm hB'B) hzB hzB'
  exact absurd (hzmax w' hw'B) (not_le.2 (hmin w' (B.2.1.1 hw'B) hw'B hw'z))

end Rigidity.Proofs.Section5
