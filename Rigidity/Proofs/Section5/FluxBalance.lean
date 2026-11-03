import Rigidity.Proofs.Section5.LeafSensitive

/-! # Lemma 5.27, Step 3: flux of the corrected plane through the block-cut tree

Proof of `FluxBalanceStep` (step:5.27-flux, eqs. `fluxincreasesthroughbiconnectedcomponents`,
`fluxincreasesthroughbiconnectedcomponents2`, corrected draft L2503-2540). Write `∇ℓ(a, b)` for
`ℓ(b) - ℓ(a)` on an edge of `𝒞_∞` (`edgeFlux`, `0` off the edges).

* Blocks (eqs. `flux0`, `flux1`, `flux2`). Let `B` be a finite non-pruning block, `p ∈ B` (the
  parent cut-vertex, or `x₁` for the root), `K = {p} ∪ {cut-vertices of B}` and `X = B \ K`. For
  `y ∈ X` and `z ∼ y` outside `B`, `ℓ(z) ≤ ℓ(y)`: if `u(z) = a` and `ℓ(z) > ℓ(y)` then `z ∈ 𝒢`
  and `y` would be a cut-vertex (`IsBlock.isCutVertex_of_adj`); if `u(z) ≠ a` and `ℓ(z) ≠ ℓ(y)`
  then `B` would prune. Summing `Δℓ = 0` over `X`, the sums of `∇ℓ` over `X × X` and `K × K`
  vanish (antisymmetry), so `Σ_{y ∈ X, c ∈ K} ∇ℓ(y, c) ≥ 0`, which is the difference of the two
  sides of eq. `fluxincreasesthroughbiconnectedcomponents` (`outgoingFlux_le_sum_incomingFlux`).
* Cut-vertices (eq. `fluxincreasesthroughbiconnectedcomponents2`). Let `c` be a kept cut-vertex
  with parent `P`; `P` does not prune. By `Δℓ(c) = 0`, `i_in(c)` is the sum of `∇ℓ(c, z)` over
  the neighbours `z ∉ P`. A neighbour `z` with `ℓ(z) > ℓ(c)` lies in `𝒢` (else `P` prunes), so the
  edge `(c, z)` lies in a block `≠ P` through `c`, which is a child of `c` in `𝒢_tree`
  (`isTreeChild_of_mem`: the path of the block-cut tree from the root to `c` ends with `P`). The
  other terms are `≤ 0`, and a neighbour of `c` lies in at most one block through `c`, so the
  remaining sum is `Σ_B i_out(c, B)` over the children `B` of `c` (`incomingFlux_le_finsum`).

No literature input is used.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-- A double sum of an antisymmetric weight over `S × S` vanishes. -/
theorem sum_sum_eq_zero_of_antisymm {α : Type*} (S : Finset α) (w : α → α → ℝ)
    (hw : ∀ a b, w a b = -w b a) : ∑ a ∈ S, ∑ b ∈ S, w a b = 0 := by
  have h : ∑ a ∈ S, ∑ b ∈ S, w a b = -∑ a ∈ S, ∑ b ∈ S, w a b := by
    calc ∑ a ∈ S, ∑ b ∈ S, w a b = ∑ a ∈ S, ∑ b ∈ S, -w b a :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hw a b
      _ = -∑ b ∈ S, ∑ a ∈ S, w b a := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_neg_distrib]
  linarith

section Tree

variable {ω : Configuration 2} {C : OpenComponent ω} {G : SimpleGraph C} {V : Set C}

/-- In a path `W` of the block-cut tree from `r` to `v`, a vertex of `W` adjacent to `v` is the
penultimate vertex of `W`. -/
theorem penultimate_eq_of_mem {r v a : BlockCutVertex C G V} (W : (blockCutTree C G V).Walk r v)
    (hW : W.IsPath) (ha : a ∈ W.support) (hav : (blockCutTree C G V).Adj a v) :
    W.penultimate = a := by
  classical
  have hP : ((W.takeUntil a ha).concat hav).IsPath :=
    (SimpleGraph.Walk.concat_isPath_iff hav).2 ⟨hW.takeUntil ha,
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil hW ha hav.ne.symm⟩
  have heq := congrArg (fun P : (blockCutTree C G V).Path r v => P.1.penultimate)
    (blockCutTree_isAcyclic.path_unique ⟨W, hW⟩ ⟨_, hP⟩)
  simpa only [SimpleGraph.Walk.penultimate_concat] using heq

end Tree

section Exploration

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- A block through a kept cut-vertex `c`, other than the parent `P` of `c`, is a child of `c` in
`𝒢_tree`: the path of the block-cut tree from the root to `c` ends with `P`, and extends to the
block through `c`. -/
theorem isTreeChild_of_mem {B₀ P B : ExplorationBlock C u ℓ x₀ x₁}
    {c : ExplorationCut C u ℓ x₀ x₁} (hx₁V : x₁ ∈ explorationSet C u ℓ x₀ x₁)
    (hx₁B₀ : x₁ ∈ B₀.val) (hPc : IsTreeChild C u ℓ x₀ x₁ B₀ (.inl P) (.inr c))
    (hcB : c.val ∈ B.val) (hBP : B ≠ P) : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B) := by
  classical
  obtain ⟨W0⟩ := blockCutTree_reachable (connectedIn_explorationSet hx₁V) (a := .inl B₀)
    (b := .inr c) hx₁B₀ (show c.val ∈ blockCutCarrier C (Sum.inr c) from rfl)
  have hW : W0.bypass.IsPath := W0.bypass_isPath
  have hPW : Sum.inl P ∈ W0.bypass.support := hPc.2.2.2.2 _ hW
  have hPc' : (blockCutTree C _ _).Adj (.inl P) (.inr c) := hPc.2.2.1
  have hBc : (blockCutTree C _ _).Adj (.inl B) (.inr c) := hcB
  have hBW : Sum.inl B ∉ W0.bypass.support := fun h => hBP (Sum.inl_injective
    ((penultimate_eq_of_mem _ hW h hBc).symm.trans (penultimate_eq_of_mem _ hW hPW hPc')))
  have hQ : (W0.bypass.concat hBc.symm).IsPath :=
    (SimpleGraph.Walk.concat_isPath_iff hBc.symm).2 ⟨hW, hBW⟩
  refine ⟨hPc.2.1, ?_, hBc.symm, isStrictAncestor_of_mem _ hQ
    (by simp [SimpleGraph.Walk.support_concat]) Sum.inr_ne_inl⟩
  show ¬ _
  rintro ⟨A, hA, hAst⟩
  have hAm := hAst.2 _ hQ
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hAm
  rcases hAm with hAm | hAm
  · exact hPc.2.1 ⟨A, hA, isStrictAncestor_of_mem _ hW hAm Sum.inl_ne_inr⟩
  · exact hAst.1 hAm

/-- A child block of a cut-vertex `c` is not the parent of `c`. -/
theorem ne_of_isTreeChild {B₀ P B : ExplorationBlock C u ℓ x₀ x₁}
    {c : ExplorationCut C u ℓ x₀ x₁} (hx₁V : x₁ ∈ explorationSet C u ℓ x₀ x₁)
    (hx₁B₀ : x₁ ∈ B₀.val) (hPc : IsTreeChild C u ℓ x₀ x₁ B₀ (.inl P) (.inr c))
    (hcB : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)) : B ≠ P := by
  classical
  rintro rfl
  obtain ⟨W0⟩ := blockCutTree_reachable (connectedIn_explorationSet hx₁V) (a := .inl B₀)
    (b := .inr c) hx₁B₀ (show c.val ∈ blockCutCarrier C (Sum.inr c) from rfl)
  have hW : W0.bypass.IsPath := W0.bypass_isPath
  have hBW := hPc.2.2.2.2 _ hW
  exact SimpleGraph.Walk.endpoint_notMem_support_takeUntil hW hBW Sum.inr_ne_inl
    (hcB.2.2.2.2 _ (hW.takeUntil hBW))

variable (C) in
/-- The flux `∇ℓ(a, b) = ℓ(b) - ℓ(a)` of `ℓ` along an edge of `𝒞_∞`, and `0` off the edges. -/
noncomputable def edgeFlux (ℓ : C → ℝ) (a b : C) : ℝ :=
  open Classical in if (componentGraph C).Adj a b then ℓ b - ℓ a else 0

theorem edgeFlux_antisymm (a b : C) : edgeFlux C ℓ a b = -edgeFlux C ℓ b a := by
  unfold edgeFlux
  by_cases h : (componentGraph C).Adj a b
  · rw [if_pos h, if_pos h.symm]
    ring
  · rw [if_neg h, if_neg fun h' => h h'.symm, neg_zero]

open Classical in
theorem outgoingFlux_eq_sum {B : Set C} (hB : B.Finite) (c : C) :
    outgoingFlux C ℓ c B = ∑ y ∈ hB.toFinset, edgeFlux C ℓ c y := by
  unfold outgoingFlux edgeFlux
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext y
  simp [SimpleGraph.mem_neighborFinset, and_comm]

theorem incomingFlux_eq_neg (B : Set C) (c : C) :
    incomingFlux C ℓ B c = -outgoingFlux C ℓ c B := by
  unfold incomingFlux outgoingFlux
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

open Classical in
/-- Eq. `fluxincreasesthroughbiconnectedcomponents` (L2513-2535): for a finite non-pruning block
`B` and `p ∈ B`, the outgoing flux of `p` into `B` is at most the sum of the incoming fluxes from
`B` of the cut-vertices of `B` other than `p`. -/
theorem outgoingFlux_le_sum_incomingFlux
    (hharm : ∀ x, ∑ y ∈ (componentGraph C).neighborFinset x, (ℓ y - ℓ x) = 0)
    {B : ExplorationBlock C u ℓ x₀ x₁} (hBf : B.val.Finite)
    (hBp : ¬ IsPruningBlock C u ℓ (u x₀) B.val) {p : C} (hp : p ∈ B.val) :
    outgoingFlux C ℓ p B.val ≤ ∑ c ∈ hBf.toFinset with
      (IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) c ∧ c ≠ p),
      incomingFlux C ℓ B.val c := by
  set Bf := hBf.toFinset with hBfdef
  set Q := Bf.filter fun c =>
    IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) c ∧ c ≠ p with hQ
  have hpQ : p ∉ Q := fun h => (Finset.mem_filter.1 h).2.2 rfl
  set K := insert p Q with hK
  have hKB : K ⊆ Bf := Finset.insert_subset (hBf.mem_toFinset.2 hp) (Finset.filter_subset _ _)
  set X := Bf \ K with hX
  have hFo : ∀ c, outgoingFlux C ℓ c B.val = ∑ y ∈ Bf, edgeFlux C ℓ c y :=
    fun c => outgoingFlux_eq_sum hBf c
  have hsplit : ∀ c, ∑ y ∈ Bf, edgeFlux C ℓ c y =
      ∑ y ∈ X, edgeFlux C ℓ c y + ∑ y ∈ K, edgeFlux C ℓ c y :=
    fun c => (Finset.sum_sdiff hKB).symm
  have hKK : ∑ c ∈ K, ∑ y ∈ K, edgeFlux C ℓ c y = 0 :=
    sum_sum_eq_zero_of_antisymm K _ edgeFlux_antisymm
  have hXX : ∑ c ∈ X, ∑ y ∈ X, edgeFlux C ℓ c y = 0 :=
    sum_sum_eq_zero_of_antisymm X _ edgeFlux_antisymm
  have hKX : ∑ c ∈ K, ∑ y ∈ X, edgeFlux C ℓ c y = -∑ y ∈ X, ∑ c ∈ K, edgeFlux C ℓ y c := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => edgeFlux_antisymm c y
  -- the neighbours of `X` outside `B` lie below
  have hEn : ∀ y ∈ X, ∑ z ∈ (componentGraph C).neighborFinset y with z ∉ B.val,
      (ℓ z - ℓ y) ≤ 0 := by
    intro y hy
    obtain ⟨hyBf, hyK⟩ := Finset.mem_sdiff.1 hy
    have hyB : y ∈ B.val := hBf.mem_toFinset.1 hyBf
    have hyV : y ∈ explorationSet C u ℓ x₀ x₁ := B.2.1.1 hyB
    have hyp : y ≠ p := fun h => hyK (h ▸ Finset.mem_insert_self _ _)
    have hyc : ¬ IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) y :=
      fun h => hyK (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hyBf, h, hyp⟩))
    refine Finset.sum_nonpos fun z hz => ?_
    obtain ⟨hzN, hzB⟩ := Finset.mem_filter.1 hz
    have hyz := (SimpleGraph.mem_neighborFinset _ _ _).1 hzN
    by_contra hpos
    have hlt : ℓ y < ℓ z := by linarith [not_le.1 hpos]
    by_cases hzu : u z = u x₀
    · have hzV := mem_explorationSet_of_adj hyV hyz hzu hlt
      exact hyc (IsBlock.isCutVertex_of_adj B.2 hyB hzV hzB ⟨hyV, hzV, hyz, hlt.ne⟩)
    · exact hBp ⟨y, hyB, z, hyz.symm, hzu, hlt.ne'⟩
  -- harmonicity on `X`
  have hE : ∀ y ∈ X, ∑ z ∈ Bf, edgeFlux C ℓ y z =
      -∑ z ∈ (componentGraph C).neighborFinset y with z ∉ B.val, (ℓ z - ℓ y) := by
    intro y _
    have h := hharm y
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun z => z ∈ B.val)] at h
    rw [← hFo]
    unfold outgoingFlux
    linarith
  have hT : 0 ≤ ∑ y ∈ X, ∑ c ∈ K, edgeFlux C ℓ y c := by
    have h1 : ∑ y ∈ X, ∑ z ∈ Bf, edgeFlux C ℓ y z = ∑ y ∈ X, ∑ c ∈ K, edgeFlux C ℓ y c := by
      simp only [hsplit, Finset.sum_add_distrib, hXX, zero_add]
    have h2 : 0 ≤ ∑ y ∈ X, ∑ z ∈ Bf, edgeFlux C ℓ y z := by
      rw [Finset.sum_congr rfl hE, Finset.sum_neg_distrib, neg_nonneg]
      exact Finset.sum_nonpos hEn
    linarith
  have hKsum : ∑ c ∈ K, ∑ y ∈ Bf, edgeFlux C ℓ c y =
      ∑ y ∈ Bf, edgeFlux C ℓ p y + ∑ c ∈ Q, ∑ y ∈ Bf, edgeFlux C ℓ c y :=
    Finset.sum_insert hpQ
  have hKsum' : ∑ c ∈ K, ∑ y ∈ Bf, edgeFlux C ℓ c y =
      -∑ y ∈ X, ∑ c ∈ K, edgeFlux C ℓ y c := by
    simp only [hsplit, Finset.sum_add_distrib, hKK, add_zero]
    exact hKX
  have hRHS : ∑ c ∈ Q, incomingFlux C ℓ B.val c = -∑ c ∈ Q, ∑ y ∈ Bf, edgeFlux C ℓ c y := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [incomingFlux_eq_neg, hFo]
  rw [hRHS, hFo]
  linarith

open Classical in
/-- Eq. `fluxincreasesthroughbiconnectedcomponents2` (L2536-2540): at a kept cut-vertex `c` with
parent `P`, the incoming flux from `P` is at most the sum of the outgoing fluxes into the children
of `c` in `𝒢_tree`. -/
theorem incomingFlux_le_finsum
    (hharm : ∀ x, ∑ y ∈ (componentGraph C).neighborFinset x, (ℓ y - ℓ x) = 0)
    (hx₁V : x₁ ∈ explorationSet C u ℓ x₀ x₁) {B₀ P : ExplorationBlock C u ℓ x₀ x₁}
    (hx₁B₀ : x₁ ∈ B₀.val) {c : ExplorationCut C u ℓ x₀ x₁}
    (hPc : IsTreeChild C u ℓ x₀ x₁ B₀ (.inl P) (.inr c)) :
    incomingFlux C ℓ P.val c.val ≤ ∑ᶠ (B : ExplorationBlock C u ℓ x₀ x₁)
      (_ : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)), outgoingFlux C ℓ c.val B.val := by
  set N := (componentGraph C).neighborFinset c.val with hN
  set D : C → Prop := fun z => ∃ B : ExplorationBlock C u ℓ x₀ x₁,
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B) ∧ z ∈ B.val with hD
  have hcV : c.val ∈ explorationSet C u ℓ x₀ x₁ := c.2.1
  have hcP : c.val ∈ P.val := hPc.2.2.1
  have hPnp : ¬ IsPruningBlock C u ℓ (u x₀) P.val := fun h => hPc.2.1 ⟨P, h, hPc.2.2.2⟩
  have hne : ∀ z ∈ N, z ≠ c.val := fun z hz => ((SimpleGraph.mem_neighborFinset _ _ _).1 hz).ne'
  -- a neighbour of `c` lies in at most one block through `c`
  have huniq : ∀ (B B' : ExplorationBlock C u ℓ x₀ x₁) (z : C), c.val ∈ B.val →
      c.val ∈ B'.val → z ∈ B.val → z ∈ B'.val → z ≠ c.val → B = B' :=
    fun B B' z hcB hcB' hzB hzB' hzc =>
      Subtype.ext (IsBlock.eq_of_mem_two B.2 B'.2 hcB hcB' hzB hzB' (Ne.symm hzc))
  have hDP : ∀ z ∈ N, D z → z ∉ P.val := by
    rintro z hz ⟨B, hB, hzB⟩ hzP
    exact ne_of_isTreeChild hx₁V hx₁B₀ hPc hB (huniq B P z hB.2.2.1 hcP hzB hzP (hne z hz))
  -- `i_in(c)` is the flux of `ℓ` from `c` to its neighbours off `P`
  have h1 : incomingFlux C ℓ P.val c.val = ∑ z ∈ N with z ∉ P.val, (ℓ z - ℓ c.val) := by
    have h := hharm c.val
    rw [← Finset.sum_filter_add_sum_filter_not N (fun z => z ∈ P.val)] at h
    rw [incomingFlux_eq_neg]
    unfold outgoingFlux
    linarith
  -- the neighbours off `P` and off the children of `c` lie below
  have h2 : ∑ z ∈ N with z ∉ P.val, (ℓ z - ℓ c.val) ≤ ∑ z ∈ N with D z, (ℓ z - ℓ c.val) := by
    rw [← Finset.sum_filter_add_sum_filter_not (N.filter fun z => z ∉ P.val) D]
    have hfe : (N.filter fun z => z ∉ P.val).filter D = N.filter D := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hDP z h.1 h.2⟩, h.2⟩⟩
    rw [hfe]
    have hrest : ∑ z ∈ (N.filter fun z => z ∉ P.val).filter (fun z => ¬ D z),
        (ℓ z - ℓ c.val) ≤ 0 := by
      refine Finset.sum_nonpos fun z hz => ?_
      simp only [Finset.mem_filter] at hz
      obtain ⟨⟨hzN, hzP⟩, hzD⟩ := hz
      have hcz := (SimpleGraph.mem_neighborFinset _ _ _).1 hzN
      by_contra hpos
      have hlt : ℓ c.val < ℓ z := by linarith [not_le.1 hpos]
      by_cases hzu : u z = u x₀
      · have hzV := mem_explorationSet_of_adj hcV hcz hzu hlt
        obtain ⟨B', hB', hsub⟩ :=
          exists_isBlock_superset (biconnectedIn_pair hcV hzV
            (show (explorationGraph C u ℓ x₀ x₁).Adj c.val z from ⟨hcV, hzV, hcz, hlt.ne⟩))
        have hcB' : c.val ∈ B' := hsub (Set.mem_insert _ _)
        have hzB' : z ∈ B' := hsub (Set.mem_insert_of_mem _ rfl)
        have hB'P : (⟨B', hB'⟩ : ExplorationBlock C u ℓ x₀ x₁) ≠ P := fun h => hzP (by
          rw [← h]
          exact hzB')
        exact hzD ⟨⟨B', hB'⟩, isTreeChild_of_mem hx₁V hx₁B₀ hPc hcB' hB'P, hzB'⟩
      · exact hPnp ⟨c.val, hcP, z, hcz.symm, hzu, hlt.ne'⟩
    linarith
  -- the flux to the neighbours in the children of `c`, grouped by child
  let β : C → ExplorationBlock C u ℓ x₀ x₁ := fun z => if h : D z then h.choose else P
  have hβ : ∀ z, D z → IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl (β z)) ∧ z ∈ (β z).val :=
    fun z h => by
      simp only [β, dif_pos h]
      exact h.choose_spec
  set F := (N.filter D).image β with hF
  have hFCh : ∀ B ∈ F, IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B) := by
    intro B hB
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hB
    exact (hβ z (Finset.mem_filter.1 hz).2).1
  have hfib : ∀ B ∈ F, ∑ z ∈ N.filter D with β z = B, (ℓ z - ℓ c.val) =
      outgoingFlux C ℓ c.val B.val := by
    intro B hB
    unfold outgoingFlux
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hzN, hzD⟩, rfl⟩
      exact ⟨hzN, (hβ z hzD).2⟩
    · rintro ⟨hzN, hzB⟩
      have hzD : D z := ⟨B, hFCh B hB, hzB⟩
      exact ⟨⟨hzN, hzD⟩, huniq _ _ z (hβ z hzD).1.2.2.1 (hFCh B hB).2.2.1 (hβ z hzD).2 hzB
        (hne z hzN)⟩
  have hsupp : Function.support (fun B : ExplorationBlock C u ℓ x₀ x₁ =>
      ∑ᶠ (_ : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)), outgoingFlux C ℓ c.val B.val) ⊆
      (F : Set (ExplorationBlock C u ℓ x₀ x₁)) := by
    intro B hB
    rw [Function.mem_support, finsum_eq_if] at hB
    by_cases hChB : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)
    · rw [if_pos hChB] at hB
      obtain ⟨z, hz, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hB
      obtain ⟨hzN, hzB⟩ := Finset.mem_filter.1 hz
      have hzD : D z := ⟨B, hChB, hzB⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hzN, hzD⟩,
        huniq _ _ z (hβ z hzD).1.2.2.1 hChB.2.2.1 (hβ z hzD).2 hzB (hne z hzN)⟩)
    · rw [if_neg hChB] at hB
      exact absurd rfl hB
  have h3 : ∑ z ∈ N with D z, (ℓ z - ℓ c.val) = ∑ᶠ (B : ExplorationBlock C u ℓ x₀ x₁)
      (_ : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)), outgoingFlux C ℓ c.val B.val := by
    rw [finsum_eq_sum_of_support_subset _ hsupp,
      ← Finset.sum_fiberwise_of_maps_to (s := N.filter D) (t := F) (g := β)
        (fun z hz => Finset.mem_image_of_mem β hz)]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [hfib B hB, finsum_eq_if, if_pos (hFCh B hB)]
  rw [h1]
  exact h2.trans h3.le

end Exploration

/-- step:5.27-flux (L2503-2540): summing `Δℓ = 0` over a finite non-pruning kept block minus its
cut-vertices, and at a kept cut-vertex. -/
theorem fluxBalanceStep : FluxBalanceStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj _ hu B₀ hx₁B₀
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  have hharm : ∀ x, ∑ y ∈ (componentGraph C).neighborFinset x, (ℓ y - ℓ x) = 0 :=
    fun x => hℓ.1.1 x
  exact ⟨fun hB hBp => outgoingFlux_le_sum_incomingFlux hharm hB hBp hx₁B₀,
    fun B c₀ hc₀ hB hBp => outgoingFlux_le_sum_incomingFlux hharm hB hBp hc₀.2.2.1,
    fun P c hPc => incomingFlux_le_finsum hharm hx₁V hx₁B₀ hPc⟩

end Rigidity.Proofs.Section5
