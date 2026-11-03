import Rigidity.Proofs.Section5.LeafExit

/-!
# Lemma 5.28: the separator `𝒢_f` of three finite leaf branches

This file proves `LeafSeparatorStep` (the set `𝒢_f` of the corrected draft L2698-2699, Lemma
5.28), with the block theory of `Rigidity/Proofs/Section5/LeafExit.lean`.

Let `S₁, S₂, S₃` be distinct finite leaf branches of `𝒢_tree`, with paths `Wᵢ` from the root to
their leaves `vᵢ`, and exits `zᵢ`. The separator `X` is the set of points of `𝒢` carried by a
vertex of some `Wᵢ`, other than `z₁, z₂, z₃`.

* An exit `zᵢ` is carried by no vertex of `𝒢_tree` reachable from the root other than `vᵢ`
  (`eq_leaf_of_mem_prunedCarrier`): a neighbour of `vᵢ` in `𝒢_tree` is on `Wᵢ`, and a second block
  `B'` through `zᵢ` makes `zᵢ` a cut-vertex, so the path of the block-cut tree from the root to `B'`
  would run through `vᵢ` and `zᵢ`, a vertex off `𝒢_tree`.
* The leaves are distinct (paths of `𝒢_tree` are unique), hence no leaf `vⱼ` is on `Wᵢ` for
  `j ≠ i`, and `zⱼ` is carried by no vertex of `Wᵢ`.
* A leaf `vᵢ` is a block `L` (a leaf cut-vertex `zᵢ` lies in its parent block), its parent is a
  cut-vertex `c ∈ L` other than `zᵢ`, so `zᵢ` has a neighbour in `L \ {zᵢ} ⊆ X`.
* Along `Wᵢ` the carriers minus `zᵢ` are connected (a block minus a point is connected),
  consecutive carriers share their cut-vertex, which is not an exit, and `x₁ ∈ B₀` is not an exit:
  `X` is connected.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

variable {ω : Configuration 2} {C : OpenComponent ω}

/-- Sets connected along a walk, consecutive ones meeting, are joined inside `X`. -/
theorem joinedIn_of_walk {V' : Type*} {P : SimpleGraph V'} {K : V' → Set C} {X : Set C} :
    ∀ {a b : V'} (W : P.Walk a b), (∀ v ∈ W.support, ∀ x ∈ K v, ∀ y ∈ K v, JoinedIn C X x y) →
      (∀ d ∈ W.darts, (K d.fst ∩ K d.snd).Nonempty) →
      ∀ v ∈ W.support, ∀ x ∈ K a, ∀ y ∈ K v, JoinedIn C X x y
  | _, _, .nil, hK, _, v, hv, x, hx, y, hy => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact hK _ (by simp) x hx y hy
  | _, _, .cons h W', hK, hd, v, hv, x, hx, y, hy => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hK _ (by simp) x hx y hy
    · obtain ⟨m, hm, hm'⟩ := hd (SimpleGraph.Dart.mk (_, _) h) (by simp)
      exact joinedIn_trans (hK _ (by simp) x hx m hm)
        (joinedIn_of_walk W' (fun v hv => hK v (by simp [hv]))
          (fun d hd' => hd d (by simp [hd'])) v hv m hm' y hy)

section Pruned

variable {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- A connected set of `𝒢` inside `X` is joined inside `X`. -/
theorem joinedIn_of_connectedIn {S X : Set C} (hSX : S ⊆ X)
    (hS : ConnectedIn C (explorationGraph C u ℓ x₀ x₁) S) :
    ∀ a ∈ S, ∀ b ∈ S, JoinedIn C X a b := by
  intro a ha b hb
  obtain ⟨ha', hb', ⟨p⟩⟩ := hS a ha b hb
  let φ : (explorationGraph C u ℓ x₀ x₁).induce S →g (componentGraph C).induce X :=
    ⟨fun q => ⟨q.val, hSX q.2⟩, fun h => h.2.2.1⟩
  exact ⟨hSX ha, hSX hb, ⟨p.map φ⟩⟩

/-- The points carried by a vertex of the block-cut tree of `𝒢` are in `𝒢`. -/
theorem blockCutCarrier_subset_explorationGraph (v : BlockCutVertex C (explorationGraph C u ℓ x₀ x₁)
    (explorationSet C u ℓ x₀ x₁)) : blockCutCarrier C v ⊆ explorationSet C u ℓ x₀ x₁ := by
  rcases v with B | x
  · exact B.2.1.1
  · rintro y rfl
    exact x.2.1

/-- An exit `z` of the branch `W` with leaf `e` is carried by no vertex of `𝒢_tree` joined to the
root by a path, other than `e`. -/
theorem eq_leaf_of_mem_prunedCarrier {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {e X' : PrunedVertex C u ℓ x₀ x₁ B₀}
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) e) (hW : W.IsPath)
    (her : e ≠ prunedRoot C u ℓ x₀ x₁ B₀) (hle : ∃! w, (prunedTree C u ℓ x₀ x₁ B₀).Adj e w)
    {z : C} (hze : z ∈ prunedCarrier C u ℓ x₀ x₁ B₀ e)
    (huniq : ∀ v ∈ W.support, z ∈ prunedCarrier C u ℓ x₀ x₁ B₀ v → v = e)
    (W' : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) X') (hW' : W'.IsPath)
    (hzX : z ∈ prunedCarrier C u ℓ x₀ x₁ B₀ X') : X' = e := by
  by_cases hXW : X' ∈ W.support
  · exact huniq X' hXW hzX
  have hnb : ∀ w, (prunedTree C u ℓ x₀ x₁ B₀).Adj e w → w ∈ W.support := fun w hw =>
    (eq_penultimate_of_unique_adj W (Ne.symm her) hle hw) ▸ W.getVert_mem_support _
  change z ∈ blockCutCarrier C e.val at hze
  change z ∈ blockCutCarrier C X'.val at hzX
  rcases he1 : e.val with B | x <;> rcases he2 : X'.val with B' | x' <;>
    rw [he1] at hze <;> rw [he2] at hzX
  · have hzB : z ∈ B.val := hze
    have hzB' : z ∈ B'.val := hzX
    by_cases hBB' : B.val = B'.val
    · exact Subtype.ext (he2.trans ((congrArg Sum.inl (Subtype.ext hBB')).symm.trans he1.symm))
    exfalso
    let zc : {y // IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁) y} := ⟨z, IsBlock.isCutVertex B.2 B'.2 hBB' hzB hzB'⟩
    -- the cut-vertex `z` is not a vertex of `𝒢_tree`: it would be a neighbour of the leaf `e`
    have hnone : ∀ Y : PrunedVertex C u ℓ x₀ x₁ B₀, Y.val ≠ .inr zc := by
      intro Y hY
      have hadj : (prunedTree C u ℓ x₀ x₁ B₀).Adj e Y := by
        show (blockCutTree C _ _).Adj e.val Y.val
        rw [he1, hY]
        exact hzB
      have hzY : z ∈ prunedCarrier C u ℓ x₀ x₁ B₀ Y := by
        change z ∈ blockCutCarrier C Y.val
        rw [hY]
        rfl
      exact Sum.inl_ne_inr (he1.symm.trans
        ((congrArg Subtype.val (huniq Y (hnb Y hadj) hzY)).symm.trans hY))
    have hWf : (W.map (prunedHom B₀)).IsPath := hW.map (prunedHom_injective B₀)
    have hW'f : (W'.map (prunedHom B₀)).IsPath := hW'.map (prunedHom_injective B₀)
    have h1 : (Sum.inr zc) ∉ (W.map (prunedHom B₀)).support := by
      rw [mem_support_map_prunedHom]
      rintro ⟨Y, -, hY⟩
      exact hnone Y hY
    have hadj1 : (blockCutTree C _ _).Adj e.val (.inr zc) := by
      rw [he1]
      exact hzB
    have hadj2 : (blockCutTree C _ _).Adj (.inr zc) X'.val := by
      rw [he2]
      exact hzB'
    have hp : (((W.map (prunedHom B₀)).concat hadj1).concat hadj2).IsPath := by
      refine (SimpleGraph.Walk.concat_isPath_iff hadj2).2
        ⟨(SimpleGraph.Walk.concat_isPath_iff hadj1).2 ⟨hWf, h1⟩, fun h => ?_⟩
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · rw [mem_support_map_prunedHom] at h
        obtain ⟨Y, hY, hYX⟩ := h
        exact hXW (Subtype.ext hYX ▸ hY)
      · exact Sum.inl_ne_inr (he2.symm.trans h)
    have heq := congrArg Subtype.val
      (blockCutTree_isAcyclic.path_unique ⟨_, hp⟩ ⟨_, hW'f⟩)
    simp only at heq
    have hmem : (Sum.inr zc) ∈ (W'.map (prunedHom B₀)).support := by
      rw [← heq]
      simp [SimpleGraph.Walk.support_concat]
    rw [mem_support_map_prunedHom] at hmem
    obtain ⟨Y, -, hY⟩ := hmem
    exact hnone Y hY
  · have hzx : z = x'.val := hzX
    have hT : (prunedTree C u ℓ x₀ x₁ B₀).Adj e X' := by
      show (blockCutTree C _ _).Adj e.val X'.val
      rw [he1, he2]
      show x'.val ∈ B.val
      rw [← hzx]
      exact hze
    exact absurd (hnb X' hT) hXW
  · have hzx : z = x.val := hze
    have hT : (prunedTree C u ℓ x₀ x₁ B₀).Adj e X' := by
      show (blockCutTree C _ _).Adj e.val X'.val
      rw [he1, he2]
      show x.val ∈ B'.val
      rw [← hzx]
      exact hzX
    exact absurd (hnb X' hT) hXW
  · have hzx : z = x.val := hze
    have hzx' : z = x'.val := hzX
    exact Subtype.ext (he2.trans ((congrArg Sum.inr (Subtype.ext
      (hzx'.symm.trans hzx))).trans he1.symm))

end Pruned
/-- The set `𝒢_f` (L2698-2699): the points of `𝒢` carried along three distinct finite leaf
branches of `𝒢_tree`, other than their exits, form a connected subset of `L_{u(x₀)}` adjacent to
each exit. -/
theorem leafSeparatorStep : LeafSeparatorStep := by
  classical
  intro ω C u ℓ x₀ x₁ _ _ B₀ hx₁ S z hSi hS hz
  choose v hvr hvl hW _ using hS
  choose W hWp hSW using hW
  -- the exit `z i` is carried by the leaf `v i` and by no other vertex of `W i`
  have hzv : ∀ i, z i ∈ prunedCarrier C u ℓ x₀ x₁ B₀ (v i) ∧
      ∀ v' ∈ (W i).support, z i ∈ prunedCarrier C u ℓ x₀ x₁ B₀ v' → v' = v i := by
    intro i
    obtain ⟨e, he, her, hle, hze, huniq⟩ := hz i
    rw [hSW i] at he huniq
    have hev : e = v i := eq_end_of_unique_adj (W i) (hWp i) he her hle
    rw [hev] at hze huniq
    exact ⟨hze, fun v' hv' h => huniq v' hv' h⟩
  have hkey : ∀ i (X' : PrunedVertex C u ℓ x₀ x₁ B₀)
      (W' : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) X'), W'.IsPath →
      z i ∈ prunedCarrier C u ℓ x₀ x₁ B₀ X' → X' = v i := fun i _ W' hW' h =>
    eq_leaf_of_mem_prunedCarrier (W i) (hWp i) (hvr i) (hvl i) (hzv i).1 (hzv i).2 W' hW' h
  -- the leaves are distinct, so no leaf `v j` lies on `W i` for `j ≠ i`
  have hacyc : (prunedTree C u ℓ x₀ x₁ B₀).IsAcyclic := blockCutTree_isAcyclic.induce _
  have hvinj : ∀ i j, v i = v j → i = j := by
    intro i j hij
    apply hSi
    rw [hSW i, hSW j]
    have key : ∀ a b (Wa : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) a)
        (Wb : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) b), a = b →
        Wa.IsPath → Wb.IsPath → {x | x ∈ Wa.support} = {x | x ∈ Wb.support} := by
      rintro a b Wa Wb rfl ha hb
      rw [show Wa = Wb from congrArg Subtype.val (hacyc.path_unique ⟨Wa, ha⟩ ⟨Wb, hb⟩)]
    exact key _ _ (W i) (W j) hij (hWp i) (hWp j)
  have hnoleaf : ∀ i j, v j ∈ (W i).support → j = i := fun i j h =>
    hvinj j i (eq_end_of_unique_adj (W i) (hWp i) h (hvr j) (hvl j))
  have hzW : ∀ i j, j ≠ i → ∀ v' ∈ (W i).support, z j ∉ prunedCarrier C u ℓ x₀ x₁ B₀ v' := by
    intro i j hji v' hv' h
    have := hkey j v' ((W i).takeUntil v' hv') ((hWp i).takeUntil hv') h
    exact hji (hnoleaf i j (this ▸ hv'))
  -- the leaf `v i` is a block in which `z i` has a neighbour
  have hleafblk : ∀ i, ∃ L : ExplorationBlock C u ℓ x₀ x₁, (v i).val = .inl L ∧
      ∃ y ∈ L.val, (explorationGraph C u ℓ x₀ x₁).Adj (z i) y := by
    intro i
    have hnil : ¬ (W i).Nil := SimpleGraph.Walk.not_nil_of_ne (Ne.symm (hvr i))
    have hpa : (blockCutTree C _ _).Adj (W i).penultimate.val (v i).val :=
      (W i).adj_penultimate hnil
    have hpz : z i ∉ blockCutCarrier C (W i).penultimate.val := fun h =>
      ((W i).adj_penultimate hnil).ne ((hzv i).2 _ ((W i).getVert_mem_support _) h)
    have hzκ : z i ∈ blockCutCarrier C (v i).val := (hzv i).1
    rcases h1 : (v i).val with L | x <;> rcases h2 : (W i).penultimate.val with B | c <;>
      rw [h1] at hzκ hpa <;> rw [h2] at hpz hpa
    · exact hpa.elim
    · refine ⟨L, rfl, ?_⟩
      have hcL : c.val ∈ L.val := hpa
      have hzL : z i ∈ L.val := hzκ
      have hcz : z i ≠ c.val := fun e => hpz e
      obtain ⟨hz', hc', ⟨q⟩⟩ := L.2.1.2.1 (z i) hzL c.val hcL
      have hq : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne fun e => hcz (congrArg Subtype.val e)
      exact ⟨q.snd.val, q.snd.2, q.adj_snd hq⟩
    · exact (hpz (by rw [show z i = x.val from hzκ]; exact hpa)).elim
    · exact hpa.elim
  -- the separator
  set X : Set C := {y | (∃ i, ∃ v' ∈ (W i).support, y ∈ prunedCarrier C u ℓ x₀ x₁ B₀ v') ∧
    ∀ j, y ≠ z j} with hXdef
  have hKX : ∀ i, ∀ v' ∈ (W i).support, prunedCarrier C u ℓ x₀ x₁ B₀ v' \ {z i} ⊆ X := by
    intro i v' hv' y ⟨hy, hyz⟩
    refine ⟨⟨i, v', hv', hy⟩, fun j hj => ?_⟩
    by_cases hji : j = i
    · exact hyz (hji ▸ hj)
    · exact hzW i j hji v' hv' (hj ▸ hy)
  have hconn : ∀ i v', ConnectedIn C (explorationGraph C u ℓ x₀ x₁)
      (prunedCarrier C u ℓ x₀ x₁ B₀ v' \ {z i}) := by
    intro i v'
    change ConnectedIn C _ (blockCutCarrier C v'.val \ {z i})
    generalize v'.val = t
    rcases t with B | c
    · exact BiconnectedIn.connectedIn_diff B.2.1 (z i)
    · intro a ha b hb
      have e : a = b := (show a = c.val from ha.1).trans (show b = c.val from hb.1).symm
      subst e
      exact ⟨ha, ha, SimpleGraph.Reachable.refl _⟩
  have hdart : ∀ i, ∀ d ∈ (W i).darts, ((prunedCarrier C u ℓ x₀ x₁ B₀ d.fst \ {z i}) ∩
      (prunedCarrier C u ℓ x₀ x₁ B₀ d.snd \ {z i})).Nonempty := by
    intro i d hd
    obtain ⟨L, hL, -⟩ := hleafblk i
    -- a cut-vertex on `W i` is not `z i`: the leaf `v i` is a block
    have hcut : ∀ v' ∈ (W i).support, ∀ c, v'.val = .inr c → c.val ≠ z i := by
      intro v' hv' c hc e
      have := (hzv i).2 v' hv' (by
        change z i ∈ blockCutCarrier C v'.val
        rw [hc, ← e]
        exact Set.mem_singleton _)
      rw [this, hL] at hc
      exact Sum.inl_ne_inr hc
    have h1 := (W i).dart_fst_mem_support_of_mem_darts hd
    have h2 := (W i).dart_snd_mem_support_of_mem_darts hd
    have hadj : (blockCutTree C _ _).Adj d.fst.val d.snd.val := d.adj
    change ((blockCutCarrier C d.fst.val \ {z i}) ∩
      (blockCutCarrier C d.snd.val \ {z i})).Nonempty
    rcases he1 : d.fst.val with B | c <;> rcases he2 : d.snd.val with B' | c' <;>
      rw [he1, he2] at hadj
    · exact hadj.elim
    · exact ⟨c'.val, ⟨hadj, hcut _ h2 c' he2⟩, ⟨Set.mem_singleton _, hcut _ h2 c' he2⟩⟩
    · exact ⟨c.val, ⟨Set.mem_singleton _, hcut _ h1 c he1⟩, ⟨hadj, hcut _ h1 c he1⟩⟩
    · exact hadj.elim
  -- `x₁ ∈ B₀` is joined inside `X` to the carriers along each `W i`
  have hx₁X : ∀ i, x₁ ∈ prunedCarrier C u ℓ x₀ x₁ B₀ (prunedRoot C u ℓ x₀ x₁ B₀) \ {z i} := by
    intro i
    refine ⟨hx₁, fun h => hvr i ((hzv i).2 _ (W i).start_mem_support ?_).symm⟩
    have h' : x₁ = z i := h
    rw [← h']
    exact hx₁
  have hjoin : ∀ i, ∀ v' ∈ (W i).support, ∀ y ∈ prunedCarrier C u ℓ x₀ x₁ B₀ v' \ {z i},
      JoinedIn C X x₁ y := fun i v' hv' y hy =>
    joinedIn_of_walk (K := fun v' => prunedCarrier C u ℓ x₀ x₁ B₀ v' \ {z i}) (W i)
      (fun v' hv' => joinedIn_of_connectedIn (hKX i v' hv') (hconn i v')) (hdart i) v' hv' x₁
      (hx₁X i) y hy
  refine ⟨X, fun y hy => ?_, ?_, fun i hi => hi.2 i rfl, fun i => ?_⟩
  · obtain ⟨⟨i, v', -, hy⟩, -⟩ := hy
    exact levelSet_of_mem_explorationSet (blockCutCarrier_subset_explorationGraph v'.val hy)
  · have hx : ∀ y ∈ X, JoinedIn C X x₁ y := by
      rintro y ⟨⟨i, v', hv', hy⟩, hyz⟩
      exact hjoin i v' hv' y ⟨hy, hyz i⟩
    intro a ha b hb
    obtain ⟨h1, h2, r⟩ := hx a ha
    exact joinedIn_trans ⟨h2, h1, r.symm⟩ (hx b hb)
  · obtain ⟨L, hL, y, hyL, hadj⟩ := hleafblk i
    refine ⟨y, hKX i (v i) (W i).end_mem_support ⟨?_, fun h => hadj.ne (Eq.symm h)⟩, hadj.2.2.1⟩
    change y ∈ blockCutCarrier C (v i).val
    rw [hL]
    exact hyL

end Rigidity.Proofs.Section5
