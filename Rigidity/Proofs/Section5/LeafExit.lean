import Rigidity.Steps.Section5.FiniteBranches

/-! # Lemma 5.28: exits of the finite leaf branches of `𝒢_tree`

Proofs of `LeafExitStep` (step:5.27-tree, corrected draft L2498-2501) and `ExitsDistinctStep` of
the carving of Lemma 5.28 (`Rigidity/Steps/Section5/FiniteBranches.lean`).

Block theory of `(V, G)` (here `V = 𝒢`, `G` its graph), with blocks the maximal biconnected
subsets and the block-cut tree of `Rigidity/Draft/Section5dStatements.lean`:
* a path of `G` in `V` between two distinct points of a block stays in the block
  (`IsBlock.support_subset`: adding the path keeps the set biconnected);
* two distinct blocks share at most one point (`IsBlock.eq_of_mem_two`), and a shared point `x`
  separates them in `V \ {x}` (`IsBlock.not_reachIn`), so it is a cut-vertex;
* a point of a block with a neighbour outside the block is a cut-vertex;
* the block-cut tree is acyclic (`blockCutTree_isAcyclic`): a cycle through a cut-vertex `x`
  joins two blocks containing `x` in `V \ {x}`;
* every biconnected set lies in a block (Zorn), so a cut-vertex lies in two blocks.

Leaf exits. Let `L` be the leaf of a finite leaf branch and `c` its parent in `𝒢_tree`. A leaf
cut-vertex would lie in a second block, kept since `𝒢_tree` only removes descendants of pruning
blocks, so `L` is a block and `c` a cut-vertex. Every `y ∈ L \ {c}` is an exit point. If `L` is a
pruning block through `y`, then `y ≠ c` (else the parent block of `c` prunes `L`) and the
neighbour of `y` off `L_a` is the exit edge. Otherwise `c` is the only cut-vertex of `L`, `ℓ` is
minimal on `L` exactly at `c` (an increasing path from `x₁` enters `L` through `c`), its maximum
`z` on `L` has a smaller neighbour in `L`, harmonicity of `ℓ` gives `p ∼ z` with `ℓ(p) > ℓ(z)`,
and `u(p) = a` would make `p ∈ 𝒢 \ L` a neighbour of `z ≠ c`, so `z` a cut-vertex of `L`.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

section Walks

variable {α : Type*} {G : SimpleGraph α}

/-- `x` and `y` are joined by a walk of `G` inside `S`. -/
def GraphReachIn (G : SimpleGraph α) (S : Set α) (x y : α) : Prop :=
  ∃ p : G.Walk x y, ∀ v ∈ p.support, v ∈ S

theorem GraphReachIn.refl {S : Set α} {x : α} (hx : x ∈ S) : GraphReachIn G S x x :=
  ⟨.nil, by simpa using hx⟩

theorem GraphReachIn.symm {S : Set α} {x y : α} (h : GraphReachIn G S x y) : GraphReachIn G S y x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

theorem GraphReachIn.trans {S : Set α} {x y z : α} (h : GraphReachIn G S x y) (h' : GraphReachIn G S y z) :
    GraphReachIn G S x z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨p.append q, fun v hv => ?_⟩
  rcases (SimpleGraph.Walk.mem_support_append_iff p q).1 hv with h | h
  exacts [hp v h, hq v h]

theorem GraphReachIn.mono {S T : Set α} {x y : α} (h : GraphReachIn G S x y) (hST : S ⊆ T) :
    GraphReachIn G T x y := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun v hv => hST (hp v hv)⟩

theorem GraphReachIn.of_adj {S : Set α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (h : G.Adj x y) :
    GraphReachIn G S x y :=
  ⟨.cons h .nil, by simp [hx, hy]⟩

/-- A vertex of a walk reaches its end inside the walk. -/
theorem reachIn_support [DecidableEq α] {a b v : α} (p : G.Walk a b) (hv : v ∈ p.support) :
    GraphReachIn G {x | x ∈ p.support} v b :=
  ⟨p.dropUntil v hv, fun _ hw => p.support_dropUntil_subset_support hv hw⟩

/-- In a path from `s` to `t`, a vertex other than `w` reaches `s` or `t` avoiding `w`. -/
theorem reachIn_endpoint_of_isPath [DecidableEq α] {s t : α} (p : G.Walk s t) (hp : p.IsPath) (w : α) :
    ∀ v ∈ p.support, v ≠ w → (s ≠ w ∧ GraphReachIn G ({x | x ∈ p.support} \ {w}) v s) ∨
      (t ≠ w ∧ GraphReachIn G ({x | x ∈ p.support} \ {w}) v t) := by
  induction p with
  | nil =>
    intro v hv hvw
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact Or.inl ⟨hvw, .refl (by simp [hvw])⟩
  | @cons s s1 t h p ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hsub : {x | x ∈ p.support} \ {w} ⊆
        {x | x ∈ (SimpleGraph.Walk.cons h p).support} \ {w} := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_setOf_eq, SimpleGraph.Walk.support_cons,
        List.mem_cons] at hx ⊢
      tauto
    intro v hv hvw
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Or.inl ⟨hvw, .refl (by simp [hvw])⟩
    rcases ih hp.1 v hv hvw with ⟨h1, hr⟩ | ⟨h1, hr⟩
    · by_cases hsw : s = w
      · subst hsw
        refine Or.inr ⟨fun h' => hp.2 (h' ▸ p.end_mem_support), ?_⟩
        refine (reachIn_support p hv).mono fun x hx => ⟨List.mem_cons_of_mem _ hx, ?_⟩
        rintro rfl
        exact hp.2 hx
      · refine Or.inl ⟨hsw, (hr.mono hsub).trans (.of_adj ?_ ?_ h.symm)⟩
        · exact ⟨by simp, fun h' => h1 h'⟩
        · exact ⟨by simp, hsw⟩
    · exact Or.inr ⟨h1, hr.mono hsub⟩

/-- The prefix of a walk up to its first vertex in `S`. -/
theorem exists_walk_first {S : Set α} {a b : α} (p : G.Walk a b) (hb : b ∈ S) :
    ∃ q ∈ S, ∃ p' : G.Walk a q, (∀ v ∈ p'.support, v ∈ p.support) ∧
      (∀ v ∈ p'.support, v ∈ S → v = q) ∧ (p.IsPath → p'.IsPath) := by
  induction p with
  | nil => exact ⟨_, hb, .nil, by simp, by simp, fun _ => SimpleGraph.Walk.IsPath.nil⟩
  | @cons a a1 b h p ih =>
    by_cases ha : a ∈ S
    · exact ⟨a, ha, .nil, by simp, by simp, fun _ => SimpleGraph.Walk.IsPath.nil⟩
    · obtain ⟨q, hq, p', hsub, hfirst, hpath⟩ := ih hb
      refine ⟨q, hq, .cons h p', ?_, ?_, ?_⟩
      · intro v hv
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        exacts [Or.inl rfl, Or.inr (hsub v hv)]
      · intro v hv hvS
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        exacts [absurd hvS ha, hfirst v hv hvS]
      · intro hp
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp ⊢
        exact ⟨hpath hp.1, fun h' => hp.2 (hsub _ h')⟩

/-- The suffix of a walk from its last vertex in `S`. -/
theorem exists_walk_last {S : Set α} {a b : α} (p : G.Walk a b) (ha : a ∈ S) :
    ∃ q ∈ S, ∃ p' : G.Walk q b, (∀ v ∈ p'.support, v ∈ p.support) ∧
      (∀ v ∈ p'.support, v ∈ S → v = q) ∧ (p.IsPath → p'.IsPath) := by
  obtain ⟨q, hq, p', hsub, hfirst, hpath⟩ := exists_walk_first p.reverse ha
  refine ⟨q, hq, p'.reverse, ?_, ?_, ?_⟩
  · intro v hv
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    simpa using hsub v hv
  · intro v hv hvS
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
    exact hfirst v hv hvS
  · intro hp
    exact (hpath hp.reverse).reverse

/-- Two paths meeting only at the junction append to a path. -/
theorem isPath_append {a m b : α} {p : G.Walk a m} {q : G.Walk m b} (hp : p.IsPath)
    (hq : q.IsPath) (h : ∀ v ∈ p.support, v ∈ q.support → v = m) : (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
  intro v hv w hw hvw
  subst hvw
  have hvm := h v hv (List.mem_of_mem_tail hw)
  subst hvm
  have hq' := hq.support_nodup
  rw [← SimpleGraph.Walk.cons_tail_support, List.nodup_cons] at hq'
  exact hq'.1 hw

/-- A walk in `V` from `a ≠ x` to `x` gives a neighbour of `x` reached from `a` in `V \ {x}`. -/
theorem exists_adj_reachIn {V : Set α} {a x : α} (p : G.Walk a x) (hp : ∀ v ∈ p.support, v ∈ V)
    (hax : a ≠ x) : ∃ y, G.Adj y x ∧ GraphReachIn G (V \ {x}) a y := by
  induction p with
  | nil => exact absurd rfl hax
  | @cons a a1 x h p ih =>
    by_cases h1 : a1 = x
    · rw [h1] at h
      exact ⟨a, h, GraphReachIn.refl (show a ∈ V \ {x} from ⟨hp a (by simp), hax⟩)⟩
    · obtain ⟨y, hy, hr⟩ := ih (fun v hv => hp v (by simp [hv])) h1
      exact ⟨y, hy, (GraphReachIn.of_adj (S := V \ {x}) ⟨hp a (by simp), hax⟩ ⟨hp a1 (by simp), h1⟩ h).trans hr⟩

theorem GraphReachIn.mem_right {S : Set α} {x y : α} (h : GraphReachIn G S x y) : y ∈ S := by
  obtain ⟨p, hp⟩ := h
  exact hp y p.end_mem_support

/-- A vertex of a path, other than its ends, with a unique neighbour does not exist. -/
theorem eq_end_of_unique_adj {a b e : α} (W : G.Walk a b) (hW : W.IsPath) (he : e ∈ W.support)
    (hea : e ≠ a) (hleaf : ∃! w, G.Adj e w) : e = b := by
  by_contra heb
  obtain ⟨i, rfl, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 he
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hea W.getVert_zero
  have hil : i ≠ W.length := by
    rintro rfl
    exact heb W.getVert_length
  have h1 : G.Adj (W.getVert i) (W.getVert (i - 1)) := by
    have := W.adj_getVert_succ (i := i - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at this
    exact this.symm
  have h2 : G.Adj (W.getVert i) (W.getVert (i + 1)) := W.adj_getVert_succ (by omega)
  have h12 := hW.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) (hleaf.unique h1 h2)
  omega

/-- The unique neighbour of the end of a nontrivial walk is its penultimate vertex. -/
theorem eq_penultimate_of_unique_adj {a b w : α} (W : G.Walk a b) (hab : a ≠ b)
    (hleaf : ∃! x, G.Adj b x) (hw : G.Adj b w) : w = W.penultimate :=
  hleaf.unique hw (W.adj_penultimate (W.not_nil_of_ne hab)).symm

/-- On a path whose penultimate vertex is not its start, the vertex before the penultimate. -/
theorem exists_adj_penultimate {a b : α} (W : G.Walk a b) (hW : W.IsPath)
    (hpa : W.penultimate ≠ a) : ∃ x ∈ W.support, x ≠ b ∧ G.Adj x W.penultimate := by
  have hn : 2 ≤ W.length := by
    by_contra h
    apply hpa
    rw [SimpleGraph.Walk.penultimate, show W.length - 1 = 0 by omega, W.getVert_zero]
  refine ⟨W.getVert (W.length - 2), W.getVert_mem_support _, fun h => ?_, ?_⟩
  · have := hW.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) (h.trans W.getVert_length.symm)
    omega
  · have := W.adj_getVert_succ (i := W.length - 2) (by omega)
    rwa [show W.length - 2 + 1 = W.length - 1 by omega] at this

end Walks

section Blocks

variable {ω : Configuration 2} {C : OpenComponent ω} {G : SimpleGraph C} {V : Set C}

theorem connectedIn_iff {S : Set C} :
    ConnectedIn C G S ↔ ∀ x ∈ S, ∀ y ∈ S, GraphReachIn G S x y := by
  constructor
  · intro h x hx y hy
    obtain ⟨_, _, hr⟩ := h x hx y hy
    let q := (Nonempty.some hr).map (SimpleGraph.Embedding.induce S).toHom
    refine ⟨q, fun v hv => ?_⟩
    have hv' : v ∈ (Nonempty.some hr).support.map (SimpleGraph.Embedding.induce S).toHom :=
      (SimpleGraph.Walk.support_map _ _) ▸ hv
    obtain ⟨v', -, rfl⟩ := List.mem_map.1 hv'
    exact v'.2
  · intro h x hx y hy
    obtain ⟨p, hp⟩ := h x hx y hy
    exact ⟨hx, hy, ⟨p.induce S hp⟩⟩

theorem connectedIn_of_reachIn {S : Set C} {z : C} (h : ∀ x ∈ S, GraphReachIn G S x z) :
    ConnectedIn C G S :=
  connectedIn_iff.2 fun x hx y hy => (h x hx).trans (h y hy).symm

theorem ConnectedIn.union {S T : Set C} (hS : ConnectedIn C G S) (hT : ConnectedIn C G T)
    {z : C} (hzS : z ∈ S) (hzT : z ∈ T) : ConnectedIn C G (S ∪ T) := by
  refine connectedIn_of_reachIn (z := z) fun x hx => ?_
  rcases hx with hx | hx
  · exact (connectedIn_iff.1 hS x hx z hzS).mono Set.subset_union_left
  · exact (connectedIn_iff.1 hT x hx z hzT).mono Set.subset_union_right

theorem connectedIn_of_subset_pair {S : Set C} {z p : C} (h : G.Adj z p) (hS : S ⊆ {z, p}) :
    ConnectedIn C G S := by
  rw [connectedIn_iff]
  intro x hx y hy
  rcases hS hx with rfl | rfl <;> rcases hS hy with rfl | rfl
  · exact .refl hx
  · exact .of_adj hx hy h
  · exact .of_adj hx hy h.symm
  · exact .refl hx

theorem biconnectedIn_pair {z p : C} (hz : z ∈ V) (hp : p ∈ V) (h : G.Adj z p) :
    BiconnectedIn C G V {z, p} :=
  ⟨Set.insert_subset hz (Set.singleton_subset_iff.2 hp), connectedIn_of_subset_pair h le_rfl,
    fun _ _ => connectedIn_of_subset_pair h Set.sdiff_subset⟩

theorem BiconnectedIn.connectedIn_diff {S : Set C} (h : BiconnectedIn C G V S) (w : C) :
    ConnectedIn C G (S \ {w}) := by
  by_cases hw : w ∈ S
  · exact h.2.2 w hw
  · rw [Set.sdiff_singleton_eq_self hw]
    exact h.2.1

/-- A path of `(V, G)` between two distinct points of a block stays in the block. -/
theorem IsBlock.support_subset {B : Set C} (hB : IsBlock C G V B) {s t : C} (p : G.Walk s t)
    (hp : p.IsPath) (hpV : ∀ v ∈ p.support, v ∈ V) (hs : s ∈ B) (ht : t ∈ B) (hst : s ≠ t) :
    ∀ v ∈ p.support, v ∈ B := by
  have hbi : BiconnectedIn C G V (B ∪ {x | x ∈ p.support}) := by
    refine ⟨Set.union_subset hB.1.1 hpV, ?_, ?_⟩
    · refine connectedIn_of_reachIn (z := t) fun x hx => ?_
      rcases hx with hx | hx
      · exact (connectedIn_iff.1 hB.1.2.1 x hx t ht).mono Set.subset_union_left
      · exact (reachIn_support p hx).mono Set.subset_union_right
    · intro w _
      obtain ⟨e, heB, hew⟩ : ∃ e ∈ B, e ≠ w := by
        by_cases h : s = w
        · exact ⟨t, ht, fun h' => hst (h.trans h'.symm)⟩
        · exact ⟨s, hs, h⟩
      have hBw := connectedIn_iff.1 (BiconnectedIn.connectedIn_diff hB.1 w)
      have hsub1 : B \ {w} ⊆ (B ∪ {x | x ∈ p.support}) \ {w} :=
        Set.sdiff_subset_sdiff_left Set.subset_union_left
      have hsub2 : {x | x ∈ p.support} \ {w} ⊆ (B ∪ {x | x ∈ p.support}) \ {w} :=
        Set.sdiff_subset_sdiff_left Set.subset_union_right
      refine connectedIn_of_reachIn (z := e) fun x hx => ?_
      rcases hx with ⟨hx | hx, hxw⟩
      · exact (hBw x ⟨hx, hxw⟩ e ⟨heB, hew⟩).mono hsub1
      · rcases reachIn_endpoint_of_isPath p hp w x hx hxw with ⟨h1, hr⟩ | ⟨h1, hr⟩
        · exact (hr.mono hsub2).trans ((hBw s ⟨hs, h1⟩ e ⟨heB, hew⟩).mono hsub1)
        · exact (hr.mono hsub2).trans ((hBw t ⟨ht, h1⟩ e ⟨heB, hew⟩).mono hsub1)
  have hU := hB.2 _ hbi Set.subset_union_left
  intro v hv
  rw [← hU]
  exact Or.inr hv

/-- Two distinct blocks share at most one point. -/
theorem IsBlock.eq_of_mem_two {B B' : Set C} (hB : IsBlock C G V B) (hB' : IsBlock C G V B')
    {x y : C} (hx : x ∈ B) (hx' : x ∈ B') (hy : y ∈ B) (hy' : y ∈ B') (hxy : x ≠ y) :
    B = B' := by
  have hbi : BiconnectedIn C G V (B ∪ B') := by
    refine ⟨Set.union_subset hB.1.1 hB'.1.1, ConnectedIn.union hB.1.2.1 hB'.1.2.1 hx hx', ?_⟩
    intro w _
    rw [Set.union_sdiff_distrib]
    by_cases hxw : x = w
    · have hyw : y ∉ ({w} : Set C) := fun h => hxy (hxw.trans h.symm)
      exact ConnectedIn.union (BiconnectedIn.connectedIn_diff hB.1 w) (BiconnectedIn.connectedIn_diff hB'.1 w) ⟨hy, hyw⟩ ⟨hy', hyw⟩
    · exact ConnectedIn.union (BiconnectedIn.connectedIn_diff hB.1 w) (BiconnectedIn.connectedIn_diff hB'.1 w) ⟨hx, hxw⟩ ⟨hx', hxw⟩
  exact (hB.2 _ hbi Set.subset_union_left).symm.trans (hB'.2 _ hbi Set.subset_union_right)

/-- A block sharing a point `x` with another block has a point other than `x`. -/
theorem IsBlock.exists_ne_of_ne {B B' : Set C} (hB : IsBlock C G V B) (hB' : IsBlock C G V B')
    (hne : B ≠ B') {x : C} (_hx : x ∈ B) (hx' : x ∈ B') : ∃ b ∈ B, b ≠ x := by
  by_contra h
  push Not at h
  exact hne (hB.2 B' hB'.1 fun b hb => (h b hb) ▸ hx').symm

/-- A point `x` shared by two distinct blocks separates them in `V \ {x}`. -/
theorem IsBlock.not_reachIn {B B' : Set C} (hB : IsBlock C G V B) (hB' : IsBlock C G V B')
    (hne : B ≠ B') {x b b' : C} (hx : x ∈ B) (hx' : x ∈ B') (hb : b ∈ B) (hb' : b' ∈ B') :
    ¬ GraphReachIn G (V \ {x}) b' b := by
  rintro ⟨w, hw⟩
  have hπV : ∀ v ∈ w.bypass.support, v ∈ V \ {x} := fun v hv => hw v (w.support_bypass_subset_support hv)
  obtain ⟨q, hqB, π1, hs1, -, hp1⟩ := exists_walk_first (S := B) w.bypass hb
  obtain ⟨q', hq'B', π2, hs2, hf2, hp2⟩ := exists_walk_last (S := B') π1 hb'
  obtain ⟨σ0, hσ0⟩ := connectedIn_iff.1 hB'.1.2.1 x hx' q' hq'B'
  have hσB' : ∀ v ∈ σ0.bypass.support, v ∈ B' := fun v hv => hσ0 v (σ0.support_bypass_subset_support hv)
  have hpath : (σ0.bypass.append π2).IsPath :=
    isPath_append σ0.bypass_isPath (hp2 (hp1 w.bypass_isPath))
      fun v hv hv2 => hf2 v hv2 (hσB' v hv)
  have hqV : q ∈ V \ {x} := hπV q (hs1 q π1.end_mem_support)
  have hq'V : q' ∈ V \ {x} := hπV q' (hs1 q' (hs2 q' π2.start_mem_support))
  have hsubB := IsBlock.support_subset hB (σ0.bypass.append π2) hpath ?_ hx hqB fun h => hqV.2 h.symm
  · have hq'B : q' ∈ B := hsubB q' (by
      rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl σ0.bypass.end_mem_support)
    exact hne (IsBlock.eq_of_mem_two hB hB' hx hx' hq'B hq'B' fun h => hq'V.2 h.symm)
  · intro v hv
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hv with h | h
    · exact hB'.1.1 (hσB' v h)
    · exact (hπV v (hs1 v (hs2 v h))).1

/-- A point shared by two distinct blocks is a cut-vertex. -/
theorem IsBlock.isCutVertex {B B' : Set C} (hB : IsBlock C G V B) (hB' : IsBlock C G V B')
    (hne : B ≠ B') {x : C} (hx : x ∈ B) (hx' : x ∈ B') : IsCutVertex C G V x := by
  refine ⟨hB.1.1 hx, fun hconn => ?_⟩
  obtain ⟨b, hb, hbx⟩ := IsBlock.exists_ne_of_ne hB hB' hne hx hx'
  obtain ⟨b', hb', hb'x⟩ := IsBlock.exists_ne_of_ne hB' hB (Ne.symm hne) hx' hx
  exact IsBlock.not_reachIn hB hB' hne hx hx' hb hb'
    (connectedIn_iff.1 hconn b' ⟨hB'.1.1 hb', hb'x⟩ b ⟨hB.1.1 hb, hbx⟩)

/-- A point of a block with a neighbour in `V` off the block is a cut-vertex. -/
theorem IsBlock.isCutVertex_of_adj {B : Set C} (hB : IsBlock C G V B) {z p : C} (hz : z ∈ B)
    (hpV : p ∈ V) (hpB : p ∉ B) (hzp : G.Adj z p) : IsCutVertex C G V z := by
  refine ⟨hB.1.1 hz, fun hconn => ?_⟩
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ B, w ≠ z := by
    by_contra h
    push Not at h
    have hU := hB.2 _ (biconnectedIn_pair (hB.1.1 hz) hpV hzp)
      fun b hb => by rw [h b hb]; exact Set.mem_insert _ _
    exact hpB (hU ▸ Set.mem_insert_of_mem _ rfl)
  have hpz : p ≠ z := fun h => hpB (h ▸ hz)
  obtain ⟨π0, hπ0⟩ := connectedIn_iff.1 hconn p ⟨hpV, hpz⟩ w ⟨hB.1.1 hw, hwz⟩
  obtain ⟨q, hqB, π1, hs1, -, hp1⟩ := exists_walk_first (S := B) π0.bypass hw
  have hπV : ∀ v ∈ π1.support, v ∈ V \ {z} :=
    fun v hv => hπ0 v (π0.support_bypass_subset_support (hs1 v hv))
  have hpath : (SimpleGraph.Walk.cons hzp π1).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨hp1 π0.bypass_isPath, fun h => (hπV z h).2 rfl⟩
  have hsub := IsBlock.support_subset hB _ hpath ?_ hz hqB fun h => (hπV q π1.end_mem_support).2 h.symm
  · exact hpB (hsub p (by simp))
  · intro v hv
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    exacts [hB.1.1 hz, (hπV v hv).1]

/-- Every biconnected subset of `V` lies in a block (Zorn). -/
theorem exists_isBlock_superset {S : Set C} (hS : BiconnectedIn C G V S) :
    ∃ B, IsBlock C G V B ∧ S ⊆ B := by
  suffices H : ∀ c ⊆ {T | BiconnectedIn C G V T}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {T | BiconnectedIn C G V T}, ∀ s ∈ c, s ⊆ ub by
    obtain ⟨m, hSm, hm⟩ := zorn_subset_nonempty {T | BiconnectedIn C G V T} H S hS
    exact ⟨m, ⟨hm.prop, fun T hT hmT => (hm.eq_of_subset hT hmT).symm⟩, hSm⟩
  intro c hc hchain _
  have up : ∀ A ∈ c, ∀ B ∈ c, ∃ D ∈ c, A ⊆ D ∧ B ⊆ D := fun A hA B hB =>
    (hchain.total hA hB).elim (fun h => ⟨B, hB, h, le_rfl⟩) (fun h => ⟨A, hA, le_rfl, h⟩)
  refine ⟨⋃₀ c, ⟨Set.sUnion_subset fun T hT => (hc hT).1, ?_, ?_⟩,
    fun T hT => Set.subset_sUnion_of_mem hT⟩
  · rw [connectedIn_iff]
    rintro x ⟨T1, hT1, hx⟩ y ⟨T2, hT2, hy⟩
    obtain ⟨D, hD, h1, h2⟩ := up T1 hT1 T2 hT2
    exact (connectedIn_iff.1 (hc hD).2.1 x (h1 hx) y (h2 hy)).mono
      (Set.subset_sUnion_of_mem hD)
  · rintro w ⟨T0, hT0, hw⟩
    rw [connectedIn_iff]
    rintro x ⟨⟨T1, hT1, hx⟩, hxw⟩ y ⟨⟨T2, hT2, hy⟩, hyw⟩
    obtain ⟨D, hD, h1, h2⟩ := up T1 hT1 T2 hT2
    obtain ⟨E, hE, hDE, h0⟩ := up D hD T0 hT0
    exact (connectedIn_iff.1 ((hc hE).2.2 w (h0 hw)) x ⟨hDE (h1 hx), hxw⟩ y
      ⟨hDE (h2 hy), hyw⟩).mono (Set.sdiff_subset_sdiff_left (Set.subset_sUnion_of_mem hE))

/-- A walk of the block-cut tree avoiding the cut-vertex `x` joins the points of its end carriers
in `V \ {x}`. -/
theorem reachIn_of_blockCutWalk {x : C} {v w : BlockCutVertex C G V}
    (W : (blockCutTree C G V).Walk v w)
    (hW : ∀ y : {y // IsCutVertex C G V y}, Sum.inr y ∈ W.support → y.val ≠ x) :
    ∀ p ∈ blockCutCarrier C v, p ≠ x → ∀ q ∈ blockCutCarrier C w, q ≠ x →
      GraphReachIn G (V \ {x}) p q := by
  induction W with
  | nil =>
    rename_i v
    intro p hp hpx q hq hqx
    rcases v with B | y
    · exact (connectedIn_iff.1 (BiconnectedIn.connectedIn_diff B.2.1 x) p ⟨hp, hpx⟩ q ⟨hq, hqx⟩).mono
        (Set.sdiff_subset_sdiff_left B.2.1.1)
    · have hp' : p = y.val := hp
      have hq' : q = y.val := hq
      subst hp' hq'
      exact .refl ⟨y.2.1, hpx⟩
  | @cons v v1 w h W ih =>
    have hW' : ∀ y : {y // IsCutVertex C G V y}, Sum.inr y ∈ W.support → y.val ≠ x :=
      fun y hy => hW y (by simp [hy])
    intro p hp hpx q hq hqx
    rcases v with B | y <;> rcases v1 with B1 | y1
    · exact h.elim
    · have hy1 : y1.val ≠ x := hW' y1 W.start_mem_support
      have hyB : y1.val ∈ B.val := h
      refine ((connectedIn_iff.1 (BiconnectedIn.connectedIn_diff B.2.1 x) p ⟨hp, hpx⟩ y1.val
        ⟨hyB, hy1⟩).mono (Set.sdiff_subset_sdiff_left B.2.1.1)).trans ?_
      exact ih hW' y1.val rfl hy1 q hq hqx
    · have hp' : p = y.val := hp
      subst hp'
      exact ih hW' y.val h hpx q hq hqx
    · exact h.elim

/-- The block-cut tree is acyclic. -/
theorem blockCutTree_isAcyclic : (blockCutTree C G V).IsAcyclic := by
  have cyc : ∀ (y : {y // IsCutVertex C G V y}) (B : {S // IsBlock C G V S})
      (p : (blockCutTree C G V).Walk (.inr y) (.inl B)), p.IsPath → y.val ∈ B.val →
      s(Sum.inr y, Sum.inl B) ∉ p.edges → False := by
    intro y B p hp hyB hedge
    cases p with
    | cons h p1 =>
      rename_i u
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      rcases u with B1 | y1
      · have hyB1 : y.val ∈ B1.val := h
        have hne : B.val ≠ B1.val := by
          intro heq
          have : B1 = B := Subtype.ext heq.symm
          subst this
          exact hedge (by simp)
        obtain ⟨b, hb, hby⟩ := IsBlock.exists_ne_of_ne B.2 B1.2 hne hyB hyB1
        obtain ⟨b1, hb1, hb1y⟩ := IsBlock.exists_ne_of_ne B1.2 B.2 (Ne.symm hne) hyB1 hyB
        refine IsBlock.not_reachIn B.2 B1.2 hne hyB hyB1 hb hb1 ?_
        refine reachIn_of_blockCutWalk p1 (fun y' hy' heq => hp.2 ?_) b1 hb1 hb1y b hb hby
        have : y' = y := Subtype.ext heq
        exact this ▸ hy'
      · exact h.elim
  intro v c hc
  cases c with
  | nil => exact hc.ne_nil rfl
  | cons h c' =>
    rename_i v1
    rw [SimpleGraph.Walk.cons_isCycle_iff] at hc
    rcases v with B | y <;> rcases v1 with B1 | y1
    · exact h.elim
    · exact cyc y1 B c' hc.1 h (by rw [Sym2.eq_swap]; exact hc.2)
    · exact cyc y B1 c'.reverse hc.1.reverse h (by
        rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
        exact hc.2)
    · exact h.elim

/-- A cut-vertex `x` of a connected `(V, G)` lies in a block other than a given block. -/
theorem exists_isBlock_ne (hV : ConnectedIn C G V) {x : C} (hx : IsCutVertex C G V x)
    {B : Set C} (hB : IsBlock C G V B) : ∃ B', IsBlock C G V B' ∧ x ∈ B' ∧ B' ≠ B := by
  have key : ∃ y, G.Adj y x ∧ y ∈ V ∧ y ≠ x ∧ y ∉ B := by
    by_contra hcon
    push Not at hcon
    apply hx.2
    have hnb : ∀ a ∈ V \ {x}, ∃ y ∈ B \ {x}, GraphReachIn G (V \ {x}) a y := by
      intro a ha
      obtain ⟨w, hw⟩ := connectedIn_iff.1 hV a ha.1 x hx.1
      obtain ⟨y, hyx, hr⟩ := exists_adj_reachIn w hw ha.2
      have hyV := hr.mem_right
      exact ⟨y, ⟨hcon y hyx hyV.1 hyV.2, hyV.2⟩, hr⟩
    have hBx := connectedIn_iff.1 (BiconnectedIn.connectedIn_diff hB.1 x)
    refine connectedIn_iff.2 fun a ha b hb => ?_
    obtain ⟨ya, hya, hra⟩ := hnb a ha
    obtain ⟨yb, hyb, hrb⟩ := hnb b hb
    exact hra.trans (((hBx ya hya yb hyb).mono (Set.sdiff_subset_sdiff_left hB.1.1)).trans hrb.symm)
  obtain ⟨y, hyx, hyV, -, hyB⟩ := key
  obtain ⟨B', hB', hsub⟩ := exists_isBlock_superset (biconnectedIn_pair hx.1 hyV hyx.symm)
  exact ⟨B', hB', hsub (Set.mem_insert _ _), fun h => hyB (h ▸ hsub (Set.mem_insert_of_mem _ rfl))⟩

/-- A vertex of a path of the block-cut tree from `r` is a strict ancestor of its end. -/
theorem isStrictAncestor_of_mem {r a b : BlockCutVertex C G V} (W : (blockCutTree C G V).Walk r b)
    (hW : W.IsPath) (ha : a ∈ W.support) (hab : a ≠ b) :
    IsStrictAncestor (blockCutTree C G V) r a b :=
  ⟨hab, fun W' hW' => by
    have h := blockCutTree_isAcyclic.path_unique ⟨W', hW'⟩ ⟨W, hW⟩
    rw [show W' = W from congrArg Subtype.val h]
    exact ha⟩

end Blocks

section Exploration

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- Membership in `𝒢` through an `ℕ`-indexed path. -/
theorem mem_explorationSet_iff {y : C} : y ∈ explorationSet C u ℓ x₀ x₁ ↔
    ∃ n, 1 ≤ n ∧ ∃ γ : ℕ → C, (∀ i < n, (componentGraph C).Adj (γ i) (γ (i + 1))) ∧
      (∀ i ≤ n, u (γ i) = u x₀) ∧ γ 0 = x₀ ∧ γ 1 = x₁ ∧ γ n = y ∧
      ∀ i, 1 ≤ i → i < n → ℓ (γ i) < ℓ (γ (i + 1)) := by
  constructor
  · rintro ⟨n, hn, γ, hadj, hu, h0, h1, hy, hℓ⟩
    let γN : ℕ → C := fun i => γ ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩
    have hγN : ∀ i (hi : i ≤ n), γN i = γ ⟨i, Nat.lt_succ_of_le hi⟩ :=
      fun i hi => congrArg γ (Fin.ext (min_eq_left hi))
    refine ⟨n, hn, γN, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, fun i h1i hi => ?_⟩
    · rw [hγN i hi.le, hγN (i + 1) hi]
      exact hadj ⟨i, hi⟩
    · rw [hγN i hi]
      exact hu _
    · rw [hγN 0 (Nat.zero_le _)]
      exact (congrArg γ (Fin.ext (by simp))).trans h0
    · rw [hγN 1 hn]
      exact (congrArg γ (Fin.ext (by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]))).trans h1
    · rw [hγN n le_rfl]
      exact hy
    · rw [hγN i hi.le, hγN (i + 1) hi]
      exact hℓ ⟨i, hi⟩ h1i
  · rintro ⟨n, hn, γ, hadj, hu, h0, h1, hy, hℓ⟩
    refine ⟨n, hn, fun i => γ i.val, fun i => by simpa using hadj i i.2,
      fun i => hu i (Nat.lt_succ_iff.1 i.2), by simpa using h0, ?_, by simpa using hy,
      fun i h1i => by simpa using hℓ i h1i i.2⟩
    show γ (1 : Fin (n + 1)).val = x₁
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    exact h1

theorem levelSet_of_mem_explorationSet {y : C} (hy : y ∈ explorationSet C u ℓ x₀ x₁) :
    u y = u x₀ := by
  obtain ⟨n, -, γ, -, hu, -, -, rfl, -⟩ := mem_explorationSet_iff.1 hy
  exact hu n le_rfl

theorem x₁_mem_explorationSet (h : (componentGraph C).Adj x₀ x₁) (hu : u x₁ = u x₀) :
    x₁ ∈ explorationSet C u ℓ x₀ x₁ := by
  refine mem_explorationSet_iff.2 ⟨1, le_rfl, fun i => if i = 0 then x₀ else x₁, ?_, ?_,
    by simp, by simp, by simp, fun i h1 h2 => by omega⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simpa using h
  · intro i hi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl <;> simp [hu]

/-- `𝒢` contains the neighbours of its points in `L_{u(x₀)}` with a larger value of `ℓ`. -/
theorem mem_explorationSet_of_adj {y p : C} (hy : y ∈ explorationSet C u ℓ x₀ x₁)
    (hyp : (componentGraph C).Adj y p) (hp : u p = u x₀) (hℓ : ℓ y < ℓ p) :
    p ∈ explorationSet C u ℓ x₀ x₁ := by
  obtain ⟨n, hn, γ, hadj, hu, h0, h1, rfl, hinc⟩ := mem_explorationSet_iff.1 hy
  refine mem_explorationSet_iff.2 ⟨n + 1, by omega, fun i => if i ≤ n then γ i else p,
    fun i hi => ?_, fun i hi => ?_, by simpa using h0, by simpa [hn] using h1, by simp,
    fun i h1i hi => ?_⟩
  · by_cases hin : i < n
    · simpa [hin.le, show i + 1 ≤ n by omega] using hadj i hin
    · obtain rfl : i = n := by omega
      simpa using hyp
  · by_cases hin : i ≤ n
    · simpa [hin] using hu i hin
    · simpa [hin] using hp
  · by_cases hin : i < n
    · simpa [hin.le, show i + 1 ≤ n by omega] using hinc i h1i hin
    · obtain rfl : i = n := by omega
      simpa using hℓ

/-- Induction along the increasing paths defining `𝒢`. -/
theorem explorationSet_induction {P : C → Prop} (h1 : P x₁)
    (hstep : ∀ y y', y ∈ explorationSet C u ℓ x₀ x₁ → y' ∈ explorationSet C u ℓ x₀ x₁ →
      (componentGraph C).Adj y y' → ℓ y < ℓ y' → P y → P y') :
    ∀ y ∈ explorationSet C u ℓ x₀ x₁, P y := by
  intro y hy
  obtain ⟨n, hn, γ, hadj, hu, h0, h1', rfl, hinc⟩ := mem_explorationSet_iff.1 hy
  have hmem : ∀ k, 1 ≤ k → k ≤ n → γ k ∈ explorationSet C u ℓ x₀ x₁ := fun k hk hkn =>
    mem_explorationSet_iff.2 ⟨k, hk, γ, fun i hi => hadj i (by omega),
      fun i hi => hu i (by omega), h0, h1', rfl, fun i hi hi' => hinc i hi (by omega)⟩
  have key : ∀ k, k + 1 ≤ n → P (γ (k + 1)) := by
    intro k
    induction k with
    | zero => intro _; simpa [h1'] using h1
    | succ k ih =>
      intro hk
      exact hstep _ _ (hmem (k + 1) (by omega) (by omega)) (hmem (k + 2) (by omega) hk)
        (hadj (k + 1) (by omega)) (hinc (k + 1) (by omega) (by omega)) (ih (by omega))
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m le_rfl

/-- `𝒢` is connected. -/
theorem connectedIn_explorationSet (hx₁ : x₁ ∈ explorationSet C u ℓ x₀ x₁) :
    ConnectedIn C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) := by
  have h : ∀ y ∈ explorationSet C u ℓ x₀ x₁,
      GraphReachIn (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) x₁ y :=
    explorationSet_induction (.refl hx₁) fun y y' hy hy' hadj hlt h =>
      h.trans (.of_adj hy hy' ⟨hy, hy', hadj, hlt.ne⟩)
  exact connectedIn_of_reachIn fun y hy => (h y hy).symm

end Exploration

section Pruned

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- The inclusion of `𝒢_tree` into the block-cut tree. -/
abbrev prunedHom (B₀ : ExplorationBlock C u ℓ x₀ x₁) :
    prunedTree C u ℓ x₀ x₁ B₀ →g
      blockCutTree C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) :=
  (SimpleGraph.Embedding.induce _).toHom

theorem prunedHom_injective (B₀ : ExplorationBlock C u ℓ x₀ x₁) :
    Function.Injective (prunedHom B₀) :=
  fun _ _ h => Subtype.ext h

theorem mem_support_map_prunedHom {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {a b : PrunedVertex C u ℓ x₀ x₁ B₀} (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk a b) {t} :
    t ∈ (W.map (prunedHom B₀)).support ↔ ∃ v ∈ W.support, v.val = t := by
  rw [SimpleGraph.Walk.support_map, List.mem_map]
  constructor <;> rintro ⟨v, hv, rfl⟩ <;> exact ⟨v, hv, rfl⟩

/-- `𝒢_tree` only removes descendants of pruning blocks: a neighbour in the block-cut tree of a
kept vertex `v` off the path from the root to `v` is kept, unless `v` is a pruning block. -/
theorem mem_keptVertices_of_adj {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {v : PrunedVertex C u ℓ x₀ x₁ B₀}
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v) (hW : W.IsPath)
    {w : BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)}
    (hvw : (blockCutTree C _ _).Adj v.val w) (hwW : ∀ v' ∈ W.support, v'.val ≠ w)
    (hprune : ∀ A, v.val = .inl A → ¬ IsPruningBlock C u ℓ (u x₀) A.val) :
    w ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) := by
  show ¬ _
  rintro ⟨A, hA, hne, hall⟩
  have hWf : (W.map (prunedHom B₀)).IsPath := hW.map (prunedHom_injective B₀)
  have hwWf : w ∉ (W.map (prunedHom B₀)).support := by
    rw [mem_support_map_prunedHom]
    rintro ⟨v', hv', rfl⟩
    exact hwW v' hv' rfl
  have hAm := hall _ ((SimpleGraph.Walk.concat_isPath_iff hvw).2 ⟨hWf, hwWf⟩)
  rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hAm
  rcases hAm with hAm | hAm
  · by_cases hAv : (Sum.inl A : BlockCutVertex C _ _) = v.val
    · exact hprune A hAv.symm hA
    · exact v.2 ⟨A, hA, isStrictAncestor_of_mem _ hWf hAm hAv⟩
  · exact hne hAm

/-- A kept neighbour, in the block-cut tree, of the leaf of a branch is its parent. -/
theorem eq_parent_of_adj {B₀ : ExplorationBlock C u ℓ x₀ x₁} {v : PrunedVertex C u ℓ x₀ x₁ B₀}
    (hvr : v ≠ prunedRoot C u ℓ x₀ x₁ B₀) (hleaf : ∃! w, (prunedTree C u ℓ x₀ x₁ B₀).Adj v w)
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v)
    {w : BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)}
    (hw : w ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀)) (hvw : (blockCutTree C _ _).Adj v.val w) :
    w = W.penultimate.val :=
  congrArg Subtype.val (eq_penultimate_of_unique_adj W (Ne.symm hvr) hleaf
    (show (prunedTree C u ℓ x₀ x₁ B₀).Adj v ⟨w, hw⟩ from hvw))

/-- Every neighbour, in the block-cut tree, of a leaf which is not a pruning block is its
parent. -/
theorem eq_parent_of_adj_of_not_pruning {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {v : PrunedVertex C u ℓ x₀ x₁ B₀} (hvr : v ≠ prunedRoot C u ℓ x₀ x₁ B₀)
    (hleaf : ∃! w, (prunedTree C u ℓ x₀ x₁ B₀).Adj v w)
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v) (hW : W.IsPath)
    (hprune : ∀ A, v.val = .inl A → ¬ IsPruningBlock C u ℓ (u x₀) A.val)
    {w : BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)}
    (hvw : (blockCutTree C _ _).Adj v.val w) : w = W.penultimate.val := by
  by_cases hwW : ∃ v' ∈ W.support, v'.val = w
  · obtain ⟨v', -, rfl⟩ := hwW
    exact eq_parent_of_adj hvr hleaf W v'.2 hvw
  · push Not at hwW
    exact eq_parent_of_adj hvr hleaf W (mem_keptVertices_of_adj W hW hvw hwW hprune) hvw

/-- A point of the leaf block of a branch, other than the parent cut-vertex, is an exit point. -/
theorem isPrunedExit_of_mem {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {v : PrunedVertex C u ℓ x₀ x₁ B₀} (hvr : v ≠ prunedRoot C u ℓ x₀ x₁ B₀)
    (hleaf : ∃! w, (prunedTree C u ℓ x₀ x₁ B₀).Adj v w)
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v) (hW : W.IsPath)
    {L : ExplorationBlock C u ℓ x₀ x₁} (hvL : v.val = .inl L)
    {c0 : {y // IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) y}}
    (hc : W.penultimate.val = .inr c0) {y : C} (hyL : y ∈ L.val) (hyc : y ≠ c0.val) :
    IsPrunedExit C u ℓ x₀ x₁ B₀ {x | x ∈ W.support} y := by
  have hnbr : ∀ w ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀), (blockCutTree C _ _).Adj v.val w →
      w = .inr c0 := fun w hw h => (eq_parent_of_adj hvr hleaf W hw h).trans hc
  refine ⟨v, W.end_mem_support, hvr, hleaf, ?_, fun v' hv' hyv' => ?_⟩
  · show y ∈ blockCutCarrier C v.val
    rw [hvL]
    exact hyL
  change y ∈ blockCutCarrier C v'.val at hyv'
  rcases hv'val : v'.val with B | y'
  · rw [hv'val] at hyv'
    have hyB : y ∈ B.val := hyv'
    by_cases hBL : B = L
    · exact Subtype.ext (hv'val.trans (hBL ▸ hvL.symm))
    exfalso
    have hcut := IsBlock.isCutVertex L.2 B.2 (fun h => hBL (Subtype.ext h).symm) hyL hyB
    let yc : {y // IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁) y} := ⟨y, hcut⟩
    have hBy : (blockCutTree C _ _).Adj (.inl B) (.inr yc) := hyB
    have hyv : (blockCutTree C _ _).Adj (.inr yc) v.val := by
      rw [hvL]
      exact hyL
    have hWf : (W.map (prunedHom B₀)).IsPath := hW.map (prunedHom_injective B₀)
    have hBWf : (.inl B) ∈ (W.map (prunedHom B₀)).support :=
      (mem_support_map_prunedHom W).2 ⟨v', hv', hv'val⟩
    have hQ : (SimpleGraph.Walk.cons hBy (SimpleGraph.Walk.cons hyv .nil)).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.cons_isPath_iff]
      simp [hvL, hBL]
    have heq := congrArg Subtype.val (blockCutTree_isAcyclic.path_unique
      ⟨_, hWf.dropUntil hBWf⟩ ⟨_, hQ⟩)
    have hyW : (.inr yc) ∈ (W.map (prunedHom B₀)).support := by
      apply SimpleGraph.Walk.support_dropUntil_subset_support _ hBWf
      simp only at heq
      rw [heq]
      simp
    obtain ⟨v'', hv'', hv''val⟩ := (mem_support_map_prunedHom W).1 hyW
    have := hnbr _ (hv''val ▸ v''.2) (by rw [hvL]; exact hyL)
    exact hyc (congrArg Subtype.val (Sum.inr_injective this))
  · rw [hv'val] at hyv'
    have hyy' : y = y'.val := hyv'
    subst hyy'
    have := hnbr _ (hv'val ▸ v'.2) (by rw [hvL]; exact hyL)
    exact absurd (congrArg Subtype.val (Sum.inr_injective this)) hyc

end Pruned

/-- step:5.27-tree (L2498-2501): the leaf of a finite leaf branch of `𝒢_tree` carries an exit
edge `(z, p)` with `u(p) ≠ u(x₀)`. -/
theorem leafExitStep : LeafExitStep := by
  intro ω C u ℓ hℓ x₀ x₁ hadj hu B₀ hx₁B S hS
  obtain ⟨v, hvr, hleaf, ⟨W, hW, rfl⟩, hfin⟩ := hS
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hu
  have hVc := connectedIn_explorationSet hx₁V
  have hWf : (W.map (prunedHom B₀)).IsPath := hW.map (prunedHom_injective B₀)
  have hcv : (prunedTree C u ℓ x₀ x₁ B₀).Adj W.penultimate v :=
    W.adj_penultimate (W.not_nil_of_ne (Ne.symm hvr))
  have hcT : (blockCutTree C _ _).Adj W.penultimate.val v.val := hcv
  rcases hvval : v.val with L | x
  · rw [hvval] at hcT
    rcases hcval : W.penultimate.val with B' | c0
    · rw [hcval] at hcT
      exact hcT.elim
    rw [hcval] at hcT
    have hc0L : c0.val ∈ L.val := hcT
    have hcr : W.penultimate ≠ prunedRoot C u ℓ x₀ x₁ B₀ := fun h => by
      have := congrArg Subtype.val h
      rw [hcval] at this
      exact Sum.inr_ne_inl this
    obtain ⟨b, hbW, hbv, hbc⟩ := exists_adj_penultimate W hW hcr
    have hbT : (blockCutTree C _ _).Adj b.val W.penultimate.val := hbc
    rw [hcval] at hbT
    rcases hbval : b.val with Bpp | b'
    swap
    · rw [hbval] at hbT
      exact hbT.elim
    rw [hbval] at hbT
    have hc0B : c0.val ∈ Bpp.val := hbT
    have hBL : Bpp ≠ L := fun h => hbv (Subtype.ext (hbval.trans (h ▸ hvval.symm)))
    have hexit : ∀ y ∈ L.val, y ≠ c0.val → IsPrunedExit C u ℓ x₀ x₁ B₀ {x | x ∈ W.support} y :=
      fun y hy hyc => isPrunedExit_of_mem hvr hleaf W hW hvval hcval hy hyc
    by_cases hpr : IsPruningBlock C u ℓ (u x₀) L.val
    · obtain ⟨y, hyL, z, hzy, hz, hℓzy⟩ := hpr
      by_cases hyc : y = c0.val
      · exfalso
        apply v.2
        refine ⟨Bpp, ⟨y, hyc ▸ hc0B, z, hzy, hz, hℓzy⟩, isStrictAncestor_of_mem _ hWf ?_ ?_⟩
        · exact (mem_support_map_prunedHom W).2 ⟨b, hbW, hbval⟩
        · show (Sum.inl Bpp : BlockCutVertex C _ _) ≠ v.val
          rw [hvval]
          exact fun h => hBL (Sum.inl_injective h)
      · exact ⟨y, z, hexit y hyL hyc, levelSet_of_mem_explorationSet (L.2.1.1 hyL), hzy.symm, hz⟩
    -- `L` is not a pruning block: `c0` is its only cut-vertex
    have hpar : ∀ w, (blockCutTree C _ _).Adj (.inl L) w → w = .inr c0 := by
      intro w hw
      refine (eq_parent_of_adj_of_not_pruning hvr hleaf W hW ?_ (w := w) ?_).trans hcval
      · intro A hA
        rw [hvval] at hA
        rw [← Sum.inl_injective hA]
        exact hpr
      · rw [hvval]
        exact hw
    have hcut : ∀ y ∈ L.val, IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
        (explorationSet C u ℓ x₀ x₁) y → y = c0.val := fun y hy hcy =>
      congrArg Subtype.val (Sum.inr_injective (hpar (.inr ⟨y, hcy⟩) hy))
    obtain ⟨w0, hw0L, hw0c⟩ :=
      IsBlock.exists_ne_of_ne L.2 Bpp.2 (fun h => hBL (Subtype.ext h).symm) hc0L hc0B
    -- `ℓ` is minimal on `L` exactly at `c0`
    have hmin : ∀ y ∈ explorationSet C u ℓ x₀ x₁, y ∈ L.val → y ≠ c0.val → ℓ c0.val < ℓ y := by
      refine explorationSet_induction ?_ ?_
      · intro hx₁L hx₁c
        refine absurd (hcut x₁ hx₁L (IsBlock.isCutVertex L.2 B₀.2 ?_ hx₁L hx₁B)) hx₁c
        intro h
        apply hvr
        exact Subtype.ext (hvval.trans (congrArg Sum.inl (Subtype.ext h)))
      · intro y y' hy hy' hyy' hlt ih hy'L hy'c
        by_cases hyL : y ∈ L.val
        · by_cases hyc : y = c0.val
          · rw [← hyc]
            exact hlt
          · exact (ih hyL hyc).trans hlt
        · exact absurd (hcut y' hy'L (IsBlock.isCutVertex_of_adj L.2 hy'L hy hyL
            ⟨hy', hy, hyy'.symm, hlt.ne'⟩)) hy'c
    have hfin' : L.val.Finite := by
      change (blockCutCarrier C v.val).Finite at hfin
      rw [hvval] at hfin
      exact hfin
    obtain ⟨z, hzL, hzmax⟩ := Set.exists_max_image L.val ℓ hfin' ⟨c0.val, hc0L⟩
    have hzc : z ≠ c0.val := by
      rintro rfl
      exact absurd (hzmax w0 hw0L) (not_le.2 (hmin w0 (L.2.1.1 hw0L) hw0L hw0c))
    have hzV := L.2.1.1 hzL
    -- a neighbour of `z` in `𝒢`, and harmonicity of `ℓ` at `z`
    obtain ⟨q, -⟩ := connectedIn_iff.1 L.2.1.2.1 z hzL c0.val hc0L
    have hqlen : 0 < q.length :=
      Nat.pos_of_ne_zero fun h => hzc (SimpleGraph.Walk.eq_of_length_eq_zero h)
    have hz1 := q.adj_getVert_succ (i := 0) hqlen
    rw [q.getVert_zero] at hz1
    have hharm : ∀ x, componentLaplacian C ℓ x = 0 := hℓ.1.1
    obtain ⟨⟨p, hzp, hlt⟩, -⟩ :=
      exists_above_below_of_harmonic (u := ℓ) (hharm z) rfl hz1.2.2.1 hz1.2.2.2.symm
    refine ⟨z, p, hexit z hzL hzc, levelSet_of_mem_explorationSet hzV, hzp, fun hp => hzc ?_⟩
    have hpV := mem_explorationSet_of_adj hzV hzp hp hlt
    have hpL : p ∉ L.val := fun h => absurd (hzmax p h) (not_le.2 hlt)
    exact hcut z hzL (IsBlock.isCutVertex_of_adj L.2 hzL hpV hpL ⟨hzV, hpV, hzp, hlt.ne⟩)
  · -- a leaf cut-vertex lies in a second block, which is kept
    exfalso
    rw [hvval] at hcT
    rcases hcval : W.penultimate.val with Bp | c'
    swap
    · rw [hcval] at hcT
      exact hcT.elim
    obtain ⟨B', hB', hxB', hne⟩ := exists_isBlock_ne hVc x.2 Bp.2
    have hpar := eq_parent_of_adj_of_not_pruning hvr hleaf W hW
      (fun A hA => by rw [hvval] at hA; exact (Sum.inr_ne_inl hA).elim) (w := .inl ⟨B', hB'⟩)
      (by rw [hvval]; exact hxB')
    rw [hcval] at hpar
    exact hne (congrArg Subtype.val (Sum.inl_injective hpar))

/-- A point is an exit point of at most one branch of `𝒢_tree` ending at a leaf. -/
theorem isPrunedExit_inj {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}
    {B₀ : ExplorationBlock C u ℓ x₀ x₁} {v v' : PrunedVertex C u ℓ x₀ x₁ B₀}
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v) (hW : W.IsPath)
    (W' : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v') (hW' : W'.IsPath)
    {z : C} (hz : IsPrunedExit C u ℓ x₀ x₁ B₀ {x | x ∈ W.support} z)
    (hz' : IsPrunedExit C u ℓ x₀ x₁ B₀ {x | x ∈ W'.support} z) :
    {x | x ∈ W.support} = {x | x ∈ W'.support} := by
  by_contra hSS'
  obtain ⟨e, he, her, hle, hze, huniq⟩ := hz
  obtain ⟨e', he', her', hle', hze', huniq'⟩ := hz'
  have hev := eq_end_of_unique_adj W hW he her hle
  have hev' := eq_end_of_unique_adj W' hW' he' her' hle'
  subst hev hev'
  by_cases hee : e = e'
  · subst hee
    have hacyc : (prunedTree C u ℓ x₀ x₁ B₀).IsAcyclic := blockCutTree_isAcyclic.induce _
    have := congrArg Subtype.val (hacyc.path_unique ⟨W, hW⟩ ⟨W', hW'⟩)
    simp only at this
    exact hSS' (by rw [this])
  have hnb : ∀ w, (prunedTree C u ℓ x₀ x₁ B₀).Adj e w → w ∈ W.support := fun w hw =>
    (eq_penultimate_of_unique_adj W (Ne.symm her) hle hw) ▸ W.getVert_mem_support _
  have hnb' : ∀ w, (prunedTree C u ℓ x₀ x₁ B₀).Adj e' w → w ∈ W'.support := fun w hw =>
    (eq_penultimate_of_unique_adj W' (Ne.symm her') hle' hw) ▸ W'.getVert_mem_support _
  change z ∈ blockCutCarrier C e.val at hze
  change z ∈ blockCutCarrier C e'.val at hze'
  rcases he1 : e.val with B | x <;> rcases he2 : e'.val with B' | x' <;>
    rw [he1] at hze <;> rw [he2] at hze'
  · have hzB : z ∈ B.val := hze
    have hzB' : z ∈ B'.val := hze'
    have hBB' : B.val ≠ B'.val := fun h =>
      hee (Subtype.ext (he1.trans ((congrArg Sum.inl (Subtype.ext h)).trans he2.symm)))
    let zc : {y // IsCutVertex C (explorationGraph C u ℓ x₀ x₁)
      (explorationSet C u ℓ x₀ x₁) y} := ⟨z, IsBlock.isCutVertex B.2 B'.2 hBB' hzB hzB'⟩
    have hnot : ∀ X : PrunedVertex C u ℓ x₀ x₁ B₀, X.val = .inr zc →
        X ∉ W.support ∧ X ∉ W'.support := by
      intro X hX
      have hzX : z ∈ prunedCarrier C u ℓ x₀ x₁ B₀ X := by
        change z ∈ blockCutCarrier C X.val
        rw [hX]
        rfl
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact Sum.inl_ne_inr (he1.symm.trans
          ((congrArg Subtype.val (huniq X h hzX)).symm.trans hX))
      · exact Sum.inl_ne_inr (he2.symm.trans
          ((congrArg Subtype.val (huniq' X h hzX)).symm.trans hX))
    have hWf : (W.map (prunedHom B₀)).IsPath := hW.map (prunedHom_injective B₀)
    have hW'f : (W'.map (prunedHom B₀)).IsPath := hW'.map (prunedHom_injective B₀)
    have h1 : (Sum.inr zc) ∉ (W.map (prunedHom B₀)).support := by
      rw [mem_support_map_prunedHom]
      rintro ⟨X, hX, hXv⟩
      exact (hnot X hXv).1 hX
    have h2 : (Sum.inr zc) ∉ (W'.map (prunedHom B₀)).support := by
      rw [mem_support_map_prunedHom]
      rintro ⟨X, hX, hXv⟩
      exact (hnot X hXv).2 hX
    have h3 : (Sum.inl B') ∉ (W.map (prunedHom B₀)).support := by
      rw [mem_support_map_prunedHom]
      rintro ⟨X, hX, hXv⟩
      have hXe : X = e' := Subtype.ext (hXv.trans he2.symm)
      subst hXe
      have : z ∈ prunedCarrier C u ℓ x₀ x₁ B₀ X := by
        change z ∈ blockCutCarrier C X.val
        rw [he2]
        exact hze'
      exact hee (huniq _ hX this).symm
    have hadj1 : (blockCutTree C _ _).Adj e.val (.inr zc) := by
      rw [he1]
      exact hzB
    have hadj2 : (blockCutTree C _ _).Adj (.inr zc) e'.val := by
      rw [he2]
      exact hzB'
    have hp : (((W.map (prunedHom B₀)).concat hadj1).concat hadj2).IsPath := by
      refine (SimpleGraph.Walk.concat_isPath_iff hadj2).2
        ⟨(SimpleGraph.Walk.concat_isPath_iff hadj1).2 ⟨hWf, h1⟩, fun h => ?_⟩
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact h3 (by rw [← he2]; exact h)
      · exact Sum.inl_ne_inr (he2.symm.trans h)
    have heq := congrArg Subtype.val
      (blockCutTree_isAcyclic.path_unique ⟨_, hp⟩ ⟨_, hW'f⟩)
    apply h2
    simp only at heq
    rw [← heq]
    simp [SimpleGraph.Walk.support_concat]
  · have hzB : z ∈ B.val := hze
    have hzx : z = x'.val := hze'
    have hT : (blockCutTree C _ _).Adj e.val e'.val := by
      rw [he1, he2]
      show x'.val ∈ B.val
      rw [← hzx]
      exact hzB
    exact hee (huniq e' (hnb e' hT) (by change z ∈ blockCutCarrier C e'.val; rw [he2]; exact hze')).symm
  · have hzx : z = x.val := hze
    have hzB' : z ∈ B'.val := hze'
    have hT : (blockCutTree C _ _).Adj e'.val e.val := by
      rw [he1, he2]
      show x.val ∈ B'.val
      rw [← hzx]
      exact hzB'
    exact hee (huniq' e (hnb' e hT) (by change z ∈ blockCutCarrier C e.val; rw [he1]; exact hze))
  · have hzx : z = x.val := hze
    have hzx' : z = x'.val := hze'
    exact hee (Subtype.ext (he1.trans ((congrArg Sum.inr (Subtype.ext
      (hzx.symm.trans hzx'))).trans he2.symm)))


/-- Distinct finite leaf branches of `𝒢_tree` have distinct exit points. -/
theorem exitsDistinctStep : ExitsDistinctStep := by
  intro ω C u ℓ x₀ x₁ _ _ B₀ _ S S' z z' hS hS' hz hz' hSS' hzz'
  subst hzz'
  obtain ⟨v, -, -, ⟨W, hW, rfl⟩, -⟩ := hS
  obtain ⟨v', -, -, ⟨W', hW', rfl⟩, -⟩ := hS'
  exact hSS' (isPrunedExit_inj W hW W' hW' hz hz')

end Rigidity.Proofs.Section5
