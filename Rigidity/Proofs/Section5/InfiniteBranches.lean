import Rigidity.Proofs.Section5.LeafExit
import LatticeProb.Graph.Konig

/-! # Lemma 5.28: rays and infinite leaves of `𝒢_tree`

Proof of `InfiniteBranchesStep` (prop:5.12 input of Lemma 5.28, corrected draft L2690) of the
carving in `Rigidity/Steps/Section5/FiniteBranches.lean`.

Each branch `S` of `𝒢_tree` which does not end at a finite leaf gets a tail set of points of `𝒢`:
* a ray `ρ` of `𝒢_tree`: the points carried by `ρ n`, `n ≥ N`; consecutive carriers meet, so the
  tail is connected, and it is infinite since `ρ` is injective;
* a path from the root to a leaf `v` with infinite carrier: `v` is a block `L` (cut-vertices carry
  one point), its parent a cut-vertex `c`, and the tail is `L \ {c}`, connected as `L` is
  biconnected.
For `N` large the tails are pairwise disjoint. A point `p` carried by two vertices `a, b` of the
block-cut tree joins them by a walk through `a, b` and `p` (as a cut-vertex), and the block-cut
tree is acyclic, so paths from the root are unique: two rays agreeing at no index `≥ n₀` carry no
common point beyond depth `n₀ + 2`, and a ray carries no point of a leaf block at depth `d`
beyond depth `d + 3`; two leaf tails meeting at `p` make `p` an exit point of both branches,
which then coincide (`isPrunedExit_inj`). König's lemma gives an infinite path in each tail.
`𝒢 ⊆ L_{u(x₀)}` is infinite and `u → 0`, so `u(x₀) = 0`, and `𝒢` is connected in `L_0`.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5 Filter Topology

namespace Rigidity.Proofs.Section5

section Konig

variable {α : Type*} {G : SimpleGraph α}

theorem GraphReachIn.mapLe {G' : SimpleGraph α} (hle : G ≤ G') {S : Set α} {x y : α}
    (h : GraphReachIn G S x y) : GraphReachIn G' S x y := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.mapLe hle, by rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hp⟩

/-- König's lemma: an infinite set, connected in a locally finite graph, contains an infinite
path. -/
theorem exists_ray_of_infinite [G.LocallyFinite] {X : Set α} (hX : X.Infinite) {x0 : α}
    (hconn : ∀ y ∈ X, GraphReachIn G X x0 y) :
    ∃ γ : ℕ → α, Function.Injective γ ∧ (∀ n, G.Adj (γ n) (γ (n + 1))) ∧ ∀ n, γ n ∈ X := by
  classical
  let P : List α → Prop := fun l => l.Nodup ∧
    (∀ i (h : i + 1 < l.length), G.Adj l[i] l[i + 1]) ∧ (∀ a ∈ l, a ∈ X) ∧
    ∀ h : 0 < l.length, l[0] = x0
  have hpre : ∀ l a, P (l ++ [a]) → P l := by
    rintro l a ⟨h1, h2, h3, h4⟩
    refine ⟨h1.sublist (List.sublist_append_left _ _), fun i hi => ?_,
      fun b hb => h3 b (List.mem_append_left _ hb), fun hl => ?_⟩
    · have := h2 i (by simp; omega)
      rwa [List.getElem_append_left (by omega), List.getElem_append_left hi] at this
    · have := h4 (by simp)
      rwa [List.getElem_append_left hl] at this
  have hfin : ∀ l, {a | P (l ++ [a])}.Finite := by
    intro l
    rcases Nat.eq_zero_or_pos l.length with hl | hl
    · rw [List.length_eq_zero_iff] at hl
      subst hl
      refine (Set.finite_singleton x0).subset fun a ha => ?_
      have := ha.2.2.2 (by simp)
      simpa using this
    · refine (G.neighborSet l[l.length - 1]).toFinite.subset fun a ha => ?_
      have := ha.2.1 (l.length - 1) (by simp; omega)
      simp only [List.getElem_append, show l.length - 1 < l.length by omega, dite_true,
        show ¬ (l.length - 1 + 1 < l.length) by omega, dite_false] at this
      simpa [show l.length - 1 + 1 - l.length = 0 by omega] using this
  have hball : ∀ n, {y | ∃ p : G.Walk x0 y, p.length ≤ n}.Finite := by
    intro n
    induction n with
    | zero =>
      refine (Set.finite_singleton x0).subset ?_
      rintro y ⟨p, hp⟩
      exact (SimpleGraph.Walk.eq_of_length_eq_zero (p := p) (by omega)).symm
    | succ n ih =>
      refine (ih.union (ih.biUnion fun y _ => (G.neighborSet y).toFinite)).subset ?_
      rintro y ⟨p, hp⟩
      by_cases hpn : p.length ≤ n
      · exact Or.inl ⟨p, hpn⟩
      · right
        have hnil : ¬ p.Nil := fun h => by
          rw [← SimpleGraph.Walk.length_eq_zero_iff] at h
          omega
        exact Set.mem_biUnion (x := p.penultimate)
          ⟨p.dropLast, by rw [SimpleGraph.Walk.length_dropLast]; omega⟩
          (p.adj_penultimate hnil)
  have hlong : ∀ n, ∃ l, P l ∧ n ≤ l.length := by
    intro n
    obtain ⟨y, hyX, hyB⟩ := (hX.sdiff (hball n)).nonempty
    obtain ⟨w, hw⟩ := hconn y hyX
    have hπ : w.bypass.IsPath := w.bypass_isPath
    have hπX : ∀ v ∈ w.bypass.support, v ∈ X :=
      fun v hv => hw v (w.support_bypass_subset_support hv)
    have hlen : n < w.bypass.length := by
      by_contra h
      exact hyB ⟨w.bypass, by omega⟩
    refine ⟨w.bypass.support, ⟨hπ.support_nodup, fun i hi => ?_, hπX, fun _ => ?_⟩, ?_⟩
    · rw [SimpleGraph.Walk.length_support] at hi
      rw [← w.bypass.getVert_eq_support_getElem (by omega),
        ← w.bypass.getVert_eq_support_getElem (by omega)]
      exact w.bypass.adj_getVert_succ (by omega)
    · rw [← w.bypass.getVert_eq_support_getElem (by omega)]
      exact w.bypass.getVert_zero
    · rw [SimpleGraph.Walk.length_support]
      omega
  obtain ⟨x, hx⟩ := LatticeProb.Graph.konig P hpre hfin hlong
  refine ⟨x, fun i j hij => ?_, fun n => ?_, fun n => ?_⟩
  · exact List.inj_on_of_nodup_map (hx (max i j + 1)).1 (List.mem_range.2 (by omega))
      (List.mem_range.2 (by omega)) hij
  · have h := (hx (n + 2)).2.1 n (by simp)
    simpa using h
  · exact (hx (n + 1)).2.2.1 _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)

end Konig

section Rays

variable {β : Type*} {T : SimpleGraph β}

/-- The walk `ρ 0, …, ρ n` along a sequence of adjacent vertices. -/
def rayPrefix (ρ : ℕ → β) (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))) : ∀ n, T.Walk (ρ 0) (ρ n)
  | 0 => .nil
  | n + 1 => (rayPrefix ρ hρ n).concat (hρ n)

theorem support_rayPrefix (ρ : ℕ → β) (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))) (n : ℕ) :
    (rayPrefix ρ hρ n).support = (List.range (n + 1)).map ρ := by
  induction n with
  | zero => simp [rayPrefix]
  | succ n ih => simp [rayPrefix, ih, List.range_succ (n := n + 1)]

theorem mem_support_rayPrefix {ρ : ℕ → β} {hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))} {n : ℕ} {x : β} :
    x ∈ (rayPrefix ρ hρ n).support ↔ ∃ i ≤ n, ρ i = x := by
  rw [support_rayPrefix]
  simp

theorem length_rayPrefix (ρ : ℕ → β) (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))) (n : ℕ) :
    (rayPrefix ρ hρ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rayPrefix, ih]

theorem isPath_rayPrefix {ρ : ℕ → β} (hinj : Function.Injective ρ)
    (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))) (n : ℕ) : (rayPrefix ρ hρ n).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, support_rayPrefix]
  exact List.nodup_range.map hinj

/-- In an acyclic graph, every walk passes through the vertices of the path with the same ends. -/
theorem support_subset_of_isAcyclic [DecidableEq β] (hT : T.IsAcyclic) {a b : β} (p : T.Walk a b)
    (hp : p.IsPath) (w : T.Walk a b) : ∀ x ∈ p.support, x ∈ w.support := by
  have h := congrArg Subtype.val (hT.path_unique ⟨p, hp⟩ ⟨w.bypass, w.bypass_isPath⟩)
  intro x hx
  simp only at h
  rw [h] at hx
  exact w.support_bypass_subset_support hx

/-- In an acyclic graph, an injective sequence of adjacent vertices has no chord. -/
theorem eq_succ_of_adj_ray (hT : T.IsAcyclic) {ρ : ℕ → β} (hinj : Function.Injective ρ)
    (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))) {i j : ℕ} (h : T.Adj (ρ i) (ρ j)) (hij : i < j) :
    j = i + 1 := by
  have hp : ((rayPrefix ρ hρ i).concat h).IsPath := by
    refine (SimpleGraph.Walk.concat_isPath_iff h).2 ⟨isPath_rayPrefix hinj hρ i, fun hm => ?_⟩
    obtain ⟨k, hk, hkj⟩ := mem_support_rayPrefix.1 hm
    have := hinj hkj
    omega
  have := congrArg (fun p => SimpleGraph.Walk.length p) (congrArg Subtype.val
    (hT.path_unique ⟨_, hp⟩ ⟨_, isPath_rayPrefix hinj hρ j⟩))
  simp only [SimpleGraph.Walk.length_concat, length_rayPrefix] at this
  omega

/-- In an acyclic graph, two injective sequences of adjacent vertices from the same vertex meet
only at the same index, after agreeing up to it. -/
theorem ray_eq_of_eq (hT : T.IsAcyclic) {ρ ρ' : ℕ → β} (hinj : Function.Injective ρ)
    (hinj' : Function.Injective ρ') (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1)))
    (hρ' : ∀ n, T.Adj (ρ' n) (ρ' (n + 1))) (h0 : ρ 0 = ρ' 0) {a b : ℕ} (hab : ρ a = ρ' b) :
    a = b ∧ ∀ i ≤ a, ρ i = ρ' i := by
  have hp' : ((rayPrefix ρ' hρ' b).copy h0.symm hab.symm).IsPath :=
    (SimpleGraph.Walk.isPath_copy _ _ _).2 (isPath_rayPrefix hinj' hρ' b)
  have heq := congrArg Subtype.val
    (hT.path_unique ⟨_, isPath_rayPrefix hinj hρ a⟩ ⟨_, hp'⟩)
  have hs := congrArg SimpleGraph.Walk.support heq
  simp only [SimpleGraph.Walk.support_copy, support_rayPrefix] at hs
  have hlen := congrArg List.length hs
  simp only [List.length_map, List.length_range] at hlen
  obtain rfl : a = b := by omega
  refine ⟨rfl, fun i hi => ?_⟩
  exact (List.map_inj_left.1 hs) i (List.mem_range.2 (by omega))

/-- In an acyclic graph, a path from `ρ 0` through `ρ k` has length at least `k`. -/
theorem le_length_of_mem_ray [DecidableEq β] (hT : T.IsAcyclic) {ρ : ℕ → β} (hinj : Function.Injective ρ)
    (hρ : ∀ n, T.Adj (ρ n) (ρ (n + 1))) {w : β} (p : T.Walk (ρ 0) w) (hp : p.IsPath) {k : ℕ}
    (hk : ρ k ∈ p.support) : k ≤ p.length := by
  have heq := congrArg Subtype.val
    (hT.path_unique ⟨_, hp.takeUntil hk⟩ ⟨_, isPath_rayPrefix hinj hρ k⟩)
  have hlen := congrArg SimpleGraph.Walk.length heq
  simp only [length_rayPrefix] at hlen
  rw [← hlen]
  exact p.length_takeUntil_le_length hk

end Rays

section BlockCutRays

variable {ω : Configuration 2} {C : OpenComponent ω} {G : SimpleGraph C} {V : Set C}

theorem blockCutCarrier_subset (a : BlockCutVertex C G V) : blockCutCarrier C a ⊆ V := by
  rcases a with B | y
  · exact B.2.1.1
  · rintro x rfl
    exact y.2.1

theorem connectedIn_blockCutCarrier (a : BlockCutVertex C G V) :
    ConnectedIn C G (blockCutCarrier C a) := by
  rcases a with B | y
  · exact B.2.1.2.1
  · refine connectedIn_iff.2 fun x hx z hz => ?_
    have hx' : x = y.val := hx
    have hz' : z = y.val := hz
    subst hx' hz'
    exact .refl rfl

theorem exists_mem_blockCutCarrier_of_adj {a b : BlockCutVertex C G V}
    (h : (blockCutTree C G V).Adj a b) :
    ∃ y, y ∈ blockCutCarrier C a ∧ y ∈ blockCutCarrier C b := by
  rcases a with B | y <;> rcases b with B' | y'
  · exact h.elim
  · exact ⟨y'.val, h, rfl⟩
  · exact ⟨y.val, rfl, h⟩
  · exact h.elim

/-- A point carried by two vertices of the block-cut tree joins them through itself. -/
theorem exists_walk_of_mem_blockCutCarrier {a b : BlockCutVertex C G V} {p : C}
    (ha : p ∈ blockCutCarrier C a) (hb : p ∈ blockCutCarrier C b) :
    ∃ Q : (blockCutTree C G V).Walk a b, ∀ t ∈ Q.support, t = a ∨ t = b ∨
      ∃ hp : IsCutVertex C G V p, t = .inr ⟨p, hp⟩ := by
  rcases a with B | y <;> rcases b with B' | y'
  · by_cases hBB : B = B'
    · subst hBB
      exact ⟨.nil, by simp⟩
    · have hp := IsBlock.isCutVertex B.2 B'.2 (fun h => hBB (Subtype.ext h)) ha hb
      refine ⟨.cons (show (blockCutTree C G V).Adj (.inl B) (.inr ⟨p, hp⟩) from ha)
        (.cons (show (blockCutTree C G V).Adj (.inr ⟨p, hp⟩) (.inl B') from hb) .nil),
        fun t ht => ?_⟩
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨hp, rfl⟩)
      · exact Or.inr (Or.inl rfl)
  · have hp : p = y'.val := hb
    subst hp
    refine ⟨.cons (show (blockCutTree C G V).Adj (.inl B) (.inr y') from ha) .nil,
      fun t ht => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl rfl)]
  · have hp : p = y.val := ha
    subst hp
    refine ⟨.cons (show (blockCutTree C G V).Adj (.inr y) (.inl B') from hb) .nil,
      fun t ht => ?_⟩
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl rfl)]
  · have hp : p = y.val := ha
    have hp' : p = y'.val := hb
    obtain rfl : y = y' := Subtype.ext (hp.symm.trans hp')
    exact ⟨.nil, by simp⟩

/-- The points carried by `ρ n`, `n ≥ N`. -/
def rayTail (ρ : ℕ → BlockCutVertex C G V) (N : ℕ) : Set C :=
  {x | ∃ n, N ≤ n ∧ x ∈ blockCutCarrier C (ρ n)}

theorem rayTail_subset (ρ : ℕ → BlockCutVertex C G V) (N : ℕ) : rayTail ρ N ⊆ V :=
  fun _ ⟨_, _, hx⟩ => blockCutCarrier_subset _ hx

theorem connectedIn_rayTail {ρ : ℕ → BlockCutVertex C G V}
    (hρ : ∀ n, (blockCutTree C G V).Adj (ρ n) (ρ (n + 1))) (N : ℕ) :
    ConnectedIn C G (rayTail ρ N) := by
  obtain ⟨z, hz, -⟩ := exists_mem_blockCutCarrier_of_adj (hρ N)
  have key : ∀ k, ∀ x ∈ blockCutCarrier C (ρ (N + k)), GraphReachIn G (rayTail ρ N) x z := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact (connectedIn_iff.1 (connectedIn_blockCutCarrier (ρ N)) x hx z hz).mono
        fun y hy => ⟨N, le_rfl, hy⟩
    | succ k ih =>
      intro x hx
      obtain ⟨y, hy, hy'⟩ := exists_mem_blockCutCarrier_of_adj (hρ (N + k))
      refine GraphReachIn.trans ?_ (ih y hy)
      exact (connectedIn_iff.1 (connectedIn_blockCutCarrier (ρ (N + (k + 1)))) x hx y
        hy').mono fun w hw => ⟨N + (k + 1), by omega, hw⟩
  refine connectedIn_of_reachIn (z := z) fun x ⟨n, hn, hx⟩ => ?_
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
  exact key k x hx

theorem infinite_rayTail {ρ : ℕ → BlockCutVertex C G V} (hinj : Function.Injective ρ) (N : ℕ) :
    (rayTail ρ N).Infinite := by
  intro hfin
  have h1 : {B : {S // IsBlock C G V S} | B.val ⊆ rayTail ρ N}.Finite :=
    hfin.finite_subsets.preimage Subtype.val_injective.injOn
  have h2 : {y : {y // IsCutVertex C G V y} | y.val ∈ rayTail ρ N}.Finite :=
    hfin.preimage Subtype.val_injective.injOn
  have hF : {a : BlockCutVertex C G V | blockCutCarrier C a ⊆ rayTail ρ N}.Finite := by
    refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
    rintro (B | y) h
    · exact Or.inl ⟨B, h, rfl⟩
    · exact Or.inr ⟨y, h (Set.mem_singleton _), rfl⟩
  refine Set.infinite_of_injective_forall_mem (f := fun n => ρ (N + n))
    (fun i j h => by have := hinj h; omega) (fun n => ?_) hF
  intro x hx
  exact ⟨N + n, by omega, hx⟩

/-- Two rays of the block-cut tree from the same vertex, differing at index `n₀`, carry no
common point beyond `n₀ + 2`. -/
theorem disjoint_rayTail {ρ ρ' : ℕ → BlockCutVertex C G V} (hinj : Function.Injective ρ)
    (hinj' : Function.Injective ρ') (hρ : ∀ n, (blockCutTree C G V).Adj (ρ n) (ρ (n + 1)))
    (hρ' : ∀ n, (blockCutTree C G V).Adj (ρ' n) (ρ' (n + 1))) (h0 : ρ 0 = ρ' 0) {n₀ : ℕ}
    (hn₀ : ρ n₀ ≠ ρ' n₀) {N : ℕ} (hN : n₀ + 2 ≤ N) : Disjoint (rayTail ρ N) (rayTail ρ' N) := by
  classical
  have hT : (blockCutTree C G V).IsAcyclic := blockCutTree_isAcyclic
  rw [Set.disjoint_left]
  rintro p ⟨m, hm, hpm⟩ ⟨m', hm', hpm'⟩
  obtain ⟨Q, hQ⟩ := exists_walk_of_mem_blockCutCarrier hpm' hpm
  have hsub := support_subset_of_isAcyclic hT _ (isPath_rayPrefix hinj hρ m)
    (((rayPrefix ρ' hρ' m').append Q).copy h0.symm rfl)
  have hmem := hsub _ (mem_support_rayPrefix.2 ⟨n₀, by omega, rfl⟩)
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.mem_support_append_iff] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨j, -, hj⟩ := mem_support_rayPrefix.1 hmem
    obtain ⟨-, hall⟩ := ray_eq_of_eq hT hinj hinj' hρ hρ' h0 hj.symm
    exact hn₀ (hall n₀ le_rfl)
  rcases hQ _ hmem with h | h | ⟨hp, h⟩
  · obtain ⟨-, hall⟩ := ray_eq_of_eq hT hinj hinj' hρ hρ' h0 h
    exact hn₀ (hall n₀ le_rfl)
  · have := hinj h
    omega
  · rcases hρm : ρ m with B | y
    · rw [hρm] at hpm
      have hadj : (blockCutTree C G V).Adj (ρ n₀) (ρ m) := by
        rw [h, hρm]
        exact hpm
      have := eq_succ_of_adj_ray hT hinj hρ hadj (by omega)
      omega
    · rw [hρm] at hpm
      have hpy : p = y.val := hpm
      have : ρ n₀ = ρ m := by
        rw [h, hρm]
        congr 1
        exact Subtype.ext hpy
      have := hinj this
      omega

/-- A ray of the block-cut tree carries no point of the end of a path of length `d` from its
start beyond `d + 3`. -/
theorem disjoint_rayTail_blockCutCarrier {ρ : ℕ → BlockCutVertex C G V}
    (hinj : Function.Injective ρ) (hρ : ∀ n, (blockCutTree C G V).Adj (ρ n) (ρ (n + 1)))
    {a : BlockCutVertex C G V} (W : (blockCutTree C G V).Walk (ρ 0) a) (hW : W.IsPath) {N : ℕ}
    (hN : W.length + 3 ≤ N) : Disjoint (rayTail ρ N) (blockCutCarrier C a) := by
  classical
  have hT : (blockCutTree C G V).IsAcyclic := blockCutTree_isAcyclic
  rw [Set.disjoint_left]
  rintro p ⟨m, hm, hpm⟩ hpa
  obtain ⟨Q, hQ⟩ := exists_walk_of_mem_blockCutCarrier hpa hpm
  have hsub := support_subset_of_isAcyclic hT _ (isPath_rayPrefix hinj hρ m) (W.append Q)
  have key : ∀ k, m - 2 ≤ k → k < m → ∃ hp : IsCutVertex C G V p, ρ k = .inr ⟨p, hp⟩ := by
    intro k hk hkm
    have hmem := hsub _ (mem_support_rayPrefix.2 ⟨k, by omega, rfl⟩)
    rw [SimpleGraph.Walk.mem_support_append_iff] at hmem
    rcases hmem with hmem | hmem
    · have := le_length_of_mem_ray hT hinj hρ W hW hmem
      omega
    rcases hQ _ hmem with h | h | h
    · have := le_length_of_mem_ray hT hinj hρ W hW (by rw [h]; exact W.end_mem_support)
      omega
    · have := hinj h
      omega
    · exact h
  obtain ⟨hp1, h1⟩ := key (m - 1) (by omega) (by omega)
  obtain ⟨hp2, h2⟩ := key (m - 2) le_rfl (by omega)
  have := hinj (h1.trans h2.symm)
  omega

end BlockCutRays

section Branches

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- A branch of `𝒢_tree`: a ray from the root, or a path from the root to a leaf. -/
abbrev BranchDatum (B₀ : ExplorationBlock C u ℓ x₀ x₁) : Type :=
  (ℕ → PrunedVertex C u ℓ x₀ x₁ B₀) ⊕
    (Σ v : PrunedVertex C u ℓ x₀ x₁ B₀,
      (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v)

/-- The datum `d` describes the branch `S`, which does not end at a finite leaf. -/
def IsBranchDatum {B₀ : ExplorationBlock C u ℓ x₀ x₁} (S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)) :
    BranchDatum B₀ → Prop
  | .inl ρ => Function.Injective ρ ∧ ρ 0 = prunedRoot C u ℓ x₀ x₁ B₀ ∧
      (∀ n, (prunedTree C u ℓ x₀ x₁ B₀).Adj (ρ n) (ρ (n + 1))) ∧ S = Set.range ρ
  | .inr ⟨v, W⟩ => v ≠ prunedRoot C u ℓ x₀ x₁ B₀ ∧
      (∃! w, (prunedTree C u ℓ x₀ x₁ B₀).Adj v w) ∧ W.IsPath ∧ S = {x | x ∈ W.support} ∧
      (prunedCarrier C u ℓ x₀ x₁ B₀ v).Infinite

/-- The tail of a branch: points carried by a ray beyond depth `N`, or the leaf block minus its
parent cut-vertex. -/
def branchTail {B₀ : ExplorationBlock C u ℓ x₀ x₁} : BranchDatum B₀ → ℕ → Set C
  | .inl ρ, N => rayTail (fun n => (ρ n).val) N
  | .inr ⟨v, W⟩, _ =>
      prunedCarrier C u ℓ x₀ x₁ B₀ v \ prunedCarrier C u ℓ x₀ x₁ B₀ W.penultimate

theorem exists_isBranchDatum {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)} (hS : IsPrunedBranch C u ℓ x₀ x₁ B₀ S)
    (hS' : ¬ IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S) : ∃ d, IsBranchDatum S d := by
  rcases hS with ⟨v, hvr, hleaf, W, hW, hSW⟩ | ⟨ρ, hinj, h0, hadj, hSρ⟩
  · exact ⟨.inr ⟨v, W⟩, hvr, hleaf, hW, hSW, fun hfin => hS' ⟨v, hvr, hleaf, ⟨W, hW, hSW⟩, hfin⟩⟩
  · exact ⟨.inl ρ, hinj, h0, hadj, hSρ⟩

/-- A leaf with infinite carrier is a block, and its parent a cut-vertex. -/
theorem exists_leaf_block {B₀ : ExplorationBlock C u ℓ x₀ x₁} {v : PrunedVertex C u ℓ x₀ x₁ B₀}
    (hvr : v ≠ prunedRoot C u ℓ x₀ x₁ B₀)
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v)
    (hinf : (prunedCarrier C u ℓ x₀ x₁ B₀ v).Infinite) :
    ∃ L c0, v.val = .inl L ∧ W.penultimate.val = .inr c0 := by
  have hcT : (blockCutTree C _ _).Adj W.penultimate.val v.val :=
    W.adj_penultimate (W.not_nil_of_ne (Ne.symm hvr))
  rcases hv : v.val with L | x
  · rw [hv] at hcT
    rcases hc : W.penultimate.val with B' | c0
    · rw [hc] at hcT
      exact hcT.elim
    · exact ⟨L, c0, rfl, rfl⟩
  · refine absurd ?_ hinf
    change (blockCutCarrier C v.val).Finite
    rw [hv]
    exact Set.finite_singleton _

theorem branchTail_props {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)} {d : BranchDatum B₀} (hd : IsBranchDatum S d)
    (N : ℕ) : (branchTail d N).Infinite ∧
      ConnectedIn C (explorationGraph C u ℓ x₀ x₁) (branchTail d N) ∧
      branchTail d N ⊆ explorationSet C u ℓ x₀ x₁ := by
  rcases d with ρ | ⟨v, W⟩
  · obtain ⟨hinj, -, hadj, -⟩ := hd
    exact ⟨infinite_rayTail (Subtype.val_injective.comp hinj) N, connectedIn_rayTail hadj N,
      rayTail_subset _ N⟩
  · obtain ⟨hvr, -, -, -, hinf⟩ := hd
    obtain ⟨L, c0, hv, hc⟩ := exists_leaf_block hvr W hinf
    change (blockCutCarrier C v.val \ blockCutCarrier C W.penultimate.val).Infinite ∧
      ConnectedIn C _ (blockCutCarrier C v.val \ blockCutCarrier C W.penultimate.val) ∧
      blockCutCarrier C v.val \ blockCutCarrier C W.penultimate.val ⊆ _
    have hinf' : (blockCutCarrier C v.val).Infinite := hinf
    rw [hv] at hinf'
    rw [hv, hc]
    exact ⟨hinf'.sdiff (Set.finite_singleton _), BiconnectedIn.connectedIn_diff L.2.1 c0.val,
      Set.sdiff_subset.trans L.2.1.1⟩

/-- A point of the tail of a branch ending at a leaf is an exit point of the branch. -/
theorem isPrunedExit_of_mem_branchTail {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {v : PrunedVertex C u ℓ x₀ x₁ B₀} (hvr : v ≠ prunedRoot C u ℓ x₀ x₁ B₀)
    (hleaf : ∃! w, (prunedTree C u ℓ x₀ x₁ B₀).Adj v w)
    (W : (prunedTree C u ℓ x₀ x₁ B₀).Walk (prunedRoot C u ℓ x₀ x₁ B₀) v) (hW : W.IsPath)
    (hinf : (prunedCarrier C u ℓ x₀ x₁ B₀ v).Infinite) {p : C}
    (hp : p ∈ prunedCarrier C u ℓ x₀ x₁ B₀ v \ prunedCarrier C u ℓ x₀ x₁ B₀ W.penultimate) :
    IsPrunedExit C u ℓ x₀ x₁ B₀ {x | x ∈ W.support} p := by
  obtain ⟨L, c0, hv, hc⟩ := exists_leaf_block hvr W hinf
  change p ∈ blockCutCarrier C v.val \ blockCutCarrier C W.penultimate.val at hp
  rw [hv, hc] at hp
  exact isPrunedExit_of_mem hvr hleaf W hW hv hc hp.1 hp.2

theorem exists_disjoint_branchTail {B₀ : ExplorationBlock C u ℓ x₀ x₁}
    {S S' : Set (PrunedVertex C u ℓ x₀ x₁ B₀)} {d d' : BranchDatum B₀}
    (hd : IsBranchDatum S d) (hd' : IsBranchDatum S' d') (hne : S ≠ S') :
    ∃ N₀, ∀ N ≥ N₀, Disjoint (branchTail d N) (branchTail d' N) := by
  rcases d with ρ | ⟨v, W⟩ <;> rcases d' with ρ' | ⟨v', W'⟩
  · obtain ⟨hinj, h0, hadj, rfl⟩ := hd
    obtain ⟨hinj', h0', hadj', rfl⟩ := hd'
    obtain ⟨n₀, hn₀⟩ : ∃ n, ρ n ≠ ρ' n := by
      by_contra h
      push Not at h
      exact hne (by rw [show ρ = ρ' from funext h])
    exact ⟨n₀ + 2, fun N hN => disjoint_rayTail (ρ := fun n => (ρ n).val)
      (ρ' := fun n => (ρ' n).val) (Subtype.val_injective.comp hinj)
      (Subtype.val_injective.comp hinj') hadj hadj' (congrArg Subtype.val (h0.trans h0'.symm))
      (fun h => hn₀ (Subtype.ext h)) hN⟩
  · obtain ⟨hinj, h0, hadj, -⟩ := hd
    obtain ⟨-, -, hW', -, -⟩ := hd'
    refine ⟨W'.length + 3, fun N hN => ?_⟩
    have hWf := (SimpleGraph.Walk.isPath_copy _ (congrArg Subtype.val h0).symm rfl).2
      (hW'.map (prunedHom_injective B₀))
    exact (disjoint_rayTail_blockCutCarrier (ρ := fun n => (ρ n).val)
      (Subtype.val_injective.comp hinj) hadj _ hWf
      (by
        rw [SimpleGraph.Walk.length_copy]
        exact Nat.le_trans (Nat.add_le_add_right (le_of_eq (SimpleGraph.Walk.length_map _ _)) 3)
          hN)).mono_right
      Set.sdiff_subset
  · obtain ⟨-, -, hW, -, -⟩ := hd
    obtain ⟨hinj', h0', hadj', -⟩ := hd'
    refine ⟨W.length + 3, fun N hN => ?_⟩
    have hWf := (SimpleGraph.Walk.isPath_copy _ (congrArg Subtype.val h0').symm rfl).2
      (hW.map (prunedHom_injective B₀))
    exact ((disjoint_rayTail_blockCutCarrier (ρ := fun n => (ρ' n).val)
      (Subtype.val_injective.comp hinj') hadj' _ hWf
      (by
        rw [SimpleGraph.Walk.length_copy]
        exact Nat.le_trans (Nat.add_le_add_right (le_of_eq (SimpleGraph.Walk.length_map _ _)) 3)
          hN)).mono_right
      Set.sdiff_subset).symm
  · obtain ⟨hvr, hleaf, hW, rfl, hinf⟩ := hd
    obtain ⟨hvr', hleaf', hW', rfl, hinf'⟩ := hd'
    refine ⟨0, fun N _ => Set.disjoint_left.2 fun p hp hp' => hne ?_⟩
    exact isPrunedExit_inj W hW W' hW'
      (isPrunedExit_of_mem_branchTail hvr hleaf W hW hinf hp)
      (isPrunedExit_of_mem_branchTail hvr' hleaf' W' hW' hinf' hp')

end Branches

/-- prop:5.12 input (L2690): finitely many rays of `𝒢_tree` from the root and branches ending at
an infinite leaf block give as many disjoint infinite paths in one connected component of
`L_0`. -/
theorem infiniteBranchesStep : InfiniteBranchesStep := by
  intro ω C f u hu ℓ x₀ x₁ hadj hux B₀ _ s hs hbr
  classical
  have hx₁V := x₁_mem_explorationSet (ℓ := ℓ) hadj hux
  have hd : ∀ S ∈ s, ∃ d : BranchDatum B₀, IsBranchDatum S d :=
    fun S hS => exists_isBranchDatum (hbr S hS).1 (hbr S hS).2
  haveI : Nonempty (BranchDatum B₀) := ⟨.inl fun _ => prunedRoot C u ℓ x₀ x₁ B₀⟩
  haveI : Nonempty C := ⟨x₁⟩
  choose! d hd using hd
  have h2 : ∀ S ∈ s, ∀ S' ∈ s, S ≠ S' →
      ∃ N₀, ∀ N ≥ N₀, Disjoint (branchTail (d S) N) (branchTail (d S') N) :=
    fun S hS S' hS' hne => exists_disjoint_branchTail (hd S hS) (hd S' hS') hne
  choose! N₀ hN₀ using h2
  let N := (s ×ˢ s).sup fun q => N₀ q.1 q.2
  have hdisj : ∀ S ∈ s, ∀ S' ∈ s, S ≠ S' →
      Disjoint (branchTail (d S) N) (branchTail (d S') N) := fun S hS S' hS' hne =>
    hN₀ S hS S' hS' hne N (Finset.le_sup (f := fun q => N₀ q.1 q.2) (b := (S, S'))
      (Finset.mem_product.2 ⟨hS, hS'⟩))
  have hray : ∀ S ∈ s, ∃ γ : ℕ → C, Function.Injective γ ∧
      (∀ n, (componentGraph C).Adj (γ n) (γ (n + 1))) ∧ ∀ n, γ n ∈ branchTail (d S) N := by
    intro S hS
    obtain ⟨hinf, hconn, -⟩ := branchTail_props (hd S hS) N
    obtain ⟨x0, hx0⟩ := hinf.nonempty
    exact exists_ray_of_infinite (G := componentGraph C) hinf fun y hy =>
      GraphReachIn.mapLe (G := explorationGraph C u ℓ x₀ x₁) (G' := componentGraph C)
        (fun _ _ h => h.2.2.1) (connectedIn_iff.1 hconn x0 hx0 y hy)
  choose! γ hγ using hray
  obtain ⟨S0, hS0⟩ := hs
  have ha : u x₀ = 0 := by
    by_contra ha
    have hev := hu.2.eventually (Metric.ball_mem_nhds (0 : ℝ) (abs_pos.2 ha))
    rw [Filter.eventually_cofinite] at hev
    have hfinV : (explorationSet C u ℓ x₀ x₁).Finite := hev.subset fun y hy => by
      simp [levelSet_of_mem_explorationSet hy]
    exact (branchTail_props (hd S0 hS0) N).1 (hfinV.subset (branchTail_props (hd S0 hS0) N).2.2)
  have hjoin : ∀ y ∈ explorationSet C u ℓ x₀ x₁, JoinedIn C (levelSet u 0) x₁ y := by
    intro y hy
    obtain ⟨p, hp⟩ := connectedIn_iff.1 (connectedIn_explorationSet hx₁V) x₁ hx₁V y hy
    have hle : explorationGraph C u ℓ x₀ x₁ ≤ componentGraph C := fun _ _ h => h.2.2.1
    have hp0 : ∀ v ∈ (p.mapLe hle).support, v ∈ levelSet u 0 := by
      intro v hv
      rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
      show u v = 0
      rw [levelSet_of_mem_explorationSet (hp v hv), ha]
    exact ⟨hp0 _ (p.mapLe hle).start_mem_support, hp0 _ (p.mapLe hle).end_mem_support,
      ⟨(p.mapLe hle).induce _ hp0⟩⟩
  refine ⟨{y | JoinedIn C (levelSet u 0) x₁ y}, ⟨x₁, by simp [levelSet, hux, ha], rfl⟩, ?_⟩
  let e := s.equivFin
  refine ⟨fun j => γ (e.symm j).1, fun j => ⟨(hγ _ (e.symm j).2).1, (hγ _ (e.symm j).2).2.1,
    fun n => hjoin _ ((branchTail_props (hd _ (e.symm j).2) N).2.2
      ((hγ _ (e.symm j).2).2.2 n))⟩, fun j j' hjj' => ?_⟩
  have hne : (e.symm j).1 ≠ (e.symm j').1 := fun h => hjj' (e.symm.injective (Subtype.ext h))
  rw [Set.disjoint_left]
  rintro x ⟨n, rfl⟩ ⟨n', hn'⟩
  have hn'' : γ (e.symm j').1 n' = γ (e.symm j).1 n := hn'
  exact Set.disjoint_left.1 (hdisj _ (e.symm j).2 _ (e.symm j').2 hne)
    ((hγ _ (e.symm j).2).2.2 n) (hn'' ▸ (hγ _ (e.symm j').2).2.2 n')

end Rigidity.Proofs.Section5
