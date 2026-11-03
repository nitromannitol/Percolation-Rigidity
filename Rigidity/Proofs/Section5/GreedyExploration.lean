import Rigidity.Steps.Section5.LargeGradientSensitive
import Rigidity.Proofs.Section5.LeafExit

/-! # Lemma 5.27, Step 5: the greedy path of maximal flux

Proof of `GreedyExplorationStep` (step:5.27-explore, corrected draft L2563-2602, eq.
`lowerboundiin1410`) of the carving `Rigidity/Steps/Section5/LargeGradientSensitive.lean`.

Write `T` for the block-cut tree of `𝒢`, acyclic by `blockCutTree_isAcyclic`, rooted at `B₀`.
A *chain* of length `p` is a sequence `f 0 = B₀, f 1, …, f p` of distinct, consecutively adjacent
vertices of `T`. Paths of `T` are unique, so two chains ending at the same vertex coincide, the
strict ancestors of `f p` are `f 0, …, f (p - 1)`, a neighbour of `f p` off the chain has `f p` as
a strict ancestor, and a neighbour of `f p` on the chain is `f (p - 1)`.

The greedy path. From a block `B` with parent point `p` (`x₁` for the root), the candidates are the
cut-vertices of `B` other than `p`; Step 3 (`FluxBalance`) bounds the flux entering `B` at `p` by
their total incoming flux, and the path goes to a candidate `c` of maximal incoming flux. From `c`
the candidates are the children blocks of `c` in `𝒢_tree` of nonzero outgoing flux; Step 3 bounds
the incoming flux at `c` by their total outgoing flux, and the path goes to a candidate of maximal
outgoing flux. The path stops at the first block which is infinite or a pruning block: as long as
the flux is positive the candidates exist. Hence the flux at the `j`-th vertex is at least
`i₀ / ∏_{j' < j} m_{j'}`, `m_{j'}` the number of candidates at the `j'`-th vertex.

Branches. Every candidate is a child in `𝒢_tree`; for each step `j'` and each candidate `w` not on
the greedy path, the chain to `w` extends, through children chosen as long as they exist, to a
branch of `𝒢_tree` (a ray, or a path to a vertex without child, which is a leaf). Two such branches
are distinct (by uniqueness of chains, a branch through `w` and through `w'` would put `w` or `w'`
on the greedy path), so `∑ (m_{j'} - 1) ≤ C_branches` and, by `m ≤ e^{m - 1}`, every incoming flux
along the path is at least `i₀ e^{-C_branches}`.

The cut-vertices of the path are points of `𝒞_∞`, their cut-vertex property being part of the
link clause of `GreedyPath`: if `𝒢` has no cut-vertex, the greedy path is the root block alone.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5 Classical

namespace Rigidity.Proofs.Section5

namespace Greedy

/-! ### Chains in a graph -/

section Chains

variable {β : Type*} {T : SimpleGraph β}

/-- The walk `f 0, f 1, …, f n` along a sequence with consecutive adjacencies below `n`. -/
def chainWalk (f : ℕ → β) : ∀ n, (∀ t < n, T.Adj (f t) (f (t + 1))) → T.Walk (f 0) (f n)
  | 0, _ => .nil
  | n + 1, h => (chainWalk f n fun t ht => h t (by omega)).concat (h n (by omega))

theorem support_chainWalk (f : ℕ → β) : ∀ (n : ℕ) (h : ∀ t < n, T.Adj (f t) (f (t + 1))),
    (chainWalk f n h).support = (List.range (n + 1)).map f
  | 0, _ => rfl
  | n + 1, h => by
    rw [chainWalk, SimpleGraph.Walk.support_concat, support_chainWalk f n,
      List.range_succ (n := n + 1), List.map_append, List.map_singleton]

/-- `f` is a chain of `T` of length `n` from `r`: `f 0 = r, …, f n` are distinct and consecutive
ones are adjacent. -/
structure IsChain (T : SimpleGraph β) (r : β) (f : ℕ → β) (n : ℕ) : Prop where
  zero : f 0 = r
  inj : Set.InjOn f (Set.Iic n)
  adj : ∀ t < n, T.Adj (f t) (f (t + 1))

variable {r : β} {f g : ℕ → β} {p q : ℕ}

theorem IsChain.isPath (hf : IsChain T r f p) : (chainWalk f p hf.adj).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, support_chainWalk]
  refine List.Nodup.map_on (fun x hx y hy hxy => hf.inj ?_ ?_ hxy) List.nodup_range
  · rw [List.mem_range] at hx
    exact Set.mem_Iic.2 (by omega)
  · rw [List.mem_range] at hy
    exact Set.mem_Iic.2 (by omega)

/-- The walk of a chain, from `r`. -/
def IsChain.walk (hf : IsChain T r f p) : T.Walk r (f p) :=
  (chainWalk f p hf.adj).copy hf.zero rfl

theorem IsChain.walk_isPath (hf : IsChain T r f p) : hf.walk.IsPath :=
  (SimpleGraph.Walk.isPath_copy _ _ _).2 hf.isPath

theorem IsChain.support_walk (hf : IsChain T r f p) :
    hf.walk.support = (List.range (p + 1)).map f := by
  rw [IsChain.walk, SimpleGraph.Walk.support_copy, support_chainWalk]

theorem IsChain.mono (hf : IsChain T r f p) (hq : q ≤ p) : IsChain T r f q :=
  ⟨hf.zero, hf.inj.mono (Set.Iic_subset_Iic.2 hq), fun t ht => hf.adj t (by omega)⟩

theorem IsChain.congr (hf : IsChain T r f p) (hfg : ∀ t ≤ p, f t = g t) : IsChain T r g p := by
  refine ⟨by rw [← hfg 0 (Nat.zero_le _)]; exact hf.zero, fun a ha b hb h => hf.inj ha hb ?_,
    fun t ht => ?_⟩
  · rw [hfg a ha, hfg b hb]
    exact h
  · rw [← hfg t (by omega), ← hfg (t + 1) (by omega)]
    exact hf.adj t ht

/-- Two chains of an acyclic graph ending at the same vertex coincide. -/
theorem IsChain.unique (hT : T.IsAcyclic) (hf : IsChain T r f p) (hg : IsChain T r g q)
    (hfg : f p = g q) : p = q ∧ ∀ t ≤ p, f t = g t := by
  have key := hT.path_unique ⟨hf.walk, hf.walk_isPath⟩
    ⟨hg.walk.copy rfl hfg.symm, (SimpleGraph.Walk.isPath_copy _ _ _).2 hg.walk_isPath⟩
  have hs := congrArg (fun P : T.Path r (f p) => P.1.support) key
  simp only [SimpleGraph.Walk.support_copy, IsChain.support_walk] at hs
  have hpq : p = q := by simpa using congrArg List.length hs
  subst hpq
  refine ⟨rfl, fun t ht => ?_⟩
  have := congrArg (fun l => l[t]?) hs
  simpa [List.getElem?_range (show t < p + 1 by omega)] using this

/-- The strict ancestors of the end of a chain are its earlier vertices. -/
theorem IsChain.isStrictAncestor_iff (hT : T.IsAcyclic) (hf : IsChain T r f p) {a : β} :
    IsStrictAncestor T r a (f p) ↔ ∃ t < p, f t = a := by
  constructor
  · rintro ⟨hne, hall⟩
    have hm := hall hf.walk hf.walk_isPath
    rw [hf.support_walk, List.mem_map] at hm
    obtain ⟨t, ht, rfl⟩ := hm
    rw [List.mem_range] at ht
    refine ⟨t, lt_of_le_of_ne (by omega) ?_, rfl⟩
    rintro rfl
    exact hne rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun h => ht.ne (hf.inj (Set.mem_Iic.2 ht.le) (Set.mem_Iic.2 le_rfl) h),
      fun W hW => ?_⟩
    rw [show W = hf.walk from congrArg Subtype.val (hT.path_unique ⟨W, hW⟩ ⟨_, hf.walk_isPath⟩),
      hf.support_walk]
    exact List.mem_map.2 ⟨t, List.mem_range.2 (by omega), rfl⟩

/-- `f` up to `p`, then `y`. -/
def chainSnoc (f : ℕ → β) (p : ℕ) (y : β) : ℕ → β := fun t => if t ≤ p then f t else y

theorem chainSnoc_of_le {t : ℕ} {y : β} (ht : t ≤ p) : chainSnoc f p y t = f t := if_pos ht

theorem chainSnoc_succ {y : β} : chainSnoc f p y (p + 1) = y := if_neg (by omega)

theorem IsChain.snoc (hf : IsChain T r f p) {y : β} (hadj : T.Adj (f p) y)
    (hy : ∀ t ≤ p, f t ≠ y) : IsChain T r (chainSnoc f p y) (p + 1) := by
  refine ⟨by rw [chainSnoc_of_le (Nat.zero_le _)]; exact hf.zero, ?_, fun t ht => ?_⟩
  · intro a ha b hb h
    rw [Set.mem_Iic] at ha hb
    by_cases h1 : a ≤ p <;> by_cases h2 : b ≤ p <;>
      simp only [chainSnoc, h1, h2, ↓reduceIte] at h
    · exact hf.inj h1 h2 h
    · exact absurd h (hy a h1)
    · exact absurd h.symm (hy b h2)
    · omega
  · rcases Nat.lt_or_ge t p with h | h
    · rw [chainSnoc_of_le h.le, chainSnoc_of_le h]
      exact hf.adj t h
    · rw [show t = p by omega, chainSnoc_of_le le_rfl, chainSnoc_succ]
      exact hadj

/-- A vertex having the end of a chain as a strict ancestor is off the chain. -/
theorem IsChain.ne_of_isStrictAncestor (hT : T.IsAcyclic) (hf : IsChain T r f p) {y : β}
    (hy : IsStrictAncestor T r (f p) y) : ∀ t ≤ p, f t ≠ y := by
  rintro t ht rfl
  obtain ⟨s, hs, hsp⟩ := ((hf.mono ht).isStrictAncestor_iff hT).1 hy
  have := hf.inj (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 le_rfl) hsp
  omega

/-- A neighbour of the end of a chain off the chain has the end as a strict ancestor. -/
theorem IsChain.isStrictAncestor_of_ne (hT : T.IsAcyclic) (hf : IsChain T r f p) {y : β}
    (hadj : T.Adj (f p) y) (hy : ∀ t ≤ p, f t ≠ y) : IsStrictAncestor T r (f p) y := by
  have h := ((hf.snoc hadj hy).isStrictAncestor_iff hT (a := f p)).2
    ⟨p, by omega, chainSnoc_of_le le_rfl⟩
  rwa [chainSnoc_succ] at h

/-- A neighbour of the end of a chain on the chain is the previous vertex. -/
theorem IsChain.succ_eq_of_adj (hT : T.IsAcyclic) (hf : IsChain T r f p) {t : ℕ} (ht : t ≤ p)
    (hadj : T.Adj (f p) (f t)) : t + 1 = p := by
  have htp : t < p := lt_of_le_of_ne ht (by rintro rfl; exact hadj.ne rfl)
  have hg : IsChain T r (chainSnoc f t (f p)) (t + 1) :=
    (hf.mono ht).snoc hadj.symm fun s hs h => by
      have := hf.inj (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 le_rfl) h
      omega
  exact (hg.unique hT hf (by rw [chainSnoc_succ])).1

end Chains

/-! ### Branches of `𝒢_tree` through a chain -/

section Branches

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}

/-- The vertices of the block-cut tree of `𝒢`. -/
abbrev ExplorationNode (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C) : Type :=
  BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)

/-- The block-cut tree of `𝒢`. -/
abbrev explorationTree (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C) :
    SimpleGraph (ExplorationNode C u ℓ x₀ x₁) :=
  blockCutTree C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)

theorem explorationTree_isAcyclic : (explorationTree C u ℓ x₀ x₁).IsAcyclic :=
  blockCutTree_isAcyclic

variable (B₀ : ExplorationBlock C u ℓ x₀ x₁)

/-- The end of a chain from `B₀` is kept if no earlier vertex of the chain is a pruning block. -/
theorem mem_keptVertices_of_chain {f : ℕ → ExplorationNode C u ℓ x₀ x₁} {p : ℕ}
    (hf : IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) f p)
    (h : ∀ t < p, ∀ A, f t = .inl A → ¬ IsPruningBlock C u ℓ (u x₀) A.val) :
    f p ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) := by
  show ¬ _
  rintro ⟨A, hA, hanc⟩
  obtain ⟨t, ht, hft⟩ := (hf.isStrictAncestor_iff explorationTree_isAcyclic).1 hanc
  exact h t ht A hft hA

/-- A chain of kept vertices of length `p ≥ 1` extends, through children chosen as long as they
exist, to a branch of `𝒢_tree`; the points of the branch are ends of chains along `ρ`. -/
theorem exists_branch {f : ℕ → ExplorationNode C u ℓ x₀ x₁} {p : ℕ}
    (hf : IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) f p) (hp : 1 ≤ p)
    (hkept : ∀ t ≤ p, f t ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀)) :
    ∃ (S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)) (ρ : ℕ → ExplorationNode C u ℓ x₀ x₁),
      IsPrunedBranch C u ℓ x₀ x₁ B₀ S ∧ (∀ t ≤ p, ρ t = f t) ∧ (∃ x ∈ S, x.val = f p) ∧
      ∀ x ∈ S, ∃ q, IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) ρ q ∧ ρ q = x.val := by
  have hT := (explorationTree_isAcyclic : (explorationTree C u ℓ x₀ x₁).IsAcyclic)
  let d : ℕ → ExplorationNode C u ℓ x₀ x₁ := fun s => Nat.rec (f p)
    (fun _ v => if h : ∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ v w then h.choose else v) s
  have hdsucc : ∀ s, d (s + 1) =
      if h : ∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ (d s) w then h.choose else d s := fun s => rfl
  have hdchild : ∀ s, (∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ (d s) w) →
      IsTreeChild C u ℓ x₀ x₁ B₀ (d s) (d (s + 1)) := by
    intro s h
    rw [hdsucc, dif_pos h]
    exact h.choose_spec
  have hdkept : ∀ s, d s ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) := by
    intro s
    induction s with
    | zero => exact hkept p le_rfl
    | succ s ih =>
      rw [hdsucc]
      split_ifs with h
      · exact h.choose_spec.2.1
      · exact ih
  let ρ : ℕ → ExplorationNode C u ℓ x₀ x₁ := fun t => if t ≤ p then f t else d (t - p)
  have hρle : ∀ t ≤ p, ρ t = f t := fun t ht => if_pos ht
  have hρd : ∀ s, ρ (p + s) = d s := by
    intro s
    rcases s with _ | s
    · exact hρle p le_rfl
    · show (if p + (s + 1) ≤ p then f (p + (s + 1)) else d (p + (s + 1) - p)) = d (s + 1)
      rw [if_neg (by omega), show p + (s + 1) - p = s + 1 by omega]
  have hρkept : ∀ t, ρ t ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) := by
    intro t
    by_cases ht : t ≤ p
    · rw [hρle t ht]
      exact hkept t ht
    · show (if t ≤ p then f t else d (t - p)) ∈ _
      rw [if_neg ht]
      exact hdkept _
  have hchain : ∀ s, (∀ s' < s, ∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ (d s') w) →
      IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) ρ (p + s) := by
    intro s
    induction s with
    | zero => exact fun _ => hf.congr fun t ht => (hρle t ht).symm
    | succ s ih =>
      intro hs
      have hc := ih fun s' hs' => hs s' (by omega)
      have htc : IsTreeChild C u ℓ x₀ x₁ B₀ (ρ (p + s)) (ρ (p + s + 1)) := by
        rw [hρd, show p + s + 1 = p + (s + 1) by omega, hρd]
        exact hdchild s (hs s (by omega))
      refine (hc.snoc htc.2.2.1 (hc.ne_of_isStrictAncestor hT htc.2.2.2)).congr fun t ht => ?_
      rcases Nat.lt_or_ge t (p + s + 1) with h | h
      · exact chainSnoc_of_le (by omega)
      · rw [show t = p + s + 1 by omega, chainSnoc_succ]
  let ρ' : ℕ → PrunedVertex C u ℓ x₀ x₁ B₀ := fun t => ⟨ρ t, hρkept t⟩
  have hρ'0 : ρ' 0 = prunedRoot C u ℓ x₀ x₁ B₀ := Subtype.ext ((hf.congr fun t ht =>
    (hρle t ht).symm).zero)
  by_cases hall : ∀ s, ∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ (d s) w
  · -- a ray of `𝒢_tree`
    have hc : ∀ q, IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) ρ q := fun q =>
      (hchain q fun s' _ => hall s').mono (by omega)
    refine ⟨Set.range ρ', ρ, Or.inr ⟨ρ', fun a b h => ?_, hρ'0, fun n => (hc (n + 1)).adj n
      (by omega), rfl⟩, hρle, ⟨ρ' p, ⟨p, rfl⟩, hρle p le_rfl⟩, ?_⟩
    · exact (hc (max a b)).inj (Set.mem_Iic.2 (le_max_left _ _))
        (Set.mem_Iic.2 (le_max_right _ _)) (congrArg Subtype.val h)
    · rintro _ ⟨q, rfl⟩
      exact ⟨q, hc q, rfl⟩
  · -- a path to a leaf of `𝒢_tree`
    have hex : ∃ s, ¬ ∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ (d s) w := not_forall.1 hall
    set s₀ := Nat.find hex
    have hs₀ : ¬ ∃ w, IsTreeChild C u ℓ x₀ x₁ B₀ (d s₀) w := Nat.find_spec hex
    have hc := hchain s₀ fun s' hs' => not_not.1 (Nat.find_min hex hs')
    set L := p + s₀ with hL
    have hc' : IsChain (prunedTree C u ℓ x₀ x₁ B₀) (prunedRoot C u ℓ x₀ x₁ B₀) ρ' L :=
      ⟨hρ'0, fun a ha b hb h => hc.inj ha hb (congrArg Subtype.val h), fun t ht => hc.adj t ht⟩
    refine ⟨{x | x ∈ hc'.walk.support}, ρ, Or.inl ⟨ρ' L, fun h => ?_, ⟨ρ' (L - 1), ?_, ?_⟩,
      hc'.walk, hc'.walk_isPath, rfl⟩, hρle, ⟨ρ' p, ?_, hρle p le_rfl⟩, ?_⟩
    · have := hc'.inj (Set.mem_Iic.2 le_rfl) (Set.mem_Iic.2 (Nat.zero_le _)) (h.trans hρ'0.symm)
      omega
    · have := hc'.adj (L - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at this
      exact this.symm
    · intro w hw
      have hadj : (explorationTree C u ℓ x₀ x₁).Adj (ρ L) w.val := hw
      by_cases hon : ∃ t ≤ L, ρ t = w.val
      · obtain ⟨t, ht, hρt⟩ := hon
        rw [← hρt] at hadj
        have := hc.succ_eq_of_adj hT ht hadj
        exact Subtype.ext (by rw [← hρt, show t = L - 1 by omega])
      · push Not at hon
        refine absurd ⟨w.val, ?_⟩ hs₀
        have hanc := hc.isStrictAncestor_of_ne hT hadj hon
        rw [hρd] at hadj hanc
        exact ⟨hdkept s₀, w.2, hadj, hanc⟩
    · show ρ' p ∈ hc'.walk.support
      rw [hc'.support_walk]
      exact List.mem_map.2 ⟨p, List.mem_range.2 (by omega), rfl⟩
    · intro x hx
      change x ∈ hc'.walk.support at hx
      rw [hc'.support_walk, List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, hc.mono (by rw [List.mem_range] at hq; omega), rfl⟩

/-- The side children along a chain give distinct branches of `𝒢_tree`, so there are at most
`C_branches` of them. -/
theorem sum_card_side_le {Cbr : ℕ}
    (hbr : ∀ (n : ℕ) (b : Fin n → Set (PrunedVertex C u ℓ x₀ x₁ B₀)),
      (∀ k, IsPrunedBranch C u ℓ x₀ x₁ B₀ (b k)) → Function.Injective b → n ≤ Cbr)
    {v : ℕ → ExplorationNode C u ℓ x₀ x₁} {m : ℕ}
    (hv : IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) v m)
    (hvk : ∀ t ≤ m, v t ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀))
    (side : ℕ → Finset (ExplorationNode C u ℓ x₀ x₁))
    (hside : ∀ j < m, ∀ w ∈ side j, IsTreeChild C u ℓ x₀ x₁ B₀ (v j) w ∧ w ≠ v (j + 1)) :
    ∑ j ∈ Finset.range m, (side j).card ≤ Cbr := by
  have hT := (explorationTree_isAcyclic : (explorationTree C u ℓ x₀ x₁).IsAcyclic)
  set I := (Finset.range m).sigma side with hI
  have memI : ∀ x ∈ I, x.1 < m ∧ x.2 ∈ side x.1 := fun x hx => by
    rw [Finset.mem_sigma, Finset.mem_range] at hx
    exact hx
  have hch : ∀ x ∈ I,
      IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) (chainSnoc v x.1 x.2) (x.1 + 1) := by
    intro x hx
    obtain ⟨htc, -⟩ := hside x.1 (memI x hx).1 x.2 (memI x hx).2
    have hvj := hv.mono (memI x hx).1.le
    exact hvj.snoc htc.2.2.1 (hvj.ne_of_isStrictAncestor hT htc.2.2.2)
  have hbranch : ∀ x ∈ I, ∃ (S : Set (PrunedVertex C u ℓ x₀ x₁ B₀))
      (ρ : ℕ → ExplorationNode C u ℓ x₀ x₁), IsPrunedBranch C u ℓ x₀ x₁ B₀ S ∧
      (∀ t ≤ x.1 + 1, ρ t = chainSnoc v x.1 x.2 t) ∧
      (∃ y ∈ S, y.val = chainSnoc v x.1 x.2 (x.1 + 1)) ∧
      ∀ y ∈ S, ∃ q, IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) ρ q ∧ ρ q = y.val := by
    intro x hx
    refine exists_branch B₀ (hch x hx) (by omega) fun t ht => ?_
    rcases Nat.lt_or_ge t (x.1 + 1) with h | h
    · rw [chainSnoc_of_le (by omega)]
      exact hvk t (by have := (memI x hx).1; omega)
    · rw [show t = x.1 + 1 by omega, chainSnoc_succ]
      exact (hside x.1 (memI x hx).1 x.2 (memI x hx).2).1.2.1
  haveI : Nonempty (ExplorationNode C u ℓ x₀ x₁) := ⟨.inl B₀⟩
  choose! S ρ hS hρ hmem hρS using hbranch
  have hinj : Set.InjOn S I := by
    rintro ⟨j, w⟩ hx ⟨j', w'⟩ hx' hSS
    rw [Finset.mem_coe] at hx hx'
    obtain ⟨hj, hw⟩ := memI _ hx
    obtain ⟨hj', hw'⟩ := memI _ hx'
    obtain ⟨y, hy, hyv⟩ := hmem _ hx'
    rw [← hSS] at hy
    obtain ⟨q, hq, hqy⟩ := hρS _ hx y hy
    obtain ⟨rfl, hu⟩ := hq.unique hT (hch _ hx') (by rw [hqy, hyv])
    have hρw := hρ _ hx
    simp only at hρw hu
    rcases lt_trichotomy j j' with h | rfl | h
    · have e1 := hρw (j + 1) le_rfl
      have e2 := hu (j + 1) (by omega)
      rw [chainSnoc_succ] at e1
      rw [chainSnoc_of_le (by omega)] at e2
      exact absurd (e1.symm.trans e2) (hside j hj w hw).2
    · have e1 := hρw (j + 1) le_rfl
      have e2 := hu (j + 1) le_rfl
      rw [chainSnoc_succ] at e1 e2
      rw [e1.symm.trans e2]
    · have e1 := hρw (j' + 1) (by omega)
      have e2 := hu (j' + 1) le_rfl
      rw [chainSnoc_of_le (by omega)] at e1
      rw [chainSnoc_succ] at e2
      exact absurd (e2.symm.trans e1) (hside j' hj' w' hw').2
  have hcard : I.card ≤ Cbr :=
    hbr I.card (fun k => S (I.equivFin.symm k).1) (fun k => hS _ (I.equivFin.symm k).2)
      fun a b h => I.equivFin.symm.injective
        (Subtype.ext (hinj (I.equivFin.symm a).2 (I.equivFin.symm b).2 h))
  rwa [hI, Finset.card_sigma] at hcard

end Branches

/-! ### The greedy construction -/

section Construction

variable {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ} {x₀ x₁ : C}
  (B₀ : ExplorationBlock C u ℓ x₀ x₁)

theorem pos_of_le_mul {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (h : a ≤ b * c) : 0 < c := by
  by_contra hc
  rw [not_lt] at hc
  linarith [mul_nonpos_of_nonneg_of_nonpos hb hc]

theorem prod_card_le_exp {α : Type*} {m : ℕ} (s : ℕ → Finset α) :
    ∏ j ∈ Finset.range m, ((s j).card : ℝ) ≤
      Real.exp (∑ j ∈ Finset.range m, (((s j).card : ℝ) - 1)) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => ?_
  have := Real.add_one_le_exp (((s j).card : ℝ) - 1)
  linarith

/-- The candidates for the cut-vertex following the block `B` with parent point `p`: the
cut-vertices of `B` other than `p` (none if `B` is infinite). -/
noncomputable def candCut (B : ExplorationBlock C u ℓ x₀ x₁) (p : C) :
    Finset (ExplorationCut C u ℓ x₀ x₁) :=
  if hB : B.val.Finite then (hB.toFinset.filter (· ≠ p)).subtype _ else ∅

theorem sum_candCut {B : ExplorationBlock C u ℓ x₀ x₁} (hB : B.val.Finite) (p : C) (F : C → ℝ) :
    ∑ c ∈ hB.toFinset with
      (IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) c ∧ c ≠ p), F c =
      ∑ c ∈ candCut B p, F c.val := by
  rw [candCut, dif_pos hB, Finset.sum_subtype_eq_sum_filter, Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr fun c _ => and_comm) fun _ _ => rfl

theorem mem_candCut {B : ExplorationBlock C u ℓ x₀ x₁} {p : C} {c : ExplorationCut C u ℓ x₀ x₁}
    (hc : c ∈ candCut B p) : B.val.Finite ∧ c.val ∈ B.val ∧ c.val ≠ p := by
  unfold candCut at hc
  by_cases hB : B.val.Finite
  · rw [dif_pos hB, Finset.mem_subtype, Finset.mem_filter, Set.Finite.mem_toFinset] at hc
    exact ⟨hB, hc⟩
  · rw [dif_neg hB] at hc
    simp at hc

/-- The outgoing flux of the cut-vertex `c` into `B` if `B` is a child of `c` in `𝒢_tree`, and `0`
otherwise (the summand of Step 3 at a cut-vertex). -/
noncomputable def childFlux (c : ExplorationCut C u ℓ x₀ x₁) (B : ExplorationBlock C u ℓ x₀ x₁) :
    ℝ :=
  ∑ᶠ (_ : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)), outgoingFlux C ℓ c.val B.val

/-- The candidates for the block following the cut-vertex `c`: its children in `𝒢_tree` of
nonzero outgoing flux. -/
noncomputable def candBlock (c : ExplorationCut C u ℓ x₀ x₁) :
    Finset (ExplorationBlock C u ℓ x₀ x₁) :=
  if h : (Function.support (childFlux B₀ c)).Finite then h.toFinset else ∅

theorem mem_candBlock {c : ExplorationCut C u ℓ x₀ x₁} {B : ExplorationBlock C u ℓ x₀ x₁}
    (hB : B ∈ candBlock B₀ c) : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B) ∧
      childFlux B₀ c B = outgoingFlux C ℓ c.val B.val := by
  unfold candBlock at hB
  by_cases h : (Function.support (childFlux B₀ c)).Finite
  · rw [dif_pos h, Set.Finite.mem_toFinset, Function.mem_support] at hB
    unfold childFlux at hB ⊢
    rw [finsum_eq_if] at hB ⊢
    by_cases hc : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)
    · rw [if_pos hc]
      exact ⟨hc, rfl⟩
    · rw [if_neg hc] at hB
      exact absurd rfl hB
  · rw [dif_neg h] at hB
    simp at hB

theorem finsum_childFlux_eq {c : ExplorationCut C u ℓ x₀ x₁} (h : 0 < ∑ᶠ B, childFlux B₀ c B) :
    ∑ᶠ B, childFlux B₀ c B = ∑ B ∈ candBlock B₀ c, outgoingFlux C ℓ c.val B.val := by
  have hfin : (Function.support (childFlux B₀ c)).Finite := by
    by_contra hinf
    rw [finsum_of_infinite_support hinf] at h
    exact lt_irrefl _ h
  have hcand : candBlock B₀ c = hfin.toFinset := dif_pos hfin
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  exact Finset.sum_congr hcand.symm fun B hB => (mem_candBlock B₀ (hcand ▸ hB)).2

/-- One step of the greedy path from the block `σ.1` with parent point `σ.2`: the block is not a
pruning block, `cB.1` is a candidate cut-vertex of maximal incoming flux, and `cB.2` a candidate
child block of `cB.1` of maximal outgoing flux. -/
def IsGreedyStep (σ : ExplorationBlock C u ℓ x₀ x₁ × C)
    (cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁) : Prop :=
  ¬ IsPruningBlock C u ℓ (u x₀) σ.1.val ∧ cB.1 ∈ candCut σ.1 σ.2 ∧
    (∀ c ∈ candCut σ.1 σ.2, incomingFlux C ℓ σ.1.val c.val ≤ incomingFlux C ℓ σ.1.val cB.1.val) ∧
    cB.2 ∈ candBlock B₀ cB.1 ∧
    ∀ B ∈ candBlock B₀ cB.1, outgoingFlux C ℓ cB.1.val B.val ≤ outgoingFlux C ℓ cB.1.val cB.2.val

/-- The greedy step, if any. -/
noncomputable def greedyStep (σ : ExplorationBlock C u ℓ x₀ x₁ × C) :
    Option (ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁) :=
  if h : ∃ cB, IsGreedyStep B₀ σ cB then some h.choose else none

theorem isGreedyStep_of_eq_some {σ : ExplorationBlock C u ℓ x₀ x₁ × C}
    {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁}
    (h : greedyStep B₀ σ = some cB) : IsGreedyStep B₀ σ cB := by
  unfold greedyStep at h
  by_cases hex : ∃ cB, IsGreedyStep B₀ σ cB
  · rw [dif_pos hex, Option.some.injEq] at h
    rw [← h]
    exact hex.choose_spec
  · rw [dif_neg hex] at h
    simp at h

theorem not_isGreedyStep_of_eq_none {σ : ExplorationBlock C u ℓ x₀ x₁ × C}
    (h : greedyStep B₀ σ = none) : ¬ ∃ cB, IsGreedyStep B₀ σ cB := by
  intro hex
  unfold greedyStep at h
  rw [dif_pos hex] at h
  simp at h

/-- The `k`-th block of the greedy path and its parent point. -/
noncomputable def greedyState : ℕ → ExplorationBlock C u ℓ x₀ x₁ × C
  | 0 => (B₀, x₁)
  | k + 1 => match greedyStep B₀ (greedyState k) with
    | some cB => (cB.2, cB.1.val)
    | none => greedyState k

theorem greedyState_succ {k : ℕ} {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁}
    (h : greedyStep B₀ (greedyState B₀ k) = some cB) :
    greedyState B₀ (k + 1) = (cB.2, cB.1.val) := by
  simp only [greedyState, h]

/-- The `j`-th vertex of the greedy path in the block-cut tree: blocks at even, cut-vertices at
odd indices. -/
noncomputable def greedyVertex (j : ℕ) : ExplorationNode C u ℓ x₀ x₁ :=
  if j % 2 = 0 then .inl (greedyState B₀ (j / 2)).1 else
    match greedyStep B₀ (greedyState B₀ (j / 2)) with
    | some cB => .inr cB.1
    | none => .inl (greedyState B₀ (j / 2)).1

/-- The candidates at the `j`-th vertex of the greedy path. -/
noncomputable def greedyCand (j : ℕ) : Finset (ExplorationNode C u ℓ x₀ x₁) :=
  if j % 2 = 0 then
    (candCut (greedyState B₀ (j / 2)).1 (greedyState B₀ (j / 2)).2).map
      ⟨Sum.inr, Sum.inr_injective⟩
  else match greedyStep B₀ (greedyState B₀ (j / 2)) with
    | some cB => (candBlock B₀ cB.1).map ⟨Sum.inl, Sum.inl_injective⟩
    | none => ∅

/-- The flux at the `j`-th vertex of the greedy path: entering the block from its parent point,
or entering the cut-vertex from its parent block. -/
noncomputable def greedyFlux (j : ℕ) : ℝ :=
  if j % 2 = 0 then outgoingFlux C ℓ (greedyState B₀ (j / 2)).2 (greedyState B₀ (j / 2)).1.val
  else match greedyStep B₀ (greedyState B₀ (j / 2)) with
    | some cB => incomingFlux C ℓ (greedyState B₀ (j / 2)).1.val cB.1.val
    | none => 0

theorem greedyVertex_even (t : ℕ) : greedyVertex B₀ (2 * t) = .inl (greedyState B₀ t).1 := by
  rw [greedyVertex, if_pos (by omega), show 2 * t / 2 = t by omega]

theorem greedyVertex_odd {t : ℕ} {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁}
    (h : greedyStep B₀ (greedyState B₀ t) = some cB) : greedyVertex B₀ (2 * t + 1) = .inr cB.1 := by
  rw [greedyVertex, if_neg (by omega), show (2 * t + 1) / 2 = t by omega]
  simp only [h]

theorem greedyVertex_eq_inl {t : ℕ} {A : ExplorationBlock C u ℓ x₀ x₁}
    (h : greedyVertex B₀ t = .inl A) : A = (greedyState B₀ (t / 2)).1 := by
  unfold greedyVertex at h
  by_cases ht : t % 2 = 0
  · rw [if_pos ht] at h
    exact (Sum.inl_injective h).symm
  · rw [if_neg ht] at h
    rcases hs : greedyStep B₀ (greedyState B₀ (t / 2)) with _ | cB
    · simp only [hs] at h
      exact (Sum.inl_injective h).symm
    · simp only [hs, reduceCtorEq] at h

theorem greedyCand_even (t : ℕ) : greedyCand B₀ (2 * t) =
    (candCut (greedyState B₀ t).1 (greedyState B₀ t).2).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  rw [greedyCand, if_pos (by omega), show 2 * t / 2 = t by omega]

theorem greedyCand_odd {t : ℕ} {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁}
    (h : greedyStep B₀ (greedyState B₀ t) = some cB) :
    greedyCand B₀ (2 * t + 1) = (candBlock B₀ cB.1).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  rw [greedyCand, if_neg (by omega), show (2 * t + 1) / 2 = t by omega]
  simp only [h]

theorem greedyFlux_even (t : ℕ) : greedyFlux B₀ (2 * t) =
    outgoingFlux C ℓ (greedyState B₀ t).2 (greedyState B₀ t).1.val := by
  rw [greedyFlux, if_pos (by omega), show 2 * t / 2 = t by omega]

/-- The invariant of the greedy path after `k` blocks: its vertices form a chain of kept
vertices, the blocks passed are not pruning blocks, every candidate is a child, and the flux at
the `k`-th block is at least `i₀` divided by the product of the numbers of candidates. -/
structure GreedyInv (i₀ : ℝ) (k : ℕ) : Prop where
  chain : IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) (greedyVertex B₀) (2 * k)
  kept : ∀ t ≤ 2 * k, greedyVertex B₀ t ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀)
  not_pruning : ∀ t < k, ¬ IsPruningBlock C u ℓ (u x₀) (greedyState B₀ t).1.val
  parent : 0 < k → ∃ c : ExplorationCut C u ℓ x₀ x₁, greedyVertex B₀ (2 * k - 1) = .inr c ∧
    c.val = (greedyState B₀ k).2 ∧
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl (greedyState B₀ k).1)
  cand : ∀ j < 2 * k, greedyVertex B₀ (j + 1) ∈ greedyCand B₀ j ∧
    ∀ w ∈ greedyCand B₀ j, IsTreeChild C u ℓ x₀ x₁ B₀ (greedyVertex B₀ j) w
  flux : i₀ ≤ (∏ j ∈ Finset.range (2 * k), ((greedyCand B₀ j).card : ℝ)) * greedyFlux B₀ (2 * k)

theorem greedyInv_zero {i₀ : ℝ} (h : i₀ ≤ outgoingFlux C ℓ x₁ B₀.val) : GreedyInv B₀ i₀ 0 where
  chain := ⟨by have := greedyVertex_even B₀ 0; rwa [Nat.mul_zero] at this,
    fun a ha b hb _ => by rw [Set.mem_Iic] at ha hb; omega, fun t ht => by omega⟩
  kept := fun t ht => by
    rw [show t = 2 * 0 by omega, greedyVertex_even]
    exact (prunedRoot C u ℓ x₀ x₁ B₀).2
  not_pruning := fun t ht => by omega
  parent := fun h => by omega
  cand := fun j hj => by omega
  flux := by
    rw [greedyFlux_even, Nat.mul_zero, Finset.prod_range_zero, one_mul]
    exact h

variable {B₀}

/-- The candidate cut-vertices of a block of the greedy path which is not a pruning block are
its children in `𝒢_tree`. -/
theorem GreedyInv.isTreeChild_of_mem_candCut {i₀ : ℝ} {k : ℕ} (hI : GreedyInv B₀ i₀ k)
    (hnp : ¬ IsPruningBlock C u ℓ (u x₀) (greedyState B₀ k).1.val)
    {c : ExplorationCut C u ℓ x₀ x₁} (hc : c ∈ candCut (greedyState B₀ k).1 (greedyState B₀ k).2) :
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (greedyState B₀ k).1) (.inr c) := by
  have hT := (explorationTree_isAcyclic : (explorationTree C u ℓ x₀ x₁).IsAcyclic)
  obtain ⟨-, hcB, hcp⟩ := mem_candCut hc
  have hv := greedyVertex_even B₀ k
  have hadj : (explorationTree C u ℓ x₀ x₁).Adj (greedyVertex B₀ (2 * k)) (.inr c) := by
    rw [hv]
    exact hcB
  have hoff : ∀ t ≤ 2 * k, greedyVertex B₀ t ≠ .inr c := by
    intro t ht heq
    have h1 := hI.chain.succ_eq_of_adj hT ht (by rw [heq]; exact hadj)
    obtain ⟨c', hc', hc'v, -⟩ := hI.parent (by omega)
    rw [show 2 * k - 1 = t by omega, heq] at hc'
    exact hcp (by rw [Sum.inr_injective hc']; exact hc'v)
  have hanc := hI.chain.isStrictAncestor_of_ne hT hadj hoff
  have hch := hI.chain.snoc hadj hoff
  have hkept := mem_keptVertices_of_chain B₀ hch fun t ht A hA => by
    rw [chainSnoc_of_le (by omega)] at hA
    rw [greedyVertex_eq_inl B₀ hA]
    rcases Nat.lt_or_ge (t / 2) k with h | h
    · exact hI.not_pruning _ h
    · rw [show t / 2 = k by omega]
      exact hnp
  rw [chainSnoc_succ] at hkept
  rw [hv] at hadj hanc
  exact ⟨by rw [← hv]; exact hI.kept _ le_rfl, hkept, hadj, hanc⟩

/-- Step 3 at a block of the greedy path. -/
theorem GreedyInv.outgoingFlux_le {i₀ : ℝ} {k : ℕ} (hI : GreedyInv B₀ i₀ k)
    (hFB : FluxBalance C u ℓ x₀ x₁ B₀) (hfin : (greedyState B₀ k).1.val.Finite)
    (hnp : ¬ IsPruningBlock C u ℓ (u x₀) (greedyState B₀ k).1.val) :
    outgoingFlux C ℓ (greedyState B₀ k).2 (greedyState B₀ k).1.val ≤
      ∑ c ∈ candCut (greedyState B₀ k).1 (greedyState B₀ k).2,
        incomingFlux C ℓ (greedyState B₀ k).1.val c.val := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (hFB.1 hfin hnp).trans_eq (sum_candCut hfin _ _)
  · obtain ⟨c₀, -, hc₀, htc⟩ := hI.parent hk
    have := hFB.2.1 _ c₀ htc hfin hnp
    rw [hc₀] at this
    exact this.trans_eq (sum_candCut hfin _ _)

theorem GreedyInv.flux_succ {i₀ : ℝ} {k : ℕ}
    {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁} (hI : GreedyInv B₀ i₀ k)
    (hFB : FluxBalance C u ℓ x₀ x₁ B₀) (hs : greedyStep B₀ (greedyState B₀ k) = some cB) :
    i₀ ≤ (∏ j ∈ Finset.range (2 * k + 1), ((greedyCand B₀ j).card : ℝ)) *
      incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val := by
  obtain ⟨hnp, hc, hmax, -, -⟩ := isGreedyStep_of_eq_some B₀ hs
  have h1 := hI.outgoingFlux_le hFB (mem_candCut hc).1 hnp
  have h2 := Finset.sum_le_card_nsmul _ _ _ hmax
  rw [nsmul_eq_mul] at h2
  calc i₀ ≤ (∏ j ∈ Finset.range (2 * k), ((greedyCand B₀ j).card : ℝ)) * greedyFlux B₀ (2 * k) :=
        hI.flux
    _ ≤ (∏ j ∈ Finset.range (2 * k), ((greedyCand B₀ j).card : ℝ)) *
        (((candCut (greedyState B₀ k).1 (greedyState B₀ k).2).card : ℝ) *
          incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val) := by
        rw [greedyFlux_even]
        exact mul_le_mul_of_nonneg_left (h1.trans h2)
          (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = _ := by rw [Finset.prod_range_succ, greedyCand_even, Finset.card_map, mul_assoc]

/-- One greedy step preserves the invariant. -/
theorem GreedyInv.succ {i₀ : ℝ} {k : ℕ}
    {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁} (hi₀ : 0 < i₀)
    (hI : GreedyInv B₀ i₀ k) (hFB : FluxBalance C u ℓ x₀ x₁ B₀)
    (hs : greedyStep B₀ (greedyState B₀ k) = some cB) : GreedyInv B₀ i₀ (k + 1) := by
  have hT := (explorationTree_isAcyclic : (explorationTree C u ℓ x₀ x₁).IsAcyclic)
  obtain ⟨hnp, hc, -, hB, hBmax⟩ := isGreedyStep_of_eq_some B₀ hs
  have hσ := greedyState_succ B₀ hs
  have hv0 := greedyVertex_even B₀ k
  have hv1 := greedyVertex_odd B₀ hs
  have hv2 : greedyVertex B₀ (2 * k + 1 + 1) = .inl cB.2 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, greedyVertex_even, hσ]
  have htc1 := hI.isTreeChild_of_mem_candCut hnp hc
  have htc2 := (mem_candBlock B₀ hB).1
  have hch1 : IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) (greedyVertex B₀) (2 * k + 1) := by
    refine (hI.chain.snoc (y := .inr cB.1) (by rw [hv0]; exact htc1.2.2.1)
      (hI.chain.ne_of_isStrictAncestor hT (by rw [hv0]; exact htc1.2.2.2))).congr fun t ht => ?_
    rcases Nat.lt_or_ge t (2 * k + 1) with h | h
    · exact chainSnoc_of_le (by omega)
    · rw [show t = 2 * k + 1 by omega, chainSnoc_succ, hv1]
  have hch2 :
      IsChain (explorationTree C u ℓ x₀ x₁) (.inl B₀) (greedyVertex B₀) (2 * k + 1 + 1) := by
    refine (hch1.snoc (y := .inl cB.2) (by rw [hv1]; exact htc2.2.2.1)
      (hch1.ne_of_isStrictAncestor hT (by rw [hv1]; exact htc2.2.2.2))).congr fun t ht => ?_
    rcases Nat.lt_or_ge t (2 * k + 1 + 1) with h | h
    · exact chainSnoc_of_le (by omega)
    · rw [show t = 2 * k + 1 + 1 by omega, chainSnoc_succ, hv2]
  have h1 := hI.flux_succ hFB hs
  have hin := pos_of_le_mul hi₀ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) h1
  refine ⟨by rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; exact hch2, fun t ht => ?_,
    fun t ht => ?_, fun _ => ⟨cB.1, ?_, by rw [hσ], by rw [hσ]; exact htc2⟩, fun j hj => ?_, ?_⟩
  · rcases Nat.lt_or_ge t (2 * k + 1) with h | h
    · rcases Nat.lt_or_ge t (2 * k + 1 - 1) with h' | h'
      · exact hI.kept t (by omega)
      · rw [show t = 2 * k by omega]
        exact hI.kept _ le_rfl
    · rcases Nat.lt_or_ge t (2 * k + 1 + 1) with h' | h'
      · rw [show t = 2 * k + 1 by omega, hv1]
        exact htc1.2.1
      · rw [show t = 2 * k + 1 + 1 by omega, hv2]
        exact htc2.2.1
  · rcases Nat.lt_or_ge t k with h | h
    · exact hI.not_pruning t h
    · rw [show t = k by omega]
      exact hnp
  · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, hv1]
  · rcases Nat.lt_or_ge j (2 * k) with h | h
    · exact hI.cand j h
    · rcases Nat.lt_or_ge j (2 * k + 1) with h' | h'
      · rw [show j = 2 * k by omega, hv1, greedyCand_even, hv0]
        refine ⟨Finset.mem_map_of_mem _ hc, fun w hw => ?_⟩
        obtain ⟨c, hc', rfl⟩ := Finset.mem_map.1 hw
        exact hI.isTreeChild_of_mem_candCut hnp hc'
      · rw [show j = 2 * k + 1 by omega, hv2, greedyCand_odd B₀ hs, hv1]
        refine ⟨Finset.mem_map_of_mem _ hB, fun w hw => ?_⟩
        obtain ⟨B, hB', rfl⟩ := Finset.mem_map.1 hw
        exact (mem_candBlock B₀ hB').1
  · have h3 : incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val ≤ ∑ᶠ B, childFlux B₀ cB.1 B :=
      hFB.2.2 _ cB.1 htc1
    rw [finsum_childFlux_eq B₀ (hin.trans_le h3)] at h3
    have h4 := Finset.sum_le_card_nsmul _ _ _ hBmax
    rw [nsmul_eq_mul] at h4
    calc i₀ ≤ (∏ j ∈ Finset.range (2 * k + 1), ((greedyCand B₀ j).card : ℝ)) *
          incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val := h1
      _ ≤ (∏ j ∈ Finset.range (2 * k + 1), ((greedyCand B₀ j).card : ℝ)) *
          (((candBlock B₀ cB.1).card : ℝ) * outgoingFlux C ℓ cB.1.val cB.2.val) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
      _ = _ := by
          rw [greedyFlux_even, hσ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
            Finset.prod_range_succ _ (2 * k + 1), greedyCand_odd B₀ hs, Finset.card_map, mul_assoc]

/-- If the greedy path stops at a block, the block is infinite or a pruning block: otherwise the
positive flux entering it provides a greedy step. -/
theorem GreedyInv.stop {i₀ : ℝ} {k : ℕ} (hi₀ : 0 < i₀) (hI : GreedyInv B₀ i₀ k)
    (hFB : FluxBalance C u ℓ x₀ x₁ B₀) (hs : greedyStep B₀ (greedyState B₀ k) = none) :
    ¬ (greedyState B₀ k).1.val.Finite ∨
      IsPruningBlock C u ℓ (u x₀) (greedyState B₀ k).1.val := by
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨hfin, hnp⟩ := hcon
  apply not_isGreedyStep_of_eq_none B₀ hs
  have hpos := pos_of_le_mul hi₀ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) hI.flux
  rw [greedyFlux_even] at hpos
  have h1 := hI.outgoingFlux_le hFB hfin hnp
  have hne : (candCut (greedyState B₀ k).1 (greedyState B₀ k).2).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at h1
    linarith
  obtain ⟨c, hc, hcmax⟩ := Finset.exists_max_image _
    (fun c : ExplorationCut C u ℓ x₀ x₁ => incomingFlux C ℓ (greedyState B₀ k).1.val c.val) hne
  have h2 := Finset.sum_le_card_nsmul _ _ _ hcmax
  rw [nsmul_eq_mul] at h2
  have hcpos := pos_of_le_mul hpos (Nat.cast_nonneg _) (h1.trans h2)
  have htc := hI.isTreeChild_of_mem_candCut hnp hc
  have h3 : incomingFlux C ℓ (greedyState B₀ k).1.val c.val ≤ ∑ᶠ B, childFlux B₀ c B :=
    hFB.2.2 _ c htc
  have hfpos := hcpos.trans_le h3
  have hne' : (candBlock B₀ c).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [finsum_childFlux_eq B₀ hfpos, h, Finset.sum_empty] at hfpos
    exact lt_irrefl _ hfpos
  obtain ⟨B, hB, hBmax⟩ := Finset.exists_max_image _
    (fun B : ExplorationBlock C u ℓ x₀ x₁ => outgoingFlux C ℓ c.val B.val) hne'
  exact ⟨(c, B), hnp, hc, hcmax, hB, hBmax⟩

/-- The flux bound `eq. lowerboundiin1410` at the cut-vertex after the `k`-th block: the side
candidates give distinct branches (Lemma 5.28 bound) and `m ≤ e^{m - 1}`. -/
theorem GreedyInv.flux_le {i₀ : ℝ} {k : ℕ} {Cbr : ℕ}
    {cB : ExplorationCut C u ℓ x₀ x₁ × ExplorationBlock C u ℓ x₀ x₁} (hi₀ : 0 < i₀)
    (hI : GreedyInv B₀ i₀ k) (hFB : FluxBalance C u ℓ x₀ x₁ B₀)
    (hbr : ∀ (n : ℕ) (b : Fin n → Set (PrunedVertex C u ℓ x₀ x₁ B₀)),
      (∀ k, IsPrunedBranch C u ℓ x₀ x₁ B₀ (b k)) → Function.Injective b → n ≤ Cbr)
    (hs : greedyStep B₀ (greedyState B₀ k) = some cB) :
    i₀ * Real.exp (-(Cbr : ℝ)) ≤ incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val := by
  have hI' := hI.succ hi₀ hFB hs
  have h1 := hI.flux_succ hFB hs
  have hside := sum_card_side_le B₀ hbr (hI'.chain.mono (show 2 * k + 1 ≤ 2 * (k + 1) by omega))
    (fun t ht => hI'.kept t (by omega))
    (fun j => (greedyCand B₀ j).erase (greedyVertex B₀ (j + 1)))
    fun j hj w hw => ⟨(hI'.cand j (by omega)).2 w (Finset.mem_of_mem_erase hw),
      Finset.ne_of_mem_erase hw⟩
  have hprod : ∏ j ∈ Finset.range (2 * k + 1), ((greedyCand B₀ j).card : ℝ) ≤ Real.exp Cbr := by
    refine (prod_card_le_exp _).trans (Real.exp_le_exp.2 ?_)
    have : ∑ j ∈ Finset.range (2 * k + 1), (((greedyCand B₀ j).card : ℝ) - 1) =
        ((∑ j ∈ Finset.range (2 * k + 1),
          ((greedyCand B₀ j).erase (greedyVertex B₀ (j + 1))).card : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hmem := (hI'.cand j (by omega)).1
      rw [Finset.card_erase_of_mem hmem,
        Nat.cast_sub (Finset.card_pos.2 ⟨_, hmem⟩), Nat.cast_one]
    rw [this]
    exact_mod_cast hside
  have hin := pos_of_le_mul hi₀ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) h1
  have h2 : i₀ ≤ Real.exp Cbr * incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val :=
    h1.trans (mul_le_mul_of_nonneg_right hprod hin.le)
  calc i₀ * Real.exp (-(Cbr : ℝ)) ≤
        Real.exp Cbr * incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val *
          Real.exp (-(Cbr : ℝ)) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = incomingFlux C ℓ (greedyState B₀ k).1.val cB.1.val := by
        rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
          mul_one]

end Construction

end Greedy

open Greedy

/-- Step 5 (step:5.27-explore, L2563-2602, eq. `lowerboundiin1410`): the greedy path of maximal
flux has incoming flux at least `i₀ e^{-C_branches}` at each of its cut-vertices. -/
theorem greedyPath_of_flux {ω : Configuration 2} {C : OpenComponent ω} {u ℓ : C → ℝ}
    {x₀ x₁ : C} {B₀ : ExplorationBlock C u ℓ x₀ x₁} {Cbr : ℕ} {i₀ : ℝ} (hi₀ : 0 < i₀)
    (hflux : i₀ ≤ outgoingFlux C ℓ x₁ B₀.val) (hFB : FluxBalance C u ℓ x₀ x₁ B₀)
    (hbr : ∀ (n : ℕ) (b : Fin n → Set (PrunedVertex C u ℓ x₀ x₁ B₀)),
      (∀ k, IsPrunedBranch C u ℓ x₀ x₁ B₀ (b k)) → Function.Injective b → n ≤ Cbr) :
    GreedyPath C u ℓ x₀ x₁ B₀ (i₀ * Real.exp (-(Cbr : ℝ))) := by
  have hInv : ∀ k, (∀ k' < k, greedyStep B₀ (greedyState B₀ k') ≠ none) → GreedyInv B₀ i₀ k := by
    intro k
    induction k with
    | zero => exact fun _ => greedyInv_zero B₀ hflux
    | succ k ih =>
      intro h
      obtain ⟨cB, hcB⟩ := Option.ne_none_iff_exists'.1 (h k (by omega))
      exact (ih fun k' hk' => h k' (by omega)).succ hi₀ hFB hcB
  have hlink : ∀ k, GreedyInv B₀ i₀ k → greedyStep B₀ (greedyState B₀ k) ≠ none →
      ∃ hc : IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)
        (greedyState B₀ (k + 1)).2,
        IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (greedyState B₀ k).1) (.inr ⟨_, hc⟩) ∧
        IsTreeChild C u ℓ x₀ x₁ B₀ (.inr ⟨_, hc⟩) (.inl (greedyState B₀ (k + 1)).1) ∧
        i₀ * Real.exp (-(Cbr : ℝ)) ≤
          incomingFlux C ℓ (greedyState B₀ k).1.val (greedyState B₀ (k + 1)).2 := by
    intro k hI hne
    obtain ⟨cB, hs⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨hnp, hc, -, hB, -⟩ := isGreedyStep_of_eq_some B₀ hs
    rw [greedyState_succ B₀ hs]
    exact ⟨cB.1.2, hI.isTreeChild_of_mem_candCut hnp hc, (mem_candBlock B₀ hB).1,
      hI.flux_le hi₀ hFB hbr hs⟩
  by_cases hex : ∃ k, greedyStep B₀ (greedyState B₀ k) = none
  · refine ⟨(Nat.find hex : ℕ∞), fun k => (greedyState B₀ k).1, fun k => (greedyState B₀ k).2,
      rfl, fun k hk => ?_, fun k hk => ?_⟩
    · have hk' : k + 1 ≤ Nat.find hex := by exact_mod_cast hk
      exact hlink k (hInv k fun k' _ => Nat.find_min hex (by omega)) (Nat.find_min hex (by omega))
    · have hk' : k = Nat.find hex := by exact_mod_cast hk
      subst hk'
      exact ((hInv _ fun k' hk'' => Nat.find_min hex hk'').stop hi₀ hFB
        (Nat.find_spec hex)).elim Or.inl fun h => Or.inr (Or.inl h)
  · push Not at hex
    exact ⟨⊤, fun k => (greedyState B₀ k).1, fun k => (greedyState B₀ k).2, rfl,
      fun k _ => hlink k (hInv k fun k' _ => hex k') (hex k),
      fun k hk => absurd hk (ENat.coe_ne_top k)⟩

/-- **step:5.27-explore** (Step 5, L2563-2602). -/
theorem greedyExplorationStep : GreedyExplorationStep :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hi₀ hflux hFB hbr => greedyPath_of_flux hi₀ hflux hFB hbr

end Rigidity.Proofs.Section5
