import Rigidity.Steps.Section5.DisjointPathsToInfinity

/-!
# Menger's theorem for rays (step `step:5.21-menger` of Proposition 5.21)

`MengerRaysStep` (`Rigidity/Steps/Section5/DisjointPathsToInfinity.lean`): in an open cluster, if
no set of fewer than `k` vertices meets every infinite path starting in the finite set `S`, there
are `k` disjoint infinite paths starting in `S`. No literature input is used.

* **Finite Menger** (`Menger.exists_linkage`, vertex form, Göring's proof by induction on the
  number of edges): for a finite edge set `E` and vertex sets `A`, `B`, if every set separating
  `A` from `B` has at least `k` vertices, there are `k` disjoint paths from `A` to `B`. If
  deleting an edge `e` leaves a separator `S` of fewer than `k` vertices, `e = xy` with `x`
  joined to `A` and `y` joined to `B` off `S`; the sets `X = S ∪ {x}` and `Y = S ∪ {y}` have `k`
  vertices, every `A`-`X` (resp. `Y`-`B`) separator after deleting `e` separates `A` from `B`,
  and the two path systems given by induction glue along `S` and `e`.
* **Balls** (`Menger.ball`): the vertices within graph distance `n` of `S`, finite in a locally
  finite graph. Finite Menger in the edges of `ball (t + 1)`, with target `ball (t + 1) \ ball t`,
  gives `k` disjoint paths from `S` with `t + 1` steps: a ray from `S` avoiding a set `X` leaves
  `ball t` and its initial segment is a path to the target avoiding `X`.
* **Compactness** (`Menger.exists_forall_levelPaths`, König's lemma): the `k`-tuples of
  sequences whose `n`-th terms lie in `ball n` form a compact set for the product of discrete
  topologies; the tuples which are disjoint paths up to step `t` form a decreasing sequence of
  nonempty closed subsets, whose intersection consists of `k` disjoint rays.
-/

noncomputable section

open Classical Function Set

namespace Rigidity.Proofs.Section5

namespace Menger

variable {V : Type*}

/-! ### Walks along a finite edge set -/

/-- `l` is a walk from `A` to `B` along the edges of `E`: consecutive vertices span edges of `E`,
the first vertex lies in `A` and the last one in `B`. -/
def IsLinkWalk (E : Finset (Sym2 V)) (A B : Set V) (l : List V) : Prop :=
  l.IsChain (fun a b => s(a, b) ∈ E) ∧ (∃ a ∈ l.head?, a ∈ A) ∧ ∃ b ∈ l.getLast?, b ∈ B

/-- `T` separates `A` from `B` along `E`: every walk from `A` to `B` meets `T`. -/
def Separates (E : Finset (Sym2 V)) (A B T : Set V) : Prop :=
  ∀ l, IsLinkWalk E A B l → ∃ v ∈ l, v ∈ T

/-- A linkage of `A` to `B` along `E`: a finite set of pairwise disjoint paths from `A` to `B`. -/
def IsLinkage (E : Finset (Sym2 V)) (A B : Set V) (𝓛 : Finset (List V)) : Prop :=
  (∀ l ∈ 𝓛, IsLinkWalk E A B l ∧ l.Nodup) ∧ ∀ l ∈ 𝓛, ∀ l' ∈ 𝓛, l ≠ l' → ∀ v ∈ l, v ∉ l'

/-- `v` is joined to `A` by a walk along `E` avoiding `T`. -/
def ReachAvoid (E : Finset (Sym2 V)) (A T : Set V) (v : V) : Prop :=
  ∃ l, IsLinkWalk E A {v} l ∧ ∀ u ∈ l, u ∉ T

variable {E E' : Finset (Sym2 V)} {A B T Z : Set V}

theorem isLinkWalk_reverse {l : List V} :
    IsLinkWalk E A B l.reverse ↔ IsLinkWalk E B A l := by
  have h : (fun a b : V => s(b, a) ∈ E) = fun a b => s(a, b) ∈ E := by
    funext a b
    rw [Sym2.eq_swap]
  simp only [IsLinkWalk, List.isChain_reverse, h, List.head?_reverse, List.getLast?_reverse]
  tauto

theorem Separates.symm (h : Separates E A B T) : Separates E B A T := fun l hl => by
  obtain ⟨v, hv, hvT⟩ := h l.reverse (isLinkWalk_reverse.2 hl)
  exact ⟨v, List.mem_reverse.1 hv, hvT⟩

theorem IsLinkWalk.mono {l : List V} (h : IsLinkWalk E A B l) (hE : E ⊆ E') :
    IsLinkWalk E' A B l :=
  ⟨h.1.imp fun _ _ hab => hE hab, h.2⟩

theorem IsLinkWalk.ne_nil {l : List V} (h : IsLinkWalk E A B l) : l ≠ [] := by
  rintro rfl
  obtain ⟨a, ha, -⟩ := h.2.1
  simp at ha

/-- Two walks sharing their junction vertex `v` concatenate. -/
theorem IsLinkWalk.append_tail {l l' : List V} {v : V} (h : IsLinkWalk E A {v} l)
    (h' : IsLinkWalk E {v} B l') : IsLinkWalk E A B (l ++ l'.tail) := by
  obtain ⟨hc, ⟨a, ha, haA⟩, ⟨b, hb, hbv⟩⟩ := h
  obtain ⟨hc', ⟨a', ha', hav⟩, ⟨b', hb', hbB⟩⟩ := h'
  rw [Set.mem_singleton_iff] at hbv hav
  rw [hbv] at hb
  rw [hav] at ha'
  obtain ⟨t, rfl⟩ : ∃ t, l' = v :: t := by
    cases l' with
    | nil => simp at ha'
    | cons c t =>
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
      exact ⟨t, by rw [ha']⟩
  have hne : l ≠ [] := by rintro rfl; simp at ha
  refine ⟨hc.append hc'.tail fun x hx y hy => ?_, ⟨a, ?_, haA⟩, ?_⟩
  · rw [Option.mem_def, hb, Option.some.injEq] at hx
    subst hx
    exact (List.isChain_cons.1 hc').1 y hy
  · rw [List.head?_append_of_ne_nil _ hne]
    exact ha
  · rcases t with _ | ⟨c, t⟩
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb'
      exact ⟨v, by simpa using hb, hb' ▸ hbB⟩
    · refine ⟨b', ?_, hbB⟩
      rw [List.tail_cons, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rw [List.getLast?_cons_cons] at hb'
      exact hb'

theorem isLinkWalk_singleton {v : V} (hA : v ∈ A) (hB : v ∈ B) : IsLinkWalk E A B [v] :=
  ⟨List.isChain_singleton _, ⟨v, rfl, hA⟩, ⟨v, rfl, hB⟩⟩

theorem isLinkWalk_pair {u v : V} (h : s(u, v) ∈ E) : IsLinkWalk E {u} {v} [u, v] :=
  ⟨List.isChain_pair.2 h, ⟨u, rfl, rfl⟩, ⟨v, rfl, rfl⟩⟩

theorem mem_of_getLast? {l : List V} {b : V} (h : b ∈ l.getLast?) : b ∈ l :=
  List.mem_of_getLast? h

theorem mem_of_head? {l : List V} {a : V} (h : a ∈ l.head?) : a ∈ l :=
  List.mem_of_mem_head? h

theorem ReachAvoid.not_mem {v : V} (h : ReachAvoid E A T v) : v ∉ T := by
  obtain ⟨l, hl, hT⟩ := h
  obtain ⟨b, hb, hbv⟩ := hl.2.2
  rw [Set.mem_singleton_iff] at hbv
  exact hbv ▸ hT b (mem_of_getLast? hb)

theorem reachAvoid_self {v : V} (hA : v ∈ A) (hT : v ∉ T) : ReachAvoid E A T v :=
  ⟨[v], isLinkWalk_singleton hA rfl, by simpa using hT⟩

theorem ReachAvoid.step {u v : V} (h : ReachAvoid E A T v) (he : s(v, u) ∈ E) (hu : u ∉ T) :
    ReachAvoid E A T u := by
  obtain ⟨l, hl, hT⟩ := h
  refine ⟨l ++ [u], by simpa using hl.append_tail (isLinkWalk_pair he), fun w hw => ?_⟩
  rcases List.mem_append.1 hw with hw | hw
  · exact hT w hw
  · rw [List.mem_singleton] at hw
    exact hw ▸ hu

/-- A vertex joined to `A` and to `B` off a separator `T` does not exist. -/
theorem Separates.not_reachAvoid (hT : Separates E A B T) {v : V} (hA : ReachAvoid E A T v)
    (hB : ReachAvoid E B T v) : False := by
  obtain ⟨l, hl, hlT⟩ := hA
  obtain ⟨l', hl', hl'T⟩ := hB
  obtain ⟨w, hw, hwT⟩ := hT _ (hl.append_tail (isLinkWalk_reverse.2 hl'))
  rcases List.mem_append.1 hw with hw | hw
  · exact hlT w hw hwT
  · exact hl'T w (List.mem_reverse.1 (List.mem_of_mem_tail hw)) hwT

/-- A walk avoiding one endpoint of the edge `e` is a walk without `e`. -/
theorem isChain_erase {l : List V} {x y : V} (hl : l.IsChain fun a b => s(a, b) ∈ E)
    (hx : x ∉ l) : l.IsChain fun a b => s(a, b) ∈ E.erase s(x, y) := by
  refine hl.imp_of_mem_imp fun a b ha hb hab => Finset.mem_erase.2 ⟨fun he => ?_, hab⟩
  rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
  exacts [hx ha, hx hb]

/-- Along a chain from a vertex with property `P` to one without, some step leaves `P`. -/
theorem exists_rel_of_isChain {R : V → V → Prop} {P : V → Prop} :
    ∀ {l : List V}, l.IsChain R → ∀ a ∈ l.head?, P a → ∀ b ∈ l.getLast?, ¬ P b →
      ∃ u v, u ∈ l ∧ v ∈ l ∧ R u v ∧ P u ∧ ¬ P v
  | [], _, a, ha, _, _, _, _ => by simp at ha
  | [c], _, a, ha, hPa, b, hb, hPb => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb
    exact absurd (hb ▸ ha ▸ hPa) hPb
  | c :: d :: l, hl, a, ha, hPa, b, hb, hPb => by
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha
    rw [List.isChain_cons_cons] at hl
    by_cases hd : P d
    · obtain ⟨u, v, hu, hv, h⟩ := exists_rel_of_isChain hl.2 d rfl hd b
        (by rwa [List.getLast?_cons_cons] at hb) hPb
      exact ⟨u, v, List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv, h⟩
    · exact ⟨c, d, by simp, by simp, hl.1, hPa, hd⟩

/-! ### Truncation at the first visit of a set -/

/-- The initial segment of `l` up to its first vertex in `Z` (all of `l` if it misses `Z`). -/
def truncAt (Z : Set V) : List V → List V
  | [] => []
  | v :: l => if v ∈ Z then [v] else v :: truncAt Z l

theorem truncAt_prefix (Z : Set V) : ∀ l : List V, truncAt Z l <+: l
  | [] => List.prefix_refl _
  | v :: l => by
    unfold truncAt
    split_ifs
    · exact ⟨l, rfl⟩
    · exact (List.prefix_cons_inj v).2 (truncAt_prefix Z l)

theorem head?_truncAt (Z : Set V) : ∀ l : List V, (truncAt Z l).head? = l.head?
  | [] => rfl
  | v :: l => by
    unfold truncAt
    split_ifs <;> rfl

theorem isChain_truncAt {R : V → V → Prop} (Z : Set V) :
    ∀ {l : List V}, l.IsChain R → (truncAt Z l).IsChain R
  | [], _ => List.isChain_nil
  | v :: l, h => by
    unfold truncAt
    split_ifs
    · exact List.isChain_singleton _
    · refine List.isChain_cons.2 ⟨fun y hy => ?_, isChain_truncAt Z h.tail⟩
      rw [head?_truncAt] at hy
      exact (List.isChain_cons.1 h).1 y hy

theorem truncAt_spec (Z : Set V) : ∀ l : List V, (∃ v ∈ l, v ∈ Z) →
    ∃ l₁ z, truncAt Z l = l₁ ++ [z] ∧ z ∈ Z ∧ ∀ u ∈ l₁, u ∉ Z
  | [], ⟨v, hv, _⟩ => by simp at hv
  | v :: l, ⟨w, hw, hwZ⟩ => by
    unfold truncAt
    split_ifs with hv
    · exact ⟨[], v, rfl, hv, by simp⟩
    · have hl : ∃ u ∈ l, u ∈ Z := by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact absurd hwZ hv
        · exact ⟨w, hw, hwZ⟩
      obtain ⟨l₁, z, h, hz, hl₁⟩ := truncAt_spec Z l hl
      refine ⟨v :: l₁, z, by rw [h]; rfl, hz, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      exacts [hv, hl₁ u hu]

/-- A walk from `A` meeting `Z` has an initial segment from `A` to `Z` meeting `Z` only at its
end. -/
theorem IsLinkWalk.truncAt {l : List V} (h : IsLinkWalk E A B l) (hZ : ∃ v ∈ l, v ∈ Z) :
    IsLinkWalk E A Z (truncAt Z l) ∧ (truncAt Z l).Sublist l ∧
      ∃ l₁ z, truncAt Z l = l₁ ++ [z] ∧ z ∈ Z ∧ ∀ u ∈ l₁, u ∉ Z := by
  obtain ⟨l₁, z, hl, hz, hl₁⟩ := truncAt_spec Z l hZ
  refine ⟨⟨isChain_truncAt Z h.1, ?_, z, by rw [hl]; simp, hz⟩, (truncAt_prefix Z l).sublist,
    l₁, z, hl, hz, hl₁⟩
  rw [head?_truncAt]
  exact h.2.1

/-- A vertex of a walk from `A` before its first visit of `T` is joined to `A` off `T`. -/
theorem reachAvoid_of_mem {l l₁ l₂ : List V} {u : V} (h : IsLinkWalk E A B l)
    (hl : l = l₁ ++ l₂) (hl₁ : ∀ w ∈ l₁, w ∉ T) (hu : u ∈ l₁) : ReachAvoid E A T u := by
  obtain ⟨p, q, rfl⟩ := List.mem_iff_append.1 hu
  subst hl
  have hc := h.1
  rw [List.append_assoc, List.cons_append, List.isChain_append] at hc
  refine ⟨p ++ [u], ⟨hc.1.append (List.isChain_singleton u) fun x hx y hy => ?_, ?_, u, by simp,
    rfl⟩, fun w hw => hl₁ w ?_⟩
  · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hc.2.2 x hx u rfl
  · obtain ⟨a, ha, haA⟩ := h.2.1
    refine ⟨a, ?_, haA⟩
    rcases p with _ | ⟨c, p⟩
    · simpa using ha
    · simpa using ha
  · rcases List.mem_append.1 hw with hw | hw
    · exact List.mem_append_left _ hw
    · rw [List.mem_singleton] at hw
      exact hw ▸ List.mem_append_right _ (List.mem_cons_self ..)

/-! ### Finite Menger -/

/-- Trivial paths at the points of `F ⊆ A ∩ B`. -/
theorem isLinkage_singletons {F : Finset V} (hF : (F : Set V) ⊆ A ∩ B) :
    IsLinkage E A B (F.image fun v => [v]) ∧ (F.image fun v => [v]).card = F.card := by
  refine ⟨⟨fun l hl => ?_, fun l hl l' hl' hne v hv hv' => ?_⟩,
    Finset.card_image_of_injective _ fun a b h => List.singleton_injective h⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hl
    exact ⟨isLinkWalk_singleton (hF hv).1 (hF hv).2, List.nodup_singleton v⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hl'
    rw [List.mem_singleton] at hv hv'
    exact hne (by rw [← hv, hv'])

theorem IsLinkage.mono {𝓛 : Finset (List V)} (h : IsLinkage E A B 𝓛) (hE : E ⊆ E') :
    IsLinkage E' A B 𝓛 :=
  ⟨fun l hl => ⟨(h.1 l hl).1.mono hE, (h.1 l hl).2⟩, h.2⟩

/-- Finite Menger without edges: the paths are single vertices of `A ∩ B`. -/
theorem exists_linkage_empty (k : ℕ)
    (h : ∀ T : Finset V, Separates ∅ A B T → k ≤ T.card) :
    ∃ 𝓛 : Finset (List V), IsLinkage ∅ A B 𝓛 ∧ 𝓛.card = k := by
  have hw : ∀ l, IsLinkWalk (∅ : Finset (Sym2 V)) A B l → ∃ v, l = [v] ∧ v ∈ A ∩ B := by
    rintro (_ | ⟨a, _ | ⟨b, l⟩⟩) ⟨hc, ⟨a', ha', hA⟩, ⟨b', hb', hB⟩⟩
    · simp at ha'
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hb'
      subst ha' hb'
      exact ⟨_, rfl, hA, hB⟩
    · simp at hc
  obtain ⟨F, hF, hFk⟩ : ∃ F : Finset V, (F : Set V) ⊆ A ∩ B ∧ F.card = k := by
    by_cases hfin : (A ∩ B).Finite
    · have hk := h hfin.toFinset fun l hl => by
        obtain ⟨v, rfl, hv⟩ := hw l hl
        exact ⟨v, List.mem_singleton_self v, by simpa using hv⟩
      obtain ⟨F, hF, hFk⟩ := Finset.exists_subset_card_eq hk
      exact ⟨F, fun v hv => by simpa using hF hv, hFk⟩
    · exact Set.Infinite.exists_subset_card_eq hfin k
  obtain ⟨h1, h2⟩ := isLinkage_singletons (E := ∅) hF
  exact ⟨_, h1, h2.trans hFk⟩

/-- Deleting the edge `e` from `E` leaves the separator `S` while the walk `l` avoids `S`: then
`e = xy` with `x` joined to `A` and `y` joined to `B` off `S`. -/
theorem exists_edge_of_separates_erase {e : Sym2 V} {S : Set V} {l : List V}
    (hS : Separates (E.erase e) A B S) (hl : IsLinkWalk E A B l) (hlS : ∀ v ∈ l, v ∉ S) :
    ∃ x y, s(x, y) = e ∧ ReachAvoid (E.erase e) A S x ∧ ReachAvoid (E.erase e) B S y := by
  obtain ⟨a, ha, haA⟩ := hl.2.1
  obtain ⟨b, hb, hbB⟩ := hl.2.2
  have hRA : ReachAvoid (E.erase e) A S a := reachAvoid_self haA (hlS a (mem_of_head? ha))
  have hRB : ReachAvoid (E.erase e) B S b := reachAvoid_self hbB (hlS b (mem_of_getLast? hb))
  obtain ⟨x, y, hx, hy, hxy, hRx, hRy⟩ := exists_rel_of_isChain (P := ReachAvoid (E.erase e) A S)
    hl.1 a ha hRA b hb fun h => hS.not_reachAvoid h hRB
  have hexy : s(x, y) = e := by
    by_contra hne
    exact hRy (hRx.step (Finset.mem_erase.2 ⟨hne, hxy⟩) (hlS y hy))
  obtain ⟨x', y', hx', hy', hxy', hRx', hRy'⟩ :=
    exists_rel_of_isChain (P := fun v => ¬ ReachAvoid (E.erase e) B S v)
    hl.1 a ha (fun h => hS.not_reachAvoid hRA h) b hb (not_not.2 hRB)
  rw [not_not] at hRy'
  have hexy' : s(x', y') = e := by
    by_contra hne
    exact hRx' (hRy'.step (by rw [Sym2.eq_swap]; exact Finset.mem_erase.2 ⟨hne, hxy'⟩)
      (hlS x' hx'))
  rcases Sym2.eq_iff.1 (hexy'.trans hexy.symm) with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨x, y', hexy, hRx, hRy'⟩
  · exact (hS.not_reachAvoid hRx hRy').elim

theorem separates_self : Separates E A Z Z := fun _ hl => by
  obtain ⟨b, hb, hbZ⟩ := hl.2.2
  exact ⟨b, mem_of_getLast? hb, hbZ⟩

/-- After deleting `e = xy`, with `y` joined to `B` off the separator `S`, every set separating
`A` from `S ∪ {x}` separates `A` from `B` along `E`. -/
theorem separates_of_separates_insert {x y : V} {S : Set V}
    (hS : Separates (E.erase s(x, y)) A B S) (hy : ReachAvoid (E.erase s(x, y)) B S y)
    (hT : Separates (E.erase s(x, y)) A (insert x S) T) : Separates E A B T := by
  intro l hl
  have hX : ∃ v ∈ l, v ∈ insert x S := by
    by_contra hne
    have hxl : x ∉ l := fun h => hne ⟨x, h, Set.mem_insert _ _⟩
    obtain ⟨v, hv, hvS⟩ := hS l ⟨isChain_erase hl.1 hxl, hl.2⟩
    exact hne ⟨v, hv, Set.mem_insert_of_mem _ hvS⟩
  obtain ⟨hw, hsub, l₁, z, hl₁, -, hl₁X⟩ := hl.truncAt hX
  have hxl₁ : x ∉ l₁ := fun h => hl₁X x h (Set.mem_insert _ _)
  have hc := hw.1
  rw [hl₁, List.isChain_append] at hc
  have hc₁ := isChain_erase (y := y) hc.1 hxl₁
  have hw' : IsLinkWalk (E.erase s(x, y)) A (insert x S) (truncAt (insert x S) l) := by
    refine ⟨?_, hw.2⟩
    rw [hl₁]
    refine hc₁.append (List.isChain_singleton z) fun a ha b hb => ?_
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    rw [← hb]
    refine Finset.mem_erase.2 ⟨fun he => ?_, hc.2.2 a ha z (by simp)⟩
    have hax : a ≠ x := fun h => hl₁X a (mem_of_getLast? ha) (h ▸ Set.mem_insert _ _)
    rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hax h1
    · rw [h1] at ha
      have hne : l₁ ≠ [] := by rintro rfl; simp at ha
      obtain ⟨c, hc', hcA⟩ := hw.2.1
      rw [hl₁, List.head?_append_of_ne_nil _ hne] at hc'
      exact hS.not_reachAvoid ⟨l₁, ⟨hc₁, ⟨c, hc', hcA⟩, y, ha, rfl⟩,
        fun u hu hu' => hl₁X u hu (Set.mem_insert_of_mem _ hu')⟩ hy
  obtain ⟨v, hv, hvT⟩ := hT _ hw'
  exact ⟨v, hsub.subset hv, hvT⟩

/-- The paths of `𝓛` meet `Z` only at their last vertex. -/
def EndsAt (Z : Set V) (𝓛 : Finset (List V)) : Prop :=
  ∀ l ∈ 𝓛, ∃ l₁ z, l = l₁ ++ [z] ∧ z ∈ Z ∧ ∀ u ∈ l₁, u ∉ Z

/-- Truncating the paths of a linkage at their first visit of the target. -/
theorem IsLinkage.truncAt {𝓛 : Finset (List V)} (h : IsLinkage E A Z 𝓛) :
    IsLinkage E A Z (𝓛.image (truncAt Z)) ∧ (𝓛.image (truncAt Z)).card = 𝓛.card ∧
      EndsAt Z (𝓛.image (truncAt Z)) := by
  have hZ : ∀ l ∈ 𝓛, ∃ v ∈ l, v ∈ Z := fun l hl => by
    obtain ⟨b, hb, hbZ⟩ := (h.1 l hl).1.2.2
    exact ⟨b, mem_of_getLast? hb, hbZ⟩
  have hinj : Set.InjOn (Menger.truncAt Z) 𝓛 := by
    intro l hl l' hl' heq
    by_contra hne
    obtain ⟨a, ha, -⟩ := (h.1 l hl).1.2.1
    have ha' : a ∈ Menger.truncAt Z l := mem_of_head? (by rw [head?_truncAt]; exact ha)
    rw [heq] at ha'
    exact h.2 l hl l' hl' hne a (mem_of_head? ha) ((truncAt_prefix Z l').subset ha')
  refine ⟨⟨fun l hl => ?_, fun l hl l' hl' hne v hv hv' => ?_⟩, Finset.card_image_of_injOn hinj,
    fun l hl => ?_⟩
  · obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨hw, hsub, -⟩ := (h.1 l₀ hl₀).1.truncAt (hZ l₀ hl₀)
    exact ⟨hw, (h.1 l₀ hl₀).2.sublist hsub⟩
  · obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨l₀', hl₀', rfl⟩ := Finset.mem_image.1 hl'
    exact h.2 l₀ hl₀ l₀' hl₀' (fun he => hne (he ▸ rfl)) v ((truncAt_prefix Z l₀).subset hv)
      ((truncAt_prefix Z l₀').subset hv')
  · obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.1 hl
    exact ((h.1 l₀ hl₀).1.truncAt (hZ l₀ hl₀)).2.2

/-- A linkage to `Z` with at least `|Z|` paths, each meeting `Z` only at its end, ends at every
vertex of `Z`. -/
theorem exists_append_mem_of_endsAt {Z : Finset V} {𝓛 : Finset (List V)}
    (h : IsLinkage E A Z 𝓛) (he : EndsAt Z 𝓛) (hc : Z.card ≤ 𝓛.card) :
    ∀ z ∈ Z, ∃ l₁, l₁ ++ [z] ∈ 𝓛 := by
  have hsub : 𝓛.image List.getLast? ⊆ Z.image some := by
    intro o ho
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ho
    obtain ⟨l₁, z, rfl, hz, -⟩ := he l hl
    exact Finset.mem_image.2 ⟨z, hz, by simp⟩
  have hinj : Set.InjOn List.getLast? (𝓛 : Set (List V)) := by
    intro l hl l' hl' heq
    by_contra hne
    obtain ⟨b, hb, -⟩ := (h.1 l hl).1.2.2
    exact h.2 l hl l' hl' hne b (mem_of_getLast? hb) (mem_of_getLast? (by rw [← heq]; exact hb))
  have heq : 𝓛.image List.getLast? = Z.image some := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injOn hinj, Finset.card_image_of_injective _ (Option.some_injective _)]
    exact hc)
  intro z hz
  have hz' : some z ∈ 𝓛.image List.getLast? := heq ▸ Finset.mem_image_of_mem some hz
  obtain ⟨l, hl, hlz⟩ := Finset.mem_image.1 hz'
  obtain ⟨l₁, z', rfl, -, -⟩ := he l hl
  simp only [List.getLast?_concat, Option.some.injEq] at hlz
  exact ⟨l₁, hlz ▸ hl⟩

theorem mem_insert_coe {x u : V} {S : Finset V} :
    u ∈ ((insert x S : Finset V) : Set V) ↔ u = x ∨ u ∈ S := by
  simp

/-- The gluing step of Göring's proof: paths from `A` to `S ∪ {x}` and from `B` to `S ∪ {y}`
after deleting the edge `xy`, glued along `S` and `xy`. -/
theorem exists_linkage_glue {x y : V} {S : Finset V} {𝓟 𝓠 : Finset (List V)} {k : ℕ}
    (hE : E' ⊆ E) (he : s(x, y) ∈ E) (hx : ReachAvoid E' A S x) (hy : ReachAvoid E' B S y)
    (hdis : ∀ v, ReachAvoid E' A S v → ReachAvoid E' B S v → False)
    (h𝓟 : IsLinkage E' A (insert x S : Finset V) 𝓟) (h𝓟e : EndsAt (insert x S : Finset V) 𝓟)
    (h𝓟k : 𝓟.card = k) (h𝓠 : IsLinkage E' B (insert y S : Finset V) 𝓠)
    (h𝓠e : EndsAt (insert y S : Finset V) 𝓠) (h𝓠k : (insert y S).card ≤ 𝓠.card) :
    ∃ 𝓛 : Finset (List V), IsLinkage E A B 𝓛 ∧ 𝓛.card = k := by
  have hxS : x ∉ S := fun h => hx.not_mem (Finset.mem_coe.2 h)
  have hyS : y ∉ S := fun h => hy.not_mem (Finset.mem_coe.2 h)
  have hxy : x ≠ y := fun h => hdis x hx (h ▸ hy)
  have hRB : ∀ u, ReachAvoid E' B S u → u ∉ insert x S := by
    intro u hu hmem
    rcases Finset.mem_insert.1 hmem with rfl | hmem
    · exact hdis u hx hu
    · exact hu.not_mem (Finset.mem_coe.2 hmem)
  have hP : ∀ P ∈ 𝓟, ∃ l₁ z, P = l₁ ++ [z] ∧ z ∈ insert x S ∧
      (∀ u ∈ l₁, ReachAvoid E' A S u) ∧ IsLinkWalk E A {z} P := by
    intro P hP
    obtain ⟨l₁, z, rfl, hz, hl₁⟩ := h𝓟e P hP
    have hw := (h𝓟.1 _ hP).1
    refine ⟨l₁, z, rfl, mem_insert_coe.1 hz |> fun h => Finset.mem_insert.2 h,
      fun u hu => reachAvoid_of_mem hw rfl (fun w hw' hwS => hl₁ w hw'
        (mem_insert_coe.2 (Or.inr hwS))) hu, hw.1.imp fun _ _ h => hE h, hw.2.1, z, by simp, rfl⟩
  have hQ : ∀ Q ∈ 𝓠, ∃ m w, Q = m ++ [w] ∧ ∀ u ∈ m, ReachAvoid E' B S u := by
    intro Q hQ
    obtain ⟨m, w, rfl, -, hm⟩ := h𝓠e Q hQ
    exact ⟨m, w, rfl, fun u hu => reachAvoid_of_mem (h𝓠.1 _ hQ).1 rfl
      (fun w' hw' hwS => hm w' hw' (mem_insert_coe.2 (Or.inr hwS))) hu⟩
  have hQs := exists_append_mem_of_endsAt h𝓠 h𝓠e h𝓠k
  set m : V → List V := fun w => if h : ∃ m, m ++ [w] ∈ 𝓠 then h.choose else [] with hm_def
  have hm : ∀ w ∈ insert y S, m w ++ [w] ∈ 𝓠 := fun w hw => by
    simp only [hm_def, dif_pos (hQs w hw)]
    exact (hQs w hw).choose_spec
  have hmRB : ∀ w ∈ insert y S, ∀ u ∈ m w, ReachAvoid E' B S u := by
    intro w hw u hu
    obtain ⟨m', w', heq, hm'⟩ := hQ _ (hm w hw)
    have hmm : m w = m' := by simpa using congrArg List.dropLast heq
    exact hm' u (hmm ▸ hu)
  have hmW : ∀ w ∈ insert y S, IsLinkWalk E {w} B (m w ++ [w]).reverse ∧
      (m w ++ [w]).reverse.Nodup := by
    intro w hw
    obtain ⟨hwk, hnd⟩ := h𝓠.1 _ (hm w hw)
    refine ⟨⟨(isLinkWalk_reverse.2 hwk).1.imp fun _ _ h => hE h, ⟨w, by simp, rfl⟩,
      (isLinkWalk_reverse.2 hwk).2.2⟩, List.nodup_reverse.2 hnd⟩
  set σ : V → V := fun v => if v = x then y else v with hσ_def
  set cont : V → List V := fun v => if v = x then y :: (m y).reverse else (m v).reverse
    with hcont_def
  have hσ : ∀ v ∈ insert x S, σ v ∈ insert y S := by
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · simp [hσ_def]
    · have hvx : v ≠ x := fun h => hxS (h ▸ hv)
      simp [hσ_def, hvx, hv]
  have hσinj : ∀ v ∈ insert x S, ∀ v' ∈ insert x S, σ v = σ v' → v = v' := by
    intro v hv v' hv' h
    simp only [hσ_def] at h
    split_ifs at h with h1 h2 h2
    · rw [h1, h2]
    · rcases Finset.mem_insert.1 hv' with h3 | h3
      · exact absurd h3 h2
      · exact absurd (h ▸ h3) hyS
    · rcases Finset.mem_insert.1 hv with h3 | h3
      · exact absurd h3 h1
      · exact absurd (h.symm ▸ h3) hyS
    · exact h
  have hcont : ∀ v ∈ insert x S, (∀ u ∈ cont v, ReachAvoid E' B S u ∧ u ∈ m (σ v) ++ [σ v]) ∧
      IsLinkWalk E {v} B (v :: cont v) ∧ (cont v).Nodup := by
    intro v hv
    by_cases hvx : v = x
    · subst hvx
      have hyY : y ∈ insert y S := Finset.mem_insert_self _ _
      obtain ⟨hw, hnd⟩ := hmW y hyY
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hw hnd
      simp only [hcont_def, hσ_def, if_pos rfl]
      refine ⟨fun u hu => ?_, ⟨?_, ⟨v, rfl, rfl⟩, ?_⟩, hnd⟩
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨hy, by simp⟩
        · exact ⟨hmRB y hyY u (List.mem_reverse.1 hu), by simp [List.mem_reverse.1 hu]⟩
      · exact List.isChain_cons_cons.2 ⟨he, hw.1⟩
      · obtain ⟨b, hb, hbB⟩ := hw.2.2
        exact ⟨b, by rwa [List.getLast?_cons_cons], hbB⟩
    · have hvS : v ∈ S := (Finset.mem_insert.1 hv).resolve_left hvx
      have hvY : v ∈ insert y S := Finset.mem_insert_of_mem hvS
      obtain ⟨hw, hnd⟩ := hmW v hvY
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hw hnd
      simp only [hcont_def, hσ_def, if_neg hvx]
      exact ⟨fun u hu => ⟨hmRB v hvY u (List.mem_reverse.1 hu), by simp [List.mem_reverse.1 hu]⟩,
        hw, hnd.of_cons⟩
  have hPC : ∀ P ∈ 𝓟, ∀ v ∈ insert x S, ∀ u ∈ P, u ∉ cont v := by
    intro P hP' v hv u hu hu'
    obtain ⟨l₁, z, rfl, hz, hl₁, -⟩ := hP P hP'
    have hRu := ((hcont v hv).1 u hu').1
    rcases List.mem_append.1 hu with hu | hu
    · exact hdis u (hl₁ u hu) hRu
    · rw [List.mem_singleton] at hu
      exact hRB u hRu (hu ▸ hz)
  have hCC : ∀ v ∈ insert x S, ∀ v' ∈ insert x S, v ≠ v' → ∀ u ∈ cont v, u ∉ cont v' := by
    intro v hv v' hv' hne u hu hu'
    have hQne : m (σ v) ++ [σ v] ≠ m (σ v') ++ [σ v'] := fun h => hne (hσinj v hv v' hv' (by
      simpa using congrArg List.getLast? h))
    exact h𝓠.2 _ (hm _ (hσ v hv)) _ (hm _ (hσ v' hv')) hQne u ((hcont v hv).1 u hu).2
      ((hcont v' hv').1 u hu').2
  set glue : List V → List V := fun P => P ++ cont (P.getLastD x) with hglue_def
  have hglue : ∀ P ∈ 𝓟, ∃ z ∈ insert x S, glue P = P ++ cont z ∧ z ∈ P ∧
      IsLinkWalk E A B (glue P) ∧ (glue P).Nodup := by
    intro P hP'
    obtain ⟨l₁, z, rfl, hz, -, hw⟩ := hP P hP'
    have hg : glue (l₁ ++ [z]) = l₁ ++ [z] ++ cont z := by simp [hglue_def]
    refine ⟨z, hz, hg, by simp, ?_, ?_⟩
    · rw [hg]
      exact hw.append_tail (hcont z hz).2.1
    · rw [hg, List.nodup_append]
      exact ⟨(h𝓟.1 _ hP').2, (hcont z hz).2.2, fun a ha b hb hab =>
        hPC _ hP' z hz a ha (hab ▸ hb)⟩
  have hdisj : ∀ P ∈ 𝓟, ∀ P' ∈ 𝓟, P ≠ P' → ∀ u ∈ glue P, u ∉ glue P' := by
    intro P hP' P' hP'' hne u hu hu'
    obtain ⟨z, hz, hg, hzP, -⟩ := hglue P hP'
    obtain ⟨z', hz', hg', hzP', -⟩ := hglue P' hP''
    rw [hg] at hu
    rw [hg'] at hu'
    have hzz : z ≠ z' := fun h => h𝓟.2 P hP' P' hP'' hne z hzP (h ▸ hzP')
    rcases List.mem_append.1 hu with hu | hu <;> rcases List.mem_append.1 hu' with hu' | hu'
    · exact h𝓟.2 P hP' P' hP'' hne u hu hu'
    · exact hPC P hP' z' hz' u hu hu'
    · exact hPC P' hP'' z hz u hu' hu
    · exact hCC z hz z' hz' hzz u hu hu'
  have hinj : Set.InjOn glue (𝓟 : Set (List V)) := by
    intro P hP' P' hP'' heq
    by_contra hne
    obtain ⟨a, ha, -⟩ := (h𝓟.1 P hP').1.2.1
    obtain ⟨z, -, hg, -⟩ := hglue P hP'
    exact hdisj P hP' P' hP'' hne a (by rw [hg]; exact List.mem_append_left _ (mem_of_head? ha))
      (heq ▸ (by rw [hg]; exact List.mem_append_left _ (mem_of_head? ha)))
  refine ⟨𝓟.image glue, ⟨fun l hl => ?_, fun l hl l' hl' hne u hu hu' => ?_⟩, ?_⟩
  · obtain ⟨P, hP', rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨z, -, -, -, hw, hnd⟩ := hglue P hP'
    exact ⟨hw, hnd⟩
  · obtain ⟨P, hP', rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨P', hP'', rfl⟩ := Finset.mem_image.1 hl'
    exact hdisj P hP' P' hP'' (fun h => hne (h ▸ rfl)) u hu hu'
  · rw [Finset.card_image_of_injOn hinj, h𝓟k]

/-- **Finite Menger** (vertex form): if every set separating `A` from `B` along the finite edge
set `E` has at least `k` vertices, there are `k` disjoint paths from `A` to `B` along `E`. -/
theorem exists_linkage (E : Finset (Sym2 V)) : ∀ (A B : Set V) (k : ℕ),
    (∀ T : Finset V, Separates E A B T → k ≤ T.card) →
    ∃ 𝓛 : Finset (List V), IsLinkage E A B 𝓛 ∧ 𝓛.card = k := by
  induction E using Finset.strongInduction with
  | H E ih =>
  intro A B k h
  rcases E.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · exact exists_linkage_empty k h
  by_cases hsep : ∀ T : Finset V, Separates (E.erase e) A B T → k ≤ T.card
  · obtain ⟨𝓛, h𝓛, hk⟩ := ih _ (Finset.erase_ssubset he) A B k hsep
    exact ⟨𝓛, h𝓛.mono (Finset.erase_subset _ _), hk⟩
  simp only [not_forall, not_le] at hsep
  obtain ⟨S, hS, hSk⟩ := hsep
  obtain ⟨l, hl, hlS⟩ : ∃ l, IsLinkWalk E A B l ∧ ∀ v ∈ l, v ∉ (S : Set V) := by
    by_contra hne
    refine absurd (h S fun l hl => ?_) (not_le.2 hSk)
    by_contra hl'
    exact hne ⟨l, hl, fun v hv hvS => hl' ⟨v, hv, hvS⟩⟩
  obtain ⟨x, y, rfl, hx, hy⟩ := exists_edge_of_separates_erase hS hl hlS
  have hswap : s(y, x) = s(x, y) := Sym2.eq_swap
  have hcX : ((insert x S : Finset V) : Set V) = insert x (S : Set V) := Finset.coe_insert x S
  have hcY : ((insert y S : Finset V) : Set V) = insert y (S : Set V) := Finset.coe_insert y S
  have h1 : ∀ T : Finset V, Separates (E.erase s(x, y)) A (insert x S : Finset V) T →
      k ≤ T.card := fun T hT => h T (separates_of_separates_insert hS hy (hcX ▸ hT))
  have h2 : ∀ T : Finset V, Separates (E.erase s(x, y)) B (insert y S : Finset V) T →
      k ≤ T.card := by
    intro T hT
    refine h T (Separates.symm ?_)
    rw [← hswap] at hS hx hT
    exact separates_of_separates_insert hS.symm hx (hcY ▸ hT)
  obtain ⟨𝓟, h𝓟, h𝓟k⟩ := ih _ (Finset.erase_ssubset he) _ _ k h1
  obtain ⟨𝓠, h𝓠, h𝓠k⟩ := ih _ (Finset.erase_ssubset he) _ _ k h2
  obtain ⟨h𝓟', h𝓟k', h𝓟e⟩ := h𝓟.truncAt
  obtain ⟨h𝓠', h𝓠k', h𝓠e⟩ := h𝓠.truncAt
  refine exists_linkage_glue (Finset.erase_subset _ _) he hx hy
    (fun v hA hB => hS.not_reachAvoid hA hB) h𝓟' h𝓟e (h𝓟k'.trans h𝓟k) h𝓠' h𝓠e ?_
  rw [h𝓠k', h𝓠k]
  exact (Finset.card_insert_le _ _).trans hSk

/-! ### Balls around a finite set -/

variable {G : SimpleGraph V} {S : Set V} {k : ℕ}

/-- The vertices within graph distance `n` of `S`. -/
def ball (G : SimpleGraph V) (S : Set V) : ℕ → Set V
  | 0 => S
  | n + 1 => ball G S n ∪ {v | ∃ u ∈ ball G S n, G.Adj u v}

theorem ball_finite (hG : ∀ v, (G.neighborSet v).Finite) (hS : S.Finite) :
    ∀ n, (ball G S n).Finite
  | 0 => hS
  | n + 1 => (ball_finite hG hS n).union (((ball_finite hG hS n).biUnion fun u _ => hG u).subset
      fun _ ⟨_, hu, huv⟩ => Set.mem_biUnion hu huv)

theorem ball_subset_succ (n : ℕ) : ball G S n ⊆ ball G S (n + 1) := Set.subset_union_left

theorem ball_mono {m n : ℕ} (h : m ≤ n) : ball G S m ⊆ ball G S n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (ball_subset_succ n)

theorem mem_ball_succ {n : ℕ} {u v : V} (hu : u ∈ ball G S n) (huv : G.Adj u v) :
    v ∈ ball G S (n + 1) :=
  Or.inr ⟨u, hu, huv⟩

/-- The `i`-th vertex of a walk from `S` lies in `ball i`. -/
theorem getElem_mem_ball {l : List V} (hl : l.IsChain G.Adj) (hS : ∃ a ∈ l.head?, a ∈ S) :
    ∀ (i : ℕ) (hi : i < l.length), l[i] ∈ ball G S i
  | 0, hi => by
    obtain ⟨a, ha, haS⟩ := hS
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi, Option.mem_def,
      Option.some.injEq] at ha
    rw [ha]
    exact haS
  | i + 1, hi => mem_ball_succ (getElem_mem_ball hl hS i (by omega)) (hl.getElem i hi)

/-- A walk from `S` to a vertex outside `ball t` has at least `t + 2` vertices. -/
theorem le_length_of_not_mem_ball {l : List V} {t : ℕ} (hl : l.IsChain G.Adj)
    (hS : ∃ a ∈ l.head?, a ∈ S) {b : V} (hb : b ∈ l.getLast?) (hbt : b ∉ ball G S t) :
    t + 2 ≤ l.length := by
  by_contra hlt
  have hpos : 0 < l.length := by
    rcases l with _ | _
    · simp at hb
    · simp
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.mem_def,
    Option.some.injEq] at hb
  exact hbt (ball_mono (by omega) (hb ▸ getElem_mem_ball hl hS _ (by omega)))

/-- The edges of `G` with both endpoints in the finite set `F`. -/
def edgesIn (G : SimpleGraph V) {F : Set V} (hF : F.Finite) : Finset (Sym2 V) :=
  ((hF.prod hF).toFinset.filter fun p => G.Adj p.1 p.2).image fun p => s(p.1, p.2)

theorem mem_edgesIn {F : Set V} {hF : F.Finite} {a b : V} :
    s(a, b) ∈ edgesIn G hF ↔ G.Adj a b ∧ a ∈ F ∧ b ∈ F := by
  constructor
  · intro h
    obtain ⟨⟨c, d⟩, hp, he⟩ := Finset.mem_image.1 h
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_prod] at hp
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp.2, hp.1.1, hp.1.2⟩
    · exact ⟨hp.2.symm, hp.1.2, hp.1.1⟩
  · rintro ⟨hab, ha, hb⟩
    exact Finset.mem_image.2 ⟨(a, b), by simp [ha, hb, hab], rfl⟩

/-! ### Compactness -/

/-- The restriction of `k` sequences to the steps `0, …, t`. -/
def restrictSteps (t : ℕ) (g : Fin k → ℕ → V) : Fin k → Fin (t + 1) → V := fun j i => g j i

/-- `k` disjoint paths from `S` with `t` steps. -/
def LevelPathsFin (G : SimpleGraph V) (S : Set V) (k t : ℕ) (f : Fin k → Fin (t + 1) → V) :
    Prop :=
  (∀ j, Injective (f j)) ∧ (∀ j (i : Fin t), G.Adj (f j i.castSucc) (f j i.succ)) ∧
    (∀ j, f j 0 ∈ S) ∧ ∀ j j', j ≠ j' → ∀ i i', f j i ≠ f j' i'

/-- The `k` sequences `g` are disjoint paths from `S` up to step `t`. -/
def LevelPaths (G : SimpleGraph V) (S : Set V) (k t : ℕ) (g : Fin k → ℕ → V) : Prop :=
  LevelPathsFin G S k t (restrictSteps t g)

theorem LevelPaths.of_succ {t : ℕ} {g : Fin k → ℕ → V} (h : LevelPaths G S k (t + 1) g) :
    LevelPaths G S k t g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun j i i' hii' => Fin.castSucc_injective _ (h1 j hii'), fun j i => h2 j i.castSucc,
    h3, fun j j' hjj' i i' => h4 j j' hjj' i.castSucc i'.castSucc⟩

/-- The `i`-th terms of disjoint paths from `S` lie in `ball i`. -/
theorem LevelPaths.mem_ball {t : ℕ} {g : Fin k → ℕ → V} (h : LevelPaths G S k t g) (j : Fin k) :
    ∀ i ≤ t, g j i ∈ ball G S i
  | 0, _ => h.2.2.1 j
  | i + 1, hi => mem_ball_succ (LevelPaths.mem_ball h j i (by omega))
      (h.2.1 j ⟨i, by omega⟩)

theorem levelPaths_congr {t : ℕ} {g g' : Fin k → ℕ → V} (h : ∀ j, ∀ i ≤ t, g j i = g' j i) :
    LevelPaths G S k t g ↔ LevelPaths G S k t g' := by
  have : restrictSteps t g = restrictSteps t g' := by
    funext j i
    exact h j i (by omega)
  rw [LevelPaths, LevelPaths, this]

/-- **König's lemma**: if there are `k` disjoint paths from the finite set `S` with `t` steps for
every `t`, there are `k` sequences forming disjoint paths up to every step. -/
theorem exists_forall_levelPaths (hG : ∀ v, (G.neighborSet v).Finite) (hS : S.Finite)
    (h : ∀ t, ∃ g, LevelPaths G S k t g) : ∃ g, ∀ t, LevelPaths G S k t g := by
  letI : TopologicalSpace V := ⊥
  haveI : DiscreteTopology V := ⟨rfl⟩
  set K : Set (Fin k → ℕ → V) := Set.pi Set.univ fun _ => Set.pi Set.univ fun i => ball G S i
  have hK : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun i => (ball_finite hG hS i).isCompact
  have hcl : ∀ t, IsClosed {g : Fin k → ℕ → V | LevelPaths G S k t g} := fun t => by
    have hc : Continuous (restrictSteps (V := V) (k := k) t) :=
      continuous_pi fun j => continuous_pi fun i => (continuous_apply (i : ℕ)).comp
        (continuous_apply j)
    exact (isClosed_discrete {f | LevelPathsFin G S k t f}).preimage hc
  obtain ⟨g, hg⟩ := hK.inter_right (hcl 0) |>.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun t => K ∩ {g | LevelPaths G S k t g})
    (fun t => Set.inter_subset_inter_right _ fun g hg => LevelPaths.of_succ hg)
    (fun t => by
      obtain ⟨g, hg⟩ := h t
      refine ⟨fun j i => if i ≤ t then g j i else g j 0, fun j _ i _ => ?_, ?_⟩
      · dsimp only
        split_ifs with hi
        · exact hg.mem_ball j i hi
        · exact ball_mono (Nat.zero_le i) (hg.2.2.1 j)
      · exact (levelPaths_congr fun j i hi => by simp [hi]).2 hg)
    (fun t => hK.isClosed.inter (hcl t))
  exact ⟨g, fun t => (Set.mem_iInter.1 hg t).2⟩

/-- Sequences forming disjoint paths from `S` up to every step are disjoint rays from `S`. -/
theorem rays_of_forall_levelPaths {g : Fin k → ℕ → V} (h : ∀ t, LevelPaths G S k t g) :
    (∀ j, Injective (g j) ∧ (∀ n, G.Adj (g j n) (g j (n + 1))) ∧ g j 0 ∈ S) ∧
      ∀ j j', j ≠ j' → Disjoint (range (g j)) (range (g j')) := by
  refine ⟨fun j => ⟨fun a b hab => ?_, fun n => (h (n + 1)).2.1 j ⟨n, by omega⟩, (h 0).2.2.1 j⟩,
    fun j j' hjj' => Set.disjoint_left.2 ?_⟩
  · have := (h (max a b)).1 j (a₁ := ⟨a, by omega⟩) (a₂ := ⟨b, by omega⟩) hab
    simpa using this
  · rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact (h (max a b)).2.2.2 j j' hjj' ⟨a, by omega⟩ ⟨b, by omega⟩ hb.symm

/-- `k` disjoint paths from `S` with at least `t` steps, as lists, give a level of `t` steps. -/
theorem exists_levelPaths_of_lists {t : ℕ} (L : Fin k → List V)
    (hL : ∀ j, (L j).IsChain G.Adj ∧ (L j).Nodup ∧ (∃ a ∈ (L j).head?, a ∈ S) ∧
      t + 1 ≤ (L j).length)
    (hd : ∀ j j', j ≠ j' → ∀ v ∈ L j, v ∉ L j') : ∃ g, LevelPaths G S k t g := by
  refine ⟨fun j i => if hi : i < (L j).length then (L j)[i] else
    (L j)[0]'(by have := (hL j).2.2.2; omega), ?_⟩
  have hg : ∀ j (i : Fin (t + 1)), restrictSteps t (fun j i => if hi : i < (L j).length then
      (L j)[i] else (L j)[0]'(by have := (hL j).2.2.2; omega)) j i =
        (L j)[(i : ℕ)]'(by have := (hL j).2.2.2; omega) := by
    intro j i
    simp only [restrictSteps]
    rw [dif_pos (by have := (hL j).2.2.2; omega)]
  refine ⟨fun j i i' hii' => ?_, fun j i => ?_, fun j => ?_, fun j j' hjj' i i' hii' => ?_⟩
  · rw [hg, hg] at hii'
    exact Fin.ext ((List.Nodup.getElem_inj_iff (hL j).2.1).1 hii')
  · rw [hg, hg]
    exact (hL j).1.getElem i (by have := (hL j).2.2.2; simp; omega)
  · rw [hg]
    exact getElem_mem_ball (hL j).1 (hL j).2.2.1 0 _
  · rw [hg, hg] at hii'
    exact hd j j' hjj' _ (List.getElem_mem _) (by rw [hii']; exact List.getElem_mem _)

/-! ### Menger's theorem for rays -/

/-- **Menger's theorem for rays** in a locally finite graph: if every set of fewer than `k`
vertices misses some ray starting in the finite set `S`, there are `k` disjoint rays starting in
`S`. -/
theorem exists_disjoint_rays (hG : ∀ v, (G.neighborSet v).Finite) (hS : S.Finite)
    (h : ∀ X : Finset V, X.card < k → ∃ γ : ℕ → V, Injective γ ∧
      (∀ n, G.Adj (γ n) (γ (n + 1))) ∧ (∀ n, γ n ∉ X) ∧ γ 0 ∈ S) :
    ∃ γ : Fin k → ℕ → V, (∀ j, Injective (γ j) ∧ (∀ n, G.Adj (γ j n) (γ j (n + 1))) ∧
      γ j 0 ∈ S) ∧ ∀ j j', j ≠ j' → Disjoint (range (γ j)) (range (γ j')) := by
  suffices ∀ t, ∃ g, LevelPaths G S k t g by
    obtain ⟨g, hg⟩ := exists_forall_levelPaths hG hS this
    exact ⟨g, rays_of_forall_levelPaths hg⟩
  intro t
  have hF := ball_finite hG hS (t + 1)
  set E := edgesIn G hF
  have hsep : ∀ T : Finset V, Separates E S (ball G S (t + 1) \ ball G S t) T → k ≤ T.card := by
    intro T hT
    by_contra hlt
    obtain ⟨γ, hinj, hadj, hγT, hγ0⟩ := h T (not_le.1 hlt)
    have hex : ∃ n, γ n ∉ ball G S t := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      exact Set.infinite_range_of_injective hinj ((ball_finite hG hS t).subset
        (Set.range_subset_iff.2 hne))
    have hn0 : Nat.find hex ≠ 0 := fun h0 => (h0 ▸ Nat.find_spec hex) (ball_mono
      (Nat.zero_le t) hγ0)
    have hbefore : ∀ i ≤ Nat.find hex, γ i ∈ ball G S (t + 1) := by
      intro i hi
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · exact ball_subset_succ t (not_not.1 (Nat.find_min hex hi))
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        have hγn : γ n ∈ ball G S t := not_not.1 (Nat.find_min hex (by omega))
        rw [hn]
        exact mem_ball_succ hγn (hadj n)
    have hwalk : IsLinkWalk E S (ball G S (t + 1) \ ball G S t)
        ((List.range (Nat.find hex + 1)).map γ) := by
      refine ⟨?_, ⟨γ 0, by rw [List.head?_map, List.head?_range, if_neg (Nat.succ_ne_zero _)]; rfl,
        hγ0⟩, γ (Nat.find hex), by simp [List.getLast?_range],
        hbefore _ le_rfl, Nat.find_spec hex⟩
      refine (List.isChain_map γ).2 ((List.isChain_range_succ _ _).2 fun i hi => ?_)
      exact mem_edgesIn.2 ⟨hadj i, hbefore i hi.le, hbefore (i + 1) hi⟩
    obtain ⟨v, hv, hvT⟩ := hT _ hwalk
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
    exact hγT i hvT
  obtain ⟨𝓛, h𝓛, hk⟩ := exists_linkage E S _ k hsep
  set e := (𝓛.equivFin.trans (finCongr hk)).symm
  refine exists_levelPaths_of_lists (fun j => (e j : List V)) (fun j => ?_) (fun j j' hjj' => ?_)
  · obtain ⟨⟨hc, ha, b, hb, hbB⟩, hnd⟩ := h𝓛.1 _ (e j).2
    have hc' : (e j : List V).IsChain G.Adj := hc.imp fun _ _ h => (mem_edgesIn.1 h).1
    exact ⟨hc', hnd, ha, by have := le_length_of_not_mem_ball hc' ha hb hbB.2; omega⟩
  · exact h𝓛.2 _ (e j).2 _ (e j').2 fun h => hjj' (e.injective (Subtype.ext h))

/-- **König's lemma for rays**: a vertex with infinitely many vertices reachable from it in a
locally finite graph starts a ray. -/
theorem exists_ray_of_infinite (hG : ∀ v, (G.neighborSet v).Finite) {v : V}
    (h : {w | G.Reachable v w}.Infinite) :
    ∃ γ : ℕ → V, Injective γ ∧ (∀ n, G.Adj (γ n) (γ (n + 1))) ∧ γ 0 = v := by
  suffices ∀ t, ∃ g, LevelPaths G {v} 1 t g by
    obtain ⟨g, hg⟩ := exists_forall_levelPaths hG (Set.finite_singleton v) this
    obtain ⟨hr, -⟩ := rays_of_forall_levelPaths hg
    exact ⟨g 0, (hr 0).1, (hr 0).2.1, (hr 0).2.2⟩
  intro t
  obtain ⟨w, hw, hwt⟩ := (h.sdiff (ball_finite hG (Set.finite_singleton v) t)).nonempty
  obtain ⟨p⟩ := hw
  set q := p.toPath
  have hc := (q : G.Walk v w).isChain_adj_support
  have ha : ∃ a ∈ (q : G.Walk v w).support.head?, a ∈ ({v} : Set V) :=
    ⟨v, by rw [← SimpleGraph.Walk.cons_tail_support]; rfl, rfl⟩
  have hb : w ∈ (q : G.Walk v w).support.getLast? := by
    rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support]; rfl
  refine exists_levelPaths_of_lists (fun _ => (q : G.Walk v w).support) (fun _ => ⟨hc,
    q.2.support_nodup, ha, by have := le_length_of_not_mem_ball hc ha hb hwt; omega⟩)
    fun j j' hjj' => absurd (Subsingleton.elim j j') hjj'

end Menger

open LatticeProb.Percolation in
/-- **Step `step:5.21-menger`** (Menger's theorem for rays): in an open cluster, if every set of
fewer than `k` vertices misses some infinite path starting in the finite set `S`, there are `k`
disjoint infinite paths starting in `S`. -/
theorem mengerRaysStep : Rigidity.Steps.Section5.MengerRaysStep := by
  intro ω C S k hS h
  obtain ⟨γ, hγ, hdisj⟩ := Menger.exists_disjoint_rays (G := componentGraph C)
    (fun _ => Set.toFinite _) hS fun X hX => by
      obtain ⟨γ, ⟨hinj, hadj, hX'⟩, h0⟩ := h X hX
      exact ⟨γ, hinj, hadj, hX', h0⟩
  exact ⟨γ, fun j => ⟨⟨(hγ j).1, (hγ j).2.1, fun _ => Set.mem_univ _⟩, (hγ j).2.2⟩, hdisj⟩


end Rigidity.Proofs.Section5
