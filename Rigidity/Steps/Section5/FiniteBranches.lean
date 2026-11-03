import Rigidity.Draft.Section5dStatements
import Rigidity.Proofs.Section5.Signs
import Rigidity.Steps.Section5.InfiniteDisjointPaths

/-! # Lemma 5.28: finitely many branches of the pruned block-cut tree

Carving of Lemma 5.28 (`FiniteBranchesStmt`, corrected draft L2686-2715, with the objects of Steps
1-2 of the proof of Lemma 5.27, L2456-2501). Write `a = u(x₀)`, `𝒢 ⊆ L_a` for the exploration set,
`𝒢_tree` for the pruned block-cut tree rooted at a block `B₀ ∋ x₁`, and `N = |supp f|`. A branch of
`𝒢_tree` ends at a leaf or is a ray from the root.

* `InfiniteBranchesStep` (prop:5.12 input, L2690): rays of `𝒢_tree`, and branches ending at an
  infinite leaf block, give as many disjoint infinite paths in one connected component of `L_0`.
  `𝒢` is connected in `L_a` and infinite, so `a = 0` as `u → 0`. Rays become disjoint after
  their last common vertex (cut them at a common cut-vertex depth and join consecutive
  cut-vertices inside the blocks); an infinite leaf block `L` with parent cut-vertex `c` contains
  a ray in `L \ {c}`, which meets no other block. Prop 5.12 then bounds their number by `N + 2`.
* `LeafExitStep` (step:5.27-tree, L2498-2501): the leaf `L` of a finite leaf branch is a block
  and carries an exit edge `(z, p)`, `z` in `L` and in no other vertex of the branch,
  `u(p) ≠ a`. If `L` is a pruning block this is the definition (`z` is not the parent cut-vertex,
  else the parent block of that cut-vertex prunes `L`). Otherwise `L` is a leaf of the unpruned
  tree; `ℓ_{e₁}` is minimal on `L` exactly at its parent cut-vertex, its maximum `z` on the finite
  set `L` has a smaller neighbour in `L`, and harmonicity of `ℓ_{e₁}` gives `p ∼ z` with
  `ℓ(p) > ℓ(z)`; `u(p) = a` would put `p` in `𝒢` and in `L`.
* `ExitsDistinctStep`: exits of distinct finite leaf branches are distinct (the leaves differ
  and an exit lies in its leaf block only).
* `LeafSeparatorStep` (the set `𝒢_f` of L2698-2699): for three distinct finite leaf branches
  with exits `z₁, z₂, z₃`, the points of `𝒢` carried by `𝒢_tree`, minus `z₁, z₂, z₃`, form a
  connected subset of `L_a` adjacent to each `z_i` (each kept block contains at most one exit, and
  a block minus one point is connected).
* `NoK33MinorStep` (L2711-2715, with the Jordan curve theorem on `S²`, Lemma 2.14): no three
  disjoint connected sets of `𝒞_∞` are each adjacent to three distinct points outside them (this
  would be a `K_{3,3}` minor of the planar lattice).

Glue (proved below): at most `N` exits lie in `supp f` (exits are distinct). At any other exit
`u` is harmonic, so `z` has neighbours `p, n` with `u(p) > a > u(n)`; by Lemma 5.17 (for `f` and
`-f`) the components of `p` in `{u > a}` and of `n` in `{u < a}` contain poles. With more than
`2 N²` such exits, three of them share both poles (pigeonhole), and the separator of
`LeafSeparatorStep` with these two components is a `K_{3,3}` minor. Hence
`C_branches = 2 N² + 2 N + 2`, and `M = 0`.

Deviation from the printed proof. The pigeonhole is on pairs of poles instead of pairs of points
of `∂Q_R`, and the trap of L2711-2715 is the non-planarity of `K_{3,3}`. The scale `M_h` (used
at L2695 for `z_i ∉ supp f` and at L2705 for `Q_R ∩ C₁ = ∅`) and Prop 5.20 (finite blocks, L2491,
used by the leaf claim L2498) are not needed: exits in `supp f` are counted, and leaves with an
infinite block are counted with the rays. The hypothesis `ℓ(x₀) < ℓ(x₁)` and the cone condition
of the statement are not used.

Printed issues.
* L2705: Step 1 (L2487) keeps `Q_r ⊇ supp f` away from `𝒢` and its bounded holes, while L2705
  needs this for `Q_R ⊋ Q_{R/2} ⊇ supp f`: `M_h` must be defined with `Q_R`.
* L2711: three triples with the same pair `(q₁, q₂)` need more than `2 |∂Q_R|²` triples
  (true for `R³` once `R > 128`).
-/

open LatticeProb.Percolation Rigidity.Section5

namespace Rigidity.Steps.Section5

/-- `S` is the branch of the tree `P` rooted at `r` ending at a leaf `v` whose carrier `κ v` is
finite. -/
def IsFiniteLeafBranch {α V : Type*} (P : SimpleGraph V) (r : V) (κ : V → Set α) (S : Set V) :
    Prop :=
  ∃ v, v ≠ r ∧ (∃! w, P.Adj v w) ∧ (∃ W : P.Walk r v, W.IsPath ∧ S = {x | x ∈ W.support}) ∧
    (κ v).Finite

/-- `z` is an exit point of the branch `S` of the tree `P` rooted at `r`: it is carried by a leaf
`v ∈ S` and by no other vertex of `S`. -/
def IsBranchExit {α V : Type*} (P : SimpleGraph V) (r : V) (κ : V → Set α) (S : Set V) (z : α) :
    Prop :=
  ∃ v ∈ S, v ≠ r ∧ (∃! w, P.Adj v w) ∧ z ∈ κ v ∧ ∀ v' ∈ S, z ∈ κ v' → v' = v

section Pruned

variable {ω : Configuration 2} (C : OpenComponent ω)

/-- The points of `𝒞_∞` carried by a vertex of the block-cut tree: the block, or the
cut-vertex. -/
def blockCutCarrier {G : SimpleGraph C} {V : Set C} : BlockCutVertex C G V → Set C
  | .inl B => B.val
  | .inr x => {x.val}

/-- The blocks of the exploration graph `𝒢`. -/
abbrev ExplorationBlock (u ℓ : C → ℝ) (x₀ x₁ : C) : Type :=
  {S : Set C // IsBlock C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) S}

/-- The vertices of `𝒢_tree` rooted at the block `B₀`. -/
abbrev PrunedVertex (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) : Type :=
  ↥(keptVertices C u ℓ x₀ x₁ (.inl B₀))

/-- The pruned block-cut tree `𝒢_tree` rooted at the block `B₀`. -/
abbrev prunedTree (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) :
    SimpleGraph (PrunedVertex C u ℓ x₀ x₁ B₀) :=
  (blockCutTree C _ _).induce (keptVertices C u ℓ x₀ x₁ (.inl B₀))

/-- The root `B₀` of `𝒢_tree`. -/
def prunedRoot (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) :
    PrunedVertex C u ℓ x₀ x₁ B₀ :=
  ⟨.inl B₀, by
    simp only [keptVertices, Set.mem_setOf_eq]
    rintro ⟨B, -, hne, hall⟩
    exact hne (by simpa using hall .nil .nil)⟩

/-- The points of `𝒢` carried by a vertex of `𝒢_tree`. -/
def prunedCarrier (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (v : PrunedVertex C u ℓ x₀ x₁ B₀) : Set C :=
  blockCutCarrier C v.val

/-- `S` is a branch of `𝒢_tree`. -/
abbrev IsPrunedBranch (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)) : Prop :=
  IsBranch (prunedTree C u ℓ x₀ x₁ B₀) (prunedRoot C u ℓ x₀ x₁ B₀) S

/-- `S` is a branch of `𝒢_tree` ending at a finite leaf. -/
abbrev IsPrunedFiniteLeafBranch (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)) : Prop :=
  IsFiniteLeafBranch (prunedTree C u ℓ x₀ x₁ B₀) (prunedRoot C u ℓ x₀ x₁ B₀)
    (prunedCarrier C u ℓ x₀ x₁ B₀) S

/-- `z ∈ 𝒢` is an exit point of the branch `S` of `𝒢_tree`. -/
abbrev IsPrunedExit (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (S : Set (PrunedVertex C u ℓ x₀ x₁ B₀)) (z : C) : Prop :=
  IsBranchExit (prunedTree C u ℓ x₀ x₁ B₀) (prunedRoot C u ℓ x₀ x₁ B₀)
    (prunedCarrier C u ℓ x₀ x₁ B₀) S z

end Pruned

/-- prop:5.12 input (L2690): finitely many rays of `𝒢_tree` from the root and branches ending at
an infinite leaf block give as many disjoint infinite paths in one connected component of
`L_0`. -/
def InfiniteBranchesStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (f : Vertex 2 → ℤ) (u : C → ℝ),
    IsDecayingPotential C f u → ∀ (ℓ : C → ℝ) (x₀ x₁ : C), (componentGraph C).Adj x₀ x₁ →
    u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
    ∀ s : Finset (Set (PrunedVertex C u ℓ x₀ x₁ B₀)), s.Nonempty →
      (∀ S ∈ s, IsPrunedBranch C u ℓ x₀ x₁ B₀ S ∧ ¬ IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S) →
      ∃ T, IsComponentOf C (levelSet u 0) T ∧ HasDisjointInfinitePaths C T s.card

/-- step:5.27-tree (L2498-2501): the leaf of a finite leaf branch of `𝒢_tree` carries an exit
edge `(z, p)` with `u(p) ≠ u(x₀)`. -/
def LeafExitStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    IsCorrectedPlane C (Pi.single 0 1) ℓ → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
    ∀ S, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S →
      ∃ z p : C, IsPrunedExit C u ℓ x₀ x₁ B₀ S z ∧ u z = u x₀ ∧ (componentGraph C).Adj z p ∧
        u p ≠ u x₀

/-- Distinct finite leaf branches of `𝒢_tree` have distinct exit points. -/
def ExitsDistinctStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C),
    (componentGraph C).Adj x₀ x₁ → u x₁ = u x₀ →
    ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
    ∀ S S' z z', IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S →
      IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S' → IsPrunedExit C u ℓ x₀ x₁ B₀ S z →
      IsPrunedExit C u ℓ x₀ x₁ B₀ S' z' → S ≠ S' → z ≠ z'

/-- The set `𝒢_f` (L2698-2699): for three distinct finite leaf branches of `𝒢_tree` with exit
points `z i`, a connected subset of `L_{u(x₀)}` avoids the `z i` and is adjacent to each. -/
def LeafSeparatorStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C),
    (componentGraph C).Adj x₀ x₁ → u x₁ = u x₀ →
    ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
    ∀ (S : Fin 3 → Set (PrunedVertex C u ℓ x₀ x₁ B₀)) (z : Fin 3 → C), Function.Injective S →
      (∀ i, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ (S i)) →
      (∀ i, IsPrunedExit C u ℓ x₀ x₁ B₀ (S i) (z i)) →
      ∃ X ⊆ levelSet u (u x₀), IsConnectedSet C X ∧ (∀ i, z i ∉ X) ∧
        ∀ i, ∃ y ∈ X, (componentGraph C).Adj (z i) y

/-- L2711-2715, from the Jordan curve theorem on `S²`: three disjoint connected sets of `𝒞_∞`
cannot each be adjacent to three distinct points outside them (no `K_{3,3}` minor in the planar
lattice). -/
def NoK33MinorStep : Prop :=
  External.JordanCurveTheoremSphere →
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (X : Fin 3 → Set C) (z : Fin 3 → C),
    (∀ j, IsConnectedSet C (X j)) → (∀ j k, j ≠ k → Disjoint (X j) (X k)) →
    Function.Injective z → (∀ i j, z i ∉ X j) →
    (∀ i j, ∃ y ∈ X j, (componentGraph C).Adj (z i) y) → False

variable {ω : Configuration 2}

/-- Fewer disjoint infinite paths. -/
theorem hasDisjointInfinitePaths_mono {C : OpenComponent ω} {S : Set C} {k m : ℕ}
    (h : HasDisjointInfinitePaths C S k) (hmk : m ≤ k) : HasDisjointInfinitePaths C S m := by
  obtain ⟨γ, hγ, hd⟩ := h
  exact ⟨fun j => γ (Fin.castLE hmk j), fun j => hγ _,
    fun j j' hjj' => hd _ _ fun h => hjj' (Fin.ext (by simpa using congrArg Fin.val h))⟩

/-- At a point `z` of the level set `L_a` where `u` is harmonic, a neighbour off `L_a` forces
neighbours of `z` above and below `a`. -/
theorem exists_above_below_of_harmonic {C : OpenComponent ω} {u : C → ℝ} {a : ℝ} {z w : C}
    (hz : componentLaplacian C u z = 0) (hza : u z = a) (hzw : (componentGraph C).Adj z w)
    (hw : u w ≠ a) :
    (∃ p, (componentGraph C).Adj z p ∧ a < u p) ∧ ∃ n, (componentGraph C).Adj z n ∧ u n < a := by
  obtain ⟨⟨p, hp, hp'⟩, n, hn, hn'⟩ :=
    Proofs.Section5.exists_pos_neg_of_harmonic (u := fun x => u x - a) (z := z) (w := w)
      (by simpa [componentLaplacian] using hz) (by simp [hza]) hzw (by simpa [sub_eq_zero] using hw)
  exact ⟨⟨p, hp, by simp at hp'; linarith⟩, n, hn, by simp at hn'; linarith⟩

/-- The counting argument of Lemma 5.28 on one cluster, given the conclusions of Prop 5.12 and
of Lemma 5.17 for `u` and `-u`. -/
theorem branches_card_le (hJ : External.JordanCurveTheoremSphere) (hI : InfiniteBranchesStep)
    (hE : LeafExitStep) (hD : ExitsDistinctStep) (hS : LeafSeparatorStep) (hK : NoK33MinorStep)
    {C : OpenComponent ω} {f : Vertex 2 → ℤ} (hf : (Function.support f).Finite) {u : C → ℝ}
    (hu : IsDecayingPotential C f u)
    (h512ω : ∀ T, IsComponentOf C (levelSet u 0) T →
      ¬ HasDisjointInfinitePaths C T ((Function.support f).ncard + 3))
    (hP : ∀ (a : ℝ) T, IsComponentOf C {x | a < u x} T → ∃ y ∈ T, f y.val ≠ 0)
    (hP' : ∀ (a : ℝ) T, IsComponentOf C {x | a < (-u) x} T → ∃ y ∈ T, (-f) y.val ≠ 0)
    {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C (Pi.single 0 1) ℓ) {x₀ x₁ : C}
    (hadj : (componentGraph C).Adj x₀ x₁) (hux : u x₁ = u x₀) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (hB₀ : x₁ ∈ B₀.val) {n : ℕ} (b : Fin n → Set (PrunedVertex C u ℓ x₀ x₁ B₀))
    (hb : ∀ i, IsPrunedBranch C u ℓ x₀ x₁ B₀ (b i)) (hbinj : Function.Injective b) :
    n ≤ 2 * (Function.support f).ncard ^ 2 + 2 * (Function.support f).ncard + 2 := by
  classical
  set N := (Function.support f).ncard with hN
  -- the branches as a finset, split into finite leaf branches and the others
  set s : Finset (Set (PrunedVertex C u ℓ x₀ x₁ B₀)) := Finset.univ.image b
  have hscard : s.card = n := by
    rw [Finset.card_image_of_injective _ hbinj, Finset.card_univ, Fintype.card_fin]
  have hsb : ∀ S ∈ s, IsPrunedBranch C u ℓ x₀ x₁ B₀ S := by
    intro S hS
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
    exact hb i
  set sF := s.filter (IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀)
  set sI := s.filter (fun S => ¬ IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S)
  have hsplit : sF.card + sI.card = s.card := Finset.card_filter_add_card_filter_not _
  -- infinite branches: Prop 5.12
  have hcardI : sI.card ≤ N + 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨T, hT, hpaths⟩ := hI ω C f u hu ℓ x₀ x₁ hadj hux B₀ hB₀ sI
      (Finset.card_pos.1 (by omega))
      (fun S hS => ⟨hsb S (Finset.mem_filter.1 hS).1, (Finset.mem_filter.1 hS).2⟩)
    exact h512ω T hT (hasDisjointInfinitePaths_mono hpaths (by omega))
  -- exits of the finite leaf branches
  have hex : ∀ S : Set (PrunedVertex C u ℓ x₀ x₁ B₀), ∃ z q : C,
      IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S → IsPrunedExit C u ℓ x₀ x₁ B₀ S z ∧
        u z = u x₀ ∧ (componentGraph C).Adj z q ∧ u q ≠ u x₀ := by
    intro S
    by_cases hS : IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S
    · obtain ⟨z, q, hz⟩ := hE ω C u ℓ hℓ x₀ x₁ hadj hux B₀ hB₀ S hS
      exact ⟨z, q, fun _ => hz⟩
    · exact ⟨x₀, x₀, fun h => absurd h hS⟩
  choose z q hz using hex
  have hFS : ∀ S ∈ sF, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ S :=
    fun S hS => (Finset.mem_filter.1 hS).2
  have hzinj : ∀ S ∈ sF, ∀ S' ∈ sF, z S = z S' → S = S' := by
    intro S hS S' hS' hzz
    by_contra hne
    exact hD ω C u ℓ x₀ x₁ hadj hux B₀ hB₀ S S' (z S) (z S') (hFS S hS) (hFS S' hS')
      (hz S (hFS S hS)).1 (hz S' (hFS S' hS')).1 hne hzz
  -- exits at poles: at most `N`
  set sB := sF.filter (fun S => f (z S).val ≠ 0)
  set sG := sF.filter (fun S => ¬ f (z S).val ≠ 0)
  have hsplitF : sB.card + sG.card = sF.card := Finset.card_filter_add_card_filter_not _
  have hcardB : sB.card ≤ N := by
    rw [hN, Set.ncard_eq_toFinset_card _ hf]
    refine Finset.card_le_card_of_injOn (fun S => (z S).val) (fun S hS => ?_) ?_
    · simpa using (Finset.mem_filter.1 hS).2
    · intro S hS S' hS' hzz
      exact hzinj S (Finset.mem_filter.1 hS).1 S' (Finset.mem_filter.1 hS').1 (Subtype.ext hzz)
  -- harmonic exits: neighbours above and below, and their poles (Lemma 5.17 for `f` and `-f`)
  have hpole : ∀ S : Set (PrunedVertex C u ℓ x₀ x₁ B₀), ∃ qp qn πp πn : C, S ∈ sG →
      (componentGraph C).Adj (z S) qp ∧ (componentGraph C).Adj (z S) qn ∧
      f πp.val ≠ 0 ∧ f πn.val ≠ 0 ∧ JoinedIn C {x | u x₀ < u x} qp πp ∧
      JoinedIn C {x | -u x₀ < (-u) x} qn πn := by
    intro S
    by_cases hSG : S ∈ sG
    · obtain ⟨hSF, hf0⟩ := Finset.mem_filter.1 hSG
      obtain ⟨-, hza, hzq, hq⟩ := hz S (hFS S hSF)
      have hlap : componentLaplacian C u (z S) = 0 := by
        simpa [not_not.1 hf0] using hu.1 (z S)
      obtain ⟨⟨qp, hqp, hqp'⟩, qn, hqn, hqn'⟩ := exists_above_below_of_harmonic hlap hza hzq hq
      obtain ⟨πp, hπp, hfπp⟩ := hP (u x₀) _ ⟨qp, hqp', rfl⟩
      obtain ⟨πn, hπn, hfπn⟩ := hP' (-u x₀) _ ⟨qn, (show -u x₀ < (-u) qn by simp; linarith), rfl⟩
      exact ⟨qp, qn, πp, πn, fun _ => ⟨hqp, hqn, hfπp, by simpa using hfπn, hπp, hπn⟩⟩
    · exact ⟨x₀, x₀, x₀, x₀, fun h => absurd h hSG⟩
  choose qp qn πp πn hπ using hpole
  -- three harmonic exits sharing both poles form a `K_{3,3}` minor
  have hPf : {y : C | f y.val ≠ 0}.Finite := hf.preimage Subtype.val_injective.injOn
  have hPcard : hPf.toFinset.card ≤ N := by
    rw [hN, Set.ncard_eq_toFinset_card _ hf]
    exact Finset.card_le_card_of_injOn Subtype.val (fun y hy => by simpa using hy)
      Subtype.val_injective.injOn
  have hcardG : sG.card ≤ 2 * N ^ 2 := by
    by_contra hlt
    push Not at hlt
    have hmaps : ∀ S ∈ sG, (πp S, πn S) ∈ hPf.toFinset ×ˢ hPf.toFinset := by
      intro S hS
      obtain ⟨-, -, h1, h2, -, -⟩ := hπ S hS
      simp [h1, h2]
    have hlt' : (hPf.toFinset ×ˢ hPf.toFinset).card * 2 < sG.card := by
      rw [Finset.card_product]
      calc hPf.toFinset.card * hPf.toFinset.card * 2 ≤ N * N * 2 := by gcongr
        _ = 2 * N ^ 2 := by ring
        _ < sG.card := hlt
    obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt'
    obtain ⟨S₁, S₂, S₃, h1, h2, h3, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 hy
    set Sf : Fin 3 → Set (PrunedVertex C u ℓ x₀ x₁ B₀) := ![S₁, S₂, S₃]
    have hSf : ∀ i, Sf i ∈ sG ∧ (πp (Sf i), πn (Sf i)) = y := by
      intro i
      fin_cases i
      exacts [Finset.mem_filter.1 h1, Finset.mem_filter.1 h2, Finset.mem_filter.1 h3]
    have hSfinj : Function.Injective Sf := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first | rfl | exact absurd hij h12 | exact absurd hij h13 | exact absurd hij h23 |
          exact absurd hij.symm h12 | exact absurd hij.symm h13 | exact absurd hij.symm h23
    have hFi : ∀ i, IsPrunedFiniteLeafBranch C u ℓ x₀ x₁ B₀ (Sf i) :=
      fun i => hFS _ (Finset.mem_filter.1 (hSf i).1).1
    obtain ⟨X₀, hX₀a, hX₀c, hX₀z, hX₀adj⟩ := hS ω C u ℓ x₀ x₁ hadj hux B₀ hB₀ Sf
      (fun i => z (Sf i)) hSfinj hFi (fun i => (hz _ (hFi i)).1)
    set Xp := {w | JoinedIn C {x | u x₀ < u x} y.1 w}
    set Xn := {w | JoinedIn C {x | -u x₀ < (-u) x} y.2 w}
    have hqp : ∀ i, qp (Sf i) ∈ Xp := fun i => by
      have h := (hπ _ (hSf i).1).2.2.2.2.1
      rw [show πp (Sf i) = y.1 from congrArg Prod.fst (hSf i).2] at h
      exact joinedIn_symm h
    have hqn : ∀ i, qn (Sf i) ∈ Xn := fun i => by
      have h := (hπ _ (hSf i).1).2.2.2.2.2
      rw [show πn (Sf i) = y.2 from congrArg Prod.snd (hSf i).2] at h
      exact joinedIn_symm h
    obtain ⟨hXpc, hXpa⟩ := isConnectedSet_of_isComponentOf
      (show IsComponentOf C {x | u x₀ < u x} Xp from ⟨y.1, (hqp 0).1, rfl⟩)
    obtain ⟨hXnc, hXna⟩ := isConnectedSet_of_isComponentOf
      (show IsComponentOf C {x | -u x₀ < (-u) x} Xn from ⟨y.2, (hqn 0).1, rfl⟩)
    have hlev : ∀ i, u (z (Sf i)) = u x₀ := fun i => (hz _ (hFi i)).2.1
    -- the three sets lie in the three classes `u = a`, `u > a`, `u < a`
    have hcls : ∀ j, ∀ w ∈ ![X₀, Xp, Xn] j,
        (if u w = u x₀ then (0 : Fin 3) else if u x₀ < u w then 1 else 2) = j := by
      intro j w hw
      fin_cases j
      · simp [show u w = u x₀ from hX₀a hw]
      · have h := hXpa hw
        simp only [Set.mem_setOf_eq] at h
        simp [h.ne', h]
      · have h := hXna hw
        simp only [Set.mem_setOf_eq, Pi.neg_apply, neg_lt_neg_iff] at h
        simp [h.ne, not_lt.2 h.le]
    refine hK hJ ω C ![X₀, Xp, Xn] (fun i => z (Sf i)) (fun j => ?_) (fun j k hjk => ?_)
      (fun i j hij => ?_) (fun i j => ?_) (fun i j => ?_)
    · fin_cases j
      exacts [hX₀c, hXpc, hXnc]
    · exact Set.disjoint_left.2 fun w hj hk => hjk ((hcls j w hj).symm.trans (hcls k w hk))
    · by_contra hne
      exact hD ω C u ℓ x₀ x₁ hadj hux B₀ hB₀ (Sf i) (Sf j) _ _ (hFi i) (hFi j)
        (hz _ (hFi i)).1 (hz _ (hFi j)).1 (fun h => hne (hSfinj h)) hij
    · intro hmem
      have h := hcls j _ hmem
      fin_cases j
      · exact hX₀z i hmem
      · simp [hlev i] at h
      · simp [hlev i] at h
    · fin_cases j
      · exact hX₀adj i
      · exact ⟨qp (Sf i), hqp i, (hπ _ (hSf i).1).1⟩
      · exact ⟨qn (Sf i), hqn i, (hπ _ (hSf i).1).2.1⟩
  omega

/-- Lemma 5.28 follows from Prop 5.12, Lemma 5.17 (through Lemma 5.16), the Jordan curve theorem
on `S²` and the five steps. -/
theorem finiteBranches_of_steps {p : unitInterval} {f : Vertex 2 → ℤ}
    (hJ : External.JordanCurveTheoremSphere) (h516 : StrongMaxPrincipleStmt p)
    (h512 : InfiniteDisjointPathsStmt p f) (hI : InfiniteBranchesStep) (hE : LeafExitStep)
    (hD : ExitsDistinctStep) (hS : LeafSeparatorStep) (hK : NoK33MinorStep) :
    FiniteBranchesStmt p f := by
  intro hf
  have hf' : (Function.support (-f)).Finite := by simpa using hf
  refine ⟨2 * (Function.support f).ncard ^ 2 + 2 * (Function.support f).ncard + 2, ?_⟩
  filter_upwards [h512 hf,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 f hf,
    polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple h516 (-f) hf']
    with ω ⟨h, h512ω⟩ ⟨_, hP⟩ ⟨_, hP'⟩
  exact ⟨h, 0, fun u hu hsupp ℓ hℓ x₀ x₁ hadj _ hux _ _ B₀ hB₀ n b hb hbinj =>
    branches_card_le hJ hI hE hD hS hK hf hu (h512ω u hu hsupp) (hP u hu hsupp)
      (hP' (-u) (isDecayingPotential_neg hu) (by simpa using hsupp)) hℓ hadj hux B₀ hB₀ b hb
      hbinj⟩

end Rigidity.Steps.Section5
