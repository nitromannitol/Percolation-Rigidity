import Rigidity.Draft.Section5cStatements
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Statement of Lemma 5.28 (finitely many branches of the pruned block-cut tree). The lemma
lives inside the proof of Lemma 5.27; its objects are defined here as in Steps 1-2 of that proof.

Given `x₀` and a neighbour `x₁` of `x₀` in `𝒞_∞` with `ℓ_{e₁}(x₁) > ℓ_{e₁}(x₀)` and
`u(x₁) = u(x₀) = a` (in the proof of Lemma 5.27, `x₁` is the neighbour of `x₀` given by the event
`G₃(x₀, C_χ)`, written `x₀ + e₁` there, [C32]):
* `𝒢` is the set of `y ∈ L_a` reached from `x₀` through `x₁` by a path of `𝒞_∞` in `L_a` along
  which `ℓ_{e₁}` increases strictly after the first step; its edges are the edges of `𝒞_∞` between
  points of `𝒢` across which `ℓ_{e₁}` is not constant;
* its blocks are the maximal biconnected subsets (the paper's definition of biconnected) and its
  cut-vertices the points whose removal disconnects `𝒢`; the block-cut tree joins a block to each
  cut-vertex it contains, and is rooted at a block containing `x₁` (any such block);
* the pruned tree `𝒢_tree` removes every strict descendant of a block that contains a point `y`
  with a neighbour `z ∈ 𝒞_∞ \ L_a`, `ℓ_{e₁}(z) ≠ ℓ_{e₁}(y)`;
* a branch is the vertex set of a path of `𝒢_tree` from the root to a leaf (a non-root vertex
  with exactly one neighbour), or of an infinite path of `𝒢_tree` from the root.
The hypotheses are those of Lemma 5.27 (ii) used by the proof of Lemma 5.28: the standing event,
`x₀` in the cone `x₀,₁ ≥ |x₀,₂|` beyond the random scale `M_h`.

Convention: like every `...Stmt` of the draft, the statement omits the paper's standing
assumption `p_c(d) < p < 1` (corrected draft L66, L231); composed theorems in
`Rigidity/Proofs/Assembly` carry it as hypotheses (`criticalProbability 2 < p`, `p < 1`). Read
alone, outside that regime, it may be false. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Section5

variable {ω : Configuration 2} (C : OpenComponent ω)

/-- The vertex set of `𝒢`. -/
def explorationSet (u ℓ : C → ℝ) (x₀ x₁ : C) : Set C :=
  {y | ∃ n : ℕ, 1 ≤ n ∧ ∃ γ : Fin (n + 1) → C,
    (∀ i : Fin n, (componentGraph C).Adj (γ i.castSucc) (γ i.succ)) ∧
    (∀ i, u (γ i) = u x₀) ∧ γ 0 = x₀ ∧ γ 1 = x₁ ∧ γ (Fin.last n) = y ∧
    ∀ i : Fin n, 1 ≤ (i : ℕ) → ℓ (γ i.castSucc) < ℓ (γ i.succ)}

/-- The graph `𝒢`: edges of `𝒞_∞` between points of `𝒢` across which `ℓ` is not constant. -/
def explorationGraph (u ℓ : C → ℝ) (x₀ x₁ : C) : SimpleGraph C where
  Adj a b := a ∈ explorationSet C u ℓ x₀ x₁ ∧ b ∈ explorationSet C u ℓ x₀ x₁ ∧
    (componentGraph C).Adj a b ∧ ℓ a ≠ ℓ b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.1.symm, fun e => h.2.2.2 e.symm⟩⟩
  loopless := ⟨fun _ h => (componentGraph C).loopless.irrefl _ h.2.2.1⟩

/-- `S` is connected in the graph `G`. -/
def ConnectedIn (G : SimpleGraph C) (S : Set C) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ hx : x ∈ S, ∃ hy : y ∈ S, (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩

/-- `S ⊆ V` is biconnected in `G`: connected, and connected after removing any of its points. -/
def BiconnectedIn (G : SimpleGraph C) (V S : Set C) : Prop :=
  S ⊆ V ∧ ConnectedIn C G S ∧ ∀ x ∈ S, ConnectedIn C G (S \ {x})

/-- A block of `(V, G)`: a maximal biconnected subset. -/
def IsBlock (G : SimpleGraph C) (V S : Set C) : Prop :=
  BiconnectedIn C G V S ∧ ∀ T, BiconnectedIn C G V T → S ⊆ T → T = S

/-- A cut-vertex of `(V, G)`. -/
def IsCutVertex (G : SimpleGraph C) (V : Set C) (x : C) : Prop :=
  x ∈ V ∧ ¬ ConnectedIn C G (V \ {x})

/-- The vertices of the block-cut tree: blocks and cut-vertices. -/
abbrev BlockCutVertex (G : SimpleGraph C) (V : Set C) : Type :=
  {S : Set C // IsBlock C G V S} ⊕ {x : C // IsCutVertex C G V x}

/-- The block-cut tree: a block is joined to each cut-vertex it contains. -/
def blockCutTree (G : SimpleGraph C) (V : Set C) : SimpleGraph (BlockCutVertex C G V) where
  Adj v w := match v, w with
    | .inl B, .inr x => x.val ∈ B.val
    | .inr x, .inl B => x.val ∈ B.val
    | _, _ => False
  symm := ⟨fun v w h => by cases v <;> cases w <;> simp_all⟩
  loopless := ⟨fun v h => by cases v <;> simp_all⟩

/-- `a` is a strict ancestor of `v` in the tree `T` rooted at `r`. -/
def IsStrictAncestor {V : Type*} (T : SimpleGraph V) (r a v : V) : Prop :=
  a ≠ v ∧ ∀ W : T.Walk r v, W.IsPath → a ∈ W.support

/-- A block that triggers pruning: it contains `y` with a neighbour `z ∈ 𝒞_∞ \ L_a` such that
`ℓ(z) ≠ ℓ(y)`. -/
def IsPruningBlock (u ℓ : C → ℝ) (a : ℝ) (B : Set C) : Prop :=
  ∃ y ∈ B, ∃ z, (componentGraph C).Adj z y ∧ u z ≠ a ∧ ℓ z ≠ ℓ y

/-- The vertices kept in `𝒢_tree`: those with no pruning block as a strict ancestor. -/
def keptVertices (u ℓ : C → ℝ) (x₀ x₁ : C)
    (r : BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)) :
    Set (BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)) :=
  {v | ¬ ∃ B, IsPruningBlock C u ℓ (u x₀) B.val ∧
    IsStrictAncestor (blockCutTree C _ _) r (.inl B) v}

/-- `S` is a branch of the tree `P` rooted at `r`: the vertex set of a path from `r` to a leaf,
or of an infinite path from `r`. -/
def IsBranch {V : Type*} (P : SimpleGraph V) (r : V) (S : Set V) : Prop :=
  (∃ v, v ≠ r ∧ (∃! w, P.Adj v w) ∧ ∃ W : P.Walk r v, W.IsPath ∧ S = {x | x ∈ W.support}) ∨
  (∃ ρ : ℕ → V, Function.Injective ρ ∧ ρ 0 = r ∧ (∀ n, P.Adj (ρ n) (ρ (n + 1))) ∧
    S = Set.range ρ)

/-- Lemma 5.28: there is `C_branches` such that, almost surely, on the standing event and for
every `x₀` in the cone beyond a random scale and every neighbour `x₁` of `x₀` in `𝒞_∞` with
`ℓ_{e₁}(x₁) > ℓ_{e₁}(x₀)` and `u(x₁) = u(x₀)`, the pruned block-cut tree `𝒢_tree` rooted at a
block `B₀ ∋ x₁` has at most `C_branches` branches. -/
def FiniteBranchesStmt (p : unitInterval) (f : Vertex 2 → ℤ) : Prop :=
  (Function.support f).Finite → ∃ Cbr : ℕ,
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ M : ℝ,
    ∀ u, IsDecayingPotential (uniqueInfiniteComponent h) f u → (Function.support u).Infinite →
    ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
    ∀ x₀ x₁ : uniqueInfiniteComponent h,
      (componentGraph _).Adj x₀ x₁ → ℓ x₀ < ℓ x₁ → u x₁ = u x₀ →
      |x₀.val 1| ≤ x₀.val 0 → M ≤ x₀.val 0 →
    ∀ B₀ : {S // IsBlock _ (explorationGraph _ u ℓ x₀ x₁) (explorationSet _ u ℓ x₀ x₁) S},
      x₁ ∈ B₀.val →
    ∀ (n : ℕ) (b : Fin n → Set (keptVertices _ u ℓ x₀ x₁ (.inl B₀))),
      (∀ i, IsBranch ((blockCutTree _ _ _).induce (keptVertices _ u ℓ x₀ x₁ (.inl B₀)))
        ⟨.inl B₀, by
          simp only [keptVertices, Set.mem_setOf_eq]
          rintro ⟨B, -, hne, hall⟩
          exact hne (by simpa using hall .nil .nil)⟩ (b i)) →
      Function.Injective b → n ≤ Cbr

end Rigidity.Section5
