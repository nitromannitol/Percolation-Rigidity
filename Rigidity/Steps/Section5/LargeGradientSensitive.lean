import Rigidity.Steps.Section5.FiniteBranches
import Rigidity.External.CorrectorQuantitative

/-! # Lemma 5.27: a sensitive edge near every good point

Carving of Lemma 5.27 (`lemma:large-gradient-implies-not-in-level-set`, corrected draft L2413-2419,
proof L2434-2657). Write `ℓ = ℓ_{e₁}`, `x₁ = x₀ + e₁`, `a = u(x₀) = u(x₁)`, `𝒢 ⊆ L_a` for the
exploration set and `𝒢_tree` for the pruned block-cut tree rooted at a block `B₀ ∋ x₁` (the objects
of `Rigidity/Draft/Section5dStatements.lean`). An edge `(y, z)` of `𝒞_∞` is sensitive when
`∇ℓ(y, z) ≠ 0` and `∇u(y, z) ≠ 0`.

* `CorrectedPlaneMinimalScaleStep` (step:5.27-Mh, eq. `def-Mh`, L2457-2462): from Theorem 2.5, a
  scale `M_h`, uniform in the corrected plane, beyond which `ℓ` on the cone exceeds `ℓ` on
  `𝒞_∞ ∩ (Q_r ∪ L_-)`.
* `ExplorationBlockStep` (step:5.27-graph): the blocks of `𝒢` are biconnected subsets of `L_a`.
* `ExplorationHolesStep` (step:5.27-graph, third point, L2487-2490): beyond `M_h`, no finite
  connected component of `ℤ² \ S`, `S ⊆ 𝒢`, meets `supp f ⊆ Q_r`.
* `RootBlockStep` (Step 2, L2496, corrected): either `x₁` carries a sensitive edge or some block
  `B₀ ∋ x₁` receives from `x₁` an outgoing flux at least `C_χ / 4`.
* `LeafSensitiveStep` (step:5.27-tree, L2498-2500): a finite leaf of `𝒢_tree` carries a sensitive
  edge (maximum principle for `ℓ` on the leaf).
* `FluxBalanceStep` (step:5.27-flux, eqs. `fluxincreasesthroughbiconnectedcomponents`,
  `fluxincreasesthroughbiconnectedcomponents2`, L2503-2540): discrete integration by parts of
  `Δℓ = 0` over a finite kept block minus its cut-vertices, and at a kept cut-vertex.
* `FluxGrowthStep` (step:5.27-regularity (ii), eq. `increasevaluefluxcorr`, L2542-2561):
  `ℓ(x_cut,1) ≥ ℓ(x_cut,0) + i_in(x_cut,1) / 4`.
* `GreedyExplorationStep` (step:5.27-explore, L2563-2602, eq. `lowerboundiin1410`): the greedy
  path of maximal flux in `𝒢_tree`; from Lemma 5.28 every incoming flux along it is at least
  `(C_χ / 4) exp(-C_branches)`.
* `ExplorationAssemblyStep` (Step 6, Case 1, L2606-2627, and Case 2, L2655-2656): the points `E` of the
  blocks of the greedy path; `ℓ` grows by `i / 4` across each cut-vertex separating `x₁` from
  `y ∈ E`, and `E` contains a sensitive edge or is unbounded.
* `TerminationWindowStep` (Step 6, L2641-2652): along an exploration path, every index `i` with
  `E_R(γ(i))` lies within `W ≥ 4R²` of a visit to a separating cut-vertex, by Prop 5.20 for the
  block that would otherwise contain `W + 1` consecutive points of `γ`.

Glue (`largeGradientSensitive_of_steps`, `Rigidity/Steps/Section5/DirectionFree.lean`): with `D = |y - x₀|₁ ≥ C₀` for
`y ∈ E` and `s` the number of separating cut-vertices on an exploration path to `y`, `G_1`
gives `c₁ D ≤ (2W + 1) s`, the growth gives `ℓ(y) - ℓ(x₀) ≥ (C_χ / 16) e^{-C_branches} s`, and
`G_2` gives `ℓ(y) - ℓ(x₀) ≤ 4 ⌈D⌉`; the choice of `C_χ` makes these incompatible. Part (i)
follows from Lemma 5.25 and Prop 5.24 (below).

Constants: `C_f` from Prop 5.20 (with `r = C_f / 2`), `C_branches` from Lemma 5.28, `R ≥ 1` and
`c₁` from Prop 5.24, `W = ⌈4R²⌉`, `C_χ = max(1, 128 (2W + 1) exp(C_branches) / c₁)`, `K₀` from
Lemma 5.25 enlarged so that `C exp(-c K₀)` (Prop 5.24) is below the bound of Lemma 5.25, and
`C₀ = max(K₀, W + 1, 2)`; `M = max(M_h, M)` of Lemma 5.28.

**Printed error, eq. `defG1` (L2347-2352).** `G_1(x, K)` is printed with "there exists a path
`γ`". Step 6 (L2644-2646) applies `G_1(x₀, K₀)` to a
given path, the increasing path of `𝒢` from `x₀` to `y`; this needs "for every path `γ` of
`𝒞_∞` from `x` with `|γ(end) - x| ≥ K`". With the existential `G_1` the printed proof of (ii)
does not go through: the existential event holds as soon as some path from `x` has many points in
`E_R`, which says nothing about the paths of `𝒢`. The universal reading is also the one under
which eq. `PG1goesto1` holds: its complement is the event of Prop 5.24. (The error recorded in
`GoodEventLowerBound.lean` for `PG1goesto1` is a consequence of the existential reading.) The draft `eventG1` is the universal event ([C31]),
and the draft `eventG3` is direction-free ([C32]): the proof uses `x₁ = x₀ + e₁` only through
`|x₁ - x₀|₁ = 1`. Lemma 5.27 is proved in `Rigidity/Steps/Section5/DirectionFree.lean`
(`largeGradientSensitive_of_steps`) with `x₁` the neighbour given by `G_3`.

**Printed error, root flux (L2571-2575).** The claim `Σᵢ i_in(x_root,i) ≥ C_χ` fails when `x₁` is
a cut-vertex of `𝒢` and the root block is chosen arbitrarily: `ℓ ≥ ℓ(x₁)` on `𝒢`, so
`i_in(x₁) ≤ 0`, and the flux leaving `x₁` may enter the other blocks of `x₁`. `RootBlockStep`
chooses `B₀` maximizing the outgoing flux of `x₁` (at most four blocks contain `x₁`), and
`FluxBalance` bounds the flux into the cut-vertices of `B₀` other than `x₁`.

**Printed error, constants (L2629-2652).** With correction [C24] (`osc ≤ 4R'` on `Q_{R'}(x)`)
the last display reads `4 |y - x₀| ≥ (100/32) |y - x₀|`, which is no contradiction. Moreover a
window `|i - j| ≤ 4R²` around each separating cut-vertex covers up to `8R² + 1` indices, so the
count gives `N ≥ c₁ |y - x₀| / (8R² + 1)`, not `c₁ |y - x₀| / (4R²)` (L2650). The constant
`C_χ = 100 R² exp(C_branches) / c₁` is replaced by the one above.

Deviations. Finiteness of the blocks of `𝒢` (L2491) is not used: an infinite block on the greedy
path makes `E` unbounded, which the counting of Step 6 excludes (as in Case 2). Prop 5.12 enters
only through Lemma 5.28. `C_branches` is the bound of Lemma 5.28, not `2R³`.

The statement carries no hypothesis on `p`; the hypotheses `p_c(2) < p < 1` of Section 5 are
hypotheses of `largeGradientSensitive_of_steps` (they are needed by Theorem 2.5).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Classical

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.External

/-! ### Objects of the proof -/

/-- The negative half-line `L_- = {(-x, 0) : x ∈ ℕ}`. -/
def negativeLine : Set (Vertex 2) := {y | y 0 ≤ 0 ∧ y 1 = 0}

section Exploration

variable {ω : Configuration 2} (C : OpenComponent ω)

/-- `(y, z)` is a sensitive edge (eq. `sensitivityprop`): an edge of `𝒞_∞` with
`∇ℓ(y, z) ≠ 0` and `∇u(y, z) ≠ 0`. -/
def IsSensitiveEdge (u ℓ : C → ℝ) (y z : C) : Prop :=
  (componentGraph C).Adj y z ∧ ℓ y ≠ ℓ z ∧ u y ≠ u z

/-- `γ` is an exploration path: a path of `𝒞_∞` in `L_{u(x₀)}` from `x₀` through `x₁` along which
`ℓ` increases strictly after the first step (the paths in the definition of `𝒢`). -/
def IsExplorationPath (u ℓ : C → ℝ) (x₀ x₁ : C) {n : ℕ} (γ : Fin (n + 1) → C) : Prop :=
  1 ≤ n ∧ (∀ i : Fin n, (componentGraph C).Adj (γ i.castSucc) (γ i.succ)) ∧
    (∀ i, u (γ i) = u x₀) ∧ γ 0 = x₀ ∧ γ 1 = x₁ ∧
    ∀ i : Fin n, 1 ≤ (i : ℕ) → ℓ (γ i.castSucc) < ℓ (γ i.succ)

/-- The points of `𝒢` separating `x₁` from `y`: every walk of `𝒢` from `x₁` to `y` visits them. -/
def separators (u ℓ : C → ℝ) (x₀ x₁ y : C) : Set C :=
  {c | c ≠ x₁ ∧ c ≠ y ∧ ∀ q : (explorationGraph C u ℓ x₀ x₁).Walk x₁ y, c ∈ q.support}

/-- The number of indices at which `γ` visits a point separating `x₁` from its endpoint. -/
noncomputable def separatorCount (u ℓ : C → ℝ) (x₀ x₁ : C) {n : ℕ} (γ : Fin (n + 1) → C) : ℕ :=
  (Finset.univ.filter fun j => γ j ∈ separators C u ℓ x₀ x₁ (γ (Fin.last n))).card

/-- The incoming flux `Σ_{y ∈ B, y ∼ c} (ℓ(c) - ℓ(y))` of `ℓ` at `c` from the block `B`. -/
noncomputable def incomingFlux (ℓ : C → ℝ) (B : Set C) (c : C) : ℝ :=
  ∑ y ∈ (componentGraph C).neighborFinset c with y ∈ B, (ℓ c - ℓ y)

/-- The outgoing flux `Σ_{y ∈ B, y ∼ c} (ℓ(y) - ℓ(c))` of `ℓ` at `c` into the block `B`. -/
noncomputable def outgoingFlux (ℓ : C → ℝ) (c : C) (B : Set C) : ℝ :=
  ∑ y ∈ (componentGraph C).neighborFinset c with y ∈ B, (ℓ y - ℓ c)

/-- The cut-vertices of `𝒢`. -/
abbrev ExplorationCut (u ℓ : C → ℝ) (x₀ x₁ : C) : Type :=
  {x : C // IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) x}

/-- In `𝒢_tree` rooted at `B₀`, `w` is a child of `v`: both are kept, adjacent in the block-cut
tree, and `v` is a strict ancestor of `w`. -/
def IsTreeChild (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁)
    (v w : BlockCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁)) :
    Prop :=
  v ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) ∧ w ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) ∧
    (blockCutTree C _ _).Adj v w ∧ IsStrictAncestor (blockCutTree C _ _) (.inl B₀) v w

/-- The conclusion of Step 2 (L2498-2500): a finite kept block which is a pruning
block, or has no child in `𝒢_tree`, carries a sensitive edge. -/
def LeafSensitive (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) : Prop :=
  ∀ B : ExplorationBlock C u ℓ x₀ x₁, Sum.inl B ∈ keptVertices C u ℓ x₀ x₁ (.inl B₀) →
    B.val.Finite → (IsPruningBlock C u ℓ (u x₀) B.val ∨
      ∀ c : ExplorationCut C u ℓ x₀ x₁, ¬ IsTreeChild C u ℓ x₀ x₁ B₀ (.inl B) (.inr c)) →
    ∃ y ∈ B.val, ∃ z, IsSensitiveEdge C u ℓ y z

/-- The conclusion of Step 3 (L2503-2540, root clause corrected): for a finite non-pruning root,
the flux into its cut-vertices other than `x₁` bounds the outgoing flux of `x₁`; for a finite
non-pruning kept block with parent `x_cut,0`, eq. `fluxincreasesthroughbiconnectedcomponents`;
at a kept cut-vertex, eq. `fluxincreasesthroughbiconnectedcomponents2`. -/
def FluxBalance (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) : Prop :=
  (∀ hB : B₀.val.Finite, ¬ IsPruningBlock C u ℓ (u x₀) B₀.val →
    outgoingFlux C ℓ x₁ B₀.val ≤ ∑ c ∈ hB.toFinset with
      (IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) c ∧ c ≠ x₁),
      incomingFlux C ℓ B₀.val c) ∧
  (∀ (B : ExplorationBlock C u ℓ x₀ x₁) (c₀ : ExplorationCut C u ℓ x₀ x₁),
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c₀) (.inl B) → ∀ hB : B.val.Finite,
    ¬ IsPruningBlock C u ℓ (u x₀) B.val →
    outgoingFlux C ℓ c₀.val B.val ≤ ∑ c ∈ hB.toFinset with
      (IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) c ∧
        c ≠ c₀.val), incomingFlux C ℓ B.val c) ∧
  ∀ (P : ExplorationBlock C u ℓ x₀ x₁) (c : ExplorationCut C u ℓ x₀ x₁),
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inl P) (.inr c) →
    incomingFlux C ℓ P.val c.val ≤ ∑ᶠ (B : ExplorationBlock C u ℓ x₀ x₁)
      (_ : IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c) (.inl B)), outgoingFlux C ℓ c.val B.val

/-- The conclusion of Step 4 (ii) (eq. `increasevaluefluxcorr`): across a kept block, from its
parent cut-vertex (or from `x₁` for the root) to a child cut-vertex `x_cut,1`, `ℓ` increases by at
least `i_in(x_cut,1) / 4`. -/
def FluxGrowth (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) : Prop :=
  (∀ c : ExplorationCut C u ℓ x₀ x₁, IsTreeChild C u ℓ x₀ x₁ B₀ (.inl B₀) (.inr c) →
    ℓ x₁ + incomingFlux C ℓ B₀.val c.val / 4 ≤ ℓ c.val) ∧
  ∀ (B : ExplorationBlock C u ℓ x₀ x₁) (c₀ c₁ : ExplorationCut C u ℓ x₀ x₁),
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inr c₀) (.inl B) →
    IsTreeChild C u ℓ x₀ x₁ B₀ (.inl B) (.inr c₁) →
    ℓ c₀.val + incomingFlux C ℓ B.val c₁.val / 4 ≤ ℓ c₁.val

/-- The conclusion of Step 5: a path `B 0 = B₀, c 1, B 1, c 2, …` of `𝒢_tree` of length `N ≤ ∞`
going down from the root, with incoming flux at least `i` at each of its cut-vertices; if it is
finite, its last block is infinite, a pruning block, or without child in `𝒢_tree`. The points
`c k` are points of `𝒞_∞`, their cut-vertex property being part of the link clause, so that
`N = 0` is possible when `𝒢` has no cut-vertex. -/
def GreedyPath (u ℓ : C → ℝ) (x₀ x₁ : C) (B₀ : ExplorationBlock C u ℓ x₀ x₁) (i : ℝ) : Prop :=
  ∃ (N : ℕ∞) (B : ℕ → ExplorationBlock C u ℓ x₀ x₁) (c : ℕ → C), B 0 = B₀ ∧
    (∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) ≤ N →
      ∃ hc : IsCutVertex C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) (c (k + 1)),
        IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (B k)) (.inr ⟨c (k + 1), hc⟩) ∧
        IsTreeChild C u ℓ x₀ x₁ B₀ (.inr ⟨c (k + 1), hc⟩) (.inl (B (k + 1))) ∧
        i ≤ incomingFlux C ℓ (B k).val (c (k + 1))) ∧
    ∀ k : ℕ, (k : ℕ∞) = N → (¬ (B k).val.Finite ∨ IsPruningBlock C u ℓ (u x₀) (B k).val ∨
      ∀ c' : ExplorationCut C u ℓ x₀ x₁, ¬ IsTreeChild C u ℓ x₀ x₁ B₀ (.inl (B k)) (.inr c'))

/-- The conclusion of Steps 2-5 used by Step 6: a set `E ⊆ 𝒢` of explored points such that `ℓ`
grows by `i / 4` per separating cut-vertex visited by an exploration path to `y ∈ E`, and `E`
carries a sensitive edge or is unbounded. -/
def ExplorationConclusion (u ℓ : C → ℝ) (x₀ x₁ : C) (i : ℝ) : Prop :=
  ∃ E ⊆ explorationSet C u ℓ x₀ x₁,
    (∀ y ∈ E, ∀ (n : ℕ) (γ : Fin (n + 1) → C), IsExplorationPath C u ℓ x₀ x₁ γ →
      γ (Fin.last n) = y → i / 4 * separatorCount C u ℓ x₀ x₁ γ ≤ ℓ y - ℓ x₀) ∧
    ((∃ y ∈ E, ∃ z, IsSensitiveEdge C u ℓ y z) ∨ ∀ D : ℝ, ∃ y ∈ E, D ≤ l1 (y.val - x₀.val))

end Exploration

/-! ### The steps -/

/-- step:5.27-Mh (eq. `def-Mh`, L2457-2462): from Theorem 2.5, for `p_c(2) < p < 1` and every `r`,
almost surely there is a scale `M_h` such that every corrected plane `ℓ_{e₁}` is larger at every
point `x` of `𝒞_∞` with `x₁ ≥ |x₂|` and `x₁ ≥ M_h` than on `𝒞_∞ ∩ (Q_r ∪ L_-)`. The minimal scale
of Theorem 2.5 does not depend on the corrected plane, nor does `M_h`. -/
def CorrectedPlaneMinimalScaleStep : Prop :=
  CorrectorQuantitativeInput → ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
    (p : ℝ) < 1 → ∀ r : ℕ, ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∃ M : ℝ, ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
        ∀ x y : uniqueInfiniteComponent h, |x.val 1| ≤ x.val 0 → M ≤ x.val 0 →
          (y.val ∈ cube r ∨ y.val ∈ negativeLine) → ℓ y < ℓ x

/-- step:5.27-graph (Step 1, L2485-2491): the blocks of `𝒢` are biconnected subsets of `L_{u(x₀)}` (an edge of
`𝒢` is an edge of `𝒞_∞`). -/
def ExplorationBlockStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C) (S : Set C),
    IsBlock C (explorationGraph C u ℓ x₀ x₁) (explorationSet C u ℓ x₀ x₁) S →
      S ⊆ levelSet u (u x₀) ∧ IsBiconnected C S

/-- step:5.27-graph (Step 1, third point, L2487-2490): if `supp f ⊆ Q_r` and `ℓ(x₀)` exceeds `ℓ`
on `𝒞_∞ ∩ (Q_r ∪ L_-)`, then for every `S ⊆ 𝒢` the finite connected components of `ℤ² \ S` avoid
`supp f`. A finite component meeting `Q_r` is left by the connected unbounded set `Q_r ∪ L_-`
through a point of `S`, where `ℓ ≥ ℓ(x₁) > ℓ(x₀)`. -/
def ExplorationHolesStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (f : Vertex 2 → ℤ) (r : ℕ) (u ℓ : C → ℝ)
    (x₀ x₁ : C), (∀ x, f x ≠ 0 → x ∈ cube r) → ℓ x₀ < ℓ x₁ →
    (∀ y : C, (y.val ∈ cube r ∨ y.val ∈ negativeLine) → ℓ y < ℓ x₀) →
    ∀ S ⊆ explorationSet C u ℓ x₀ x₁, ∀ T, IsLatticeComponentOf (Subtype.val '' S)ᶜ T →
      T.Finite → ∀ x ∈ T, f x = 0

/-- Step 2, choice of the root (L2496, corrected): if `ℓ(x₁) - ℓ(x₀) ≥ C_χ > 0`, then either `x₁`
carries a sensitive edge, or by `Δℓ(x₁) = 0` the outgoing flux of `x₁` into the at most four
blocks of `𝒢` containing it is at least `C_χ`, and one of them receives at least `C_χ / 4`. -/
def RootBlockStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    IsCorrectedPlane C (Pi.single 0 1) ℓ → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    u x₁ = u x₀ → ∀ Cχ : ℝ, 0 < Cχ → Cχ ≤ ℓ x₁ - ℓ x₀ →
      (∃ z, IsSensitiveEdge C u ℓ x₁ z) ∨
        ∃ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val ∧ Cχ / 4 ≤ outgoingFlux C ℓ x₁ B₀.val

/-- step:5.27-tree (L2498-2500): a finite kept block which prunes or has no child in `𝒢_tree`
carries a sensitive edge. For a pruning block this is its definition. Otherwise the maximum `y` of
`ℓ` on the block is not its parent cut-vertex (where `ℓ` is minimal), has a smaller neighbour in
the block, hence by harmonicity a neighbour `z` with `ℓ(z) > ℓ(y)`; `u(z) = a` would put `z` in
`𝒢` outside the block and make `y` a child cut-vertex. -/
def LeafSensitiveStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    IsCorrectedPlane C (Pi.single 0 1) ℓ → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    ℓ x₀ < ℓ x₁ → u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
      LeafSensitive C u ℓ x₀ x₁ B₀

/-- step:5.27-flux (L2503-2540): summing `Δℓ = 0` over a finite non-pruning kept block minus its
cut-vertices (eqs. `flux0`, `flux1`, `flux2`) and at a kept cut-vertex. Neighbours outside `𝒢`
contribute `≤ 0`, neighbours in `𝒢` outside the block contribute `0` (an edge of `𝒢` lies in a
block), and the contributions between two cut-vertices of the block cancel. -/
def FluxBalanceStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ),
    IsCorrectedPlane C (Pi.single 0 1) ℓ → ∀ x₀ x₁ : C, (componentGraph C).Adj x₀ x₁ →
    ℓ x₀ < ℓ x₁ → u x₁ = u x₀ → ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val →
      FluxBalance C u ℓ x₀ x₁ B₀

/-- step:5.27-regularity (ii) (L2542-2561): some neighbour `y` of `x_cut,1` in the block carries a
quarter of `i_in(x_cut,1)` (degree at most four), and `ℓ(y) ≥ ℓ(x_cut,0)` since the increasing
paths to `y` pass through `x_cut,0`. -/
def FluxGrowthStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C),
    (componentGraph C).Adj x₀ x₁ → ℓ x₀ < ℓ x₁ → u x₁ = u x₀ →
    ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val → FluxGrowth C u ℓ x₀ x₁ B₀

/-- step:5.27-explore (L2563-2602): the greedy path of maximal flux. At a block the child
cut-vertex of maximal incoming flux, at a cut-vertex the child block of maximal outgoing flux
(Step 3); along the path the flux is divided at most by `∏ (#children)`, and the side children
give distinct branches of `𝒢_tree`, so with at most `C_branches` branches (Lemma 5.28) and
`m ≤ e^{m - 1}`, every incoming flux is at least `i₀ exp(-C_branches)`. -/
def GreedyExplorationStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C),
    (componentGraph C).Adj x₀ x₁ → ℓ x₀ < ℓ x₁ → u x₁ = u x₀ →
    ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val → ∀ (Cbr : ℕ) (i₀ : ℝ), 0 < i₀ →
    i₀ ≤ outgoingFlux C ℓ x₁ B₀.val → FluxBalance C u ℓ x₀ x₁ B₀ →
    (∀ (n : ℕ) (b : Fin n → Set (PrunedVertex C u ℓ x₀ x₁ B₀)),
      (∀ k, IsPrunedBranch C u ℓ x₀ x₁ B₀ (b k)) → Function.Injective b → n ≤ Cbr) →
    GreedyPath C u ℓ x₀ x₁ B₀ (i₀ * Real.exp (-(Cbr : ℝ)))

/-- Step 6, Case 1 (L2606-2627), and Case 2 (L2655-2656): `E` is the union of the blocks of the greedy
path. The separators of `x₁` and `y ∈ B k` are among `c 1, …, c k`, every increasing path to `y`
passes through `c k`, and Step 4 gives `ℓ(c k) ≥ ℓ(x₀) + k i / 4`. A finite path ends at a finite
leaf (Step 2: sensitive edge) or at an infinite block; an infinite path visits infinitely many
cut-vertices; an infinite subset of `ℤ²` is unbounded. -/
def ExplorationAssemblyStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (u ℓ : C → ℝ) (x₀ x₁ : C),
    (componentGraph C).Adj x₀ x₁ → ℓ x₀ < ℓ x₁ → u x₁ = u x₀ →
    ∀ B₀ : ExplorationBlock C u ℓ x₀ x₁, x₁ ∈ B₀.val → ∀ i : ℝ,
      GreedyPath C u ℓ x₀ x₁ B₀ i → FluxGrowth C u ℓ x₀ x₁ B₀ → LeafSensitive C u ℓ x₀ x₁ B₀ →
      ExplorationConclusion C u ℓ x₀ x₁ i

/-- step:5.27-terminate (L2641-2652): along an exploration path `γ` with
`|γ(end) - x₀|₁ ≥ W + 1`, `W ≥ 4R²`, every index `i ≥ 1` with `E_R(γ(i))` lies within `W` of an
index at which `γ` changes block, hence visits a separator of its endpoint: otherwise `W + 1`
consecutive points of `γ` lie in one block, a finite connected set of `l¹`-diameter at least `R`,
and `E_R(γ(i))` connects the block to infinity by `C_f + 1` disjoint paths. -/
def TerminationWindowStep : Prop :=
  ∀ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω)
    (u ℓ : uniqueInfiniteComponent h → ℝ) (x₀ x₁ : uniqueInfiniteComponent h) (Cf : ℕ) (R : ℝ)
    (W : ℕ), ℓ x₀ < ℓ x₁ → 1 ≤ R → 4 * R ^ 2 ≤ W →
    (∀ S, IsBlock _ (explorationGraph _ u ℓ x₀ x₁) (explorationSet _ u ℓ x₀ x₁) S →
      ¬ HasDisjointPathsToInfinity _ S (Cf + 1)) →
    ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h), IsExplorationPath _ u ℓ x₀ x₁ γ →
      (W : ℝ) + 1 ≤ l1 ((γ (Fin.last n)).val - x₀.val) →
      (goodCount ω Cf R γ : ℝ) ≤ (2 * W + 1) * separatorCount _ u ℓ x₀ x₁ γ

/-! ### Glue -/

/-- The `l¹` norm dominates each coordinate. -/
theorem abs_le_l1 (v : Vertex 2) (i : Fin 2) : |(v i : ℝ)| ≤ l1 v :=
  Finset.single_le_sum (f := fun j => |(v j : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem l1_nonneg (v : Vertex 2) : 0 ≤ l1 v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A vertex within `l¹`-distance `r` of `x` lies in `x + Q_r`. -/
theorem mem_cubeAt_of_l1_le {x y : Vertex 2} {r : ℕ} (h : l1 (y - x) ≤ r) : y ∈ cubeAt x r := by
  intro i
  have h1 := (abs_le_l1 (y - x) i).trans h
  have h2 : ((|y i - x i| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by
    simpa [Pi.sub_apply] using h1
  exact_mod_cast h2

section Glue

variable {ω : Configuration 2} {C : OpenComponent ω}

/-- `ℓ` is strictly increasing along an exploration path. -/
theorem IsExplorationPath.strictMono {u ℓ : C → ℝ} {x₀ x₁ : C} {n : ℕ} {γ : Fin (n + 1) → C}
    (hγ : IsExplorationPath C u ℓ x₀ x₁ γ) (h01 : ℓ x₀ < ℓ x₁) : StrictMono (ℓ ∘ γ) := by
  obtain ⟨hn, -, -, h0, h1, hinc⟩ := hγ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  by_cases hi : (i : ℕ) = 0
  · obtain rfl : i = 0 := Fin.ext hi
    simpa [Function.comp, h0, Fin.succ_zero_eq_one, h1] using h01
  · exact hinc i (Nat.one_le_iff_ne_zero.2 hi)

end Glue

/-- Step 6, final computation: on one cluster, the conclusion of Steps 2-5, the window count and
the events `G_1`, `G_2` at `x₀` give a sensitive edge within `l¹`-distance `C₀` of `x₀`. -/
theorem exists_sensitiveEdge_of_explorationConclusion {ω : Configuration 2}
    {h : HasUniqueInfiniteOpenComponent ω} {u ℓ : uniqueInfiniteComponent h → ℝ} {x₀ : Vertex 2}
    {X₀ X₁ : uniqueInfiniteComponent h} {Cf W : ℕ} {R c₁ K₀ C₀ i : ℝ} (hX₀ : X₀.val = x₀)
    (h01 : ℓ X₀ < ℓ X₁) (hc₁ : 0 < c₁) (hi : 32 * (2 * W + 1) ≤ i * c₁) (hK₀ : K₀ ≤ C₀)
    (hW : (W : ℝ) + 1 ≤ C₀) (h2 : 2 ≤ C₀) (hE : ExplorationConclusion _ u ℓ X₀ X₁ i)
    (hwin : ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h),
      IsExplorationPath _ u ℓ X₀ X₁ γ → (W : ℝ) + 1 ≤ l1 ((γ (Fin.last n)).val - X₀.val) →
      (goodCount ω Cf R γ : ℝ) ≤ (2 * W + 1) * separatorCount _ u ℓ X₀ X₁ γ)
    (hG1 : ∀ (n : ℕ) (γ : Fin (n + 1) → uniqueInfiniteComponent h), IsPathOf _ γ →
      (γ 0).val = x₀ → K₀ ≤ l1 ((γ (Fin.last n)).val - x₀) →
      c₁ * l1 ((γ (Fin.last n)).val - x₀) ≤ (goodCount ω Cf R γ : ℝ))
    (hG2 : ∀ R' : ℕ, K₀ ≤ R' → ∀ y z : uniqueInfiniteComponent h, y.val ∈ cubeAt x₀ R' →
      z.val ∈ cubeAt x₀ R' → ℓ y - ℓ z ≤ 4 * R') :
    ∃ a b : uniqueInfiniteComponent h, (componentGraph _).Adj a b ∧ l1 (a.val - x₀) ≤ C₀ ∧
      ℓ a ≠ ℓ b ∧ u a ≠ u b := by
  obtain ⟨E, hEG, hEi, hEii⟩ := hE
  have hnear : ∀ y ∈ E, l1 (y.val - x₀) < C₀ := by
    intro y hy
    by_contra hfar
    replace hfar := not_lt.1 hfar
    obtain ⟨n, hn, γ, hadj, hlev, h0, h1, hlast, hinc⟩ := hEG hy
    have hγ : IsExplorationPath _ u ℓ X₀ X₁ γ := ⟨hn, hadj, hlev, h0, h1, hinc⟩
    have hinj : Function.Injective γ := (hγ.strictMono h01).injective.of_comp
    have hD := l1_nonneg (y.val - x₀)
    have hg1 := hG1 n γ ⟨hinj, hadj⟩ (by rw [h0, hX₀]) (by rw [hlast]; linarith)
    have hw := hwin n γ hγ (by rw [hlast, hX₀]; linarith)
    have hgr := hEi y hy n γ hγ hlast
    rw [hlast] at hg1
    have hDR : l1 (y.val - x₀) ≤ (⌈l1 (y.val - x₀)⌉₊ : ℝ) := Nat.le_ceil _
    have hRD : (⌈l1 (y.val - x₀)⌉₊ : ℝ) < l1 (y.val - x₀) + 1 := Nat.ceil_lt_add_one hD
    have hosc := hG2 ⌈l1 (y.val - x₀)⌉₊ (by linarith) y X₀ (mem_cubeAt_of_l1_le hDR)
      (by rw [hX₀]; intro j; simp)
    have hs0 : (0 : ℝ) ≤ separatorCount _ u ℓ X₀ X₁ γ := Nat.cast_nonneg _
    have hprod := mul_le_mul_of_nonneg_right hi hs0
    have key : c₁ * (8 * l1 (y.val - x₀)) ≤ c₁ * (i / 4 * separatorCount _ u ℓ X₀ X₁ γ) := by
      nlinarith
    have key' := le_of_mul_le_mul_left key hc₁
    linarith
  rcases hEii with ⟨y, hy, z, hadj, hℓ, hu⟩ | hunb
  · exact ⟨y, z, hadj, (hnear y hy).le, hℓ, hu⟩
  · obtain ⟨y, hy, hD⟩ := hunb C₀
    rw [hX₀] at hD
    exact absurd (hnear y hy) (not_lt.2 hD)

end Rigidity.Steps.Section5
