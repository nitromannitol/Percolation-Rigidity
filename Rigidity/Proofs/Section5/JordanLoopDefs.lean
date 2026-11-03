import Rigidity.Draft.Section2Statements
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Proposition 5.12: the data declarations of the Jordan loop

The `structure` and `inductive` declarations of `Rigidity.Proofs.Section5.JordanLoop`, with the
definitions their fields use. They live in this leaf module because a `structure` placed after
many theorems waits in `addDecl` until the earlier asynchronous proofs are checked. The names,
namespaces and signatures are those of `JordanLoop`.
-/

open Set Filter Topology Function LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.Section5.JordanLoop

/-- The plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-! ### Components on the sphere -/

open Rigidity.Section2

/-- `W` is a connected component of `S² \ Γ`. -/
structure IsComp (Γ W : Set S2) : Prop where
  subset : W ⊆ Γᶜ
  isPreconnected : IsPreconnected W
  maximal : ∀ Y : Set S2, IsPreconnected Y → Y ⊆ Γᶜ → (Y ∩ W).Nonempty → Y ⊆ W

/-- The local picture at a point `x` of the plane: off `σ⁻¹ Γ`, a neighbourhood of `x` is covered
by two nonempty preconnected sets avoiding `σ⁻¹ Γ`. -/
structure TwoSided (σ : E2 → S2) (Γ : Set S2) (x : E2) (H₁ H₂ : Set E2) : Prop where
  ne₁ : H₁.Nonempty
  ne₂ : H₂.Nonempty
  pre₁ : IsPreconnected H₁
  pre₂ : IsPreconnected H₂
  avoid₁ : ∀ q ∈ H₁, σ q ∉ Γ
  avoid₂ : ∀ q ∈ H₂, σ q ∉ Γ
  cover : ∃ r > 0, ∀ q ∈ Metric.ball x r, σ q ∉ Γ → q ∈ H₁ ∨ q ∈ H₂

/-! ### Cyclic lists -/

section Lists

variable {α : Type*}

/-- The pairs of consecutive entries of a list. -/
def chainPairs : List α → List (α × α)
  | a :: b :: l => (a, b) :: chainPairs (b :: l)
  | _ => []

/-- The pairs of cyclically consecutive entries of a list. -/
def cyc (L : List α) : List (α × α) := chainPairs (L ++ L.take 1)

end Lists

/-! ### The boundary walk of a set of cells -/

/-- The four unit directions. -/
inductive Dir
  | E | N | W | S
  deriving DecidableEq

namespace Dir

/-- The unit vector of a direction. -/
def v : Dir → ℤ × ℤ
  | E => (1, 0) | N => (0, 1) | W => (-1, 0) | S => (0, -1)

/-- The quarter turn. -/
def rot : Dir → Dir
  | E => N | N => W | W => S | S => E

/-- The opposite direction. -/
def neg : Dir → Dir
  | E => W | N => S | W => E | S => N

end Dir

/-- The first corner of the side of the cell `c` with outward normal `n`. -/
def sideStart (c : ℤ × ℤ) : Dir → ℤ × ℤ
  | .E => (c.1, c.2 - 1) | .N => c | .W => (c.1 - 1, c.2) | .S => (c.1 - 1, c.2 - 1)

/-- The last corner of the side of the cell `c` with outward normal `n`. -/
def sideEnd (c : ℤ × ℤ) : Dir → ℤ × ℤ
  | .E => c | .N => (c.1 - 1, c.2) | .W => (c.1 - 1, c.2 - 1) | .S => (c.1, c.2 - 1)

/-- The counterclockwise boundary walk of the set of cells `S`: a cyclic list of corners without
repetitions whose consecutive pairs are exactly the sides between a cell of `S` and a cell not
in `S`. -/
structure WalkProps (S : Set (ℤ × ℤ)) (L : List (ℤ × ℤ)) : Prop where
  nodup : L.Nodup
  length : 3 ≤ L.length
  sound : ∀ x ∈ cyc L, ∃ c n, c ∈ S ∧ c + n.v ∉ S ∧ x = (sideStart c n, sideEnd c n)
  complete : ∀ c n, c ∈ S → c + n.v ∉ S → (sideStart c n, sideEnd c n) ∈ cyc L

/-! ### Spanning trees of the connectors -/

/-- The pair of coordinates of a vertex. -/
def pr (a : Vertex 2) : ℤ × ℤ := (a 0, a 1)

/-- The cell of a vertex `a`: centre `a`. -/
def vcell (a : Vertex 2) : ℤ × ℤ := pr a + pr a

/-- The cell of an edge `ab`: centre `(a + b) / 2`. -/
def ecell (a b : Vertex 2) : ℤ × ℤ := pr a + pr b

section Tree

variable {ω : Configuration 2} {C : OpenComponent ω}

/-- The graph of a set of tree edges. -/
def treeGraph (E : Set (C × C)) : SimpleGraph C := SimpleGraph.fromRel fun a b => (a, b) ∈ E

/-- A tree-like spanning structure of `V ⊆ T`: edges of `𝒞_∞` inside `V`, connecting `V`. -/
structure TreeData (T V : Set C) (E : Set (C × C)) : Prop where
  sub : V ⊆ T
  finite : V.Finite
  edge : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V ∧ (componentGraph C).Adj e.1 e.2
  conn : ∀ a ∈ V, ∀ b ∈ V, (treeGraph E).Reachable a b

end Tree

/-! ### Rays leaving the connectors -/

/-- The cells of `S` are those of the vertices in `Tv` and of edges inside `Tv`. -/
structure CellsOf (Tv : Set (Vertex 2)) (S : Set (ℤ × ℤ)) : Prop where
  vert : ∀ a, vcell a ∈ S → a ∈ Tv
  edge : ∀ a b (d : Dir), pr b = pr a + d.v → ecell a b ∈ S → a ∈ Tv ∧ b ∈ Tv
  mem : ∀ a ∈ Tv, vcell a ∈ S

/-- The hypotheses on a ray: an infinite lattice path without repetitions, starting in `Tv` and
never returning to it. -/
structure IsRay (Tv : Set (Vertex 2)) (c : ℕ → Vertex 2) : Prop where
  inj : Injective c
  adj : ∀ i, (lattice 2).Adj (c i) (c (i + 1))
  start : c 0 ∈ Tv
  leave : ∀ i, c (i + 1) ∉ Tv

/-! ### The bi-infinite path through two consecutive rays -/

section PiPath

variable {ω : Configuration 2} {C : OpenComponent ω}

/-- The hypotheses on the two rays and the tree path joining their starting points. -/
structure JoinData (T : Set C) (ra rb w : ℕ → C) (K : ℕ) : Prop where
  rayA : ∀ i, (componentGraph C).Adj (ra i) (ra (i + 1))
  rayB : ∀ i, (componentGraph C).Adj (rb i) (rb (i + 1))
  injA : Injective ra
  injB : Injective rb
  leaveA : ∀ i, ra (i + 1) ∉ T
  leaveB : ∀ i, rb (i + 1) ∉ T
  disj : ∀ i j, ra i ≠ rb j
  w0 : w 0 = ra 0
  wK : w K = rb 0
  wadj : ∀ i < K, (componentGraph C).Adj (w i) (w (i + 1))
  winj : ∀ i j, i ≤ K → j ≤ K → w i = w j → i = j
  wT : ∀ i, w i ∈ T

end PiPath

end Rigidity.Proofs.Section5.JordanLoop
