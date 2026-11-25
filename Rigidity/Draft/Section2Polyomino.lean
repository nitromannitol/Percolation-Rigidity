import Rigidity.Draft.Section2Statements
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Lemma 2.13 of the corrected draft (`paper/percolation-harmonic-corrected.tex`, L722-725, with
[C39]) in the special form used in the proof of Proposition 5.12 (L2124).

Lemma 2.13 as printed (Rudin, *Real and Complex Analysis*, Remark 14.20, after Theorem 14.19): the
boundary of a bounded simply connected plane domain all of whose boundary points are simple is a
Jordan curve. The general lemma is **not formalized**. The proof of Proposition 5.12 applies it
only at L2124, to the interior `𝒮` of a finite union `A + [-1/2, 1/2]²` of closed lattice squares,
`A ⊆ ℤ²`, which is connected with connected complement in `S²`, and whose boundary points are
simple. `PolyominoJordanStmt` is this case: `∂𝒮` is a closed lattice polygon without repeated
corner, hence homeomorphic to the circle `S¹`.

* Simple connectivity is the definition of the draft (L700-702): `𝒮` and its complement in `S²`,
  through a homeomorphism `σ : ℝ² → S² \ {N}` (the inverse stereographic projection), are
  connected.
* Simple boundary points follow the definition of the draft (L704-711, Rudin, Definition 14.16):
  to every sequence `xₙ ∈ 𝒮` with `xₙ → x` there correspond a continuous `γ : [0, 1) → 𝒮` with
  `γ(t) → x` as `t → 1` and times `0 < t₁ < t₂ < ⋯ < 1` with `γ(tₙ) = xₙ`.
* The corners of the squares are the points `v + (1/2, 1/2)`, `v ∈ ℤ²`. -/

open Set Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Section2

/-- The closed square `z + [-1/2, 1/2]²` of a lattice point `z ∈ ℤ²`. -/
def latticeSquare (z : Vertex 2) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ k, |p k - z k| ≤ 1 / 2}

/-- The corner `v + (1/2, 1/2)` of the lattice squares, for `v ∈ ℤ²`. -/
noncomputable def squareCorner (v : Vertex 2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun k => (v k : ℝ) + 1 / 2

/-- A simple boundary point `x` of a plane region `Ω` (corrected draft L704-711): to every
sequence `u` in `Ω` converging to `x` there correspond a continuous map `γ : [0, 1) → Ω` with
`γ(t) → x` as `t → 1⁻` and times `0 < t₀ < t₁ < ⋯ < 1` with `γ (t n) = u n`. -/
def IsSimpleBoundaryPoint (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ u : ℕ → EuclideanSpace ℝ (Fin 2), (∀ n, u n ∈ Ω) → Tendsto u atTop (𝓝 x) →
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin 2), ContinuousOn γ (Ico 0 1) ∧ MapsTo γ (Ico 0 1) Ω ∧
      Tendsto γ (𝓝[<] 1) (𝓝 x) ∧
      ∃ t : ℕ → ℝ, StrictMono t ∧ 0 < t 0 ∧ (∀ n, t n < 1) ∧ ∀ n, γ (t n) = u n

/-- **Lemma 2.13, in the form used at L2124 of the corrected draft** (the proof of
Proposition 5.12). Let `A ⊆ ℤ²` be finite and `Ω` the interior of `⋃_{z ∈ A} (z + [-1/2, 1/2]²)`.
If `Ω` is connected, its complement `S² \ σ(Ω)` in the sphere is connected, and every boundary
point of `Ω` is simple, then `∂Ω` is homeomorphic to the circle, and it is a Jordan polygon: there
are `M ≥ 3` lattice points `c 0, …, c (M - 1)`, pairwise distinct, with `c M = c 0` and `c i`,
`c (i + 1)` adjacent, such that `∂Ω` is the union of the unit segments between the corners
`c i + (1/2, 1/2)` and `c (i + 1) + (1/2, 1/2)`.

This is the special case of Lemma 2.13 (Rudin, Remark 14.20) that the draft uses; the general
Lemma 2.13 is not formalized. -/
def PolyominoJordanStmt : Prop :=
  ∀ (A : Set (Vertex 2)), A.Finite →
    ∀ (σ : EuclideanSpace ℝ (Fin 2) → S2), IsOpenEmbedding σ → range σ = {northPole}ᶜ →
    ∀ Ω : Set (EuclideanSpace ℝ (Fin 2)), Ω = interior (⋃ z ∈ A, latticeSquare z) →
      IsConnected Ω → IsConnected (σ '' Ω)ᶜ →
      (∀ x ∈ frontier Ω, IsSimpleBoundaryPoint Ω x) →
      Nonempty (frontier Ω ≃ₜ Circle) ∧
      ∃ (M : ℕ) (c : ℕ → Vertex 2), 3 ≤ M ∧ c M = c 0 ∧
        (∀ i < M, (lattice 2).Adj (c i) (c (i + 1))) ∧
        (∀ i j, i < M → j < M → c i = c j → i = j) ∧
        frontier Ω = ⋃ i < M, segment ℝ (squareCorner (c i)) (squareCorner (c (i + 1)))

end Rigidity.Section2
