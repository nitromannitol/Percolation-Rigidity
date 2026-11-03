import LatticeProb.Prob.Percolation.LatticeBondCritical
import LatticeProb.Prob.Percolation.LatticeBondGraph

/-! Well-connected cubes (the definition before Proposition 2.3 of the corrected draft) and the
literature input Proposition 2.3: a cube of radius `N` is well-connected with probability at least
`1 - C exp(-c N^s)` in supercritical Bernoulli bond percolation on `ℤ^d`.

The statement is Proposition 2.3 of the paper (corrected draft L341-347). The results cited for it
there are single-scale and do not state it in this multiscale form: P. Antal and A. Pisztora, *On
the chemical distance for supercritical Bernoulli percolation*, Ann. Probab. 24 (1996), equation
(2.24), bounds a single box event (open paths of radius larger than `N/10`, subboxes of side larger
than `N/10`); M. D. Penrose and A. Pisztora, *Large deviations for discrete and continuous
percolation*, Adv. Appl. Probab. 28 (1996), Theorem 5, concerns site percolation and is stated
there without proof; A. Pisztora, *Surface order large deviations for Ising, Potts and percolation
models*, Probab. Theory Related Fields 104 (1996), is cited for it as Theorem 3.2 by Antal and
Pisztora and as Theorems 1.2 and 3.1 (for `d ≥ 3`) by Penrose and Pisztora.

Derivation. For a cube `Q` of radius `M` and `ψ = ⌊(M/100)^{1/d}⌋`, with probability at least
`1 - C₁ exp(-c₁ ψ)` some cluster of the open edges inside `Q` crosses `Q` and every other such
cluster has `ℓ^∞`-diameter less than `ψ`. For `d = 2` this is O. Couronné and R. J. Messikh,
*Surface order large deviations for 2D FK-percolation and Potts models*, Stochastic Process. Appl.
113 (2004), Theorem 5, (7), with `g = ψ` and FK parameter `q = 1` (Bernoulli percolation, where
their threshold `p̂_g` is `p_c(2) = 1/2`); for `d ≥ 3` it is the box estimate of Pisztora (1996).
On this event the crossing cluster is the unique largest cluster of `Q` and contains every open path
with at least `M/100` steps (it has more than `ψ^d` vertices), so `Q` is a good subcube; a union
bound over the cube `x + Q_N` and the at most `(3N)^d (N/10 + 1)` subcubes of radius
`M ≥ N^{1/(10d)²}/2` gives the statement with `s = 1/(d (10d)²)`.

Conventions. `x + Q_r` is the cube of radius `r` (`size(Q_r) := r`, so "side length `M`" is read
as radius `M`). `𝒞_*` of a cube is a largest open cluster of the cube, ties broken by the
existential (any largest cluster with the stated properties). -/

open MeasureTheory LatticeProb.Percolation Classical

namespace Rigidity.External

variable {d : ℕ}

/-- The cube `x + Q_r`. -/
def cubeAt (x : Vertex d) (r : ℕ) : Set (Vertex d) := {y | ∀ i, |y i - x i| ≤ (r : ℤ)}

/-- The open edges with both endpoints in `B`. -/
def openIn (ω : Configuration d) (B : Set (Vertex d)) : SimpleGraph (Vertex d) where
  Adj y z := (openGraph ω).Adj y z ∧ y ∈ B ∧ z ∈ B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => (openGraph ω).loopless.irrefl _ h.1⟩

/-- `V` is a largest open cluster of the finite set `B`. -/
def IsLargestClusterIn (ω : Configuration d) (B V : Set (Vertex d)) : Prop :=
  (∃ x ∈ B, V = {y | (openIn ω B).Reachable x y}) ∧
    ∀ x ∈ B, {y | (openIn ω B).Reachable x y}.ncard ≤ V.ncard

/-- `V` meets both faces of `z + Q_r` in every coordinate direction, so (being a cluster of the
cube) it joins each pair of opposite faces by a path inside the cube. -/
def CrossesCube (z : Vertex d) (r : ℕ) (V : Set (Vertex d)) : Prop :=
  ∀ i : Fin d, (∃ y ∈ V, y i = z i - r) ∧ (∃ y ∈ V, y i = z i + r)

/-- `z + Q_r` is crossing: a largest cluster `𝒞_*` of it crosses it. -/
def IsCrossingCube (ω : Configuration d) (z : Vertex d) (r : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z r) V ∧ CrossesCube z r V

/-- `z + Q_M` is crossing, by a largest cluster `𝒞_*` to which every open path of length at least
`M/100` in the cube is connected inside the cube. -/
def IsGoodSubcube (ω : Configuration d) (z : Vertex d) (M : ℕ) : Prop :=
  ∃ V, IsLargestClusterIn ω (cubeAt z M) V ∧ CrossesCube z M V ∧
    ∀ (n : ℕ) (γ : Fin (n + 1) → Vertex d), Function.Injective γ →
      (∀ i : Fin n, (openIn ω (cubeAt z M)).Adj (γ i.castSucc) (γ i.succ)) →
      (M : ℝ) / 100 ≤ n → ∃ y ∈ V, (openIn ω (cubeAt z M)).Reachable (γ 0) y

/-- `x + Q_R` is well-connected: `R^{1/(10d)²} ≤ R/100`, the cube is crossing, and every cube of
radius `M ∈ [R^{1/(10d)²}/2, R/10]` meeting it is a good subcube. -/
def IsWellConnected (ω : Configuration d) (x : Vertex d) (R : ℕ) : Prop :=
  (R : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ≤ R / 100 ∧ IsCrossingCube ω x R ∧
    ∀ (z : Vertex d) (M : ℕ), (R : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) / 2 ≤ M → (M : ℝ) ≤ R / 10 →
      (cubeAt z M ∩ cubeAt x R).Nonempty → IsGoodSubcube ω z M

/-- **Proposition 2.3** (literature input). For `d ≥ 2` and `p_c(d) < p < 1` there are
`c, C > 0` and `s > 0` such that every cube `x + Q_N` is well-connected outside an event of
probability at most `C exp(-c N^s)`. -/
def WellConnectedInput : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ c C s : ℝ, 0 < c ∧ 0 < C ∧ 0 < s ∧ ∀ (x : Vertex d) (N : ℕ),
      latticeBondLaw d p {ω | ¬ IsWellConnected ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ s)))

end Rigidity.External
