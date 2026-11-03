import LatticeProb.Network.OpenLadder
import LatticeProb.Network.OpenLadderEmbedding
import LatticeProb.Prob.Percolation.CorrectedPlaneCharacterization
import LatticeProb.Prob.Percolation.LatticeLinearGrowth
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import Rigidity.Frozen.GadgetAV1
import Rigidity.Frozen.GadgetBV1

/-! Statements of the numbered results of Section 4 (integer-valued harmonic functions) that the
paper proves. The gadget is the open carrier: the network induced by the open sites, as in the
corrected Proposition 4.1 ([C9], `paper/open-gadget-correction.tex`). The cited literature inputs
that each proof uses are added as explicit hypotheses of the final theorems.

* Convention: like every `…Stmt` of the draft, the statements omit the paper's standing assumption
  `p_c(d) < p < 1` (corrected draft L66, L231); the composed theorems (`Rigidity/Proofs/Assembly`)
  carry it as hypotheses `criticalProbability d < p` and `p < 1` (and `2 ≤ d`).
* Lemma 4.8 is stated in its printed conditional form. The joint form with the gadget isolated
  in `H` is the proved support result `Rigidity.Steps.S4.NonConstantOnGadgetJointStmt`. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Section4

open LatticeProb.Network

/-- The unit voltage of the gadget network of height `n`: zero at the source `s`, one at the
target `t`, and harmonic for the unit-conductance Laplacian at every other site. -/
def IsUnitVoltage (n : ℤ) (h : OpenLadder.Vertex n → ℝ) : Prop :=
  h (OpenLadder.source n) = 0 ∧ h (OpenLadder.target n) = 1 ∧
  ∀ v, v ≠ OpenLadder.source n → v ≠ OpenLadder.target n →
    (∑ w : OpenLadder.Vertex n, if (OpenLadder.graph n).Adj v w then h w - h v else 0) = 0

/-- The site `a = (2, 1)` of the gadget of height `n ≥ 1`. -/
def siteA (n : ℕ) (hn : 1 ≤ n) : OpenLadder.Vertex n :=
  OpenLadder.left n 1 ⟨le_refl 1, by exact_mod_cast hn⟩

/-- Lemma 4.2: the effective resistance `R_n = 1/h(a)` of the gadget network of height `n`, with
unit resistance on every edge, satisfies `R_1 = 3` and `R_{n+1} = (3 R_n + 2)/(R_n + 1)`. -/
def EffectiveResistanceRecurrenceStmt : Prop :=
  (∀ n : ℕ, 1 ≤ n → ∃! h : OpenLadder.Vertex n → ℝ, IsUnitVoltage n h) ∧
  ∃ R : ℕ → ℝ,
    (∀ n : ℕ, ∀ hn : 1 ≤ n, ∀ h, IsUnitVoltage n h → R n = 1 / h (siteA n hn)) ∧
    R 1 = 3 ∧ ∀ n : ℕ, 1 ≤ n → R (n + 1) = (3 * R n + 2) / (R n + 1)

/-- Lemma 4.3: for every `n ≥ 1`, `R_n = A_{n+1} / B_n`. -/
def ReducedRationalRecursionStmt : Prop :=
  ∀ n : ℕ, ∀ hn : 1 ≤ n, ∀ h, IsUnitVoltage n h →
    1 / h (siteA n hn) = (Gadget.A (n + 1) : ℝ) / (Gadget.B n : ℝ)

variable {d : ℕ}

/-- The cube `Q_R = {x : |x|_∞ ≤ R}`. -/
def cube (d : ℕ) (R : ℕ) : Set (Vertex d) := {x | ∀ i, |x i| ≤ (R : ℤ)}

/-- The open bonds of the component `C` with both endpoints in `S`. -/
def componentBondsIn {ω : Configuration d} (C : OpenComponent ω) (S : Set (Vertex d)) :
    Set (Bond d) :=
  {e | ω e = true ∧ ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ S ∧ z ∈ C.supp}

/-- Lemma 4.7: for a deterministic nonzero slope `q`, almost surely some edge of the infinite
cluster carries a non-integer gradient of the corrected plane `ℓ_q`. -/
def DetSlopeStmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ q : Fin d → ℝ, q ≠ 0 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∀ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u →
        ∃ x y : uniqueInfiniteComponent h, (componentGraph (uniqueInfiniteComponent h)).Adj x y ∧
          u x - u y ∉ Set.range ((↑) : ℤ → ℝ)

/-- Lemma 4.8 (printed statement, `paper/percolation-harmonic.tex` L1340-1347): for a deterministic
nonzero slope `q` there is `R₀` such that for every `R ≥ R₀` there is a deterministic subgraph `H`
of `Q_R`, containing a translate of the gadget of height `R` as an induced subgraph, with
`P[𝒞_∞ ∩ Q_R = H] > 0` and `P[ℓ_q is not constant on the gadget | 𝒞_∞ ∩ Q_R = H] ≥ c R^{-2d+2}`.
The conditional probability is the ratio `P[· ∩ {𝒞_∞ ∩ Q_R = H}] / P[𝒞_∞ ∩ Q_R = H]`, and the
positivity of its denominator, implicit in the printed conditioning, is part of the statement.
The event in the numerator quantifies over corrected planes (it is not shown measurable), so the
numerator is an outer measure; this lower bound suffices for Lemma 4.7, whose contradiction is
with an upper bound.
This is the printed conditional form. The joint form with the gadget isolated in `H` is the
proved support result
`Rigidity.Steps.S4.NonConstantOnGadgetJointStmt`. -/
def NonConstantOnGadgetStmt (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval) : Prop :=
  ∀ q : Fin d → ℝ, q ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    ∃ (H : Set (Bond d)) (τ : Vertex d),
      (∀ e ∈ H, ∀ z ∈ (e : Sym2 (Vertex d)), z ∈ cube d R) ∧
      (∀ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ), τ + x ∈ cube d R) ∧
      (∀ x (hx : x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ))
          y (hy : y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ))
          (hxy : (nearestNeighborGraph d).Adj (τ + x) (τ + y)),
        bondOfAdjacent hxy ∈ H ↔
          (OpenLadder.Embedding.ambientGraph hd (R : ℤ)).Adj ⟨x, hx⟩ ⟨y, hy⟩) ∧
      0 < latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
        componentBondsIn (uniqueInfiniteComponent h) (cube d R) = H} ∧
      c * (R : ℝ) ^ (-(2 * (d : ℤ)) + 2) ≤
        (latticeBondLaw d p ({ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
            componentBondsIn (uniqueInfiniteComponent h) (cube d R) = H} ∩
          {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
            ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧
              ∃ x ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
              ∃ y ∈ OpenLadder.Embedding.ambientSites hd (R : ℤ),
              ∃ hx : τ + x ∈ (uniqueInfiniteComponent h).supp,
              ∃ hy : τ + y ∈ (uniqueInfiniteComponent h).supp,
                u ⟨τ + x, hx⟩ ≠ u ⟨τ + y, hy⟩}) /
          latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
            componentBondsIn (uniqueInfiniteComponent h) (cube d R) = H}).toReal

/-- Lemma 4.9: if, with positive probability, the cluster carries a nonconstant integer-valued
harmonic function of linear growth, then there is a deterministic slope `q` with `|q| ≥ 1` such
that almost surely the cluster carries an integer-valued harmonic function growing like `q`.
[C11: "nonconstant" and `|q| ≥ 1` as in the corrected draft.] -/
def ErgodicityLipschitzStmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  latticeBondLaw d p {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ u : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) ∧
        (∀ x, ∃ z : ℤ, u x = (z : ℝ)) ∧
        componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u ∧ ∃ x y, u x ≠ u y} ≠ 0 →
  ∃ q : Fin d → ℝ, 1 ≤ ∑ i, |q i| ∧ ∀ᵐ ω ∂latticeBondLaw d p,
    ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ u : uniqueInfiniteComponent h → ℝ,
      (∀ x, ∃ z : ℤ, u x = (z : ℝ)) ∧ IsCorrectedPlane (uniqueInfiniteComponent h) q u

/-- The quadratic polynomial `x ↦ xᵀ M x + bᵀ x + c` at a lattice point. -/
def quadratic (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (c : ℝ) (x : Vertex d) : ℝ :=
  (∑ i, ∑ j, M i j * (x i : ℝ) * (x j : ℝ)) + (∑ i, b i * (x i : ℝ)) + c

/-- Proposition 4.10: for each deterministic harmonic polynomial `p̄` of degree at most two
(`p̄(x) = xᵀ M x + bᵀ x + c` with `M` symmetric and `tr M = 0`), almost surely the cluster carries
no nonconstant integer-valued harmonic function `u` with `|u(x) - p̄(x)| / |x| → 0`. -/
def RationalMatrixStmt (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (c : ℝ), M.IsSymm → M.trace = 0 →
    ∀ᵐ ω ∂latticeBondLaw d p, ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∀ u : uniqueInfiniteComponent h → ℝ,
        (∀ x, componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
        (∀ x, ∃ z : ℤ, u x = (z : ℝ)) →
        Tendsto (fun x : uniqueInfiniteComponent h =>
            |u x - quadratic M b c x.val| / (∑ i, |(x.val i : ℝ)|)) cofinite (𝓝 0) →
        ∀ x y, u x = u y

end Rigidity.Section4
