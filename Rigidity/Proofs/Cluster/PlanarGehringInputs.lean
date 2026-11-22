import Rigidity.Proofs.Cluster.MeyersUniform

/-!
# The partition for the reverse Hölder inequality and the averages of the reach, in dimension two

Two probabilistic statements of Sections 2 and 3 of Armstrong and Dario, in the vocabulary of the
planar modules, on which the proof of Lemma 5.5 rests.

* `PlanarGehringPartition`: the partition `𝓡` of Definition 3.7 of Armstrong and Dario, obtained
  by applying Proposition 2.1 to the cubes on which the reverse Hölder inequality holds, with the
  minimal scales of Proposition 2.4. Its cells `cube (s x) x` form a partition of `ℤ²` with
  comparable neighbours (Proposition 2.1 (ii)); every predecessor `□' = cube k y`, `s(y) ≤ k`, of a
  cell is good (Proposition 2.1 (i)), good meaning here that the planar partition cubes of the
  vertices of `3□'` have scale at most `k` and `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G |3□'|` (the
  hypotheses under which `planar_meyers` uses the reverse Hölder inequality of Lemma 3.6); and for
  every exponent `t` the cells are small and their `t`-th moment is bounded on every triadic cube,
  off an event of small probability (Propositions 2.1 (iii) and 2.4: Armstrong and Dario give a
  stretched exponential bound; a bound `C 3^{-B k}` for every `B` is used here).
* `PlanarReachConcentration`: the analogue of Proposition 2.4 for the planar partition `𝒫` and the
  weights of the coarse gradients: for every power `τ`, `∑_{x ∈ □} planarReach(x)^τ ≤ A |□|` on
  every triadic cube `□` off an event of probability at most `C 3^{-B scale □}`.

Armstrong and Dario apply Proposition 2.1 to the family of cubes on which the reverse Hölder
inequality holds (Definition 3.7) and to the family on which the Meyers estimate holds
(Definition 3.9), but these events depend on the partition `𝒫` through the clusters `𝒞_*(□)` and
are not determined by the edges of `3□`, as the hypothesis (2.1) of Proposition 2.1 requires. The
two statements are therefore kept as named hypotheses.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped ENNReal

/-- **The partition `𝓡` for the reverse Hölder inequality and its minimal scales** (Armstrong and
Dario, Definition 3.7 with Propositions 2.1 and 2.4, in dimension two). -/
def PlanarGehringPartition (p : unitInterval) : Prop :=
  ∃ CG : ℝ, 0 ≤ CG ∧ ∃ s : Configuration 2 → Vertex 2 → ℕ,
    (∀ᵐ ω ∂(latticeBondLaw 2 p),
      (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (∀ z ∈ enl 1 k y, (planarPartCube ω z).scale ≤ k) ∧
          ∑ z ∈ enl 1 k y, planarReach ω z ^ 8 ≤ ENNReal.ofReal CG * 3 ^ ((k + 1) * 2)) ∧
    ∀ t : ℝ, 0 < t → ∃ K : ℝ, 0 ≤ K ∧ ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (y : Vertex 2),
      latticeBondLaw 2 p {ω | (∃ z ∈ enl 1 k y, k < s ω z) ∨
          K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ s ω x) ^ t} ≤
        ENNReal.ofReal (C * ((3 : ℝ) ^ k)⁻¹ ^ B)

/-- **The averages of the powers of the reach of the planar partition** (the analogue of
Armstrong and Dario, Proposition 2.4, for the planar partition and its reach). -/
def PlanarReachConcentration (p : unitInterval) : Prop :=
  ∀ τ : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (y : Vertex 2),
    latticeBondLaw 2 p {ω | ENNReal.ofReal (A * (cube k y).card) <
        ∑ x ∈ cube k y, planarReach ω x ^ τ} ≤
      ENNReal.ofReal (C * ((3 : ℝ) ^ k)⁻¹ ^ B)

end Rigidity.Proofs.Cluster
