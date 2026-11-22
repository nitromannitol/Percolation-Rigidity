import Rigidity.Proofs.Cluster.MeyersUniform

/-!
# A Gehring partition in the form used by the planar Meyers estimate, and the averages of the reach

Two probabilistic statements in dimension two, in the vocabulary of the planar modules, on which
the proof of Lemma 5.5 from `PlanarGehringPartition` rests.

* `PlanarGehringPartition`: a Gehring partition in the form used by the planar Meyers estimate
  (`planar_meyers_uniform`), with minimal scales as in Proposition 2.4. Its cells `cube (s x) x`
  form a partition of `ℤ²` with comparable neighbours (as in Proposition 2.1 (ii)); every
  predecessor `□' = cube k y`, `s(y) ≤ k`, of a cell is good, good meaning here that the planar
  partition cubes of the vertices of `3□'` have scale at most `k` and
  `∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G |3□'|` (the hypotheses under which `planar_meyers` uses the
  reverse Hölder inequality of Lemma 3.6); and for every exponent `t` the cells are small and their
  `t`-th moment is bounded on every triadic cube, off an event of probability at most `C 3^{-B k}`
  for every `B`.
* `PlanarReachConcentration`: the analogue of Proposition 2.4 for the planar partition `𝒫` and the
  weights of the coarse gradients: for every power `τ`, `∑_{x ∈ □} planarReach(x)^τ ≤ A |□|` on
  every triadic cube `□` off an event of probability at most `C 3^{-B scale □}`.

The hypothesis `PlanarGehringPartition` is kept because its good cubes are not those of Armstrong
and Dario. Armstrong and Dario apply Proposition 2.1 to `{RH ≤ C}` (Definition 3.7), whose events
are local: `RH_s(□)` is defined through the crossing cluster of a good cube and `𝒞_max(3□)`. The
Meyers estimate here (`planar_meyers_uniform`) uses instead the hypotheses of Lemma 3.6 on each
predecessor (planar partition scales at most `k` on `3□'` and
`∑_{z ∈ 3□'} planarReach(z)^8 ≤ C_G |3□'|`). This family depends on `𝒫` at every scale, so
Propositions 2.1 (iv) and 2.4 do not apply to it as printed.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation
open scoped ENNReal

/-- **A Gehring partition in the form used by the planar Meyers estimate**, with its minimal scales
(in dimension two). Its good cubes are those of the hypotheses of Lemma 3.6 for the planar
partition, not the cubes `{RH ≤ C}` of Armstrong and Dario, Definition 3.7. -/
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
