import Rigidity.Steps.Section5.Common

/-! # Proposition 5.5: logarithmic growth of a charged potential

Proposition 5.5 (`LogGrowthStmt`, corrected draft L1544-1546): almost surely, if the charge `Σ f` is
nonzero then `u_f = Θ(log |x|)`. The carving uses neither Lemma 5.6 nor the gradient decay of eq.
`green-decay-estimate`, only the potential asymptotics `u_f = (Σ f) Ḡ + L + o(1)` (Dario-Gu,
`PotentialAsymptotic`) with `Ḡ(x) = -log |x|₂ / (2πκ)`. Since `Σ f` is a nonzero integer,
`|Σ f| ≥ 1` and `|(Σ f) Ḡ(x)| = a log |x|₂` with `a = |Σ f| / (2πκ) > 0`. The steps:

* `NormComparisonStep`: `|x|₂ ≤ |x| ≤ √2 |x|₂` for the `ℓ¹` norm `|x|`;
* `LogNormComparisonStep`: hence `|log |x| - log |x|₂| ≤ log 2` when `|x| ≥ 1`;
* `AsymptoticLogBoundsStep` (deterministic): on an open component, if `u - m Ḡ → L` at infinity
  with `m ≠ 0`, then `(a/2) log |x| ≤ |u(x)| ≤ 2a log |x|` for `|x|` large.

Proposition 5.5 follows on the almost sure event where the cluster is unique and the potential
asymptotics hold. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- Step: the `ℓ¹` norm is comparable to the Euclidean norm, `|x|₂ ≤ |x| ≤ √2 |x|₂`. -/
def NormComparisonStep : Prop :=
  ∀ x : Vertex 2, eucl x ≤ l1 x ∧ l1 x ≤ Real.sqrt 2 * eucl x

/-- Step: `|log |x| - log |x|₂| ≤ log 2` for `|x| ≥ 1`. -/
def LogNormComparisonStep : Prop :=
  ∀ x : Vertex 2, 1 ≤ l1 x → |Real.log (l1 x) - Real.log (eucl x)| ≤ Real.log 2

/-- Step (deterministic): on an open component, a function `u` with `u - m Ḡ → L` at infinity for
a nonzero integer `m` satisfies `c log |x| ≤ |u(x)| ≤ C log |x|` for `|x| ≥ R₀`. -/
def AsymptoticLogBoundsStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (κ : {a : ℝ // 0 < a}) (m : ℤ) (u : C → ℝ)
    (L : ℝ), m ≠ 0 → Tendsto (fun x => u x - (m : ℝ) * greenLog κ x.val) cofinite (𝓝 L) →
      ∃ c C' R₀ : ℝ, 0 < c ∧ 0 < C' ∧ ∀ x : C, R₀ ≤ l1 x.val →
        c * Real.log (l1 x.val) ≤ |u x| ∧ |u x| ≤ C' * Real.log (l1 x.val)

/-- Proposition 5.5 follows from the uniqueness of the infinite cluster, the potential
asymptotics and the deterministic two-sided logarithmic bound. -/
theorem logGrowth_of_steps {p : unitInterval} (hU : UniqueClusterAe p)
    (hA : PotentialAsymptotic p) (hB : AsymptoticLogBoundsStep) (f : Vertex 2 → ℤ) :
    LogGrowthStmt p f := by
  intro hf
  obtain ⟨κ, hκ⟩ := hA
  filter_upwards [hU, hκ f hf] with ω hω hA'
  refine ⟨hω, fun G hG hm => ?_⟩
  obtain ⟨L, hL⟩ := hA' hω
  exact hB ω _ κ _ _ L hm (hL G hG)

end Rigidity.Steps.Section5
