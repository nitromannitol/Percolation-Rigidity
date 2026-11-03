import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The smoothing parameter of a lattice (literature input): a Gaussian sum over the nonzero vectors
of the dual lattice is at most `ε` once the scale `s` exceeds `√(log(2k(1 + 1/ε))/π)` times the
length of `k` independent lattice vectors. Used for step:6.5-upper (the upper bound of Theorem 6.5),
as in D. C. Jerison, L. Levine and J. Pike, *Mixing time and eigenvalues of the abelian sandpile
Markov chain*, Trans. Amer. Math. Soc. 372 (2019), Lemma 4.2 and the proof of Theorem 4.3.

Source: D. Micciancio and O. Regev, *Worst-case to average-case reductions based on Gaussian
measures*, SIAM J. Comput. 37 (2007), Lemma 3.3: `η_ε(Λ) ≤ √(ln(2k(1 + 1/ε))/π) · λ_k(Λ)` for a
lattice `Λ` of rank `k`, where `η_ε(Λ)` is the least `s` with `Σ_{y ∈ Λ* ∖ 0} exp(-π s² ‖y‖²) ≤ ε`.
Stated here for the lattice generated over ℤ by `k` independent vectors of length at most `r` (so
`λ_k(Λ) ≤ r`), inside `ℝ^N`; the dual lattice is taken in the real span, which is the general-rank
form of Jerison–Levine–Pike, Section 4. -/


namespace Rigidity.External

/-- The dual of the lattice generated over ℤ by `b`: the vectors of the real span of `b` whose inner
product with every `b i` is an integer. -/
def dualLattice {N k : ℕ} (b : Fin k → EuclideanSpace ℝ (Fin N)) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {y | y ∈ Submodule.span ℝ (Set.range b) ∧ ∀ i, ∃ z : ℤ, inner ℝ y (b i) = z}

/-- **Micciancio–Regev, Lemma 3.3** (literature input). -/
def MicciancioRegevSmoothing : Prop :=
  ∀ (N k : ℕ) (b : Fin k → EuclideanSpace ℝ (Fin N)), LinearIndependent ℝ b →
    ∀ r : ℝ, (∀ i, ‖b i‖ ≤ r) → ∀ ε : ℝ, 0 < ε → ∀ s : ℝ,
      Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) * r ≤ s →
      Summable (fun y : {y // y ∈ dualLattice b ∧ y ≠ 0} =>
          Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2))) ∧
        ∑' y : {y // y ∈ dualLattice b ∧ y ≠ 0},
          Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2)) ≤ ε

end Rigidity.External
