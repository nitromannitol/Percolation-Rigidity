import LatticeProb.External.GreenQuantitative
import PercolationClusterHomogenization.External.PlanarInputs

/-!
# Theorem 2 of Dario and Gu in every dimension from its planar case and its case `d ≥ 3`

`LatticeProb.External.SupercriticalBondGreenQuantitative` (Dario–Gu, Theorem 2, (1.10)–(1.11), in
every dimension `d ≥ 2`) consists of a planar part, with the random additive constant `K(y)`, and a
part for `d ≥ 3`. `supercriticalBondGreenQuantitative_of_two_of_three` assembles it from the planar
statement `Rigidity.External.SupercriticalBondGreenQuantitativeTwo` and the statement for `d ≥ 3`,
`SupercriticalBondGreenQuantitativeThree`, which is the `d ≥ 3` part verbatim.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Green

open scoped Classical in
/-- **Dario–Gu, Theorem 2, for `d ≥ 3`** (the `d ≥ 3` part of
`LatticeProb.External.SupercriticalBondGreenQuantitative`): with `ḡ = continuumGreen d κ`, for every
`δ > 0` and every pole `y` there is a minimal scale `M(y)` with a stretched exponential tail such
that almost surely every Green column `g` with pole `y` satisfies
`|g(x) - ḡ(x - y)| ≤ C |x - y|^{-(1 - δ)} |x - y|^{-(d-2)}` for `|x - y| ≥ M(y)`. -/
def SupercriticalBondGreenQuantitativeThree : Prop :=
  ∀ (d : ℕ) [NeZero d] (hd : 2 ≤ d), 3 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ κ : ℝ, ∃ hκ : 0 < κ,
      ∀ δ : ℝ, 0 < δ → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
        ∀ y : Vertex d, ∃ M : Configuration d → ℝ,
          Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧
          (∀ R : ℝ, 0 ≤ R →
            latticeBondLaw d p {ω | R ≤ M ω} ≤
              ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
          ∀ᵐ ω ∂latticeBondLaw d p,
            ∀ h : HasUniqueInfiniteOpenComponent ω,
              ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                ∀ g : uniqueInfiniteComponent h → ℝ,
                  IsGreenColumn d hd (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                  ∀ x : uniqueInfiniteComponent h,
                    ∀ z : {v : EuclideanSpace ℝ (Fin d) // v ≠ 0},
                      z.val = latticeEuclideanEmbedding x.val -
                        latticeEuclideanEmbedding y →
                      M ω ≤ ‖z.val‖ →
                      |g x - continuumGreen d hd ⟨κ, hκ⟩ z| ≤
                        C / (Real.rpow ‖z.val‖ (1 - δ) *
                          ‖z.val‖ ^ (d - 2))

/-- **Dario–Gu, Theorem 2, in every dimension**, from its planar case and its case `d ≥ 3`. -/
theorem supercriticalBondGreenQuantitative_of_two_of_three
    (h2 : Rigidity.External.SupercriticalBondGreenQuantitativeTwo)
    (h3 : SupercriticalBondGreenQuantitativeThree) :
    LatticeProb.External.SupercriticalBondGreenQuantitative := by
  intro d _ hd p hpc hp1
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · obtain rfl : d = 2 := by omega
    obtain ⟨κ, hκ, hK⟩ := h2 p hpc hp1
    exact ⟨κ, hκ, fun _ => hK, fun h => absurd h (by norm_num)⟩
  · obtain ⟨κ, hκ, hK⟩ := h3 d hd hge p hpc hp1
    exact ⟨κ, hκ, fun h => absurd h (by omega), fun _ => hK⟩

end Rigidity.Green
