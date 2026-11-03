import Rigidity.Steps.Section5.Common
import Rigidity.External.KestenCrossing

/-!
# Lemma 5.14: the steps of the loops around annuli

Lemma 5.14 (`lemma:loops-around-annuli`, corrected draft L1945-1959) is carved into three steps,
with the literature input `Rigidity.External.KestenRectangleCrossing` (Kesten, Theorem 11.1)
supplying the crossing estimate of a long rectangle.

* `CrossingProbabilityStep` (union bound): if every rectangle `[0, m] × [0, n]` is crossed in its
  long direction outside an event of probability at most `C (m + 1) e^{-cn}`, then the crossings
  `AnnulusCrossings ω R` at scale `R` occur outside an event of probability at most
  `C' (R + 1) e^{-c'R}`.
* `BorelCantelliStep`: such a summable bound gives, almost surely, a scale `M` with
  `AnnulusCrossings ω R` for every `R ≥ M`.
* `LoopFromCrossingsStep` (deterministic planarity): the crossings at all scales `R ≥ M` give,
  for all large `R`, a loop of `𝒞_∞` in `Q_{2R} \ Q_R` with winding number `±1`.

`AnnulusCrossings ω R` consists of the four long crossings of the rectangles which make up the
annulus `Q_{2R} \ Q_R` (bottom and top, crossed horizontally; left and right, crossed vertically)
and one radial crossing of `[R + 1, 4R] × [0, R]`. The printed proof only uses the four crossings
of the annulus ("a union bound and planarity"); it does not show that the loop they contain lies
in `𝒞_∞`. The radial crossing fills this: it meets the right crossing at scale `R` (in
`[R + 1, 2R] × [0, R]`) and the right crossing at scale `2R` (in `[2R + 1, 4R] × [0, R]`), so the
crossings at the scales `2^k R`, `k ≥ 0`, form an infinite connected open set, which lies in the
unique infinite cluster. In each case the two paths are a horizontal and a vertical crossing of
the same rectangle of `ℤ²`, hence share a vertex.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.External

/-- The crossings at scale `R`: the long crossings of the bottom `[-2R, 2R] × [-2R, -R-1]`, the
top `[-2R, 2R] × [R+1, 2R]`, the left `[-2R, -R-1] × [-2R, 2R]` and the right
`[R+1, 2R] × [-2R, 2R]` rectangles of the annulus `Q_{2R} \ Q_R`, and the radial crossing of
`[R+1, 4R] × [0, R]` joining the right rectangles at scales `R` and `2R`. -/
def AnnulusCrossings (ω : Configuration 2) (R : ℕ) : Prop :=
  HasOpenCrossing ω ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 0 ∧
  HasOpenCrossing ω ![-(2 * R : ℤ), R + 1] (4 * R) (R - 1) 0 ∧
  HasOpenCrossing ω ![-(2 * R : ℤ), -(2 * R)] (4 * R) (R - 1) 1 ∧
  HasOpenCrossing ω ![(R : ℤ) + 1, -(2 * R)] (4 * R) (R - 1) 1 ∧
  HasOpenCrossing ω ![(R : ℤ) + 1, 0] (3 * R - 1) R 0

/-- Step `step:5.14-union-bound`: an exponential crossing estimate for long rectangles gives an
exponential bound on the probability that one of the crossings at scale `R` fails. -/
def CrossingProbabilityStep : Prop :=
  ∀ (p : unitInterval) (C c : ℝ), 0 < C → 0 < c →
    (∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2),
      latticeBondLaw 2 p {ω | ¬ HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n)))) →
    ∃ C' c' : ℝ, 0 < C' ∧ 0 < c' ∧ ∀ R : ℕ,
      latticeBondLaw 2 p {ω | ¬ AnnulusCrossings ω R} ≤
        ENNReal.ofReal (C' * (R + 1) * Real.exp (-(c' * R)))

/-- Step `step:5.14-borel-cantelli`: an exponential bound on the probability that the crossings
at scale `R` fail gives, almost surely, a scale beyond which they all occur. -/
def BorelCantelliStep : Prop :=
  ∀ (p : unitInterval) (C c : ℝ), 0 < C → 0 < c →
    (∀ R : ℕ, latticeBondLaw 2 p {ω | ¬ AnnulusCrossings ω R} ≤
      ENNReal.ofReal (C * (R + 1) * Real.exp (-(c * R)))) →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ M : ℕ, ∀ R : ℕ, M ≤ R → AnnulusCrossings ω R

/-- Step `step:5.14-planarity` (deterministic): if the crossings occur at every scale `R ≥ M`,
then for all large `R` the unique infinite cluster contains a loop in `Q_{2R} \ Q_R` with nonzero
winding number around the origin. -/
def LoopFromCrossingsStep : Prop :=
  ∀ (ω : Configuration 2) (h : HasUniqueInfiniteOpenComponent ω) (M : ℕ),
    (∀ R : ℕ, M ≤ R → AnnulusCrossings ω R) → ∃ M' : ℕ, ∀ R : ℕ, M' ≤ R →
      ∃ n : ℕ, ∃ γ : Fin (n + 1) → uniqueInfiniteComponent h,
        (∀ i, (componentGraph _).Adj (γ i) (γ (i + 1))) ∧
        (∀ i, (γ i).val ∈ cube (2 * R) \ cube R) ∧ windingNumber (fun i => (γ i).val) ≠ 0

/-- Lemma 5.14 from Kesten's crossing estimate and its three steps. -/
theorem loopsAroundAnnuli_of_steps {p : unitInterval} (hK : KestenRectangleCrossing)
    (hpc : criticalProbability 2 < (p : ℝ)) (hU : UniqueClusterAe p)
    (hC : CrossingProbabilityStep) (hB : BorelCantelliStep) (hL : LoopFromCrossingsStep) :
    LoopsAroundAnnuliStmt p := by
  obtain ⟨C, c, hC0, hc0, hbound⟩ := hK p hpc
  obtain ⟨C', c', hC'0, hc'0, hbound'⟩ := hC p C c hC0 hc0 hbound
  filter_upwards [hB p C' c' hC'0 hc'0 hbound', hU] with ω ⟨M, hM⟩ h
  exact ⟨h, hL ω h M hM⟩

end Rigidity.Steps.Section5
