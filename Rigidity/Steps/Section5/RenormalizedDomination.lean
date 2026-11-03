import Rigidity.Draft.Section5cStatements
import Rigidity.External.KestenCrossing
import Rigidity.External.WellConnected
import LatticeProb.Prob.Percolation.LSSThinInstantiation

/-!
# Lemma 5.23: the steps of the stochastic domination of the renormalized process

Lemma 5.23 (`lemma:renormalized-domination`, corrected draft L2244-2250) is carved into four
steps, with the literature inputs `Rigidity.External.WellConnectedInput` (Proposition 2.3) and
`Rigidity.External.KestenRectangleCrossing` (Kesten, Theorem 11.1).

* `VeryGoodProbabilityStep` (`step:5.21-very-good`, eq. `verygoodstretchedexpclose1`): a cube
  `x + Q_r` is very good outside an event of probability at most `C exp(-c r^s)`; Proposition 2.3
  for the well-connectedness and a union bound over the `⌊(2r+1)/⌈√r⌉⌋` bands in each direction,
  each crossed outside probability `C (2r + 1) exp(-c (⌈√r⌉ - 1))` by Kesten's estimate, for the
  channels.
* `RenormFieldMeasurableStep`: the renormalized field is measurable; each of its sites is
  determined by the finitely many edges of a cube.
* `RenormFieldOneDependentStep` (locality): the renormalized field is `1`-dependent for the
  `ℓ^∞` distance of `ℤ²`. The event that `x + Q_r` is very good, `r = ⌊11R/10⌋`, is determined by
  the edges with both endpoints in `x + Q_{r + 2⌊r/10⌋}` (the cube, its bands, and the subcubes of
  radius at most `r/10` meeting it), and `r + 2⌊r/10⌋ ≤ 33R/25`; two centres at `ℓ^∞` distance at
  least `2 (2R + 1) > 66R/25` of each other thus see disjoint sets of edges.
* `OneDependentDominationStep` (`step:5.23-domination`; Liggett, Schonmann and Stacey,
  *Domination by product measures*, Ann. Probab. 25 (1997), Theorem 1.3, for the dependency graph
  of `ℓ^∞`-neighbours of `ℤ²`, of degree `Δ = 8`): a `1`-dependent field whose sites are closed
  with probability at most `ε` dominates the Bernoulli field of every parameter at most
  `1 - C₀ ε^a`.

The printed proof applies the Liggett-Schonmann-Stacey theorem with `Δ = 4`, the degree of the
nearest-neighbour graph of `ℤ²`. The `1`-dependence for that graph is not justified: the cubes
`x + Q_{11R/10}` and `y + Q_{11R/10}` of diagonal neighbours `y - x = (2R + 1)(±1, ±1)` overlap
once `R ≥ 10`, so their events depend on common edges, although `|x - y| > 2R + 1`. The process is
`1`-dependent for the `ℓ^∞` distance (`KDependentPlanar 1`), whose dependency graph has degree
`Δ = 8`, and the theorem applies with `Δ = 8`; the conclusion is unchanged.

The statement `RenormalizedDominationStmt p` carries no hypothesis on `p`; it is false for `p = 0`
(no cube of positive radius is very good, so the renormalized field vanishes identically).
The supercritical hypothesis `p_c(2) < p` of Section 5 is a hypothesis of
`renormalizedDomination_of_steps`.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.External

/-- Step `step:5.21-very-good` (eq. `verygoodstretchedexpclose1`): from Proposition 2.3 and
Kesten's crossing estimate, for `p_c(2) < p` a cube `x + Q_r` fails to be very good with
probability at most `C exp(-c r^s)`. -/
def VeryGoodProbabilityStep : Prop :=
  WellConnectedInput → KestenRectangleCrossing →
    ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
      ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ (x : Vertex 2) (r : ℕ),
        latticeBondLaw 2 p {ω | ¬ IsVeryGood ω x r} ≤
          ENNReal.ofReal (C * Real.exp (-(c * (r : ℝ) ^ s)))

/-- Step `step:5.23-measurable`: the renormalized percolation process of size `R` is a measurable
function of the bond configuration. -/
def RenormFieldMeasurableStep : Prop :=
  ∀ R : ℕ, Measurable (renormField R)

/-- Step `step:5.23-one-dependence`: the renormalized percolation process of size `R` is
`1`-dependent for the `ℓ^∞` distance of `ℤ²`: its restrictions to two finite sets of sites at
`ℓ^∞` distance at least `2` are independent. -/
def RenormFieldOneDependentStep : Prop :=
  ∀ (p : unitInterval) (R : ℕ), KDependentPlanar 1 ((latticeBondLaw 2 p).map (renormField R))

/-- Step `step:5.23-domination` (Liggett-Schonmann-Stacey, Theorem 1.3, `Δ = 8`): there are
`C₀, a > 0` such that a `1`-dependent field on `ℤ²` (for the `ℓ^∞` distance) whose sites are
closed with probability at most `ε` gives every measurable increasing event at least the
probability of the Bernoulli field of parameter `q`, for every `q ≤ (1 - C₀ ε^a)₊`. -/
def OneDependentDominationStep : Prop :=
  ∃ C₀ a : ℝ, 0 < C₀ ∧ 0 < a ∧ ∀ ν : Measure (PlanarCarrier → Bool), IsProbabilityMeasure ν →
    KDependentPlanar 1 ν → ∀ ε : ℝ, 0 ≤ ε → (∀ z : PlanarCarrier, ν {ω | ω z = false} ≤
      ENNReal.ofReal ε) → ∀ (q : NNReal) (hq : q ≤ 1), q ≤ Real.toNNReal (1 - C₀ * ε ^ a) →
        DenseLower (bernoulliFieldPlanar q hq) ν

/-- Lemma 5.23 from Proposition 2.3, Kesten's crossing estimate and its four steps. -/
theorem renormalizedDomination_of_steps {p : unitInterval} (hW : WellConnectedInput)
    (hK : KestenRectangleCrossing) (hpc : criticalProbability 2 < (p : ℝ))
    (hV : VeryGoodProbabilityStep) (hM : RenormFieldMeasurableStep)
    (hD : RenormFieldOneDependentStep) (hL : OneDependentDominationStep) :
    RenormalizedDominationStmt p := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := hV hW hK p hpc
  obtain ⟨C₀, a, hC₀, ha, hdom⟩ := hL
  refine ⟨C₀ * C ^ a, a * c, s, by positivity, by positivity, hs, fun R _ A hA hinc => ?_⟩
  have hmeas := hM R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine hdom _ inferInstance (hD p R) (C * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s)))
    (by positivity) (fun z => ?_) _ _ ?_ A hA hinc
  · have hz : MeasurableSet {ω : PlanarCarrier → Bool | ω z = false} :=
      measurableSet_eq_fun (measurable_pi_apply z) measurable_const
    rw [Measure.map_apply hmeas hz]
    convert hbound (renormCentre R z) (11 * R / 10) using 2
    ext ω
    simp [renormField]
  · refine (min_le_right _ _).trans (Real.toNNReal_le_toNNReal ?_)
    rw [Real.mul_rpow hC.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hRr : (R : ℝ) ^ s ≤ ((11 * R / 10 : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show R ≤ 11 * R / 10 by omega))
        hs.le
    have hexp : Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s) * a) ≤
        Real.exp (-(a * c * (R : ℝ) ^ s)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRr (mul_pos ha hc).le])
    have hCa : 0 < C₀ * C ^ a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hexp hCa.le]

end Rigidity.Steps.Section5
