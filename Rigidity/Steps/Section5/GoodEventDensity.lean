import Rigidity.Steps.Section5.GoodEventLowerBound

/-!
# Lemma 5.26: the steps of the density of the good event

Lemma 5.26 (`lemma:density-bound-good-event`, corrected draft L2392-2406) is carved into three
steps; no literature input is used.

* `GoodEventMeasurableStep` (implicit in the paper): the good event `G(0, C_χ, K)` is
  null-measurable. The statement `GoodEventDensityStmt` asks for it.
* `GoodEventTranslationStep` (translation covariance, in `GoodEventLowerBound.lean`):
  `ω ∈ G(y, C_χ, K)` if and only if the environment translated by `-y` lies in `G(0, C_χ, K)`.
* `TriangleDensityStep` (eq. `spreads-evenly` with `V = Q_1` and
  `W = {x ∈ Q_1 : x₁ ≥ |x₂|}`; the ergodic theorem on the triangle `T_L`): for every
  null-measurable event `A`, almost surely `L⁻² |{y ∈ T_L : τ_{-y} ω ∈ A}| → P[A]`. The triangle
  `T_L = {|x₂| ≤ x₁ ≤ L}` has `(L + 1)²` sites.

`TriangleDensityStep` is the domain version of the ergodic theorem for cubes proved in
`Rigidity.Proofs.Ergodic.TranslateDensity` (step `step:4.10-ergodic`). The centred cubes of
`translateDensity` do not localize to `T_L`; the route goes through the anchored cubes
`[0, n)²` of `Rigidity.Proofs.Ergodic.ae_tendsto_gridAvg_integral`, which holds for every
measure-preserving action. Applied to the actions `z ↦ τ_{D z}`, `D = diag(±a, ±b)`, and to the
events `τ_v⁻¹ A` for the `ab` residues `v`, it gives the densities of `A` on the rectangles
`[0, a n) × [0, b n)` of the four quadrants (every nonzero translation of the bond law is
ergodic, `ergodic_configurationTranslation`). Inclusion-exclusion gives the rectangles with
rational corners scaled by `L`, and `T_L` is approximated from inside and from outside by unions
of such rectangles of total area `L² (1 ± ε)`.

The draft statement asks for the null-measurability of `G(0, C_χ, K)`, for all parameters. The
events `G_2` and `G_3` quantify over all corrected planes of slope `e₁` on the infinite cluster,
for every environment, including the null event where the corrected plane is not unique up to
additive constants; measurability in the product σ-algebra is not evident (the event is a priori
co-analytic), and the ergodic argument only uses null-measurability.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- The good event `G(0, C_χ, K)` is null-measurable for the law `latticeBondLaw 2 p` (implicit in
the paper). -/
def GoodEventMeasurableStep (p : unitInterval) : Prop :=
  ∀ (Cf : ℕ) (R c₁ Cχ K : ℝ), NullMeasurableSet (eventG Cf R c₁ 0 Cχ K) (latticeBondLaw 2 p)

/-- The ergodic theorem on the triangles `T_L` (eq. `spreads-evenly`): for every null-measurable
event `A`, almost surely the number of sites `y ∈ T_L` with `τ_{-y} ω ∈ A`, divided by `L²`, tends
to `P[A]`. -/
def TriangleDensityStep (p : unitInterval) : Prop :=
  ∀ A : Set (Configuration 2), NullMeasurableSet A (latticeBondLaw 2 p) →
    ∀ᵐ ω ∂latticeBondLaw 2 p,
      Tendsto (fun L : ℕ =>
          ({y | y ∈ triangle L ∧ configurationTranslation (-y) ω ∈ A}.ncard : ℝ) / (L : ℝ) ^ 2)
        atTop (𝓝 (latticeBondLaw 2 p A).toReal)

/-- Lemma 5.26 from its three steps, for every `p`. -/
theorem goodEventDensity_of_steps {p : unitInterval} (hM : GoodEventMeasurableStep p)
    (hT : GoodEventTranslationStep) (hD : TriangleDensityStep p) : GoodEventDensityStmt p := by
  intro Cf R c₁ Cχ K
  refine ⟨hM Cf R c₁ Cχ K, ?_⟩
  filter_upwards [hD _ (hM Cf R c₁ Cχ K)] with ω hω
  refine (hω.congr fun L => ?_).liminf_eq
  have hset : {y | y ∈ triangle L ∧ configurationTranslation (-y) ω ∈ eventG Cf R c₁ 0 Cχ K} =
      {y | y ∈ triangle L ∧ ω ∈ eventG Cf R c₁ y Cχ K} := by
    ext y
    exact and_congr_right fun _ => (hT Cf R c₁ Cχ K y ω).symm
  rw [hset]

end Rigidity.Steps.Section5
