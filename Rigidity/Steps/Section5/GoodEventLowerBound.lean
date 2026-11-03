import Rigidity.Draft.Section5cStatements
import Rigidity.Draft.Section3Statements
import Rigidity.External.CorrectorQuantitative
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Prob.Percolation.LatticeBondTranslationLaw

/-!
# Lemma 5.25: the steps of the lower bound on the probability of the good event

Lemma 5.25 (`lemma:good-event-lower-bound`, corrected draft L2372-2386) is carved into four steps.
Its inputs are Proposition 5.24 (through the bound `LongPathBound`, a hypothesis of the statement),
the quantitative part of Theorem 2.5 (`Rigidity.External.CorrectorQuantitativeInput`), its
qualitative part (`LatticeProb.External.SupercriticalBondCorrectorInput`, the uniqueness of the
corrected plane up to additive constants), the uniqueness of the infinite cluster
(`LatticeProb.External.SupercriticalBondUniqueness`) and Proposition 3.2
(`Rigidity.Section3.NotLipschitzStmt`).

* `GoodEventTranslationStep` (stationarity, L2381): the good event is translation covariant,
  `ω ∈ G(x, C_χ, K)` if and only if the environment translated by `-x` lies in `G(0, C_χ, K)`.
  The infinite cluster, the events `E_R`, the paths of the cluster and the corrected planes move
  with the environment.
* `FirstGoodEventStep` (eq. `PG1goesto1`, [C31]): if the origin lies in the infinite cluster and
  `G_1(0, K)` fails, the event of Proposition 5.24 holds: some path of the cluster from the origin
  reaches `|γ(end)| ≥ K` with fewer than `c₁ |γ(end)|` of its sites in `E_R`.
* `SecondGoodEventStep` (eq. `PG2goesto1`): from Theorem 2.5 and the uniqueness of the infinite
  cluster, `G_2(x, K)` fails with outer probability at most `C exp(-c K^s)`. Beyond the minimal
  scale `M ≤ O_s(C)`, the oscillation of the corrector `χ_{e₁} = ℓ_{e₁} - x₁` on `Q_{R'}(x)` is at
  most `C R'^α`, and `x₁` oscillates by `2R'` on `Q_{R'}(x)`. The complement of `G_2(x, K)`
  contains the event that there is no unique infinite cluster, which the quantitative input of
  Theorem 2.5 does not control; hence the hypothesis `SupercriticalBondUniqueness` of the step.
  The step is proved in `Rigidity/Proofs/Section5/SecondGoodEvent.lean` (`secondGoodEventStep`),
  which imports this file.
* `ThirdGoodEventStep` (L2370, [C32]): from Proposition 3.2, for every `C_χ ≥ 1` the
  direction-free event `G_3(0, C_χ)` contains a measurable event of positive probability.

**Corrections [C31], [C32].** The draft events are the corrected ones: `G_1(x, K)` is universal over
the paths of `𝒞_∞` from `x` ([C31]), and `G_3(x, C_χ)` asks for some edge `(x, y)` of `𝒞_∞` at `x`
([C32]).
* [C31]: printed with an existential over the path, `G_1(x, K)` lies in `{x ∈ 𝒞_∞}`, of probability
  `θ(p) < 1`, so eq. `PG1goesto1` fails. With the universal event, the complement of `G_1(0, K)` on
  the unique infinite cluster lies in the event of Proposition 5.24 (`FirstGoodEventStep`; its
  hypothesis `0 ∈ 𝒞_∞` is not needed), and the union bound
  `P[G] ≥ P[G_3] - P[{0 ∈ 𝒞_∞} \ G_1] - P[G_2ᶜ]` gives the lemma.
* [C32]: Proposition 3.2 bounds `|∇ℓ_{e₁}(0)|`, the sum of the gradients along `(0, e₁)` and
  `(0, e₂)`, without sign; the symmetries fixing the slope `e₁` preserve the sign of a horizontal
  increment, so the printed event on the edge `(0, e₁)` is not shown to have positive probability
  (the signed variant `HorizontalIncrementStep` is discussed in
  `Rigidity/Steps/S3/HorizontalIncrement.lean`). The direction-free `G_3(0, C_χ)` follows from
  Proposition 3.2 and translation invariance (`thirdGoodEventStep`,
  `Rigidity/Proofs/Section5/ThirdGoodEventDirectionFree.lean`).

**Lemma 5.25 as printed.** `eventG3Directional` is the printed `G_3(x, C_χ)` on the edge
`(x, x + e₁)` (the event that [C32] makes direction-free), and
`GoodEventLowerBoundDirectionalStmt p` is Lemma 5.25 with it (and the universal `G_1` of [C31]). It
is proved for `p_c(2) < p < 1` from the literature inputs in
`Rigidity/Proofs/Assembly/Section5f.lean` (`goodEventLowerBoundDirectional`), through the signed
variant `HorizontalIncrementStep p` of Proposition 3.2 and the exterior network of the surgery
region (`Rigidity.Proofs.S3.exteriorNetworkStep`).
`exists_measurable_subset_eventG1_eventG2_zero` is the union bound at the origin shared by both
forms of the lemma.

The statement `GoodEventLowerBoundStmt p` carries no hypothesis on `p`; it is false for `p ≤ p_c`
(the event `G_3` is null). The hypotheses `p_c(2) < p < 1` of Section 5 are hypotheses of
`goodEventLowerBound_of_steps`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5 Rigidity.External

/-- Translation covariance of the good event (stationarity, L2381): `G(x, C_χ, K)` holds for the
environment `ω` if and only if `G(0, C_χ, K)` holds for the environment translated by `-x`. -/
def GoodEventTranslationStep : Prop :=
  ∀ (Cf : ℕ) (R c₁ Cχ K : ℝ) (x : Vertex 2) (ω : Configuration 2),
    ω ∈ eventG Cf R c₁ x Cχ K ↔ configurationTranslation (-x) ω ∈ eventG Cf R c₁ 0 Cχ K

/-- Step of eq. `PG1goesto1` ([C31]): if the origin lies in the infinite cluster and the first good
event `G_1(0, K)` fails, then the event of Proposition 5.24 holds. -/
def FirstGoodEventStep : Prop :=
  ∀ (Cf : ℕ) (R c₁ K : ℝ),
    {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp} \
        eventG1 Cf R c₁ 0 K ⊆ badPathEvent Cf R c₁ K

/-- Step of eq. `PG2goesto1`: from Theorem 2.5 and the uniqueness of the infinite cluster, for
`p_c(2) < p < 1` the second good event `G_2(x, K)` fails with outer probability at most
`C exp(-c K^s)`. -/
def SecondGoodEventStep : Prop :=
  LatticeProb.External.SupercriticalBondUniqueness → CorrectorQuantitativeInput →
    ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) →
    (p : ℝ) < 1 → ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ (x : Vertex 2) (K : ℝ), 1 ≤ K →
      latticeBondLaw 2 p (eventG2 x K)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * K ^ s)))

/-- Step of L2370 ([C32]): from Proposition 3.2 and the uniqueness of the corrected plane up to
additive constants, for `p_c(2) < p < 1` and every `C_χ ≥ 1` the direction-free third good event
`G_3(0, C_χ)` contains a measurable event of positive probability. -/
def ThirdGoodEventStep : Prop :=
  LatticeProb.External.SupercriticalBondCorrectorInput → ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 → Rigidity.Section3.NotLipschitzStmt 2 p →
      ∀ Cχ : ℝ, 1 ≤ Cχ → ∃ A ⊆ eventG3 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A

/-! ### Lemma 5.25 as printed: the directional third good event -/

/-- The third good event `G_3(x, C_χ)` as printed (eq. `not-lipschitz`; the event on the fixed
edge that [C32] replaces by the direction-free `eventG3`): `(x, x + e₁)` is an edge of `𝒞_∞` across
which every corrected plane `ℓ_{e₁}` increases by at least `C_χ`. -/
def eventG3Directional (x : Vertex 2) (Cχ : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ hx' : x + e1 ∈ (uniqueInfiniteComponent h).supp,
      (componentGraph _).Adj ⟨x, hx⟩ ⟨x + e1, hx'⟩ ∧
      ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
        Cχ ≤ ℓ ⟨x + e1, hx'⟩ - ℓ ⟨x, hx⟩}

/-- Lemma 5.25 as printed, with the directional third good event: `GoodEventLowerBoundStmt p` with
`G_3(x, C_χ)` replaced by `eventG3Directional x C_χ` (the printed event, which [C32] makes
direction-free; the first good event is the universal one of [C31]). For every `C_χ ≥ 1` there is
`c > 0` such that, for parameters `R, c₁` satisfying the bound of Proposition 5.24,
`P[G_1(x, K) ∩ G_2(x, K) ∩ G_3(x, C_χ)] ≥ c` for all `x` and all large `K`. -/
def GoodEventLowerBoundDirectionalStmt (p : unitInterval) : Prop :=
  ∀ Cχ : ℝ, 1 ≤ Cχ → ∃ c : ℝ, 0 < c ∧ ∀ (Cf : ℕ) (R c₁ : ℝ), LongPathBound p Cf R c₁ →
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∀ x : Vertex 2,
      ∃ A ⊆ eventG1 Cf R c₁ x K ∩ eventG2 x K ∩ eventG3Directional x Cχ,
        MeasurableSet A ∧ ENNReal.ofReal c ≤ latticeBondLaw 2 p A

/-! ### The union bound at the origin -/

/-- The first two good events at the origin inside a measurable event `A₃` on which the origin
lies in the infinite cluster: a measurable event of probability at least `P[A₃] - P[D]` inside
`G_1(0, K) ∩ G_2(0, K) ∩ A₃`, where `D` covers the failures of `G_1` on the infinite cluster and
of `G_2`. -/
theorem exists_measurable_subset_eventG1_eventG2_zero {p : unitInterval}
    (h1 : FirstGoodEventStep) {Cf : ℕ} {R c₁ K : ℝ} {A₃ : Set (Configuration 2)}
    (hA₃ : A₃ ⊆ {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp})
    (hA₃m : MeasurableSet A₃) :
    ∃ A ⊆ eventG1 Cf R c₁ 0 K ∩ eventG2 0 K ∩ A₃, MeasurableSet A ∧ latticeBondLaw 2 p A₃ -
      (latticeBondLaw 2 p (badPathEvent Cf R c₁ K) + latticeBondLaw 2 p (eventG2 0 K)ᶜ) ≤
        latticeBondLaw 2 p A := by
  set μ := latticeBondLaw 2 p
  set D := toMeasurable μ (badPathEvent Cf R c₁ K ∪ (eventG2 0 K)ᶜ)
  refine ⟨A₃ \ D, fun ω hω => ?_, hA₃m.diff (measurableSet_toMeasurable _ _), ?_⟩
  · have hD : ω ∉ badPathEvent Cf R c₁ K ∪ (eventG2 0 K)ᶜ :=
      fun h => hω.2 (subset_toMeasurable _ _ h)
    refine ⟨⟨?_, ?_⟩, hω.1⟩
    · by_contra hG1
      exact hD (Or.inl (h1 Cf R c₁ K ⟨hA₃ hω.1, hG1⟩))
    · by_contra hG2
      exact hD (Or.inr hG2)
  · refine le_trans ?_ (le_measure_sdiff (μ := μ))
    rw [measure_toMeasurable]
    exact tsub_le_tsub_left (measure_union_le _ _) _

/-- The good event at the origin: a measurable event of probability at least `P[A₃] - P[D]`
inside `G(0, C_χ, K)`, where `A₃ ⊆ G_3(0, C_χ)` and `D` covers the failures of `G_1` on the
infinite cluster and of `G_2`. -/
theorem exists_measurable_subset_eventG_zero {p : unitInterval} (h1 : FirstGoodEventStep)
    {Cf : ℕ} {R c₁ Cχ K : ℝ} {A₃ : Set (Configuration 2)} (hA₃ : A₃ ⊆ eventG3 0 Cχ)
    (hA₃m : MeasurableSet A₃) :
    ∃ A ⊆ eventG Cf R c₁ 0 Cχ K, MeasurableSet A ∧ latticeBondLaw 2 p A₃ -
      (latticeBondLaw 2 p (badPathEvent Cf R c₁ K) + latticeBondLaw 2 p (eventG2 0 K)ᶜ) ≤
        latticeBondLaw 2 p A := by
  obtain ⟨A, hA, hAm, hAμ⟩ := exists_measurable_subset_eventG1_eventG2_zero (p := p) (Cf := Cf)
    (R := R) (c₁ := c₁) (K := K) h1
    (fun ω hω => by obtain ⟨h, hx, -⟩ := hA₃ hω; exact ⟨h, hx⟩) hA₃m
  exact ⟨A, fun ω hω => ⟨(hA hω).1, hA₃ (hA hω).2⟩, hAm, hAμ⟩

/-- `C exp(-c K) + C' exp(-c' K^s)` tends to zero as `K → ∞`. -/
theorem tendsto_exp_add_exp_rpow {C c C' c' s : ℝ} (hc : 0 < c) (hc' : 0 < c') (hs : 0 < s) :
    Tendsto (fun K : ℝ => C * Real.exp (-(c * K)) + C' * Real.exp (-(c' * K ^ s))) atTop
      (𝓝 0) := by
  have h1 : Tendsto (fun K : ℝ => Real.exp (-(c * K))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
  have h2 : Tendsto (fun K : ℝ => Real.exp (-(c' * K ^ s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_rpow_atTop hs).const_mul_atTop hc')
  simpa using (h1.const_mul C).add (h2.const_mul C')

/-- Lemma 5.25 from Theorem 2.5, the uniqueness of the infinite cluster, Proposition 3.2 and its
four steps, for `p_c(2) < p < 1`. -/
theorem goodEventLowerBound_of_steps {p : unitInterval} (hQ : CorrectorQuantitativeInput)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) (hT : GoodEventTranslationStep)
    (h1 : FirstGoodEventStep) (h2 : SecondGoodEventStep) (h3 : ThirdGoodEventStep) :
    GoodEventLowerBoundStmt p := by
  intro Cχ hCχ
  set μ := latticeBondLaw 2 p
  obtain ⟨A₃, hA₃, hA₃m, hA₃pos⟩ := h3 hU p hpc hp1 h32 Cχ hCχ
  have hA₃top : μ A₃ ≠ ⊤ := measure_ne_top μ A₃
  set c := (μ A₃).toReal / 2 with hc_def
  have hc : 0 < c := half_pos (ENNReal.toReal_pos hA₃pos.ne' hA₃top)
  refine ⟨c, hc, fun Cf R c₁ hL => ?_⟩
  obtain ⟨C₁, a₁, hC₁, ha₁, hbad⟩ := hL
  obtain ⟨C₂, a₂, s, hC₂, ha₂, hs, hG2⟩ := h2 hUq hQ p hpc hp1
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (((tendsto_exp_add_exp_rpow (C := C₁) (C' := C₂) ha₁ ha₂ hs).eventually
      (ge_mem_nhds hc)).and (eventually_ge_atTop 1))
  refine ⟨K₀, fun K hK x => ?_⟩
  obtain ⟨hsmall, hK1⟩ := hK₀ K hK
  obtain ⟨A₀, hA₀, hA₀m, hA₀μ⟩ :=
    exists_measurable_subset_eventG_zero (p := p) (Cf := Cf) (R := R) (c₁ := c₁) (K := K) h1 hA₃
      hA₃m
  have hD : μ (badPathEvent Cf R c₁ K) + μ (eventG2 0 K)ᶜ ≤ ENNReal.ofReal c := by
    refine (add_le_add (hbad K hK1) (hG2 0 K hK1)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsmall
  have hτ := measurePreserving_configurationTranslation p (-x)
  refine ⟨configurationTranslation (-x) ⁻¹' A₀, fun ω hω => (hT Cf R c₁ Cχ K x ω).mpr (hA₀ hω),
    hτ.measurable hA₀m, ?_⟩
  rw [hτ.measure_preimage hA₀m.nullMeasurableSet]
  refine le_trans ?_ (le_trans (tsub_le_tsub_left hD _) hA₀μ)
  rw [← ENNReal.ofReal_toReal hA₃top, ← ENNReal.ofReal_sub _ hc.le]
  exact ENNReal.ofReal_le_ofReal (by rw [hc_def]; linarith)

end Rigidity.Steps.Section5
