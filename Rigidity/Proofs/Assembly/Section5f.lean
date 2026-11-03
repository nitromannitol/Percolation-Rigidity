import Rigidity.Steps.S3.SignedIncrement
import Rigidity.Proofs.Section5.GoodEventBasics
import Rigidity.Proofs.Section5.SecondGoodEvent
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.S3.ExteriorNetwork
import Rigidity.Proofs.S3.HomogenizedCoefficient

/-! # Section 5: Lemma 5.25 by the signed route (d = 2) — the printed directional statement

The draft third good event is direction-free ([C32]), and the draft Lemma 5.25 is composed in
`Section5d.lean` (`goodEventLowerBound`, from Proposition 3.2 and `thirdGoodEventStep`). This module
proves Lemma 5.25 **as printed**, with the third good event on the edge `(x, x + e₁)`
(`eventG3Directional`, the printed third good event; equal to `eventG3Edge` by definition), through
the signed route: `goodEventLowerBoundDirectional : GoodEventLowerBoundDirectionalStmt p`, from the
literature inputs only. The exterior network step of the signed route is proved
(`Rigidity.Proofs.S3.exteriorNetworkStep`, `Rigidity/Proofs/S3/ExteriorNetwork.lean`).
The draft keeps the direction-free third good event of [C32], and `goodEventLowerBoundDirectional`
is restated in `Main` and `Audit` as Lemma 5.25 as printed.

Composition of the draft statement `GoodEventLowerBoundStmt p` (Lemma 5.25,
`Rigidity/Draft/Section5cStatements.lean`) through the printed third good event `eventG3Edge`:
`(x, x + e₁)` is an edge of `𝒞_∞` across which the corrected plane `ℓ_{e₁}` increases by at
least `C_χ`.

Route. For the printed event, the step of L2370 ("Theorem 3.1 and symmetry arguments") is a gap
of the printed proof (gap G5, [C32]; `Rigidity/Proofs/Section5/ThirdGoodEvent.lean`): it needs
the signed variant `HorizontalIncrementStep p` of Proposition 3.2. That variant follows by the
signed route (`Rigidity/Steps/S3/SignedIncrement.lean`,
`horizontalIncrementStep_of_exteriorNetwork_inputs`): Proposition 3.2 as printed
(`notLipschitz`, `Section3.lean`), the literature inputs on the uniqueness of the infinite cluster
and of the corrected planes, and `ExteriorNetworkStep p` (the trace of the exterior of the surgery
region on its terminals; proved, `Rigidity.Proofs.S3.exteriorNetworkStep`).

* `thirdGoodEventDirectionalAt_of_horizontalIncrement`: the printed third good event at a fixed
  `p`, from `HorizontalIncrementStep p` (the argument of
  `thirdGoodEventStep_of_horizontalIncrement`, which is stated for all `p` at once);
  `thirdGoodEventAt_of_horizontalIncrement`: the direction-free event, by `eventG3Edge_subset`.
* `mem_eventGDirectional_of_translation`, `goodEventLowerBoundDirectional_of_thirdGoodEventAt`:
  the printed Lemma 5.25 at a fixed `p` from the printed third good event at `p`.
* `goodEventLowerBoundDirectional`: **the printed Lemma 5.25** for `p_c(2) < p < 1`, from the
  literature inputs only (`exteriorNetworkStep` and `homogenizedCoefficientProposed` discharge
  the two derived inputs).
* `goodEventLowerBound_of_thirdGoodEventAt`: Lemma 5.25 at a fixed `p` from the third good event
  at `p`, with the translation, first and second good event steps proved
  (`goodEventTranslationStep`, `firstGoodEventStep`, `secondGoodEventStep`); the argument of
  `goodEventLowerBound_of_steps` at a fixed `p`.
* `horizontalIncrement`: `HorizontalIncrementStep p` from the cited inputs and
  `ExteriorNetworkStep p`.
* `goodEventLowerBound_of_exteriorNetwork`: the draft `GoodEventLowerBoundStmt p` for
  `p_c(2) < p < 1`, with `ExteriorNetworkStep p` as a hypothesis (the step is proved by
  `exteriorNetworkStep`).
* `thirdGoodEventStep_of_exteriorNetwork`: `ThirdGoodEventStep` (all `p` at once) from
  `ExteriorNetworkStep p` for every `p_c(2) < p < 1`; the direction-free step is also proved
  directly (`Rigidity.Proofs.Section5.thirdGoodEventStep`,
  `Rigidity/Proofs/Section5/ThirdGoodEventDirectionFree.lean`).

Hypotheses. Literature inputs (explicit hypotheses whose `Prop` lives in `Rigidity.External` or
`LatticeProb.External`): `SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`,
`CorrectorQuantitativeInput`, `ArmstrongDarioOrderZero`, `SupercriticalBondGreenColumnExistence`,
`SupercriticalBondGreenQuantitative`, `WellConnectedInput`; derived input
`HomogenizedCoefficientProposed` (through Proposition 3.2, as in `Section3.lean`; proved,
`homogenizedCoefficientProposed`) and `ExteriorNetworkStep p`
(`Rigidity/Steps/S3/SignedIncrement.lean`; proved, `exteriorNetworkStep`) in the theorems that
keep them as hypotheses; `goodEventLowerBoundDirectional` discharges both. -/

open MeasureTheory Filter Topology LatticeProb.Percolation LatticeProb.External

namespace Rigidity.Assembly

open Rigidity.Section5 Rigidity.Steps.Section5 Rigidity.Proofs.Section5

/-- The printed third good event (the edge form that [C32] replaces in the draft) is
`eventG3Edge`. -/
theorem eventG3Directional_eq_eventG3Edge : eventG3Directional = eventG3Edge := rfl

/-- The printed (directional) third good event at a fixed `p` (L2370): for `p_c(2) < p < 1` and
every `C_χ ≥ 1`, `G_3(0, C_χ)` on the edge `(0, e₁)` contains a measurable event of positive
probability, from the signed variant `HorizontalIncrementStep p` of Proposition 3.2 and the
uniqueness of the corrected plane up to additive constants. -/
theorem thirdGoodEventDirectionalAt_of_horizontalIncrement {p : unitInterval}
    (hU : SupercriticalBondCorrectorInput) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hH : HorizontalIncrementStep p) (Cχ : ℝ) (hCχ : 1 ≤ Cχ) :
    ∃ A ⊆ eventG3Directional 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  set μ := latticeBondLaw 2 p
  set q : Fin 2 → ℝ := Pi.single 0 1
  have hbad := ae_iff.mp (hU 2 le_rfl p hpc hp1)
  set N := toMeasurable μ {ω | ¬ ∀ h : HasUniqueInfiniteOpenComponent ω,
      (∀ q : Fin 2 → ℝ, ∀ o : uniqueInfiniteComponent h,
        ∃! u : uniqueInfiniteComponent h → ℝ,
          IsCorrectedPlane (uniqueInfiniteComponent h) q u ∧ u o = 0) ∧
      (∀ u : uniqueInfiniteComponent h → ℝ,
        u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1 →
        ∃! q : Fin 2 → ℝ, IsCorrectedPlane (uniqueInfiniteComponent h) q u)} with hN
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad
  set G := Nᶜ ∩ uniqueInfiniteComponentEvent 2
  have hGm : MeasurableSet G :=
    (measurableSet_toMeasurable _ _).compl.inter (measurableSet_uniqueInfiniteComponentEvent 2)
  have hvalid : G ⊆ correctorValidEvent 2 := by
    intro ω hω
    by_contra hn
    exact hω.1 (subset_toMeasurable _ _ fun hP => hn ⟨hω.2, by simpa using hP⟩)
  obtain ⟨F, hFm, hF⟩ := exists_measurable_rooted_plane_on_valid_set G hGm hvalid 0
  have hB : MeasurableSet (G ∩ infiniteComponentEvent 0) :=
    hGm.inter (measurableSet_infiniteComponentEvent 0)
  set T : Set ↥(G ∩ infiniteComponentEvent 0) :=
    {z | (openGraph z.val).Adj 0 e1 ∧ Cχ ≤ F (z, q) e1}
  have hT : MeasurableSet T := by
    refine (measurable_subtype_coe (measurableSet_openGraph_adj 0 e1)).inter ?_
    exact measurableSet_le measurable_const
      ((measurable_pi_apply e1).comp (hFm.comp (measurable_id.prodMk measurable_const)))
  refine ⟨Subtype.val '' T, ?_, hB.subtype_image hT, ?_⟩
  · rintro _ ⟨z, ⟨hadj, hval⟩, rfl⟩
    have h := (hvalid z.2.1).1
    have ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (mem_uniqueInfiniteComponent_iff h 0).mpr z.2.2
    have he : e1 ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp ho hadj
    have he' : (0 : Vertex 2) + e1 ∈ (uniqueInfiniteComponent h).supp := by
      rw [zero_add]; exact he
    refine ⟨h, ho, he', ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he').2
      (by rw [zero_add]; exact hadj), fun ℓ hℓ => ?_⟩
    rw [rootedPlane_eq hF z h ho hℓ he] at hval
    have h0e : ℓ ⟨(0 : Vertex 2) + e1, he'⟩ = ℓ ⟨e1, he⟩ :=
      congrArg ℓ (Subtype.ext (zero_add e1))
    rw [h0e]
    exact hval
  · have hS := hH Cχ hCχ
    refine pos_iff_ne_zero.mpr fun hA => hS (measure_mono_null ?_ (measure_union_null hA hN0))
    rintro ω ⟨h, ho, he, hadj, u, hu, hlt⟩
    by_cases hωN : ω ∈ N
    · exact Or.inr hωN
    · refine Or.inl ⟨⟨ω, ⟨hωN, h⟩, (mem_uniqueInfiniteComponent_iff h 0).mp ho⟩, ⟨?_, ?_⟩, rfl⟩
      · exact ((uniqueInfiniteComponent h).toSimpleGraph_adj ho he).1 hadj
      · rw [rootedPlane_eq hF _ h ho hu he]
        exact hlt.le

/-- The third good event at a fixed `p` (L2370): for `p_c(2) < p < 1` and every `C_χ ≥ 1`,
`G_3(0, C_χ)` contains a measurable event of positive probability, from the signed variant
`HorizontalIncrementStep p` of Proposition 3.2 and the uniqueness of the corrected plane up to
additive constants (through the printed event, `eventG3Edge_subset`). -/
theorem thirdGoodEventAt_of_horizontalIncrement {p : unitInterval}
    (hU : SupercriticalBondCorrectorInput) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hH : HorizontalIncrementStep p) (Cχ : ℝ) (hCχ : 1 ≤ Cχ) :
    ∃ A ⊆ eventG3 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A := by
  obtain ⟨A, hA, hAm, hApos⟩ :=
    thirdGoodEventDirectionalAt_of_horizontalIncrement hU hpc hp1 hH Cχ hCχ
  exact ⟨A, hA.trans (eventG3Edge_subset 0 Cχ), hAm, hApos⟩

/-- The directional good event moves with the environment (stationarity, L2381): if the
environment translated by `-x` lies in `G_1(0, K) ∩ G_2(0, K) ∩ G_3(0, C_χ)` (printed `G_3`), then
`ω` lies in `G_1(x, K) ∩ G_2(x, K) ∩ G_3(x, C_χ)`. -/
theorem mem_eventGDirectional_of_translation {Cf : ℕ} {R c₁ Cχ K : ℝ} (x : Vertex 2)
    {ω : LatticeProb.Percolation.Configuration 2}
    (hω : configurationTranslation (-x) ω ∈
      eventG1 Cf R c₁ 0 K ∩ eventG2 0 K ∩ eventG3Directional 0 Cχ) :
    ω ∈ eventG1 Cf R c₁ x K ∩ eventG2 x K ∩ eventG3Directional x Cχ := by
  have h : configurationTranslation x (configurationTranslation (-x) ω) ∈
      eventG1 Cf R c₁ (0 + x) K ∩ eventG2 (0 + x) K ∩ eventG3Directional (0 + x) Cχ :=
    ⟨⟨eventG1_translation x hω.1.1, eventG2_translation x hω.1.2⟩,
      eventG3Edge_translation x hω.2⟩
  rwa [configurationTranslation_add, add_neg_cancel, configurationTranslation_zero,
    zero_add] at h

/-- Lemma 5.25 as printed (`GoodEventLowerBoundDirectionalStmt p`) at a fixed `p_c(2) < p < 1`
from the printed third good event at `p`, Theorem 2.5 and the uniqueness of the infinite cluster
(the first and second good event steps are proved). -/
theorem goodEventLowerBoundDirectional_of_thirdGoodEventAt {p : unitInterval}
    (hQ : Rigidity.External.CorrectorQuantitativeInput) (hUq : SupercriticalBondUniqueness)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h3 : ∀ Cχ : ℝ, 1 ≤ Cχ →
      ∃ A ⊆ eventG3Directional 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A) :
    GoodEventLowerBoundDirectionalStmt p := by
  intro Cχ hCχ
  set μ := latticeBondLaw 2 p
  obtain ⟨A₃, hA₃, hA₃m, hA₃pos⟩ := h3 Cχ hCχ
  have hA₃top : μ A₃ ≠ ⊤ := measure_ne_top μ A₃
  set c := (μ A₃).toReal / 2 with hc_def
  have hc : 0 < c := half_pos (ENNReal.toReal_pos hA₃pos.ne' hA₃top)
  refine ⟨c, hc, fun Cf R c₁ hL => ?_⟩
  obtain ⟨C₁, a₁, hC₁, ha₁, hbad⟩ := hL
  obtain ⟨C₂, a₂, s, hC₂, ha₂, hs, hG2⟩ := secondGoodEventStep hUq hQ p hpc hp1
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (((tendsto_exp_add_exp_rpow (C := C₁) (C' := C₂) ha₁ ha₂ hs).eventually
      (ge_mem_nhds hc)).and (eventually_ge_atTop 1))
  refine ⟨K₀, fun K hK x => ?_⟩
  obtain ⟨hsmall, hK1⟩ := hK₀ K hK
  obtain ⟨A₀, hA₀, hA₀m, hA₀μ⟩ :=
    exists_measurable_subset_eventG1_eventG2_zero (p := p) (Cf := Cf) (R := R) (c₁ := c₁)
      (K := K) firstGoodEventStep
      (fun ω hω => by obtain ⟨h, hx, -⟩ := hA₃ hω; exact ⟨h, hx⟩) hA₃m
  have hD : μ (badPathEvent Cf R c₁ K) + μ (eventG2 0 K)ᶜ ≤ ENNReal.ofReal c := by
    refine (add_le_add (hbad K hK1) (hG2 0 K hK1)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsmall
  have hτ := measurePreserving_configurationTranslation p (-x)
  refine ⟨configurationTranslation (-x) ⁻¹' A₀,
    fun ω hω => mem_eventGDirectional_of_translation x ⟨(hA₀ hω).1, hA₃ (hA₀ hω).2⟩,
    hτ.measurable hA₀m, ?_⟩
  rw [hτ.measure_preimage hA₀m.nullMeasurableSet]
  refine le_trans ?_ (le_trans (tsub_le_tsub_left hD _) hA₀μ)
  rw [← ENNReal.ofReal_toReal hA₃top, ← ENNReal.ofReal_sub _ hc.le]
  exact ENNReal.ofReal_le_ofReal (by rw [hc_def]; linarith)

/-- Lemma 5.25 at a fixed `p_c(2) < p < 1` from the third good event at `p`, Theorem 2.5 and the
uniqueness of the infinite cluster (the translation, first and second good event steps are
proved). -/
theorem goodEventLowerBound_of_thirdGoodEventAt {p : unitInterval}
    (hQ : Rigidity.External.CorrectorQuantitativeInput) (hUq : SupercriticalBondUniqueness)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h3 : ∀ Cχ : ℝ, 1 ≤ Cχ →
      ∃ A ⊆ eventG3 0 Cχ, MeasurableSet A ∧ 0 < latticeBondLaw 2 p A) :
    GoodEventLowerBoundStmt p := by
  intro Cχ hCχ
  set μ := latticeBondLaw 2 p
  obtain ⟨A₃, hA₃, hA₃m, hA₃pos⟩ := h3 Cχ hCχ
  have hA₃top : μ A₃ ≠ ⊤ := measure_ne_top μ A₃
  set c := (μ A₃).toReal / 2 with hc_def
  have hc : 0 < c := half_pos (ENNReal.toReal_pos hA₃pos.ne' hA₃top)
  refine ⟨c, hc, fun Cf R c₁ hL => ?_⟩
  obtain ⟨C₁, a₁, hC₁, ha₁, hbad⟩ := hL
  obtain ⟨C₂, a₂, s, hC₂, ha₂, hs, hG2⟩ := secondGoodEventStep hUq hQ p hpc hp1
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (((tendsto_exp_add_exp_rpow (C := C₁) (C' := C₂) ha₁ ha₂ hs).eventually
      (ge_mem_nhds hc)).and (eventually_ge_atTop 1))
  refine ⟨K₀, fun K hK x => ?_⟩
  obtain ⟨hsmall, hK1⟩ := hK₀ K hK
  obtain ⟨A₀, hA₀, hA₀m, hA₀μ⟩ :=
    exists_measurable_subset_eventG_zero (p := p) (Cf := Cf) (R := R) (c₁ := c₁) (K := K)
      firstGoodEventStep hA₃ hA₃m
  have hD : μ (badPathEvent Cf R c₁ K) + μ (eventG2 0 K)ᶜ ≤ ENNReal.ofReal c := by
    refine (add_le_add (hbad K hK1) (hG2 0 K hK1)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsmall
  have hτ := measurePreserving_configurationTranslation p (-x)
  refine ⟨configurationTranslation (-x) ⁻¹' A₀,
    fun ω hω => (goodEventTranslationStep Cf R c₁ Cχ K x ω).mpr (hA₀ hω),
    hτ.measurable hA₀m, ?_⟩
  rw [hτ.measure_preimage hA₀m.nullMeasurableSet]
  refine le_trans ?_ (le_trans (tsub_le_tsub_left hD _) hA₀μ)
  rw [← ENNReal.ofReal_toReal hA₃top, ← ENNReal.ofReal_sub _ hc.le]
  exact ENNReal.ofReal_le_ofReal (by rw [hc_def]; linarith)

/-- **The signed variant of Proposition 3.2** (`HorizontalIncrementStep p`, d = 2): for
`p_c(2) < p < 1` and every `L ≥ 1`, with positive probability `(0, e₁)` is an edge of the infinite
cluster across which a corrected plane `ℓ_{e₁}` increases by more than `L`. From Proposition 3.2
as printed, the cited inputs and the exterior network of the surgery region. -/
theorem horizontalIncrement (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness) (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput) (hAD : ArmstrongDarioOrderZero)
    (hE : SupercriticalBondGreenColumnExistence) (hGQ : SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    (hNet : Steps.S3.ExteriorNetworkStep p) : HorizontalIncrementStep p :=
  Steps.S3.horizontalIncrementStep_of_exteriorNetwork_inputs hUq hCorr hpc hp1
    (notLipschitz le_rfl p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW hHom) hNet

/-- Lemma 5.25 (`GoodEventLowerBoundStmt p`) by the signed route (printed edge `G_3`; `Main` uses
the composition `goodEventLowerBound` of `Section5d.lean`): for
`p_c(2) < p < 1` and every `C_χ ≥ 1` there is `c > 0` such that, for parameters `R, c₁` satisfying
the bound of Proposition 5.24, `P[G(x, C_χ, K)] ≥ c` for all `x` and all large `K`. The step
`ExteriorNetworkStep p` of the signed route is a hypothesis here (proved by `exteriorNetworkStep`). -/
theorem goodEventLowerBound_of_exteriorNetwork (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness) (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput) (hAD : ArmstrongDarioOrderZero)
    (hE : SupercriticalBondGreenColumnExistence) (hGQ : SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    (hNet : Steps.S3.ExteriorNetworkStep p) : GoodEventLowerBoundStmt p :=
  goodEventLowerBound_of_thirdGoodEventAt hCQ hUq hpc hp1
    (thirdGoodEventAt_of_horizontalIncrement hCorr hpc hp1
      (horizontalIncrement p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW hHom hNet))

/-- `ThirdGoodEventStep` (L2370, all `p` at once) from the cited inputs and the exterior network
step at every `p_c(2) < p < 1`. -/
theorem thirdGoodEventStep_of_exteriorNetwork (hUq : SupercriticalBondUniqueness)
    (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput) (hAD : ArmstrongDarioOrderZero)
    (hE : SupercriticalBondGreenColumnExistence) (hGQ : SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hHom : Proofs.S3.HomogenizedCoefficientProposed)
    (hNet : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      Steps.S3.ExteriorNetworkStep p) : ThirdGoodEventStep :=
  thirdGoodEventStep_of_horizontalIncrement fun p hpc hp1 =>
    horizontalIncrement p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW hHom (hNet p hpc hp1)

/-- **Lemma 5.25 as printed** (`GoodEventLowerBoundDirectionalStmt p`, the printed third good
event on the edge `(x, x + e₁)` in place of the direction-free one of [C32]; not the draft
statement): for `p_c(2) < p < 1` and every `C_χ ≥ 1` there is `c > 0` such that, for parameters
`R, c₁` satisfying the bound of Proposition 5.24, `P[G_1(x, K) ∩ G_2(x, K) ∩ G_3(x, C_χ)] ≥ c` for
all `x` and all large `K`. From the literature inputs only: the signed variant of Proposition 3.2
(`horizontalIncrement`) with the exterior network of the surgery region proved
(`Rigidity.Proofs.S3.exteriorNetworkStep`) and the positivity of the homogenized coefficient proved
(`homogenizedCoefficientProposed`). -/
theorem goodEventLowerBoundDirectional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : SupercriticalBondUniqueness) (hCorr : SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput) (hAD : ArmstrongDarioOrderZero)
    (hE : SupercriticalBondGreenColumnExistence) (hGQ : SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) : GoodEventLowerBoundDirectionalStmt p :=
  goodEventLowerBoundDirectional_of_thirdGoodEventAt hCQ hUq hpc hp1
    (thirdGoodEventDirectionalAt_of_horizontalIncrement hCorr hpc hp1
      (horizontalIncrement p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW
        (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
        (Proofs.S3.exteriorNetworkStep hUq hCorr hAD hE hGQ hpc hp1)))

end Rigidity.Assembly
