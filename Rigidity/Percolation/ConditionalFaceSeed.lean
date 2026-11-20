import Rigidity.Percolation.MarkedFaceCandidates

/-!
# Conditional seed connections across an explored boundary

A supercritical seed construction provides many exterior-reaching boundary
candidates. Uniform bond marks then open at least one candidate with high
probability, even after conditioning boundary marks above prior thresholds.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External Filter
open scoped unitInterval Topology

/-- Above criticality and below density one, there are seed and cube sizes
such that, uniformly over admissible explored sets and previously revealed
boundary thresholds, a raised-threshold exit reaches an outward seed target
with conditional probability greater than `1 - ε`. -/
theorem exists_conditional_markedFaceSeedExit {d : ℕ} [NeZero d]
    (p : unitInterval) (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (i : Fin d) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ M n : ℕ, 0 < M ∧ 2 * M < n ∧ (2 * M + 1) ∣ n + 1 ∧
      ∀ R : Finset (Vertex d), centeredBondCubeFinset M ⊆ R →
        (R : Set (Vertex d)) ⊆ centeredBondCube n →
        (∀ x ∈ centeredCubeOrthantFace n i (fun _ => true), x ∉ R) →
        ∀ β : Bond d → unitInterval,
          (∀ e ∈ vertexCutBonds R, (β e : ℝ) + δ ≤ 1) →
          1 - ε < (bondMarkLaw d).real (bondMarksAbove (vertexCutBonds R) β ∩
              markedFaceSeedExit p M n i R β δ) /
            (bondMarkLaw d).real (bondMarksAbove (vertexCutBonds R) β) := by
  classical
  haveI : IsProbabilityMeasure (bondMarkLaw d) := by
    dsimp only [bondMarkLaw]
    infer_instance
  let θ : ℝ := min (ε / 3) (1 / 3)
  have hθ : 0 < θ := lt_min (by linarith) (by norm_num)
  have hθε : 3 * θ ≤ ε := by
    have h := min_le_left (ε / 3) (1 / 3)
    dsimp only [θ]
    linarith
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hδ1)
    (show 1 - δ < 1 by linarith)
  obtain ⟨t, ht⟩ := (hlim.eventually (eventually_lt_nhds hθ)).exists
  obtain ⟨M, n, hM, hn, halign, hmany⟩ :=
    exists_faceSeed_many_boundaryCandidates p hp hp1 i t θ hθ
  refine ⟨M, n, hM, hn, halign, ?_⟩
  intro R hseed hR hface β hβ
  let F := vertexCutBonds R
  let U := markedFaceSeedCandidates p M n i R
  let K := faceSeedTargets (centeredCubeOrthantFace n i (fun _ => true)) (2 * M + 1) i n
  let V : Configuration d → Finset (Bond d) := boundaryCandidateBonds R (centeredBondCube n) F K
  let A : Set (Configuration d) := {ω | (V ω).card < t}
  have hU := measurable_markedFaceSeedCandidates p M n i R hR hface
  have hsub : ∀ ω, U ω ⊆ F := by
    intro ω e he
    change e ∈ V (thresholdBondMarks p ω) at he
    exact (mem_boundaryCandidateBonds (R : Set (Vertex d)) (centeredBondCube n) F K
      (thresholdBondMarks p ω) e).mp he |>.1
  have hK := measurable_faceSeedTargets_exterior R n (2 * M + 1) i hR
    (centeredCubeOrthantFace n i (fun _ => true)) hface
  have hV := measurable_boundaryCandidateBonds R (centeredBondCube n)
    (finite_centeredBondCube n) F K hK (localBonds_sdiff_subset_vertexCutBonds_compl R _)
  have hAlocal : MeasurableSet[bondSigma (↑F : Set (Bond d))ᶜ] A := by
    have hc : @Measurable _ _ (bondSigma (↑F : Set (Bond d))ᶜ) _
        (fun ω => (V ω).card) := (measurable_of_countable Finset.card).comp hV
    exact hc (Set.to_countable {m : ℕ | m < t}).measurableSet
  have hA : MeasurableSet A := bondSigma_le _ _ hAlocal
  have hsmallCfg : (latticeBondLaw d p).real A < θ := by
    apply lt_of_le_of_lt ?_ (hmany R hseed hR hface)
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    exact Nat.le_of_lt hω
  have hsmall : (bondMarkLaw d).real {ω | (U ω).card < t} ≤ θ := by
    change (bondMarkLaw d).real (thresholdBondMarks p ⁻¹' A) ≤ θ
    rw [bondMarkLaw_real_threshold_preimage p hA]
    exact le_of_lt hsmallCfg
  let β' : Bond d → unitInterval := fun e => if e ∈ F then β e else 0
  have hβ' : ∀ e, (β' e : ℝ) + δ ≤ 1 := by
    intro e
    by_cases he : e ∈ F
    · simpa only [β', he, ↓reduceIte] using hβ e he
    · simpa [β', he] using hδ1
  have hHeq : bondMarksAbove F β' = bondMarksAbove F β := by
    ext ω
    simp only [bondMarksAbove, Set.mem_setOf_eq]
    apply forall₂_congr
    intro e he
    simp only [β', he, ↓reduceIte]
  have hCsubset : selectedBondMarkSuccess U β' δ hδ.le hβ' ⊆
      markedFaceSeedExit p M n i R β δ := by
    intro ω hω
    obtain ⟨x, hx, y, hy, hxy, hopen, z, hz, hzout, hpath⟩ :=
      selectedBondMarkSuccess_subset_markedFaceSeedExit p M n i R β' δ hδ.le hβ' hω
    have he : bondOfAdjacent hxy ∈ F := bondOfAdjacent_mem_vertexCutBonds R hx hy.2 hxy
    refine ⟨x, hx, y, hy, hxy, ?_, z, hz, hzout, hpath⟩
    simpa only [β', he, ↓reduceIte] using hopen
  have hcond := conditional_selectedBondMarkSuccess_lower F U hU hsub β' δ hδ hδ1 hβ' t θ hsmall
  have hpos := bondMarkLaw_real_bondMarksAbove_pos F β' δ hδ (fun e _ => hβ' e)
  have hnum : (bondMarkLaw d).real (bondMarksAbove F β' ∩
      selectedBondMarkSuccess U β' δ hδ.le hβ') ≤
      (bondMarkLaw d).real (bondMarksAbove F β' ∩ markedFaceSeedExit p M n i R β δ) :=
    measureReal_mono (Set.inter_subset_inter_right _ hCsubset) (measure_ne_top _ _)
  have hquot := div_le_div_of_nonneg_right hnum hpos.le
  rw [hHeq] at hcond hquot
  have h := hcond.trans hquot
  linarith

end Rigidity.Percolation
