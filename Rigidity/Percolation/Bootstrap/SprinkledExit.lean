import Rigidity.Percolation.Bootstrap.SeedFaceLink
import Rigidity.Percolation.ConditionalBondCandidates
import Rigidity.Percolation.BoundaryCandidateCut
import Rigidity.Percolation.ConditionalFaceSeedInside

/-!
# Sprinkled exits from a closed region

Let `R ⊆ W` be finite vertex sets and condition the marks of the bonds from `R` to `W \ R` to
exceed `p₀`, i.e. these bonds are closed at level `p₀`. The *candidates* are those bonds whose
exterior endpoint is joined at level `p₀` to a target `T` inside `W \ R`; they are selected by
marks outside the conditioned cut. Raising the level to `p₀ + δ` opens one of them except with
probability at most `P_{p₀}(R ↮ T in W) / (1 - p₀)^K + (1 - δ)^K` for every `K`, times the
probability of the conditioning. An opened candidate joins `R` to `T` inside `W` at level
`p₀ + δ`.

This is the sprinkling step of G. R. Grimmett and J. M. Marstrand, *The supercritical phase of
percolation is well behaved*, Proc. R. Soc. Lond. A 430 (1990), and of D. Contreras,
*Percolation on graphs of polynomial growth*, ETH Zürich dissertation (2022), Lemmas 2.3.3 and
2.3.4.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-- Thresholding at a larger level opens more bonds. -/
theorem thresholdBondMarks_mono {p q : unitInterval} (hpq : p ≤ q) (ω : BondMarks d) :
    thresholdBondMarks p ω ≤ thresholdBondMarks q ω := by
  intro e
  change markThreshold p (ω e) ≤ markThreshold q (ω e)
  unfold markThreshold
  by_cases h : ω e ≤ p
  · simp [h, h.trans hpq]
  · simp [h]

/-- The level `p + δ` as a point of the unit interval. -/
def raisedLevel (p : unitInterval) (δ : ℝ) (hδ : 0 ≤ δ) (h : (p : ℝ) + δ ≤ 1) : unitInterval :=
  ⟨(p : ℝ) + δ, add_nonneg p.property.1 hδ, h⟩

/-- The constant threshold at level `p`. -/
def constThreshold (p : unitInterval) : Bond d → unitInterval := fun _ => p

/-- The candidate exits from `R` towards `T` inside `W`, read on the level-`p` configuration. -/
def exitCandidates (p : unitInterval) (R W T : Finset (Vertex d)) (ω : BondMarks d) :
    Finset (Bond d) :=
  boundaryCandidateBonds (R : Set (Vertex d)) (W : Set (Vertex d)) (vertexCutBondsIn R W)
    (fun _ => T) (thresholdBondMarks p ω)

/-- Candidate exits are bonds of the conditioned cut. -/
theorem exitCandidates_subset (p : unitInterval) (R W T : Finset (Vertex d)) (ω : BondMarks d) :
    exitCandidates p R W T ω ⊆ vertexCutBondsIn R W := by
  intro e he
  exact ((mem_boundaryCandidateBonds _ _ _ _ _ e).1 he).1

/-- Candidate exits are selected by marks outside the conditioned cut. -/
theorem measurable_exitCandidates (p : unitInterval) (R W T : Finset (Vertex d)) :
    @Measurable _ _ (bondMarkSigma (↑(vertexCutBondsIn R W) : Set (Bond d))ᶜ) _
      (exitCandidates p R W T) := by
  classical
  have hlocal : localBonds ((W : Set (Vertex d)) \ (R : Set (Vertex d))) ⊆
      (↑(vertexCutBondsIn R W) : Set (Bond d))ᶜ := by
    intro e he hcut
    have hcut' : e ∈ vertexCutBonds R := (Finset.mem_filter.1 hcut).1
    exact localBonds_sdiff_subset_vertexCutBonds_compl R W he hcut'
  have hcand := measurable_boundaryCandidateBonds (R : Set (Vertex d)) (W : Set (Vertex d))
    W.finite_toSet (vertexCutBondsIn R W) (fun _ => T) measurable_const hlocal
  exact hcand.comp (measurable_thresholdBondMarks_bondSigma p _)

/-- The marks of the cut from `R` to `W \ R` all exceed `p`: the cut is closed at level `p`. -/
def cutClosed (p : unitInterval) (R W : Finset (Vertex d)) : Set (BondMarks d) :=
  bondMarksAbove (vertexCutBondsIn R W) (constThreshold p)

/-- Some candidate exit has mark at most `p + δ`. -/
def exitOpens (p : unitInterval) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : (p : ℝ) + δ ≤ 1)
    (R W T : Finset (Vertex d)) : Set (BondMarks d) :=
  selectedBondMarkSuccess (exitCandidates p R W T) (constThreshold p) δ hδ (fun _ => hδ1)

/-- An opened candidate exit joins `R` to `T` inside `W` at the raised level. -/
theorem exitOpens_connects (p : unitInterval) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : (p : ℝ) + δ ≤ 1)
    (R W T : Finset (Vertex d)) (hRW : (R : Set (Vertex d)) ⊆ W) {ω : BondMarks d}
    (h : ω ∈ exitOpens p δ hδ hδ1 R W T) :
    ∃ x ∈ R, ∃ z ∈ T, z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧
      (openIn (thresholdBondMarks (raisedLevel p δ hδ hδ1) ω) W).Reachable x z := by
  classical
  obtain ⟨e, he, hle⟩ := h
  obtain ⟨-, x, hx, y, hy, hxy, rfl, z, hzT, hz, hreach⟩ :=
    (mem_boundaryCandidateBonds _ _ _ _ _ _).1 he
  have hopen : thresholdBondMarks (raisedLevel p δ hδ hδ1) ω (bondOfAdjacent hxy) = true := by
    change markThreshold _ (ω (bondOfAdjacent hxy)) = true
    unfold markThreshold
    have : ω (bondOfAdjacent hxy) ≤ raisedLevel p δ hδ hδ1 := by
      simpa only [raisedBondThreshold, he, ↓reduceIte, raisedLevel, constThreshold] using hle
    simp [this]
  have hle' : p ≤ raisedLevel p δ hδ hδ1 := by
    change (p : ℝ) ≤ (p : ℝ) + δ
    linarith
  have hedge : (openIn (thresholdBondMarks (raisedLevel p δ hδ hδ1) ω) W).Adj x y :=
    ⟨(openGraph_adj_iff _ x y).2 ⟨hxy, hopen⟩, hRW hx, hy.1⟩
  have htail : (openIn (thresholdBondMarks (raisedLevel p δ hδ hδ1) ω) W).Reachable y z := by
    apply (hreach.mono (openIn_mono_configuration (thresholdBondMarks_mono hle' ω) _)).mono
    intro a b hab
    exact ⟨hab.1, hab.2.1.1, hab.2.2.1⟩
  exact ⟨x, hx, z, hzT, hz, hedge.reachable.trans htail⟩

/-- The mark law pushes forward to the Bernoulli law at every level. -/
theorem bondMarkLaw_real_preimage_threshold (p : unitInterval) {A : Set (Configuration d)}
    (hA : MeasurableSet A) :
    (bondMarkLaw d).real (thresholdBondMarks p ⁻¹' A) = (latticeBondLaw d p).real A := by
  have hm : Measurable (thresholdBondMarks (d := d) p) := by
    apply measurable_pi_lambda
    intro e
    exact (measurable_markThreshold p).comp (measurable_pi_apply e)
  rw [measureReal_def, measureReal_def, ← bondMarkLaw_map_thresholdBondMarks d p,
    Measure.map_apply hm hA]

/-- **Sprinkled exit.** Conditioned on the cut from `R` to `W \ R` being closed at level `p`, no
candidate exit opens at level `p + δ` with probability at most
`P_p(R ↮ T in W) / (1 - p)^K + (1 - δ)^K`, for every `K`. The bound is stated before division by
the probability of the conditioning. -/
theorem bondMarkLaw_real_cutClosed_inter_not_exitOpens_le (p : unitInterval)
    (hp1 : (p : ℝ) < 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : (p : ℝ) + δ ≤ 1)
    (R W T : Finset (Vertex d)) (hRW : (R : Set (Vertex d)) ⊆ W) (K : ℕ) :
    (bondMarkLaw d).real (cutClosed p R W ∩ (exitOpens p δ hδ.le hδ1 R W T)ᶜ) ≤
      ((latticeBondLaw d p).real {ω | ¬ ∃ x ∈ R, ∃ z ∈ T,
          z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧ (openIn ω W).Reachable x z} /
          (1 - (p : ℝ)) ^ K + (1 - δ) ^ K) *
        (bondMarkLaw d).real (cutClosed p R W) := by
  classical
  have hδ1' : δ ≤ 1 := by linarith [p.property.1]
  set F := vertexCutBondsIn R W with hF
  have hU := measurable_exitCandidates p R W T
  have hcandF : ∀ x ∈ (R : Set (Vertex d)), ∀ y ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)),
      ∀ hxy : (nearestNeighborGraph d).Adj x y, bondOfAdjacent hxy ∈ F :=
    fun x hx y hy hxy => bondOfAdjacent_mem_vertexCutBondsIn R W hRW hx hy hxy
  have hlocal : localBonds ((W : Set (Vertex d)) \ (R : Set (Vertex d))) ⊆
      (↑F : Set (Bond d))ᶜ := by
    intro e he hcut
    have hcut' : e ∈ vertexCutBonds R := (Finset.mem_filter.1 hcut).1
    exact localBonds_sdiff_subset_vertexCutBonds_compl R W he hcut'
  have hcandMeas : Measurable (boundaryCandidateBonds (R : Set (Vertex d)) (W : Set (Vertex d))
      F (fun _ => T)) :=
    (measurable_boundaryCandidateBonds (R : Set (Vertex d)) (W : Set (Vertex d))
      W.finite_toSet F (fun _ => T) measurable_const hlocal).mono (bondSigma_le _) le_rfl
  have hfew := measureReal_few_boundaryCandidateBonds_le p hp1 (R : Set (Vertex d))
    (W : Set (Vertex d)) W.finite_toSet F (fun _ => T) K measurable_const hlocal
  have hclosed : {ω : Configuration d | ω ∈ allBondsClosed (boundaryCandidateBonds
      (R : Set (Vertex d)) (W : Set (Vertex d)) F (fun _ => T) ω)} =
      {ω | ¬ ∃ x ∈ R, ∃ z ∈ T, z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧
        (openIn ω W).Reachable x z} := by
    ext ω
    exact allBondsClosed_boundaryCandidateBonds_iff_not_reachable _ _ hRW F hcandF _ ω
  rw [hclosed] at hfew
  have hsmall : (bondMarkLaw d).real {ω | (exitCandidates p R W T ω).card < K} ≤
      (latticeBondLaw d p).real {ω | ¬ ∃ x ∈ R, ∃ z ∈ T,
        z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧ (openIn ω W).Reachable x z} /
          (1 - (p : ℝ)) ^ K := by
    have hpre : {ω : BondMarks d | (exitCandidates p R W T ω).card < K} =
        thresholdBondMarks p ⁻¹' {η | (boundaryCandidateBonds (R : Set (Vertex d))
          (W : Set (Vertex d)) F (fun _ => T) η).card < K} := rfl
    have hmeasA : MeasurableSet {η : Configuration d | (boundaryCandidateBonds
        (R : Set (Vertex d)) (W : Set (Vertex d)) F (fun _ => T) η).card < K} :=
      ((measurable_of_countable Finset.card).comp hcandMeas)
        (Set.to_countable {n : ℕ | n < K}).measurableSet
    rw [hpre, bondMarkLaw_real_preimage_threshold p hmeasA]
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hfew
    intro η hη
    exact Nat.le_of_lt hη
  exact bondMarkLaw_real_selected_failure_le F (exitCandidates p R W T) hU
    (exitCandidates_subset p R W T) (constThreshold p) δ hδ.le hδ1' (fun _ => hδ1) K _ hsmall

/-- The mark law is a probability measure. -/
instance isProbabilityMeasure_bondMarkLaw : IsProbabilityMeasure (bondMarkLaw d) := by
  dsimp only [bondMarkLaw]
  infer_instance

/-- Marks at a fixed finite family of bonds are almost surely positive. -/
theorem bondMarkLaw_compl_bondMarksAbove_zero (G : Finset (Bond d)) :
    bondMarkLaw d (bondMarksAbove G (fun _ => 0))ᶜ = 0 := by
  have hsub : (bondMarksAbove G (fun _ => (0 : unitInterval)))ᶜ ⊆
      ⋃ e ∈ G, (fun ω : BondMarks d => ω e) ⁻¹' Set.Iic 0 := by
    intro ω hω
    simp only [bondMarksAbove, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hω
    obtain ⟨e, he, hle⟩ := hω
    exact Set.mem_biUnion he hle
  refine le_antisymm ((measure_mono hsub).trans ?_) bot_le
  refine (measure_biUnion_finset_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_eq_zero
  intro e _
  have hmp := measurePreserving_eval_infinitePi (μ := fun _ : Bond d => (volume : Measure I)) e
  change (bondMarkLaw d) ((Function.eval e) ⁻¹' Set.Iic 0) = 0
  rw [bondMarkLaw, hmp.measure_preimage measurableSet_Iic.nullMeasurableSet,
    unitInterval.volume_Iic]
  simp

/-- **Sprinkled exit with partial conditioning.** The sprinkled-exit bound holds when only a part
`F₀` of the cut from `R` to `W \ R` is conditioned to be closed at level `p`. -/
theorem bondMarkLaw_real_partialCut_inter_not_exitOpens_le (p : unitInterval)
    (hp1 : (p : ℝ) < 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : (p : ℝ) + δ ≤ 1)
    (R W T : Finset (Vertex d)) (hRW : (R : Set (Vertex d)) ⊆ W) (F₀ : Finset (Bond d))
    (hF₀ : F₀ ⊆ vertexCutBondsIn R W) (K : ℕ) :
    (bondMarkLaw d).real (bondMarksAbove F₀ (constThreshold p) ∩
        (exitOpens p δ hδ.le hδ1 R W T)ᶜ) ≤
      ((latticeBondLaw d p).real {ω | ¬ ∃ x ∈ R, ∃ z ∈ T,
          z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧ (openIn ω W).Reachable x z} /
          (1 - (p : ℝ)) ^ K + (1 - δ) ^ K) *
        (bondMarkLaw d).real (bondMarksAbove F₀ (constThreshold p)) := by
  classical
  have hδ1' : δ ≤ 1 := by linarith [p.property.1]
  set F := vertexCutBondsIn R W with hF
  set β : Bond d → unitInterval := fun e => if e ∈ F₀ then p else 0 with hβdef
  have hβ : ∀ e, (β e : ℝ) + δ ≤ 1 := by
    intro e
    simp only [hβdef]
    split_ifs
    · exact hδ1
    · simpa using hδ1'
  set Z := bondMarksAbove (F \ F₀) (fun _ => (0 : unitInterval)) with hZ
  have hZnull : bondMarkLaw d Zᶜ = 0 := bondMarkLaw_compl_bondMarksAbove_zero _
  have hH' : bondMarksAbove F β = bondMarksAbove F₀ (constThreshold p) ∩ Z := by
    ext ω
    simp only [bondMarksAbove, Set.mem_setOf_eq, Set.mem_inter_iff, hZ, Finset.mem_sdiff,
      constThreshold, hβdef]
    constructor
    · intro h
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have := h e (hF₀ he)
        simpa [he] using this
      · have := h e he.1
        simpa [he.2] using this
    · rintro ⟨h1, h2⟩ e he
      by_cases he0 : e ∈ F₀
      · simpa [he0] using h1 e he0
      · simpa [he0] using h2 e ⟨he, he0⟩
  have hU := measurable_exitCandidates p R W T
  have hcandF : ∀ x ∈ (R : Set (Vertex d)), ∀ y ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)),
      ∀ hxy : (nearestNeighborGraph d).Adj x y, bondOfAdjacent hxy ∈ F :=
    fun x hx y hy hxy => bondOfAdjacent_mem_vertexCutBondsIn R W hRW hx hy hxy
  have hlocal : localBonds ((W : Set (Vertex d)) \ (R : Set (Vertex d))) ⊆
      (↑F : Set (Bond d))ᶜ := by
    intro e he hcut
    have hcut' : e ∈ vertexCutBonds R := (Finset.mem_filter.1 hcut).1
    exact localBonds_sdiff_subset_vertexCutBonds_compl R W he hcut'
  have hcandMeas : Measurable (boundaryCandidateBonds (R : Set (Vertex d)) (W : Set (Vertex d))
      F (fun _ => T)) :=
    (measurable_boundaryCandidateBonds (R : Set (Vertex d)) (W : Set (Vertex d))
      W.finite_toSet F (fun _ => T) measurable_const hlocal).mono (bondSigma_le _) le_rfl
  have hfew := measureReal_few_boundaryCandidateBonds_le p hp1 (R : Set (Vertex d))
    (W : Set (Vertex d)) W.finite_toSet F (fun _ => T) K measurable_const hlocal
  have hclosed : {ω : Configuration d | ω ∈ allBondsClosed (boundaryCandidateBonds
      (R : Set (Vertex d)) (W : Set (Vertex d)) F (fun _ => T) ω)} =
      {ω | ¬ ∃ x ∈ R, ∃ z ∈ T, z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧
        (openIn ω W).Reachable x z} := by
    ext ω
    exact allBondsClosed_boundaryCandidateBonds_iff_not_reachable _ _ hRW F hcandF _ ω
  rw [hclosed] at hfew
  have hsmall : (bondMarkLaw d).real {ω | (exitCandidates p R W T ω).card < K} ≤
      (latticeBondLaw d p).real {ω | ¬ ∃ x ∈ R, ∃ z ∈ T,
        z ∈ (W : Set (Vertex d)) \ (R : Set (Vertex d)) ∧ (openIn ω W).Reachable x z} /
          (1 - (p : ℝ)) ^ K := by
    have hpre : {ω : BondMarks d | (exitCandidates p R W T ω).card < K} =
        thresholdBondMarks p ⁻¹' {η | (boundaryCandidateBonds (R : Set (Vertex d))
          (W : Set (Vertex d)) F (fun _ => T) η).card < K} := rfl
    have hmeasA : MeasurableSet {η : Configuration d | (boundaryCandidateBonds
        (R : Set (Vertex d)) (W : Set (Vertex d)) F (fun _ => T) η).card < K} :=
      ((measurable_of_countable Finset.card).comp hcandMeas)
        (Set.to_countable {n : ℕ | n < K}).measurableSet
    rw [hpre, bondMarkLaw_real_preimage_threshold p hmeasA]
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hfew
    intro η hη
    exact Nat.le_of_lt hη
  have hmain := bondMarkLaw_real_selected_failure_le F (exitCandidates p R W T) hU
    (exitCandidates_subset p R W T) β δ hδ.le hδ1' hβ K _ hsmall
  have hsucc : (exitOpens p δ hδ.le hδ1 R W T)ᶜ ⊆
      (selectedBondMarkSuccess (exitCandidates p R W T) β δ hδ.le hβ)ᶜ := by
    intro ω hω hsel
    apply hω
    obtain ⟨e, he, hle⟩ := hsel
    refine ⟨e, he, le_trans hle ?_⟩
    simp only [raisedBondThreshold, he, ↓reduceIte, constThreshold, hβdef]
    rw [← Subtype.coe_le_coe]
    change ((if e ∈ F₀ then p else 0 : unitInterval) : ℝ) + δ ≤ (p : ℝ) + δ
    split_ifs
    · exact le_rfl
    · change (0 : ℝ) + δ ≤ (p : ℝ) + δ
      linarith [p.property.1]
  have hconull : ∀ X : Set (BondMarks d), (bondMarkLaw d).real (X ∩ Z) =
      (bondMarkLaw d).real X := by
    intro X
    rw [measureReal_def, measureReal_def, measure_inter_conull hZnull]
  calc (bondMarkLaw d).real (bondMarksAbove F₀ (constThreshold p) ∩
        (exitOpens p δ hδ.le hδ1 R W T)ᶜ)
      = (bondMarkLaw d).real (bondMarksAbove F₀ (constThreshold p) ∩
        (exitOpens p δ hδ.le hδ1 R W T)ᶜ ∩ Z) := (hconull _).symm
    _ ≤ (bondMarkLaw d).real (bondMarksAbove F β ∩
        (selectedBondMarkSuccess (exitCandidates p R W T) β δ hδ.le hβ)ᶜ) := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        rintro ω ⟨⟨h1, h2⟩, h3⟩
        rw [hH']
        exact ⟨⟨h1, h3⟩, hsucc h2⟩
    _ ≤ _ := hmain
    _ = _ := by rw [hH', hconull]

end Rigidity.Percolation
