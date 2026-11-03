import Rigidity.Proofs.S3.SlopeSetMeasurable
import LatticeProb.Prob.Percolation.LatticeBondErgodicity
import LatticeProb.Prob.ErgodicClosedSets

/-!
# Lemma 3.1: the zero-one law and the deterministic slope

Proofs of the steps `step:3.1-zero-one` (paper L817-819 of the corrected draft) and
`step:3.1-deterministic-slope` (paper L829-838) of Lemma 3.1, carved in
`Rigidity.Steps.S3.reductionToSlopeE1_of_steps`.

* `zeroOneStep`: the event `E_L` is invariant under the translations of the lattice, and the
  translation by `e₁` is ergodic for Bernoulli bond percolation. The measurability of `E_L`, left
  implicit in the paper, comes from the step `step:lip-in-A1`: almost surely `E_L` is the event
  that the closed set of `L`-Lipschitz slopes meets `{q ≠ 0}`, which is measurable on the
  corrector-valid event. Conversely, on that event a nonzero `L`-Lipschitz slope gives a
  nonconstant `L`-Lipschitz harmonic function, its corrected plane, by the uniqueness of the slope
  of an element of `A₁`.
* `deterministicSlopeStep`: an almost surely closed random set of slopes with null-measurable
  open hits, invariant under an ergodic map, is almost surely equal to a fixed closed set; the
  paper's translation-invariant selection `p̄` is replaced by any nonzero element of that set.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation LatticeProb.External Rigidity.Section3
  Rigidity.Steps.S3

variable {d : ℕ}

section ErgodicClosedSets

open TopologicalSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]

/-- A random set which is almost surely closed, has null-measurable open hits, and is invariant
under an ergodic map, is almost surely equal to a fixed closed set. -/
theorem exists_isClosed_ae_eq_of_ergodic₀ [SecondCountableTopology X]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} (hErg : Ergodic T μ)
    (F : Ω → Set X) (hclosed : ∀ᵐ ω ∂μ, IsClosed (F ω))
    (hhit : ∀ U : Set X, IsOpen U → NullMeasurableSet {ω | (F ω ∩ U).Nonempty} μ)
    (hcov : ∀ ω, F (T ω) = F ω) :
    ∃ S : Set X, IsClosed S ∧ ∀ᵐ ω ∂μ, F ω = S := by
  classical
  have hbit : ∀ U : countableBasis X, ∃ b : Prop,
      ∀ᵐ ω ∂μ, (F ω ∩ (U : Set X)).Nonempty ↔ b := by
    intro U
    have hinv : T ⁻¹' {ω | (F ω ∩ (U : Set X)).Nonempty} =
        {ω | (F ω ∩ (U : Set X)).Nonempty} := by
      ext ω
      change (F (T ω) ∩ (U : Set X)).Nonempty ↔ (F ω ∩ (U : Set X)).Nonempty
      rw [hcov ω]
    rcases hErg.quasiErgodic.ae_empty_or_univ₀
        (hhit U (isOpen_of_mem_countableBasis U.property)) (by rw [hinv]) with h | h
    · exact ⟨False, h.mono fun ω hω => iff_of_eq hω⟩
    · exact ⟨True, h.mono fun ω hω => iff_of_eq hω⟩
  choose b hb using hbit
  have hcommon : ∀ᵐ ω ∂μ, ∀ U : countableBasis X,
      (F ω ∩ (U : Set X)).Nonempty ↔ b U := ae_all_iff.mpr hb
  obtain ⟨ω₀, hω₀, hclosed₀⟩ := (hcommon.and hclosed).exists
  refine ⟨F ω₀, hclosed₀, (hcommon.and hclosed).mono fun ω hω => ?_⟩
  apply LatticeProb.Prob.isClosed_eq_of_basis_hits (isBasis_countableBasis X) hω.2 hclosed₀
  intro U hU
  exact (hω.1 ⟨U, hU⟩).trans (hω₀ ⟨U, hU⟩).symm

end ErgodicClosedSets

/-- The unit vector `e₁`, a nonzero translation of the lattice. -/
theorem unitVertex_ne_zero [NeZero d] : (Pi.single 0 1 : Vertex d) ≠ 0 := by
  intro h
  have hi := congrFun h 0
  norm_num at hi

/-- On the corrector-valid event, a nonzero `L`-Lipschitz slope gives a nonconstant `L`-Lipschitz
harmonic function: its corrected plane, which is not constant since constants have slope `0` and
the slope of an element of `A₁` is unique. -/
theorem mem_lipschitzHarmonicEvent_of_mem_lipschitzSlopeSet {ω : Configuration d}
    (hω : ω ∈ correctorValidEvent d) {L : ℝ} {q : Fin d → ℝ}
    (hq : q ∈ lipschitzSlopeSet ω L) (hq0 : q ≠ 0) : ω ∈ lipschitzHarmonicEvent d L := by
  obtain ⟨h, hq⟩ := hq
  obtain ⟨o, ho⟩ := (uniqueInfiniteComponent h).nonempty_supp
  obtain ⟨u, hu, _⟩ := (hω.2 h).1 q ⟨o, ho⟩
  refine ⟨h, u, ((isCorrectedPlane_iff_harmonic_and_slope_asymptotics _ q u).mp hu.1).1,
    hq u hu.1, ?_⟩
  by_contra hc
  push Not at hc
  have hconst : u = fun _ => u ⟨o, ho⟩ := funext fun x => hc x _
  have h0 : IsCorrectedPlane (uniqueInfiniteComponent h) 0 u := by
    rw [hconst]
    exact isCorrectedPlane_const _ _
  exact hq0 (((hω.2 h).2 u hu.1.1).unique hu.1 h0)

/-- Step `step:3.1-zero-one`: the event `E_L` has probability `0` or `1`. -/
theorem zeroOneStep (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hA1 : LipschitzMemA1Step d p) : ZeroOneStep d p := by
  intro L
  obtain ⟨G, hG, hmass, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  have hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G := (mem_ae_iff_prob_eq_one hG).mpr hmass
  have hH := measurableSet_lipschitzSlopeSet_hit_open G hG hvalid L
    (isOpen_compl_singleton (x := (0 : Fin d → ℝ)))
  have heq : lipschitzHarmonicEvent d L =ᵐ[latticeBondLaw d p]
      {ω | ω ∈ G ∧ (lipschitzSlopeSet ω L ∩ {0}ᶜ).Nonempty} := by
    filter_upwards [hA1, hGae] with ω hA hω
    refine propext ⟨?_, ?_⟩
    · rintro ⟨h, u, hharm, hlip, hnc⟩
      obtain ⟨q, hq0, hq⟩ := hA h L u hharm hlip hnc
      exact ⟨hω, q, hq, hq0⟩
    · rintro ⟨-, q, hq, hq0⟩
      exact mem_lipschitzHarmonicEvent_of_mem_lipschitzSlopeSet (hvalid hω) hq hq0
  have hnull : NullMeasurableSet (lipschitzHarmonicEvent d L) (latticeBondLaw d p) :=
    hH.nullMeasurableSet.congr heq.symm
  rcases (ergodic_configurationTranslation p unitVertex_ne_zero).quasiErgodic.ae_empty_or_univ₀
      hnull (by rw [preimage_lipschitzHarmonicEvent]) with h | h
  · left
    rw [measure_congr h, measure_empty]
  · right
    exact h.mono fun ω hω => (iff_of_eq hω).mpr (Set.mem_univ ω)

/-- Step `step:3.1-deterministic-slope`: a nonzero slope is almost surely `L`-Lipschitz. -/
theorem deterministicSlopeStep (hclassical : SupercriticalBondUniqueness)
    (hcorrector : SupercriticalBondCorrectorInput) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    DeterministicSlopeStep d p := by
  intro L hclosed hne
  obtain ⟨G, hG, hmass, hvalid⟩ :=
    exists_measurable_corrector_valid_set hclassical hcorrector d hd p hpc hp1
  have hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G := (mem_ae_iff_prob_eq_one hG).mpr hmass
  obtain ⟨S, -, hS⟩ := exists_isClosed_ae_eq_of_ergodic₀
    (ergodic_configurationTranslation p unitVertex_ne_zero) (fun ω => lipschitzSlopeSet ω L)
    hclosed (fun U hU => nullMeasurableSet_lipschitzSlopeSet_hit_open G hG hvalid hGae L hU)
    (fun ω => lipschitzSlopeSet_translation _ ω L)
  obtain ⟨ω₀, ⟨q, hq0, hq⟩, hω₀⟩ := (hne.and hS).exists
  refine ⟨q, hq0, hS.mono fun ω hω => ?_⟩
  rw [hω, ← hω₀]
  exact hq

end Rigidity.Proofs.S3
