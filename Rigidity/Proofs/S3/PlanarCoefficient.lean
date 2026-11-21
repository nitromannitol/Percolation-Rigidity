import Rigidity.Proofs.S3.PlanarEdgeField

/-!
# The planar homogenized coefficient

The mean corrected-plane edge gradient is positive under the planar corrector estimates.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation LatticeProb.External
  Rigidity.Section3 Rigidity.Steps.S3
open scoped BigOperators Classical ENNReal

namespace Rigidity.Proofs.S3

open FluxEvent HomogenizedCoefficient

/-- Positivity of the mean corrected-plane edge gradient in dimension two. -/
def HomogenizedCoefficientProposedTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ abar > 0, ∀ X : Configuration 2 → ℝ,
      (∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (h : HasUniqueInfiniteOpenComponent ω) u,
        IsCorrectedPlane (uniqueInfiniteComponent h) (slopeE1 2) u →
        X ω = edgeDifference (uniqueInfiniteComponent h) u (unit 0) 0) →
      Integrable X (latticeBondLaw 2 p) ∧ ∫ ω, X ω ∂latticeBondLaw 2 p = abar

/-- The planar homogenized coefficient is positive. -/
theorem homogenizedCoefficient_two (hU : SupercriticalBondUniqueness)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hQ : Rigidity.External.CorrectorQuantitativeInputTwo) :
    HomogenizedCoefficientProposedTwo := by
  intro p hpc hp1
  set μ := latticeBondLaw 2 p
  obtain ⟨G, hG, hG1, Φ, hΦm, hex, hΦ⟩ := exists_edgeField_two hU hCorr p hpc hp1
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := mem_ae_iff.2 ((prob_compl_eq_zero_iff hG).2 hG1)
  have hall : ∀ᵐ ω ∂μ, ∀ z, configurationTranslation z ω ∈ G :=
    ae_all_iff.2 fun z =>
      (measurePreserving_configurationTranslation p z).quasiMeasurePreserving.ae hGae
  have hXi := fun k => integrable_edgeField_unit_two hQ p hpc hp1 hGae hΦm hex hΦ k
  have hge := integral_ge_energy (boxEnergyInequality 2) p hall hΦm hex hΦ hXi zero_le_one
  have iMin : ∀ k, Integrable (fun ω => min (Φ (unit k) 0 ω ^ 2) 1) μ := fun k =>
    (integrable_const (1 : ℝ)).mono'
      ((((hΦm _ _).pow_const 2).min measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg _) zero_le_one)]
        exact min_le_right _ _)
  have hnn : ∀ k, 0 ≤ ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ := fun k =>
    integral_nonneg fun ω => le_min (sq_nonneg _) zero_le_one
  have hpos : 0 < ∑ k, ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ := by
    by_contra hle
    rw [not_lt] at hle
    apply not_forall_ae_eq_zero p hGae hall hex hΦ
    intro k
    have h0 : ∫ ω, min (Φ (unit k) 0 ω ^ 2) 1 ∂μ = 0 := le_antisymm
      ((Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k)).trans hle) (hnn k)
    rw [integral_eq_zero_iff_of_nonneg (fun ω => le_min (sq_nonneg _) zero_le_one) (iMin k)]
      at h0
    filter_upwards [h0] with ω hω
    by_contra hne
    have h1 : 0 < Φ (unit k) 0 ω ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
    exact (lt_min h1 one_pos).ne' hω
  refine ⟨∫ ω, Φ (unit 0) 0 ω ∂μ, hpos.trans_le hge, fun X hX => ?_⟩
  have hXeq : X =ᵐ[μ] Φ (unit 0) 0 := by
    filter_upwards [hGae, hX] with ω hω hXω
    obtain ⟨h, hexu⟩ := hex ω hω
    obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
    rw [hXω h u hu]
    exact hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu _ _
  exact ⟨(hXi 0).congr hXeq.symm, integral_congr_ae hXeq⟩

end Rigidity.Proofs.S3
