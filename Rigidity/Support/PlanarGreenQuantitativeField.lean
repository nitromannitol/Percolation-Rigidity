import Rigidity.External.PlanarInputs
import LatticeProb.Prob.Percolation.GreenQuantitativeField

/-!
# Planar quantitative Green field

The planar Green input supplies a simultaneous measurable field of comparison scales.
-/

namespace Rigidity.Support

open MeasureTheory LatticeProb.Percolation
open scoped ENNReal

/-- The planar quantitative Green estimates hold simultaneously at every pole. -/
theorem exists_green_quantitative_field_two
    (input : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ K : Vertex 2 → Configuration 2 → ℝ,
      (∀ y, Measurable (K y)) ∧
      ∀ η : ℝ, 0 < η → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧
        ∃ M : Vertex 2 → Configuration 2 → ℝ,
          (∀ y, Measurable (M y)) ∧ (∀ y ω, 0 ≤ M y ω) ∧
          (∀ (y : Vertex 2) (R : ℝ), 0 ≤ R →
            latticeBondLaw 2 p {ω | R ≤ M y ω} ≤
              ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) ∧
          ∀ᵐ ω ∂latticeBondLaw 2 p,
            ∀ y : Vertex 2, ∀ h : HasUniqueInfiniteOpenComponent ω,
              ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
                ∀ g : uniqueInfiniteComponent h → ℝ,
                  IsGreenColumn 2 le_rfl (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
                  ∀ x : uniqueInfiniteComponent h,
                    ∀ z : {v : EuclideanSpace ℝ (Fin 2) // v ≠ 0},
                      z.val = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y →
                      M y ω ≤ ‖z.val‖ →
                      |g x - continuumGreen 2 le_rfl ⟨κ, hκ⟩ z - K y ω| ≤
                        C * Real.rpow ‖z.val‖ (1 - (2 : ℝ) + η) := by
  obtain ⟨κ, hκ, K, hK, hbound⟩ := input p hp hp1
  refine ⟨κ, hκ, K, hK, fun η hη => ?_⟩
  obtain ⟨C, s, hC, hs, hper⟩ := hbound η hη
  choose M hM hn ht he using fun y => (hper y).2
  refine ⟨C, s, hC, hs, M, hM, hn, ht, ?_⟩
  filter_upwards [ae_all_iff.mpr he] with ω hω
  intro y h hy g hg x z hz hthreshold
  have h := (hω y h hy g hg).2 x z hz hthreshold
  have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
  have heq : C / Real.rpow ‖z.val‖ (1 - η) =
      C * Real.rpow ‖z.val‖ (1 - (2 : ℝ) + η) := by
    change C / (‖z.val‖ ^ (1 - η)) = C * (‖z.val‖ ^ (1 - (2 : ℝ) + η))
    rw [show 1 - (2 : ℝ) + η = -(1 - η) by ring, Real.rpow_neg hr.le]
    ring
  rwa [← heq]

end Rigidity.Support
