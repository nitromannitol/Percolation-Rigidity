/- Adapted from Lattice-Probability, revision 7512f4fb, module
   LatticeProb.Prob.Percolation.MeasurableRootedPlane (`exists_measurable_corrector_valid_set`).
   Changes: specialized to d = 2, from the planar input `SupercriticalBondCorrectorInputTwo` in
   place of `SupercriticalBondCorrectorInput`; the theorem carries the suffix `_two`. -/
import Rigidity.External.PlanarInputs
import LatticeProb.Prob.Percolation.MeasurableRootedPlane

/-!
# A measurable planar corrector validity event

Uniqueness and the planar qualitative corrector input provide a measurable conull subset of
the genuine validity event.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation

/-- A conull measurable subset of the planar corrector validity event. -/
theorem exists_measurable_corrector_valid_set_two
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : Rigidity.External.SupercriticalBondCorrectorInputTwo) (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration 2), MeasurableSet G ∧ latticeBondLaw 2 p G = 1 ∧
      G ⊆ correctorValidEvent 2 := by
  have hcluster : ∀ᵐ ω ∂latticeBondLaw 2 p, HasUniqueInfiniteOpenComponent ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent 2)).mpr
      (hclassical.2 2 le_rfl p hpc hp1)
  have hae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ correctorValidEvent 2 :=
    hcluster.and (hcorrector p hpc hp1)
  have heq : (Set.univ : Set (Configuration 2)) =ᵐ[latticeBondLaw 2 p]
      correctorValidEvent 2 := by
    filter_upwards [hae] with ω hω
    exact propext ⟨fun _ => hω, fun _ => Set.mem_univ ω⟩
  have hnull : NullMeasurableSet (correctorValidEvent 2) (latticeBondLaw 2 p) :=
    MeasurableSet.univ.nullMeasurableSet.congr heq
  obtain ⟨G, hsub, hG, heqG⟩ := hnull.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G := by
    filter_upwards [hae, heqG] with ω hω heqω
    exact heqω.mpr hω
  exact ⟨G, hG, (mem_ae_iff_prob_eq_one hG).mp hGae, hsub⟩

end Rigidity.Proofs.S3
