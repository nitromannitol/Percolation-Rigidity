import Rigidity.External.PlanarInputs
import Rigidity.Proofs.S3.FlipCorrector

/-!
# Planar corrected planes after closing finitely many bonds

The finite-modification argument needs only the planar qualitative corrector input.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

/-- Closing finitely many bonds preserves the planar corrector existence event almost surely. -/
theorem flipCorrectorStep_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcorr : Rigidity.External.SupercriticalBondCorrectorInputTwo) : FlipCorrectorStep 2 p := by
  obtain ⟨A, hAae, hAmeas, hA⟩ := (hcorr p hpc hp1).exists_measurable_mem
  have hA1 : latticeBondLaw 2 p A = 1 := (prob_compl_eq_zero_iff hAmeas).1 (mem_ae_iff.1 hAae)
  have hT := finite_flip_full_measure 2 (latticeBondLaw 2 p) p
    ((criticalProbability_nonneg 2).trans_lt hpc) hp1 (latticeBondLaw_iIndepFun p)
    (latticeBondLaw_map_eval p) hAmeas hA1
  have hTae := (ae_iff_measure_eq
    (RigidityFullProduct.bond_all_masks_measurable 2 hAmeas).nullMeasurableSet).2
    (hT.trans measure_univ.symm)
  filter_upwards [hTae] with ω hω
  intro B h' q o
  have hfin : Set.Finite {e | (decide (e ∈ B) && ω e) = true} :=
    B.finite_toSet.subset fun e he => by
      simp only [Set.mem_setOf_eq, Bool.and_eq_true, decide_eq_true_eq] at he
      exact he.1
  have hmem := hω _ hfin
  rw [← closeBonds_eq_maskFlip] at hmem
  exact (hA _ hmem h').1 q o

end Rigidity.Proofs.S3
