import Rigidity.Steps.S3.CompareDifferentPlanes
import Rigidity.Frozen.FiniteFlipFullMeasureV1

/-!
# Lemma 3.3: corrected planes after closing finitely many bonds

Step `step:3.3-flip-corrector` of Lemma 3.3 (paper L888-893 of the corrected draft). The cited
qualitative corrector input `LatticeProb.External.SupercriticalBondCorrectorInput` holds on a
measurable event `A` of full measure. By Lemma 2.1 (`Rigidity.finite_flip_full_measure`), almost
surely every finite mask flip of the configuration lies in `A`. Closing the bonds of a finite set
`B` is the mask flip of the open bonds of `B`, so the corrector input applies to the configuration
in which the bonds of `B` are closed: every slope has a unique corrected plane on its unique
infinite cluster normalized at any of its vertices.
-/

namespace Rigidity.Proofs.S3

open MeasureTheory LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3

variable {d : ℕ}

/-- Closing the bonds of `B` flips exactly the open bonds of `B`. -/
theorem closeBonds_eq_maskFlip (B : Finset (Bond d)) (ω : Configuration d) :
    closeBonds B ω = RigidityFullProduct.maskFlip (fun e => decide (e ∈ B) && ω e) ω := by
  funext e
  by_cases he : e ∈ B <;> cases hω : ω e <;>
    simp [closeBonds, RigidityFullProduct.maskFlip, he, hω]

/-- Step `step:3.3-flip-corrector`: almost surely, after closing any finite set of bonds, every
slope has a unique corrected plane on the unique infinite cluster normalized at any of its
vertices. -/
theorem flipCorrectorStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    FlipCorrectorStep d p := by
  obtain ⟨A, hAae, hAmeas, hA⟩ := (hcorr d hd p hpc hp1).exists_measurable_mem
  have hA1 : latticeBondLaw d p A = 1 := (prob_compl_eq_zero_iff hAmeas).1 (mem_ae_iff.1 hAae)
  have hT := finite_flip_full_measure d (latticeBondLaw d p) p
    ((criticalProbability_nonneg d).trans_lt hpc) hp1 (latticeBondLaw_iIndepFun p)
    (latticeBondLaw_map_eval p) hAmeas hA1
  have hTae := (ae_iff_measure_eq
    (RigidityFullProduct.bond_all_masks_measurable d hAmeas).nullMeasurableSet).2
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
