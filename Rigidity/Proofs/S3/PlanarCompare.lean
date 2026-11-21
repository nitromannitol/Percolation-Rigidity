import Rigidity.Steps.S3.PlanarCompareDifferentPlanes
import Rigidity.Proofs.S3.PlanarNotLipschitz
import Rigidity.Proofs.Section5.PlanarLiteratureAdapters

/-!
# Planar corrected-plane comparison from planar inputs

The comparison lemma follows from the planar qualitative corrector, Green-column and
order-zero regularity inputs.
-/

namespace Rigidity.Proofs.S3

open LatticeProb.Percolation Rigidity.Steps.S3

/-- Lemma 3.3 from planar qualitative inputs. -/
theorem compareDifferentPlanes_two (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo) :
    Rigidity.Section3.CompareDifferentPlanesStmt 2 le_rfl p :=
  compareDifferentPlanes_of_green_event_two p hpc hp1 hCorr
    (ae_unique_green_column_for_all_poles_two hE hUq p hpc hp1)
    flipClusterStep (flipCorrectorStep_two p hpc hp1 hCorr)
    (greenLaplacianStep le_rfl) (greenColumnSublinearStep le_rfl)
    (Rigidity.Proofs.Section5.sublinearLiouvilleStep_two p hpc hp1 hAD)

end Rigidity.Proofs.S3
