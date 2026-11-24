import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorSupNorm
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectedPlaneExistence

/-!
# The corrected planes of the planar cluster from the quantitative sublinearity in `L²`

`planarCorrectedPlaneExistenceTwo_of_sublinearL2` proves `PlanarCorrectedPlaneExistenceTwo` (every
slope has a corrected plane, sublinear in the uniform norm) from (1.18)
(`PlanarCorrectorSublinearL2Two`), the order-zero regularity of Theorem 2 (iii)
(`ArmstrongDarioOrderZeroTwo`) and the minimal scales of Proposition 2.4
(`PlanarMinimalScalesTwo`), by the argument of the Remark after (1.19) of Armstrong and Dario
(arXiv:1609.09431v2):

* the Lipschitz estimate at every centre (`exists_planar_all_centres_constant_approximation`) with
  the maximum of its minimal scales over the boxes (`ae_eventually_scale_le_three`) bounds the
  increments of the corrector;
* the uniform bound at each triadic scale (`abs_corrector_le_at_scale`), from the comparison with
  the coarsening and the interpolation inequality, gives the bound of (1.22) above an almost surely
  finite scale;
* `componentSlopeAsymptotics_of_scales` turns it into the slope asymptotics.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory Filter LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2

/-- **The planar corrector input** (R2) from (1.18), the order-zero regularity, the minimal scales
of Proposition 2.4 and the bound `dim 𝒜_1 ≤ 3` of Theorem 2 (i). -/
theorem supercriticalBondCorrectorInputTwo_of_sublinearL2 (h118 : PlanarCorrectorSublinearL2Two)
    (hR3 : ArmstrongDarioOrderZeroTwo)
    (hM5 : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      PlanarMinimalScalesTwo p)
    (hdim : PlanarOrderOneDimensionTwo) : SupercriticalBondCorrectorInputTwo :=
  supercriticalBondCorrectorInputTwo_of_orderOne hR3
    (planarCorrectedPlaneExistenceTwo_of_sublinearL2 h118 hR3 hM5) hdim

end Rigidity.Proofs.Regularity
