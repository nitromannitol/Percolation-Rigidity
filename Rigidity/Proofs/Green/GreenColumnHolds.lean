import Rigidity.Proofs.Green.SupercriticalGreenColumn
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds

/-!
# The Green-column input in every dimension

Dario and Gu (*Quantitative homogenization of the parabolic and elliptic Green's functions on
percolation clusters*, Ann. Probab. 49 (2021), arXiv:1909.10439v4) state the existence and
uniqueness of the Green's function of the infinite cluster without proof (the definitions around
(1.8), p. 4, and p. 58). The input `LatticeProb.External.SupercriticalBondGreenColumnExistence`
records it for every dimension `d ≥ 2`, and it is proved here with no hypothesis: for `d ≥ 3` by
`greenColumnExistence_of_three_le` (isoperimetry of the cluster, Faber–Krahn, Nash and the
on-diagonal decay of the heat kernel), and for `d = 2` by the planar statement
`Rigidity.Proofs.Regularity.supercriticalBondGreenColumnExistenceTwo_holds`, which follows from the
planar corrector input, itself proved.
-/

namespace Rigidity.Green

/-- **The Green-column input**, with no hypothesis: for `d ≥ 2`, `p_c(d) < p < 1` and each pole
`y`, almost surely, if `y` lies in the infinite cluster, the cluster has exactly one Green column
with pole `y`. -/
theorem supercriticalBondGreenColumnExistence_holds :
    LatticeProb.External.SupercriticalBondGreenColumnExistence :=
  supercriticalBondGreenColumnExistence_of_two
    Rigidity.Proofs.Regularity.supercriticalBondGreenColumnExistenceTwo_holds

end Rigidity.Green
