import Rigidity.Proofs.Assembly.PlanarDensity
import Rigidity.Proofs.S2.PlanarDensityConcentration

/-!
# Fast decay with planar density concentration

The planar well-connectedness and density concentration estimates, as well as sphere
separation, are supplied by their proofs.
-/

namespace Rigidity.Assembly.WithPlanarDensity

open LatticeProb.Percolation Rigidity.Section5

/-- Theorem 1.3 with planar connectivity and density concentration supplied. -/
theorem fast_decay_of_planar_density (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOriginTwo)
    (hE : Rigidity.External.SupercriticalBondGreenColumnExistenceTwo)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) : FastDecayStmt p :=
  fast_decay_of_planar_connectivity p hpc hp1 hCorr hCQ hAD hAD1 hE hGQ
    Rigidity.Proofs.S2.planar_cluster_density_concentration

end Rigidity.Assembly.WithPlanarDensity
