import Rigidity.Proofs.Assembly.PlanarInputs
import Rigidity.Proofs.Section5.PlanarGreenExistence

/-!
# Fast decay without the Green-column existence input

Planar Green columns exist almost surely (`Rigidity.Proofs.Section5.planar_greenColumn_exists`),
and the order-zero estimate makes them unique. Theorem 1.3 therefore follows from the planar
qualitative and quantitative corrector estimates, the planar order-zero and order-one regularity
estimates, and the planar quantitative Green estimate.
-/

namespace Rigidity.Assembly.WithPlanarInputs

open LatticeProb.Percolation Rigidity.Section5

/-- Planar existence and uniqueness of Green columns, from the planar order-zero estimate. -/
theorem supercriticalBondGreenColumnExistenceTwo_of_orderZero
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo) :
    Rigidity.External.SupercriticalBondGreenColumnExistenceTwo :=
  Proofs.Section5.greenColumnExistenceTwo_of_exists hAD Proofs.Section5.planar_greenColumn_exists

/-- Theorem 1.3 from the planar corrector, regularity and quantitative Green estimates. -/
theorem fast_decay_of_planar_estimates (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo)
    (hCQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (hAD : Rigidity.External.ArmstrongDarioOrderZeroTwo)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOriginTwo)
    (hGQ : Rigidity.External.SupercriticalBondGreenQuantitativeTwo) : FastDecayStmt p :=
  fast_decay_of_green_exists p hpc hp1 hCorr hCQ hAD hAD1
    Proofs.Section5.planar_greenColumn_exists hGQ

end Rigidity.Assembly.WithPlanarInputs
