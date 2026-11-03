import Rigidity.Proofs.S4.ResistanceRecursion
import Rigidity.Proofs.S4.CorrectedPlaneNonconstant
import Rigidity.Proofs.S4.QuadraticGrowthMeasurable
import Rigidity.Proofs.S4.GadgetEvent
import Rigidity.Proofs.S4.ClosedBoundary
import Rigidity.Proofs.S4.Attach
import Rigidity.Proofs.S4.OuterNonConstant
import Rigidity.Steps.S4.ReducedRationalRecursion
import Rigidity.Steps.S4.ErgodicityLipschitz

/-!
# Section 4: the composed results

The numbered results of Section 4 of the corrected draft, each obtained by composing the
reduction of its carving (`Rigidity.Steps.S4`) with the proved steps (`Rigidity.Proofs.S4`).
The hypotheses are the regime `2 ≤ d`, `p_c(d) < p < 1` and the cited literature inputs used by
the steps:

* `LatticeProb.External.SupercriticalBondUniqueness`: uniqueness of the infinite cluster;
* `LatticeProb.External.SupercriticalBondCorrectorInput`: the first-order correctors of the
  infinite cluster (Armstrong-Dario), with uniqueness of the slope of an element of `A₁(C_∞)`;
* `LatticeProb.External.ArmstrongDarioOrderZero`: the Liouville theorem for sublinear harmonic
  functions on the infinite cluster (Armstrong-Dario, order zero);
* `Rigidity.External.WellConnectedInput`: the well-connected cubes of Antal-Pisztora/Penrose-Pisztora.

* Lemma 4.2 (`effectiveResistanceRecurrence`) and Lemma 4.3 (`reducedRationalRecursion`) are
  deterministic and use no input.
* Lemma 4.7 (`detSlope`) and Lemma 4.9 (`ergodicityLipschitz`, correction C11) are derived from
  the rigidity of integer-valued harmonic functions of linear growth (Theorem 1.2).
* Proposition 4.10 (`rationalMatrix`) is proved by Poincaré recurrence.
* Lemma 4.8 (`nonConstantOnGadget`, draft statement `Rigidity.Section4.NonConstantOnGadgetStmt`:
  Lemma 4.8 as printed, the conditional form) is proved
  by the averaging route of `Rigidity.Proofs.S4.OuterNonConstant` (no
  `Rigidity.Steps.S4.ConditioningStep`).
* The joint form of Lemma 4.8 with the gadget isolated in `H` (`nonConstantOnGadgetJoint`,
  `Rigidity.Steps.S4.NonConstantOnGadgetJointStmt`, exponent `#bondsNear`) is a proved support
  result, composed with the attachment bond sets `Rigidity.Proofs.S4.attachBondSet` and
  translations `Rigidity.Proofs.S4.gadgetShift`.
-/

namespace Rigidity.Assembly

open LatticeProb.Percolation

/-- **Lemma 4.2**: the gadget network of every height `n ≥ 1` carries a unique unit voltage
`h_n`, and the effective resistances `R_n = 1/h_n(a)` satisfy `R_1 = 3` and
`R_{n+1} = (3 R_n + 2)/(R_n + 1)`. -/
theorem effectiveResistanceRecurrence : Section4.EffectiveResistanceRecurrenceStmt :=
  Steps.S4.effectiveResistanceRecurrence_of_steps Proofs.S4.unitVoltageExistsUnique
    Proofs.S4.resistanceBase Proofs.S4.resistanceRecursion

/-- **Lemma 4.3**: the effective resistance of the gadget of height `n ≥ 1` is `A_{n+1}/B_n`,
from Lemma 4.2. -/
theorem reducedRationalRecursion : Section4.ReducedRationalRecursionStmt :=
  Steps.S4.reducedRationalRecursion_of_effectiveResistanceRecurrence effectiveResistanceRecurrence

/-- **Lemma 4.7**: for a deterministic nonzero slope `q`, almost surely some edge of the infinite
cluster carries a non-integer gradient of the corrected plane `ℓ_q`. Composed from the rigidity of
corrected planes with integer gradients (Theorem 1.2) and the step that a corrected plane of
nonzero slope is not constant. -/
theorem detSlope {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Section4.DetSlopeStmt d p :=
  Steps.S4.detSlope_of_steps hd p hpc hp1 hclassical hcorrector
    (Proofs.S4.correctedPlaneNonconstantStep hd p hpc hp1 hcorrector)

/-- **Lemma 4.8, joint form** (`Rigidity.Steps.S4.NonConstantOnGadgetJointStmt`, a proved support
result, not the draft statement): for a deterministic slope `q ≠ 0` there are `c > 0` and `R₀`
such that for `R ≥ R₀` some bond set `H` of `Q_R` contains a translate of the gadget of height `R`
as an induced subgraph, isolated in `H` (inside `Q_{R-1}`, attached at its terminals only), with
`P[𝒞_∞ ∩ Q_R = H] > 0` and
`P[𝒞_∞ ∩ Q_R = H, ℓ_q not constant on the gadget] ≥ c R^{-2d+2} min(p, 1-p)^{#bonds meeting Q_R}`.
Composed from the steps of Lemma 4.8 (event, closed boundary, attachment geometry and Liouville
argument, placement count) and the finite energy step. -/
theorem nonConstantOnGadgetJoint {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hwc : Rigidity.External.WellConnectedInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Steps.S4.NonConstantOnGadgetJointStmt d hd p :=
  Steps.S4.nonConstantOnGadgetJoint_of_attachSteps hd p hpc hp1
    (Proofs.S4.attachBondSet hd) (Proofs.S4.gadgetShift d)
    (Proofs.S4.eventStep hd p hpc hp1 hwc hAD hcorrector)
    (fun _ hq => Proofs.S4.closedBoundaryStep hd p hpc hp1 hq hAD hcorrector)
    (Proofs.S4.attachGeometryStep hd)
    (fun q _ => Proofs.S4.attachStep hd p hpc hp1 q hcorrector hAD)
    Proofs.S4.placementCountStep

/-- **Lemma 4.8** (draft statement `Rigidity.Section4.NonConstantOnGadgetStmt`, Lemma 4.8 as
printed, the conditional form): for a deterministic slope
`q ≠ 0` there are `c > 0` and `R₀` such that for `R ≥ R₀` some bond set `H` of `Q_R` contains a
translate of the gadget of height `R` as an induced subgraph, with `P[𝒞_∞ ∩ Q_R = H] > 0` and
`P[ℓ_q not constant on the gadget | 𝒞_∞ ∩ Q_R = H] ≥ c R^{-2d+2}`. Proved by averaging over `H`
(`Rigidity.Proofs.S4.OuterNonConstant`), with no comparison of the conditional law and the law
with free outside bonds. -/
theorem nonConstantOnGadget {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Section4.NonConstantOnGadgetStmt d hd p :=
  Proofs.S4.OuterNonConstant.nonConstantOnGadget hd p hpc hp1 hAD hcorrector

/-- **Lemma 4.9** (correction C11): if with positive probability the infinite cluster carries a
nonconstant integer-valued harmonic function of linear growth, then for some deterministic slope
`q` with `|q|₁ ≥ 1`, almost surely the cluster carries an integer-valued corrected plane of slope
`q`. Derived from Theorem 1.2: the antecedent is a null event, so the implication holds. -/
theorem ergodicityLipschitz {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Section4.ErgodicityLipschitzStmt d p :=
  Steps.S4.ergodicityLipschitz_of_integerValuedLinearGrowth hd p hpc hp1 hclassical hcorrector

/-- **Proposition 4.10**: almost surely the infinite cluster carries no nonconstant
integer-valued harmonic function within `o(|x|)` of a given harmonic quadratic. Composed by
Poincaré recurrence from the measurability of the quadratic growth event and the translate
difference step. -/
theorem rationalMatrix {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Section4.RationalMatrixStmt d p :=
  Steps.S4.rationalMatrix_of_recurrence hd p hpc hp1 hclassical hcorrector
    (Proofs.S4.quadraticGrowthEventMeasurable hd p hpc hp1 hclassical hcorrector)
    (Proofs.S4.translateDifference hd p hpc hp1 hcorrector)

end Rigidity.Assembly
