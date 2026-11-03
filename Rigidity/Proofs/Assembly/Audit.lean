import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section4
import Rigidity.Proofs.Assembly.Section5
import Rigidity.Proofs.Assembly.Section5b
import Rigidity.Proofs.Assembly.Section5Decay
import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Assembly.Section5e
import Rigidity.Proofs.Assembly.Section5f
import Rigidity.Proofs.Assembly.Section5GeneralSlope
import Rigidity.Proofs.Assembly.Section6
import Rigidity.Proofs.S2.ArmstrongDarioTranslation
import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.S3.HomogenizedCoefficient

/-!
# Fidelity audit of the assembled theorems

For each numbered result assembled in `Rigidity/Proofs/Assembly/*.lean`, an `example` whose type
is written by hand from the draft (`Rigidity/Draft/*.lean`, with the corrections C26-C35): the
draft statement, the regime of the paper
(`2 ≤ d`, `p_c(d) < p < 1`; `d = 2` in Section 5) and the cited literature inputs, i.e. the
Props of `Rigidity/External` and `LatticeProb/External`. The proof of each example is the
assembled theorem applied. External inputs are listed in one fixed order, independent of the
order in the assembled signatures: `SupercriticalBondUniqueness`,
`SupercriticalBondCorrectorInput`, `SupercriticalBondGreenQuantitative`,
`SupercriticalBondGreenColumnExistence`, `ArmstrongDarioOrderZero` (`LatticeProb.External`), then
`CorrectorQuantitativeInput`, `ArmstrongDarioOrderOneOrigin`, `ClusterDensityConcentrationInput`,
`WellConnectedInput`, `KestenRectangleCrossing`, `JordanCurveTheoremSphere`,
`MicciancioRegevSmoothing` (`Rigidity.External`).

No example takes a locally stated input as a hypothesis. The three inputs stated in
`Rigidity/Proofs` are derived inside the proofs:
`Proofs.S2.ArmstrongDarioOrderOneProposed` by `armstrongDarioOrderOneProposed_of_origin`
([C34]), `Proofs.S2.ClusterDensityInputProposed` by
`clusterDensityInputProposed_of_concentration` ([C35]) and
`Proofs.S3.HomogenizedCoefficientProposed` (the positivity of the homogenized coefficient) by
`homogenizedCoefficientProposed`.

Every example concludes the draft statement by name. Lemma 4.8 is stated as printed (the
conditional form). The statements that differ from the printed ones: Prop 3.2 (inner-measure
form), Props 5.7 and 5.11 (every slope `q ≠ 0` [C30]; 5.11 eventually in `k`, [C29]), Lemmas
5.25 and 5.27 (universal `G₁`, direction-free `G₃`, [C31] [C32]), Lemma 5.28 (any edge
`(x₀, x₁)` of `𝒞_∞`, [C32]), Lemma 5.26
(`NullMeasurableSet`, all parameters), Theorem 6.5 (the restriction event).

A hypothesis that is neither a regime condition nor an External Prop is marked `FLAG` on its
line, and a conclusion that is not the draft statement is marked `VARIANT`. Two examples carry
them, each in addition to the draft-form example of the same result: the reduction of Prop 5.3 to
the draft Props 5.7 and 5.8 (`FLAG`, kept as documentation), and Lemma 5.25 as printed
(`VARIANT`, the directional third good event).
-/

namespace Rigidity.Audit

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section5

/-! ## Section 2 -/

-- Lemma 2.16 (`Assembly.jordanCurves`): deterministic, no regime.
example (hJ : Rigidity.External.JordanCurveTheoremSphere) : Rigidity.Section2.JordanCurvesStmt :=
  Assembly.jordanCurves hJ

-- Proposition 2.6 (`Assembly.greenGradientHomogenization`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hADO : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hDGC : Rigidity.External.ClusterDensityConcentrationInput)
    : Rigidity.Section2.GreenGradientHomogenizationStmt d hd p :=
  Assembly.greenGradientHomogenization hd hpc hp1 hGQ hCQ hCorr
    (Proofs.S2.armstrongDarioOrderOneProposed_of_origin hADO hCorr)
    (Proofs.S2.clusterDensityInputProposed_of_concentration hDGC)

/-! ## Section 3 -/

-- Lemma 3.1 (`Assembly.reductionToSlopeE1`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hWC : Rigidity.External.WellConnectedInput) :
    Rigidity.Section3.ReductionToSlopeE1Stmt d p :=
  Assembly.reductionToSlopeE1 hd p hpc hp1 hUq hCorr hWC

-- Lemma 3.3 (`Assembly.compareDifferentPlanes`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero) :
    Rigidity.Section3.CompareDifferentPlanesStmt d hd p :=
  Assembly.compareDifferentPlanes hd p hpc hp1 hUq hCorr hGCE hAD0

-- Proposition 3.2 (`Assembly.notLipschitz`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput)
    : Rigidity.Section3.NotLipschitzStmt d p :=
  Assembly.notLipschitz hd p hpc hp1 hUq hCorr hCQ hAD0 hGCE hGQ hWC
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

-- Theorem 1.1 (`Assembly.lipschitz`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput)
    : Rigidity.Section3.LipschitzStmt d p :=
  Assembly.lipschitz hd p hpc hp1 hUq hCorr hCQ hAD0 hGCE hGQ hWC
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

/-! ## Section 4 -/

-- Lemma 4.2 (`Assembly.effectiveResistanceRecurrence`): deterministic.
example : Rigidity.Section4.EffectiveResistanceRecurrenceStmt :=
  Assembly.effectiveResistanceRecurrence

-- Lemma 4.3 (`Assembly.reducedRationalRecursion`): deterministic.
example : Rigidity.Section4.ReducedRationalRecursionStmt :=
  Assembly.reducedRationalRecursion

-- Lemma 4.7 (`Assembly.detSlope`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Rigidity.Section4.DetSlopeStmt d p :=
  Assembly.detSlope hd p hpc hp1 hUq hCorr

-- Lemma 4.8 (`Assembly.nonConstantOnGadget`; as printed, the conditional form).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero) :
    Rigidity.Section4.NonConstantOnGadgetStmt d hd p :=
  Assembly.nonConstantOnGadget hd p hpc hp1 hAD0 hCorr

-- Lemma 4.9 (`Assembly.ergodicityLipschitz`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Rigidity.Section4.ErgodicityLipschitzStmt d p :=
  Assembly.ergodicityLipschitz hd p hpc hp1 hUq hCorr

-- Proposition 4.10 (`Assembly.rationalMatrix`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Rigidity.Section4.RationalMatrixStmt d p :=
  Assembly.rationalMatrix hd p hpc hp1 hUq hCorr

/-! ## Section 6 -/

-- Theorem 6.5 (`Assembly.slowMixing`).
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hWC : Rigidity.External.WellConnectedInput)
    (hMR : Rigidity.External.MicciancioRegevSmoothing) :
    Rigidity.Section6.SlowMixingStmt d p :=
  Assembly.slowMixing hd p hpc hp1 hUq hWC hMR

/-! ## Section 5 (`d = 2`): Sections 5.1-5.4 -/

-- Proposition 5.5 (`Assembly.logGrowth`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) :
    LogGrowthStmt p f :=
  Assembly.logGrowth hUq hGQ hpc hp1 f

-- Lemma 5.6 (`Assembly.meanZeroRepresentation`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hWC : Rigidity.External.WellConnectedInput) :
    MeanZeroRepresentationStmt p f :=
  Assembly.meanZeroRepresentation hUq hWC hpc hp1 f

-- Proposition 5.12 (`Assembly.infiniteDisjointPaths`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    InfiniteDisjointPathsStmt p f :=
  Assembly.infiniteDisjointPaths hUq hKes hJ hpc hp1 f

-- Lemma 5.14 (`Assembly.loopsAroundAnnuli`).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hKes : Rigidity.External.KestenRectangleCrossing) :
    LoopsAroundAnnuliStmt p :=
  Assembly.loopsAroundAnnuli hUq hKes hpc hp1

-- Lemma 5.16 (`Assembly.strongMaxPrinciple`).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness) :
    StrongMaxPrincipleStmt p :=
  Assembly.strongMaxPrinciple hUq hpc hp1

-- Lemma 5.17 (`Assembly.polesSuperLevelSets`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness) :
    PolesSuperLevelSetsStmt p f :=
  Assembly.polesSuperLevelSets hUq hpc hp1 f

-- Lemma 5.18 (`Assembly.longNonzeroPaths`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness) :
    LongNonzeroPathsStmt p f :=
  Assembly.longNonzeroPaths hUq hpc hp1 f

-- Lemma 5.19 (`Assembly.noThickPaths`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    NoThickPathsStmt p f :=
  Assembly.noThickPaths hUq hKes hJ hpc hp1 f

-- Proposition 5.20 (`Assembly.boundarySize`, Section5d.lean).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    BoundarySizeStmt p f :=
  Assembly.boundarySize hUq hKes hJ hpc hp1 f

/-! ## Section 5.5 -/

-- Proposition 5.21 (`Assembly.disjointPathsToInfinity`).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing) :
    DisjointPathsToInfinityStmt p :=
  Assembly.disjointPathsToInfinity hWC hKes hpc hp1

-- Proposition 5.24 (`Assembly.longPathRenormalized`); the assembled theorem does not use `p < 1`.
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (_hp1 : (p : ℝ) < 1)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing) :
    LongPathRenormalizedStmt p :=
  Assembly.longPathRenormalized hWC hKes hpc

-- Lemma 5.25 (`Assembly.goodEventLowerBound`, Section5d.lean; universal `G₁`, direction-free `G₃`,
-- [C31] [C32]).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput) :
    GoodEventLowerBoundStmt p :=
  Assembly.goodEventLowerBound hCQ hUq hCorr hAD0 hGCE hGQ hWC
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ) hpc hp1

-- Lemma 5.25 as printed (`Assembly.goodEventLowerBoundDirectional`, Section5f.lean). VARIANT: the
-- printed third good event in place of the direction-free one of [C32]: the type is
-- `GoodEventLowerBoundStmt` with `eventG` unfolded and `eventG3` replaced by the printed third
-- good event, which asks that the edge `(x, x + e₁)` lie in `𝒞_∞` with `ℓ(x + e₁) - ℓ(x) ≥ C_χ`
-- for every corrected plane `ℓ` of slope `e₁`. The first good event is the universal one of [C31]
-- (the printed one is existential); the second and `LongPathBound` are those of the draft. The
-- draft keeps the direction-free third good event of [C32].
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput) :
    ∀ Cχ : ℝ, 1 ≤ Cχ → ∃ c : ℝ, 0 < c ∧ ∀ (Cf : ℕ) (R c₁ : ℝ), LongPathBound p Cf R c₁ →
      ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∀ x : Vertex 2,
        ∃ A ⊆ eventG1 Cf R c₁ x K ∩ eventG2 x K ∩
            {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
              ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
              ∃ hx' : x + e1 ∈ (uniqueInfiniteComponent h).supp,
                (componentGraph _).Adj ⟨x, hx⟩ ⟨x + e1, hx'⟩ ∧
                ∀ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ →
                  Cχ ≤ ℓ ⟨x + e1, hx'⟩ - ℓ ⟨x, hx⟩},
          MeasurableSet A ∧ ENNReal.ofReal c ≤ latticeBondLaw 2 p A := -- VARIANT: 5.25 as printed
  Assembly.goodEventLowerBoundDirectional p hpc hp1 hUq hCorr hCQ hAD0 hGCE hGQ hWC

-- Lemma 5.27 (`Assembly.largeGradientSensitive`, Section5Decay.lean; through the corrected good
-- event, universal `G₁` and direction-free `G₃`, [C31] [C32]).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    LargeGradientSensitiveStmt p f :=
  Assembly.largeGradientSensitive hUq hGQ hGCE hAD0 hCorr hCQ hWC hKes hJ
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ) hpc hp1 f

-- Lemma 5.28 (`Assembly.finiteBranches`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    FiniteBranchesStmt p f :=
  Assembly.finiteBranches hUq hKes hJ hpc hp1 f

/-! ## Section 5: Propositions 5.11, 5.7, 5.8, 5.3, Theorems 5.1 and 1.3 -/

-- Proposition 5.11 (`Assembly.levelSetDensity`, Section5GeneralSlope.lean; [C29] [C30]:
-- eventually in `k`, every slope `q ≠ 0`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    LevelSetDensityStmt p f :=
  Assembly.levelSetDensity p hpc hp1 f hUq hCorr hCQ hAD0 hGCE hGQ hWC hKes hJ
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

-- Proposition 5.7 (`Assembly.gradientTrichotomy`, Section5GeneralSlope.lean; every slope
-- `q ≠ 0` [C30]).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    GradientTrichotomyStmt p f :=
  Assembly.gradientTrichotomy p hpc hp1 f hUq hCorr hCQ hAD0 hGCE hGQ hWC hKes hJ
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

-- Proposition 5.8 (`Assembly.twoScaleExpansion`, Section5d.lean).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hADO : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hDGC : Rigidity.External.ClusterDensityConcentrationInput)
    (hWC : Rigidity.External.WellConnectedInput)
    : TwoScaleExpansionStmt p f :=
  Assembly.twoScaleExpansion hUq hWC hGQ hCQ hCorr
    (Proofs.S2.armstrongDarioOrderOneProposed_of_origin hADO hCorr)
    (Proofs.S2.clusterDensityInputProposed_of_concentration hDGC) hpc hp1 f

-- Proposition 5.3 from the draft Propositions 5.7 and 5.8 (`Assembly.fastDecayPotential_of_e1`,
-- a reduction: Proposition 5.7 is used at `q = e₁` only). The hypothesis `CorrectedPlanesExist p`
-- is not an External Prop; `correctedPlanesExist_of_input` derives it from
-- `SupercriticalBondCorrectorInput` in the regime. Kept as documentation.
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (h57 : GradientTrichotomyStmt p f) -- FLAG: draft statement (Prop 5.7) as a hypothesis
    (h58 : TwoScaleExpansionStmt p f) -- FLAG: draft statement (Prop 5.8) as a hypothesis
    (hplanes : Rigidity.Steps.Section5.CorrectedPlanesExist p) -- FLAG: not an External Prop
    : FastDecayPotentialStmt p f :=
  Assembly.fastDecayPotential_of_e1 (fun hf => h57 hf _ (Pi.single_ne_zero_iff.2 one_ne_zero))
    h58 hplanes

-- Proposition 5.3 (`Assembly.fastDecayPotential`).
example (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hADO : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hDGC : Rigidity.External.ClusterDensityConcentrationInput)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    : FastDecayPotentialStmt p f :=
  Assembly.fastDecayPotential hUq hGQ hGCE hAD0 hCorr hCQ hWC hKes hJ
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    (Proofs.S2.armstrongDarioOrderOneProposed_of_origin hADO hCorr)
    (Proofs.S2.clusterDensityInputProposed_of_concentration hDGC) hpc hp1 f

-- Theorem 5.1 (`Assembly.fastDecayDichotomy`).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hADO : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hDGC : Rigidity.External.ClusterDensityConcentrationInput)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    : FastDecayDichotomyStmt p :=
  Assembly.fastDecayDichotomy hUq hGQ hGCE hAD0 hCorr hCQ hWC hKes hJ
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    (Proofs.S2.armstrongDarioOrderOneProposed_of_origin hADO hCorr)
    (Proofs.S2.clusterDensityInputProposed_of_concentration hDGC) hpc hp1

-- Theorem 1.3 (`Assembly.fastDecay`).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hGCE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hAD0 : LatticeProb.External.ArmstrongDarioOrderZero)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hADO : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hDGC : Rigidity.External.ClusterDensityConcentrationInput)
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere)
    : FastDecayStmt p :=
  Assembly.fastDecay hUq hGQ hGCE hAD0 hCorr hCQ hWC hKes hJ
    (Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    (Proofs.S2.armstrongDarioOrderOneProposed_of_origin hADO hCorr)
    (Proofs.S2.clusterDensityInputProposed_of_concentration hDGC) hpc hp1

/-! ## Section 5: Lemmas 5.23 and 5.26 (`Section5e.lean`, `Section5d.lean`) -/

-- Lemma 5.23 (`Assembly.renormalizedDomination`, Section5e.lean). Regime `p_c(2) < p` only.
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ))
    (hWC : Rigidity.External.WellConnectedInput)
    (hKes : Rigidity.External.KestenRectangleCrossing)
    : RenormalizedDominationStmt p :=
  Assembly.renormalizedDomination hWC hKes hpc

-- Lemma 5.26 (`Assembly.goodEventDensity`, Section5d.lean; `NullMeasurableSet`, all
-- parameters).
example (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    GoodEventDensityStmt p :=
  Assembly.goodEventDensity hCorr hpc hp1

end Rigidity.Audit
