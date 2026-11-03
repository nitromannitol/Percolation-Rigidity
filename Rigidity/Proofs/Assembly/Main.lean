import Rigidity.Frozen.IntegerLinearGrowthV1
import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section4
import Rigidity.Proofs.Assembly.Section5Decay
import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Assembly.Section5f
import Rigidity.Proofs.Assembly.Section5GeneralSlope
import Rigidity.Proofs.Assembly.Section6
import Rigidity.Proofs.S2.ArmstrongDarioTranslation
import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.S3.HomogenizedCoefficient

/-!
# The main theorems and the results with derived inputs

This module restates the main theorems of the corrected draft (Bou-Rabee, Cooperman, Dario,
*Rigidity of harmonic functions on the supercritical percolation cluster*), and the numbered
results whose composed proofs use a locally stated input or whose statement differs from the
printed one, with their final hypotheses. Every hypothesis is a regime condition or a cited
literature input, a proposition of `LatticeProb/External` or `Rigidity/External`. The three
locally stated inputs are derived:

* [C34]: Theorem 2.4 with `k = 1` at every centre
  (`Rigidity.Proofs.S2.ArmstrongDarioOrderOneProposed`) is derived by
  `Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin` from the statement at the origin
  `Rigidity.External.ArmstrongDarioOrderOneOrigin` and `SupercriticalBondCorrectorInput`;
* [C35]: the density of the infinite cluster in balls
  (`Rigidity.Proofs.S2.ClusterDensityInputProposed`) is derived by
  `Rigidity.Proofs.S2.clusterDensityInputProposed_of_concentration` from
  `Rigidity.External.ClusterDensityConcentrationInput` (Dario-Gu, Proposition A.1);
* the positivity of the homogenized coefficient
  (`Rigidity.Proofs.S3.HomogenizedCoefficientProposed`) is proved by
  `Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed` from
  `SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput` and
  `CorrectorQuantitativeInput`.

The results:

* Theorem 1.1 (`lipschitz`), Theorem 1.2 (`integerValuedLinearGrowth`), Theorem 1.3
  (`fastDecay`, `d = 2`), Theorem 6.5 (`slowMixing`, the restriction event);
* Proposition 2.6 (`greenGradientHomogenization`);
* Proposition 3.2 (`notLipschitz`, inner-measure form);
* Lemma 4.8 (`nonConstantOnGadget`, as printed: the conditional form);
* Theorem 5.1 (`fastDecayDichotomy`), Propositions 5.3 (`fastDecayPotential`), 5.7
  (`gradientTrichotomy`, every slope `q ≠ 0` [C30]), 5.8 (`twoScaleExpansion`) and 5.11
  (`levelSetDensity`, [C29] [C30]: eventually in `k`, every slope `q ≠ 0`);
* Lemmas 5.25 (`goodEventLowerBound`, [C31] [C32]: universal `G₁`, direction-free `G₃`), 5.26
  (`goodEventDensity`, `NullMeasurableSet`, all parameters) and 5.27 (`largeGradientSensitive`,
  through the corrected good event);
* Lemma 5.25 as printed (`goodEventLowerBoundDirectional`; not the draft statement): the third
  good event on the edge `(x, x + e₁)`, the printed form in place of the direction-free one of
  [C32], with the universal first good event of [C31].

Every theorem uses the same argument order: the dimension `d`, `[NeZero d]`, `2 ≤ d` (in
Section 5, `d = 2` is fixed), the parameter `p`, the datum `f` (Section 5), the supercritical
regime `p_c(d) < p < 1`, then the cited literature inputs it uses, in the fixed order below:

* `hUq : LatticeProb.External.SupercriticalBondUniqueness`: existence and uniqueness of the
  infinite cluster;
* `hCorr : LatticeProb.External.SupercriticalBondCorrectorInput`: the first-order correctors of the
  infinite cluster (Armstrong-Dario, qualitative part of Theorem 2.5);
* `hCQ : Rigidity.External.CorrectorQuantitativeInput`: the quantitative sublinearity of the
  correctors (Theorem 2.5);
* `hAD : LatticeProb.External.ArmstrongDarioOrderZero`: Armstrong-Dario, Theorem 2 (Theorem 2.4
  with `k = 0`, centre `0`);
* `hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin`: Armstrong-Dario 2018, Theorem 2(iii)
  (Theorem 2.4 with `k = 1`, centre `0`);
* `hE : LatticeProb.External.SupercriticalBondGreenColumnExistence` and
  `hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative`: the Green function of the
  infinite cluster (Dario-Gu), the inputs of Proposition 2.8;
* `hDG : Rigidity.External.ClusterDensityConcentrationInput`: the concentration of the density of
  the infinite cluster in triadic cubes (Dario-Gu, Proposition A.1);
* `hW : Rigidity.External.WellConnectedInput`: the well-connected cubes (Proposition 2.3,
  Antal-Pisztora, Penrose-Pisztora);
* `hK : Rigidity.External.KestenRectangleCrossing`: rectangle crossings in `d = 2` (Kesten,
  Theorem 11.1);
* `hJ : Rigidity.External.JordanCurveTheoremSphere`: the Jordan curve theorem on `S²`;
* `hMR : Rigidity.External.MicciancioRegevSmoothing`: the smoothing parameter bound
  (Micciancio-Regev, Lemma 3.3).

Each of the fifteen theorems concludes exactly the draft statement of `Rigidity/Draft` (with the
changes named above), by name (for Theorem 1.2, exactly the statement of
`Rigidity/Frozen/IntegerLinearGrowthV1.lean`); `goodEventLowerBoundDirectional` concludes Lemma
5.25 as printed, named in its docstring. No open step remains in any composition.
-/

namespace Rigidity.Assembly.Main

open MeasureTheory LatticeProb.Percolation

/-! ## Main theorems -/

/-- **Theorem 1.1** (Lipschitz rigidity). For `d ≥ 2` and `p_c(d) < p < 1`, almost surely every
Lipschitz harmonic function on the infinite cluster is constant.

* Draft statement: `Rigidity.Section3.LipschitzStmt d p`
  (`Rigidity/Draft/Section3Statements.lean`).
* Proof: `Rigidity.Assembly.lipschitz` (`Rigidity/Proofs/Assembly/Section3.lean`), composed from
  Lemma 3.1 and Proposition 3.2, with `homogenizedCoefficientProposed`. -/
theorem lipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section3.LipschitzStmt d p :=
  Rigidity.Assembly.lipschitz hd p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

/-- **Theorem 1.2** (integer-valued rigidity). For `d ≥ 2` and `p_c(d) < p < 1`, almost surely
every integer-valued harmonic function of at most linear growth on the infinite cluster is a
constant integer.

* Draft statement: none. The statement is the frozen theorem
  `Rigidity.integer_valued_linear_growth` (`Rigidity/Frozen/IntegerLinearGrowthV1.lean`), restated
  verbatim.
* Cited inputs: `SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`.
* Proof: `Rigidity.integer_valued_linear_growth`. -/
theorem integerValuedLinearGrowth (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∃ h : HasUniqueInfiniteOpenComponent ω,
        ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ x : uniqueInfiniteComponent h,
            componentLaplacian (uniqueInfiniteComponent h) u x = 0) →
          (∀ x : uniqueInfiniteComponent h, ∃ z : ℤ, u x = (z : ℝ)) →
          componentPointwiseLinearGrowth (uniqueInfiniteComponent h) u →
          ∃ a : ℤ, ∀ x : uniqueInfiniteComponent h, u x = (a : ℝ) :=
  Rigidity.integer_valued_linear_growth d hd p hpc hp1 hUq hCorr

/-- **Theorem 1.3** (fast decay, `d = 2`). For `p_c(2) < p < 1`, almost surely, for every finitely
supported `f : ℤ² → ℤ`, every `u : 𝒞_∞ → ℝ` with `-Δu = f` and
`lim sup_R R sup_{B_R \ B_{R/2}} |u| = 0` has finite support.

* Draft statement: `Rigidity.Section5.FastDecayStmt p`
  (`Rigidity/Draft/Section5Statements.lean`).
* Proof: `Rigidity.Assembly.fastDecay` (`Rigidity/Proofs/Assembly/Section5Decay.lean`), with the
  derived inputs `armstrongDarioOrderOneProposed_of_origin`,
  `clusterDensityInputProposed_of_concentration` and `homogenizedCoefficientProposed`. -/
theorem fastDecay (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.FastDecayStmt p :=
  Rigidity.Assembly.fastDecay hUq hGQ hE hAD hCorr hCQ hW hK hJ
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    (Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin hAD1 hCorr)
    (Rigidity.Proofs.S2.clusterDensityInputProposed_of_concentration hDG) hpc hp1

/-- **Theorem 6.5** (sandpile mixing time, on the restriction event). There are
`c, C > 0` such that almost surely, for every `ε > 0` and every large `n`, some largest open cluster
`V` of `Q_n` lies in `𝒞_∞`, and for every such `V` meeting `∂Q_n`, the sandpile chain on `V`
satisfies `‖P^t - U‖₂² ≤ ε` for `t ≥ C n^d log n` and `‖P^t - U‖₂² ≥ ε` for `t ≤ c n^d log n`.

* Draft statement: `Rigidity.Section6.SlowMixingStmt d p`
  (`Rigidity/Draft/Section6Statements.lean`).
* Proof: `Rigidity.Assembly.slowMixing` (`Rigidity/Proofs/Assembly/Section6.lean`). -/
theorem slowMixing (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hW : Rigidity.External.WellConnectedInput)
    (hMR : Rigidity.External.MicciancioRegevSmoothing) :
    Rigidity.Section6.SlowMixingStmt d p :=
  Rigidity.Assembly.slowMixing hd p hpc hp1 hUq hW hMR

/-! ## Section 2 -/

/-- **Proposition 2.6** (homogenization of the gradient of the Green function).

* Draft statement: `Rigidity.Section2.GreenGradientHomogenizationStmt d hd p`
  (`Rigidity/Draft/Section2Statements.lean`).
* Proof: `Rigidity.Assembly.greenGradientHomogenization` (`Rigidity/Proofs/Assembly/Section2.lean`),
  with the derived inputs `armstrongDarioOrderOneProposed_of_origin` and
  `clusterDensityInputProposed_of_concentration`. -/
theorem greenGradientHomogenization (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput) :
    Rigidity.Section2.GreenGradientHomogenizationStmt d hd p :=
  Rigidity.Assembly.greenGradientHomogenization hd hpc hp1 hGQ hCQ hCorr
    (Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin hAD1 hCorr)
    (Rigidity.Proofs.S2.clusterDensityInputProposed_of_concentration hDG)

/-! ## Section 3 -/

/-- **Proposition 3.2** (inner-measure form): for `p_c(d) < p < 1` and every
`L ≥ 1`, the event that the origin is in `𝒞_∞` and `|∇ℓ_{e₁}(0)| > L`, and the event that
`ℓ_{e₁}` is not `L`-Lipschitz, each contain a measurable event of positive probability.

* Draft statement: `Rigidity.Section3.NotLipschitzStmt d p`
  (`Rigidity/Draft/Section3Statements.lean`).
* Proof: `Rigidity.Assembly.notLipschitz` (`Rigidity/Proofs/Assembly/Section3.lean`), with
  `homogenizedCoefficientProposed`. -/
theorem notLipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section3.NotLipschitzStmt d p :=
  Rigidity.Assembly.notLipschitz hd p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

/-! ## Section 4 -/

/-- **Lemma 4.8** (as printed, the conditional form): for a
deterministic slope `q ≠ 0` there are `c > 0` and `R₀` such that for `R ≥ R₀` some bond set `H` of
`Q_R` contains a translate of the gadget of height `R` as an induced subgraph, with
`P[𝒞_∞ ∩ Q_R = H] > 0` and `P[ℓ_q not constant on the gadget | 𝒞_∞ ∩ Q_R = H] ≥ c R^{-2d+2}`.

* Draft statement: `Rigidity.Section4.NonConstantOnGadgetStmt d hd p`
  (`Rigidity/Draft/Section4Statements.lean`).
* Proof: `Rigidity.Assembly.nonConstantOnGadget` (`Rigidity/Proofs/Assembly/Section4.lean`), by
  averaging over `H` (`Rigidity.Proofs.S4.OuterNonConstant`). -/
theorem nonConstantOnGadget (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero) :
    Rigidity.Section4.NonConstantOnGadgetStmt d hd p :=
  Rigidity.Assembly.nonConstantOnGadget hd p hpc hp1 hAD hCorr

/-! ## Section 5 (`d = 2`) -/

/-- **Theorem 5.1** (fast decay dichotomy).

* Draft statement: `Rigidity.Section5.FastDecayDichotomyStmt p`
  (`Rigidity/Draft/Section5Statements.lean`).
* Proof: `Rigidity.Assembly.fastDecayDichotomy` (`Rigidity/Proofs/Assembly/Section5Decay.lean`),
  with the derived inputs `armstrongDarioOrderOneProposed_of_origin`,
  `clusterDensityInputProposed_of_concentration` and `homogenizedCoefficientProposed`. -/
theorem fastDecayDichotomy (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.FastDecayDichotomyStmt p :=
  Rigidity.Assembly.fastDecayDichotomy hUq hGQ hE hAD hCorr hCQ hW hK hJ
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    (Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin hAD1 hCorr)
    (Rigidity.Proofs.S2.clusterDensityInputProposed_of_concentration hDG) hpc hp1

/-- **Proposition 5.3** (fast decay of the potential).

* Draft statement: `Rigidity.Section5.FastDecayPotentialStmt p f`
  (`Rigidity/Draft/Section5Statements.lean`).
* Proof: `Rigidity.Assembly.fastDecayPotential` (`Rigidity/Proofs/Assembly/Section5Decay.lean`),
  with the derived inputs `armstrongDarioOrderOneProposed_of_origin`,
  `clusterDensityInputProposed_of_concentration` and `homogenizedCoefficientProposed`. -/
theorem fastDecayPotential (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.FastDecayPotentialStmt p f :=
  Rigidity.Assembly.fastDecayPotential hUq hGQ hE hAD hCorr hCQ hW hK hJ
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    (Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin hAD1 hCorr)
    (Rigidity.Proofs.S2.clusterDensityInputProposed_of_concentration hDG) hpc hp1 f

/-- **Proposition 5.7** (gradient trichotomy), at every slope `q ≠ 0` [C30].

* Draft statement: `Rigidity.Section5.GradientTrichotomyStmt p f`
  (`Rigidity/Draft/Section5Statements.lean`).
* Proof: `Rigidity.Assembly.gradientTrichotomy`
  (`Rigidity/Proofs/Assembly/Section5GeneralSlope.lean`), with `homogenizedCoefficientProposed`. -/
theorem gradientTrichotomy (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.GradientTrichotomyStmt p f :=
  Rigidity.Assembly.gradientTrichotomy p hpc hp1 f hUq hCorr hCQ hAD hE hGQ hW hK hJ
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

/-- **Proposition 5.8** (two-scale expansion).

* Draft statement: `Rigidity.Section5.TwoScaleExpansionStmt p f`
  (`Rigidity/Draft/Section5Statements.lean`).
* Proof: `Rigidity.Assembly.twoScaleExpansion` (`Rigidity/Proofs/Assembly/Section5d.lean`), with
  the derived inputs `armstrongDarioOrderOneProposed_of_origin` and
  `clusterDensityInputProposed_of_concentration`. -/
theorem twoScaleExpansion (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD1 : Rigidity.External.ArmstrongDarioOrderOneOrigin)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hDG : Rigidity.External.ClusterDensityConcentrationInput)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section5.TwoScaleExpansionStmt p f :=
  Rigidity.Assembly.twoScaleExpansion hUq hW hGQ hCQ hCorr
    (Rigidity.Proofs.S2.armstrongDarioOrderOneProposed_of_origin hAD1 hCorr)
    (Rigidity.Proofs.S2.clusterDensityInputProposed_of_concentration hDG) hpc hp1 f

/-- **Proposition 5.11** (density of the level sets, [C29] [C30]): some `c > 0`
bounds the density from below for all large `k`, at every slope `q ≠ 0`.

* Draft statement: `Rigidity.Section5.LevelSetDensityStmt p f`
  (`Rigidity/Draft/Section5Statements.lean`).
* Proof: `Rigidity.Assembly.levelSetDensity`
  (`Rigidity/Proofs/Assembly/Section5GeneralSlope.lean`), with `homogenizedCoefficientProposed`. -/
theorem levelSetDensity (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.LevelSetDensityStmt p f :=
  Rigidity.Assembly.levelSetDensity p hpc hp1 f hUq hCorr hCQ hAD hE hGQ hW hK hJ
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)

/-- **Lemma 5.25** (lower bound on the probability of the good event, [C31] [C32]: universal
first good event, direction-free third good event).

* Draft statement: `Rigidity.Section5.GoodEventLowerBoundStmt p`
  (`Rigidity/Draft/Section5cStatements.lean`).
* Proof: `Rigidity.Assembly.goodEventLowerBound` (`Rigidity/Proofs/Assembly/Section5d.lean`), with
  `homogenizedCoefficientProposed`. -/
theorem goodEventLowerBound (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Section5.GoodEventLowerBoundStmt p :=
  Rigidity.Assembly.goodEventLowerBound hCQ hUq hCorr hAD hE hGQ hW
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    hpc hp1

/-- **Lemma 5.26** (density of the good event, `NullMeasurableSet`, all parameters).

* Draft statement: `Rigidity.Section5.GoodEventDensityStmt p`
  (`Rigidity/Draft/Section5cStatements.lean`).
* Proof: `Rigidity.Assembly.goodEventDensity` (`Rigidity/Proofs/Assembly/Section5d.lean`). -/
theorem goodEventDensity (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput) :
    Rigidity.Section5.GoodEventDensityStmt p :=
  Rigidity.Assembly.goodEventDensity hCorr hpc hp1

/-- **Lemma 5.27** (a large gradient is sensitive to the environment), through the corrected good
event ([C31] [C32]).

* Draft statement: `Rigidity.Section5.LargeGradientSensitiveStmt p f`
  (`Rigidity/Draft/Section5cStatements.lean`).
* Proof: `Rigidity.Assembly.largeGradientSensitive`
  (`Rigidity/Proofs/Assembly/Section5Decay.lean`), with `homogenizedCoefficientProposed`. -/
theorem largeGradientSensitive (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) :
    Rigidity.Section5.LargeGradientSensitiveStmt p f :=
  Rigidity.Assembly.largeGradientSensitive hUq hGQ hE hAD hCorr hCQ hW hK hJ
    (Rigidity.Proofs.S3.HomogenizedCoefficient.homogenizedCoefficientProposed hUq hCorr hCQ)
    hpc hp1 f

/-! ## Lemma 5.25 as printed

The draft keeps the direction-free third good event of [C32], and Lemma 5.25 as printed is
proved too. The theorem below is **not** the draft statement; it uses only cited literature
inputs. -/

/-- **Lemma 5.25 as printed** (directional form, not the draft statement: the printed third good
event in place of the direction-free one of [C32], with the universal first good event of
[C31]): the third good event `G₃(x, C_χ)` asks that the edge `(x, x + e₁)` lie in the infinite
cluster with `ℓ(x + e₁) - ℓ(x) ≥ C_χ` for every corrected plane `ℓ` of slope `e₁`. For
`p_c(2) < p < 1` and every `C_χ ≥ 1` there is `c > 0` such that, for parameters `R, c₁`
satisfying the bound of Proposition 5.24, `P[G₁(x, K) ∩ G₂(x, K) ∩ G₃(x, C_χ)] ≥ c` for all `x`
and all large `K`.

* Statement: `Rigidity.Steps.Section5.GoodEventLowerBoundDirectionalStmt p`
  (`Rigidity/Steps/Section5/GoodEventLowerBound.lean`, third good event `eventG3Directional`).
* Proof: `Rigidity.Assembly.goodEventLowerBoundDirectional`
  (`Rigidity/Proofs/Assembly/Section5f.lean`), by the signed variant of Proposition 3.2 with the
  exterior network proved (`Rigidity.Proofs.S3.exteriorNetworkStep`) and
  `homogenizedCoefficientProposed`. -/
theorem goodEventLowerBoundDirectional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hCorr : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hE : LatticeProb.External.SupercriticalBondGreenColumnExistence)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hW : Rigidity.External.WellConnectedInput) :
    Rigidity.Steps.Section5.GoodEventLowerBoundDirectionalStmt p :=
  Rigidity.Assembly.goodEventLowerBoundDirectional p hpc hp1 hUq hCorr hCQ hAD hE hGQ hW

end Rigidity.Assembly.Main
