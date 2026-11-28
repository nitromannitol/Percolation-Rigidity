import Rigidity.Proofs.Assembly.Main
import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section4
import Rigidity.Proofs.Assembly.Section5
import Rigidity.Proofs.Assembly.Section5b
import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Assembly.Section5e
import Rigidity.Proofs.Assembly.Unconditional
import Rigidity.Proofs.Assembly.ProvedDensity
import Rigidity.Proofs.Assembly.ProvedOrderOne
import Rigidity.Proofs.Assembly.ProvedOrderZero
import Rigidity.Proofs.Assembly.ProvedGreenColumn
import Rigidity.Proofs.Assembly.ProvedCorrectorQuantitative
import Rigidity.Proofs.Percolation.WellConnected
import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorInput
import PercolationClusterHomogenization.Proofs.Regularity.GeneralOrderOneHolds

/-!
# The numbered results with every literature input proved

`Rigidity.Assembly.Unconditional` states Theorems 1.1, 1.2, 1.3, 6.5 and Proposition 3.2 with the
regime as their only hypotheses. This module does the same for the other numbered results whose
theorems of `Rigidity.Assembly.Main` and of `Rigidity.Assembly.Section2` to `Section5e` take
literature inputs: Proposition 2.6, Lemmas 2.16, 3.1, 3.3, 4.7, 4.8 and 4.9, Proposition 4.10,
Theorem 5.1, Propositions 5.3, 5.5, 5.7, 5.8, 5.11, 5.12, 5.20, 5.21 and 5.24, and Lemmas 5.6, 5.14,
5.16 to 5.19, 5.23, 5.25 (both forms), 5.26, 5.27 and 5.28. Each wrapper has the conclusion of the
original theorem and, as its only hypotheses, the regime `2 ≤ d`, `p_c(d) < p < 1`
(`p_c(2) < p < 1` in dimension two), with every literature input supplied by its proof:

* supercritical uniqueness of the infinite cluster
  (`Rigidity.Percolation.supercritical_bond_uniqueness`);
* the first-order correctors
  (`Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds`);
* the quantitative sublinearity of the correctors
  (`Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds`);
* the regularity of order zero and of order one
  (`Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds`,
  `Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_holds`);
* the Green columns and their quantitative estimate
  (`Rigidity.Green.supercriticalBondGreenColumnExistence_holds`,
  `Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds`);
* the concentration of the density of the infinite cluster
  (`Rigidity.Proofs.S2.cluster_density_concentration`);
* the well-connected cubes (`Rigidity.Percolation.wellConnected_input`);
* the rectangle crossings and the Jordan curve theorem on the sphere
  (`Rigidity.Percolation.kesten_rectangle_crossing`,
  `Rigidity.Topology.jordan_curve_theorem_sphere`).
-/

namespace Rigidity.Assembly.Unconditional

open MeasureTheory LatticeProb.Percolation

/-- **Proposition 2.6**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem greenGradientHomogenization (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section2.GreenGradientHomogenizationStmt d hd p :=
  Rigidity.Assembly.WithProvedDensity.green_gradient_homogenization d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Lemma 4.8**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem nonConstantOnGadget (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section4.NonConstantOnGadgetStmt d hd p :=
  Rigidity.Assembly.WithProvedOrderZero.nonConstantOnGadget d hd p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Theorem 5.1**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem fastDecayDichotomy (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : Rigidity.Section5.FastDecayDichotomyStmt p :=
  Rigidity.Assembly.WithProvedOrderOne.fastDecayDichotomy p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Proposition 5.3**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem fastDecayPotential (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.FastDecayPotentialStmt p f :=
  Rigidity.Assembly.WithProvedOrderOne.fastDecayPotential p f hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Proposition 5.7**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem gradientTrichotomy (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.GradientTrichotomyStmt p f :=
  Rigidity.Assembly.WithProvedGreenColumn.gradientTrichotomy p f hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Proposition 5.8**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem twoScaleExpansion (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.TwoScaleExpansionStmt p f :=
  Rigidity.Assembly.Main.twoScaleExpansion p f hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds
    Rigidity.Proofs.S2.cluster_density_concentration Rigidity.Percolation.wellConnected_input

/-- **Proposition 5.11**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem levelSetDensity (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.LevelSetDensityStmt p f :=
  Rigidity.Assembly.WithProvedGreenColumn.levelSetDensity p f hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Lemma 5.25**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem goodEventLowerBound (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : Rigidity.Section5.GoodEventLowerBoundStmt p :=
  Rigidity.Assembly.WithProvedGreenColumn.goodEventLowerBound p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Lemma 5.25 as printed** (the directional form), with every literature input supplied by its
proof: the regime `p_c(2) < p < 1` is its only hypothesis. -/
theorem goodEventLowerBoundDirectional (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Steps.Section5.GoodEventLowerBoundDirectionalStmt p :=
  Rigidity.Assembly.WithProvedGreenColumn.goodEventLowerBoundDirectional p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Lemma 5.26**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem goodEventDensity (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : Rigidity.Section5.GoodEventDensityStmt p :=
  Rigidity.Assembly.Main.goodEventDensity p hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Lemma 5.27**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem largeGradientSensitive (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.LargeGradientSensitiveStmt p f :=
  Rigidity.Assembly.WithProvedGreenColumn.largeGradientSensitive p f hpc hp1
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Assembly.EveryDimension.correctorQuantitativeInput_holds
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds

/-- **Lemma 2.16**, with every literature input supplied by its proof: it has no hypothesis. -/
theorem jordanCurves : Rigidity.Section2.JordanCurvesStmt :=
  Rigidity.Assembly.jordanCurves Rigidity.Topology.jordan_curve_theorem_sphere

/-- **Lemma 3.1**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem reductionToSlopeE1 (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section3.ReductionToSlopeE1Stmt d p :=
  Rigidity.Assembly.reductionToSlopeE1 hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Percolation.wellConnected_input

/-- **Lemma 3.3**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem compareDifferentPlanes (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section3.CompareDifferentPlanesStmt d hd p :=
  Rigidity.Assembly.compareDifferentPlanes hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds
    Rigidity.Green.supercriticalBondGreenColumnExistence_holds
    Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds

/-- **Lemma 4.7**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem detSlope (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section4.DetSlopeStmt d p :=
  Rigidity.Assembly.detSlope hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Lemma 4.9**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem ergodicityLipschitz (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section4.ErgodicityLipschitzStmt d p :=
  Rigidity.Assembly.ergodicityLipschitz hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Proposition 4.10**, with every literature input supplied by its proof: the regime
`2 ≤ d`, `p_c(d) < p < 1` is its only hypothesis. -/
theorem rationalMatrix (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section4.RationalMatrixStmt d p :=
  Rigidity.Assembly.rationalMatrix hd p hpc hp1
    Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds

/-- **Proposition 5.5**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem logGrowth (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.LogGrowthStmt p f :=
  Rigidity.Assembly.logGrowth Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Assembly.EveryDimension.supercriticalBondGreenQuantitative_holds hpc hp1 f

/-- **Lemma 5.6**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem meanZeroRepresentation (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.MeanZeroRepresentationStmt p f :=
  Rigidity.Assembly.meanZeroRepresentation Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Percolation.wellConnected_input hpc hp1 f

/-- **Proposition 5.12**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem infiniteDisjointPaths (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.InfiniteDisjointPathsStmt p f :=
  Rigidity.Assembly.infiniteDisjointPaths Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere hpc hp1 f

/-- **Lemma 5.14**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem loopsAroundAnnuli (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.LoopsAroundAnnuliStmt p :=
  Rigidity.Assembly.loopsAroundAnnuli Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Percolation.kesten_rectangle_crossing hpc hp1

/-- **Lemma 5.16**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem strongMaxPrinciple (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.StrongMaxPrincipleStmt p :=
  Rigidity.Assembly.strongMaxPrinciple Rigidity.Percolation.supercritical_bond_uniqueness hpc hp1

/-- **Lemma 5.17**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem polesSuperLevelSets (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.PolesSuperLevelSetsStmt p f :=
  Rigidity.Assembly.polesSuperLevelSets Rigidity.Percolation.supercritical_bond_uniqueness hpc hp1 f

/-- **Lemma 5.18**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem longNonzeroPaths (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.LongNonzeroPathsStmt p f :=
  Rigidity.Assembly.longNonzeroPaths Rigidity.Percolation.supercritical_bond_uniqueness hpc hp1 f

/-- **Lemma 5.19**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem noThickPaths (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.NoThickPathsStmt p f :=
  Rigidity.Assembly.noThickPaths Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere hpc hp1 f

/-- **Proposition 5.20**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem boundarySize (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.BoundarySizeStmt p f :=
  Rigidity.Assembly.boundarySize Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere hpc hp1 f

/-- **Proposition 5.21**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem disjointPathsToInfinity (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (_hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.DisjointPathsToInfinityStmt p :=
  Rigidity.Assembly.disjointPathsToInfinity Rigidity.Percolation.wellConnected_input
    Rigidity.Percolation.kesten_rectangle_crossing hpc _hp1

/-- **Lemma 5.23**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem renormalizedDomination (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ)) :
    Rigidity.Section5.RenormalizedDominationStmt p :=
  Rigidity.Assembly.renormalizedDomination Rigidity.Percolation.wellConnected_input
    Rigidity.Percolation.kesten_rectangle_crossing hpc

/-- **Proposition 5.24**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem longPathRenormalized (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ)) :
    Rigidity.Section5.LongPathRenormalizedStmt p :=
  Rigidity.Assembly.longPathRenormalized Rigidity.Percolation.wellConnected_input
    Rigidity.Percolation.kesten_rectangle_crossing hpc

/-- **Lemma 5.28**, with every literature input supplied by its proof: the regime
`p_c(2) < p < 1` is its only hypothesis. -/
theorem finiteBranches (p : unitInterval) (f : Vertex 2 → ℤ)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Rigidity.Section5.FiniteBranchesStmt p f :=
  Rigidity.Assembly.finiteBranches Rigidity.Percolation.supercritical_bond_uniqueness
    Rigidity.Percolation.kesten_rectangle_crossing
    Rigidity.Topology.jordan_curve_theorem_sphere hpc hp1 f

end Rigidity.Assembly.Unconditional
