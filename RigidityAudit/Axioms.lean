import Rigidity
import Rigidity.Proofs.Assembly.Main
import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section4
import Rigidity.Proofs.Assembly.Section5
import Rigidity.Proofs.Assembly.Section5b
import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Assembly.Section5e
import Rigidity.Percolation.Blocks.SlabConnectivity
import Rigidity.Percolation.Pisztora.FiniteClusters
import Rigidity.Proofs.Assembly.PlanarInputs
import Rigidity.Proofs.Assembly.Unconditional
import Rigidity.Proofs.Assembly.ProvedDensity
import Rigidity.Proofs.Assembly.PlanarGreenInputs
import Rigidity.Proofs.Green.SupercriticalGreenColumn
import Rigidity.Proofs.Green.SupercriticalGreenBounds
import Rigidity.Proofs.Multiscale.Affine
import Rigidity.Proofs.Partition.AlmostSure
import Rigidity.Proofs.Partition.GeneralPartition
import Rigidity.Proofs.Partition.MinimalScaleCombined
import Rigidity.Proofs.Partition.Paths
import Rigidity.Proofs.Cluster.PartitionCoarseData
import Rigidity.Proofs.Cluster.PartitionSobolev
import Rigidity.Proofs.Cluster.PartitionSobolevTwo
import Rigidity.Proofs.Cluster.Caccioppoli
import Rigidity.Proofs.Cluster.ReverseHolderPartition
import Rigidity.Proofs.Cluster.Gehring
import Rigidity.Proofs.Cluster.MeyersCluster
import Rigidity.Proofs.Cluster.SobolevCube
import Rigidity.Proofs.Cluster.SobolevZero
import Rigidity.Proofs.Cluster.SobolevPartition
import Rigidity.Proofs.Cluster.SobolevCoarseZero
import Rigidity.Proofs.Cluster.SobolevReverseHolder
import Rigidity.Proofs.Percolation.PlanarNuStationarity
import Rigidity.Proofs.Percolation.PlanarNuLocal
import Rigidity.Proofs.Percolation.PlanarMuLocal
import Rigidity.Proofs.Percolation.PlanarLocalStationary
import Rigidity.Proofs.Percolation.PlanarNuConvergence
import Rigidity.Proofs.Percolation.PlanarMuConvergence
import Rigidity.Proofs.Percolation.PlanarNuQuadratic
import Rigidity.Proofs.Percolation.PlanarMuLimitBounds
import Rigidity.Proofs.Percolation.PlanarDuality
import Rigidity.Proofs.Dirichlet.LemmaSixTwoCoarse
import Rigidity.Proofs.Dirichlet.CutoffRegions
import Rigidity.Proofs.Dirichlet.LemmaSixThreeCoarse
import Rigidity.Proofs.Dirichlet.Interpolation
import Rigidity.Proofs.Dirichlet.PropSixOne
import Rigidity.Proofs.Dirichlet.LayerEnergyBound
import Rigidity.Proofs.Regularity.KIterationGeneral
import Rigidity.Proofs.Regularity.KIteration
import Rigidity.Proofs.Regularity.LatticeHarmonicExcess
import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo
import Rigidity.Proofs.Regularity.PlanarHarmonicRegularity
import Rigidity.Proofs.Regularity.PlanarHarmonicRegularityTwo
import Rigidity.Proofs.Regularity.PlanarMesoscopicRegularity
import Rigidity.Proofs.Percolation.PlanarCoarseGradientMean
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeBounds
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeClose
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeInverseLimit
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeMatrix
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeRate
import Rigidity.Proofs.Percolation.PlanarIdentification
import Rigidity.Proofs.Percolation.PlanarMuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarMuIncrements
import Rigidity.Proofs.Percolation.PlanarNuDefectTau
import Rigidity.Proofs.Percolation.PlanarNuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarOmegaDBounds
import Rigidity.Proofs.Percolation.PlanarOmegaDecayIteration
import Rigidity.Proofs.Percolation.PlanarOmegaDLimit
import Rigidity.Proofs.Percolation.PlanarOmegaIteration
import Rigidity.Proofs.Percolation.PlanarOmegaLimit
import Rigidity.Proofs.Percolation.PlanarOmegaMatrix
import Rigidity.Proofs.Percolation.PlanarOmegaStepOne
import Rigidity.Proofs.Percolation.PlanarQuadraticResponse
import Rigidity.Proofs.Percolation.PlanarSecondVariation
import Rigidity.Proofs.Percolation.PlanarSolenoidalField
import Rigidity.Proofs.Percolation.PlanarSolenoidalPairing
import Rigidity.Proofs.Percolation.PlanarTauSummable
import Rigidity.Proofs.Cluster.MeyersPartitionBox
import Rigidity.Proofs.Cluster.MeyersPlanarBox
import Rigidity.Proofs.Cluster.PartitionBoxCluster
import Rigidity.Proofs.Cluster.PartitionBoxPaths
import Rigidity.Proofs.Cluster.PartitionBoxSobolev
import Rigidity.Proofs.Cluster.PlanarBoxCluster
import Rigidity.Proofs.Cluster.PlanarBoxSobolev
import Rigidity.Proofs.Cluster.PlanarBoxWindows
import Rigidity.Proofs.Cluster.PlanarCoarseEnergy
import Rigidity.Proofs.Cluster.PlanarCoarseEnergyMoments
import Rigidity.Proofs.Cluster.PlanarCoarseEnergySecondMoment
import Rigidity.Proofs.Cluster.PlanarCoarseMeyers
import Rigidity.Proofs.Cluster.PlanarCoarseMinimizer
import Rigidity.Proofs.Cluster.PlanarEdgePairing
import Rigidity.Proofs.Cluster.PlanarHolderAway
import Rigidity.Proofs.Cluster.PlanarInnerCells
import Rigidity.Proofs.Cluster.PlanarInnerSquare
import Rigidity.Proofs.Cluster.PlanarMeyersHarmonic
import Rigidity.Proofs.Cluster.PlanarPartitionScaleTail
import Rigidity.Proofs.Cluster.PlanarRestrictCoarse
import Rigidity.Proofs.Cluster.PlanarRestrictDefect
import Rigidity.Proofs.Cluster.PlanarRestrictQuad
import Rigidity.Proofs.Cluster.PlanarSubcubePairing
import Rigidity.Proofs.Cluster.ReverseHolderMoment
import Rigidity.Proofs.Cluster.ReverseHolderPlanar
import Rigidity.Proofs.Percolation.GeneralDim.CubeBoundaryErrorBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeBoundaryWeightBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergy
import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergyBounds
import Rigidity.Proofs.Percolation.GeneralDim.CubeExceptionalTail
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuLowerBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuMoment
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuNuComparison
import Rigidity.Proofs.Percolation.GeneralDim.CubeMuUpperBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeNablaAffine
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuDirichlet
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuEnergyDefect
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLimit
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLocal
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBound
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuLowerBoundMean
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuMonotone
import Rigidity.Proofs.Percolation.GeneralDim.CubeNuSubadditiveError
import Rigidity.Proofs.Percolation.GeneralDim.CubeSecondVariation
import Rigidity.Proofs.Percolation.GeneralDim.CubeSizeMoments
import Rigidity.Proofs.Percolation.GeneralDim.CubeStokes
import Rigidity.Proofs.Percolation.GeneralDim.CubeSubadditive
import Rigidity.Proofs.Percolation.GeneralDim.CubeSubcubes
import Rigidity.Proofs.Percolation.GeneralDim.CubeVariations
import Rigidity.Proofs.Percolation.PlanarCoarseEnergyMajorant
import Rigidity.Proofs.Percolation.PlanarFlatnessAE
import Rigidity.Proofs.Percolation.PlanarFlatnessBound
import Rigidity.Proofs.Percolation.PlanarFlatnessInputs
import Rigidity.Proofs.Percolation.PlanarFlatnessMu
import Rigidity.Proofs.Percolation.PlanarFlatnessNu
import Rigidity.Proofs.Percolation.PlanarFlatnessTools
import Rigidity.Proofs.Percolation.PlanarNablaAffineMoments
import Rigidity.Proofs.Percolation.PlanarNablaAffineSq
import Rigidity.Proofs.Percolation.PlanarOmegaAssembly
import Rigidity.Proofs.Percolation.PlanarOmegaBad
import Rigidity.Proofs.Percolation.PlanarOmegaCaccioppoli
import Rigidity.Proofs.Percolation.PlanarOmegaChain
import Rigidity.Proofs.Percolation.PlanarOmegaDecay
import Rigidity.Proofs.Percolation.PlanarOmegaIntegrals
import Rigidity.Proofs.Percolation.PlanarOmegaMajorants
import Rigidity.Proofs.Percolation.PlanarOmegaPointwise
import Rigidity.Proofs.Percolation.PlanarOmegaRates
import Rigidity.Proofs.Regularity.ClusterOrderOne
import Rigidity.Proofs.Regularity.OrderOneEndpoint
import Rigidity.Proofs.Regularity.OrderOneOrigin
import Rigidity.Proofs.Cluster.PlanarRHLocal
import Rigidity.Proofs.Cluster.PlanarRHMeyers
import Rigidity.Proofs.Cluster.PlanarRHPartition
import Rigidity.Proofs.Cluster.PlanarRHEvent
import Rigidity.Proofs.Cluster.PlanarRHProb
import Rigidity.Proofs.Cluster.PlanarRHRestrictGood
import Rigidity.Proofs.Cluster.PlanarRHRestrictQuad
import Rigidity.Proofs.Cluster.PlanarRHWeakConv
import Rigidity.Proofs.Cluster.MeyersUniform
import Rigidity.Proofs.Cluster.PlanarGehringInputs
import Rigidity.Proofs.Cluster.PlanarMidCells
import Rigidity.Proofs.Cluster.PlanarOneVarEst
import Rigidity.Proofs.Cluster.PlanarOneVarEstBound
import Rigidity.Proofs.Cluster.PlanarReachConcentrationHolds
import Rigidity.Proofs.Cluster.PlanarRestrictBad
import Rigidity.Proofs.Cluster.PlanarRestrictErrorGood
import Rigidity.Proofs.Cluster.PlanarRestrictErrorMajorant
import Rigidity.Proofs.Cluster.PlanarRestrictField
import Rigidity.Proofs.Cluster.PlanarRestrictFieldCoarsen
import Rigidity.Proofs.Cluster.PlanarRestrictFieldQuad
import Rigidity.Proofs.Cluster.PlanarRestrictQuadCoarsen
import Rigidity.Proofs.Cluster.PlanarRestrictQuadGehring
import Rigidity.Proofs.Cluster.PlanarRestrictQuadGood
import Rigidity.Proofs.Cluster.PlanarSwitchLocCompare
import Rigidity.Proofs.Cluster.PlanarSwitchLocCore
import Rigidity.Proofs.Cluster.PlanarSwitchLocGeom
import Rigidity.Proofs.Cluster.PlanarSwitchLocLocal
import Rigidity.Proofs.Cluster.PlanarSwitchLocProb
import Rigidity.Proofs.Cluster.PlanarWeakConvHolds
import Rigidity.Proofs.Cluster.PlanarWeakConvOrigin
import Rigidity.Proofs.Cluster.PlanarWeakConvVariance
import Rigidity.Proofs.Percolation.PlanarDefectTauCube
import Rigidity.Proofs.Percolation.PlanarMuGeneral
import Rigidity.Proofs.Percolation.PlanarNuDefectTauCube
import Rigidity.Proofs.Percolation.PlanarReachDomination
import Rigidity.Proofs.Percolation.PlanarRestrictErrorMeasurable
import Rigidity.Proofs.Cluster.BoundedChernoff
import Rigidity.Proofs.Cluster.PlanarConvergenceRate
import Rigidity.Proofs.Cluster.PlanarMinimalSet
import Rigidity.Proofs.Cluster.PlanarOmegaSupRate
import Rigidity.Proofs.Cluster.PlanarRhoLocal
import Rigidity.Proofs.Cluster.PlanarSIStepTwo
import Rigidity.Proofs.Cluster.OsTailCalculus
import Rigidity.Proofs.Cluster.PlanarBoundN
import Rigidity.Proofs.Cluster.PlanarMinimalScales
import Rigidity.Proofs.Cluster.PlanarReachErrors
import Rigidity.Proofs.Cluster.PlanarReachEvent
import Rigidity.Proofs.Cluster.PlanarSIUpgrade
import Rigidity.Proofs.Cluster.PlanarSIUpgradeOs
import Rigidity.Proofs.Cluster.PlanarScaleForms
import Rigidity.Proofs.Cluster.PlanarScaleStatements
import Rigidity.Proofs.Cluster.PlanarSubaddOs
import Rigidity.Proofs.Cluster.PlanarSubaddOsMain
import Rigidity.Proofs.Cluster.PlanarSubaddTail
import Rigidity.Proofs.Cluster.PlanarSubcubeIndex
import Rigidity.Proofs.Corrector.OsCalculus
import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative
import Rigidity.Proofs.Green.FrullaniGaussian
import Rigidity.Proofs.Green.HeatTimeIntegrals
import Rigidity.Proofs.Green.LazyCarneVaropoulos
import Rigidity.Proofs.Green.LazyHeatKernel
import Rigidity.Proofs.Green.PlanarGreenColumnCorrector
import Rigidity.Proofs.Green.PlanarGreenDeterministic
import Rigidity.Proofs.Green.PlanarGreenQuantitative
import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import Rigidity.Proofs.Regularity.PlanarClusterInclusions
import Rigidity.Proofs.Regularity.PlanarClusterRestriction
import Rigidity.Proofs.Regularity.PlanarCorrectorReduction
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximation
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationBalls
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationSquares
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationTwo
import Rigidity.Proofs.Regularity.PlanarOrderZero
import Rigidity.Proofs.Regularity.PlanarOrderZeroInput
import Rigidity.Proofs.Regularity.PlanarHarmonicRegularityThree
import Rigidity.Proofs.Regularity.LatticeHarmonicExcessThree
import Rigidity.Proofs.Regularity.LatticeCubicComparison
import Rigidity.Proofs.Regularity.LatticeKIterationTwo
import Rigidity.Proofs.Regularity.LatticeHarmonicMeanValue
import Rigidity.Proofs.Regularity.PlanarMesoscopicTwoTopBounds
import Rigidity.Proofs.Regularity.PlanarMesoscopicTwoMain
import Rigidity.Proofs.Regularity.PlanarMesoscopicDegreeTwo
import Rigidity.Proofs.Regularity.OrderOneOriginTwo
import Rigidity.Proofs.Regularity.PlanarOrderOneOriginInputs
import Rigidity.Proofs.Cluster.PlanarAhomIsotropic
import Rigidity.Proofs.Cluster.PlanarReflectionMesh
import Rigidity.Proofs.Cluster.PlanarSignedPermCluster
import Rigidity.Proofs.Cluster.PlanarSignedPermMesh
import Rigidity.Proofs.Cluster.TriadicSignedPerm
import Rigidity.Proofs.Dirichlet.PlanarBlockGeometry
import Rigidity.Proofs.Dirichlet.PlanarChainBound
import Rigidity.Proofs.Dirichlet.PlanarClusterEdges
import Rigidity.Proofs.Dirichlet.PlanarClusterTiles
import Rigidity.Proofs.Dirichlet.PlanarDatumBounds
import Rigidity.Proofs.Dirichlet.PlanarErrorChain
import Rigidity.Proofs.Dirichlet.PlanarErrorTerms
import Rigidity.Proofs.Dirichlet.PlanarInterpolation
import Rigidity.Proofs.Dirichlet.PlanarLemmaSixThree
import Rigidity.Proofs.Dirichlet.PlanarLemmaSixTwo
import Rigidity.Proofs.Dirichlet.PlanarMuTest
import Rigidity.Proofs.Dirichlet.PlanarPoincareZero
import Rigidity.Proofs.Dirichlet.PlanarPropSixOne
import Rigidity.Proofs.Dirichlet.PlanarStatements
import Rigidity.Proofs.Dirichlet.PlanarTheoremOne
import Rigidity.Proofs.Dirichlet.PlanarTheoremOneHolds
import Rigidity.Proofs.Dirichlet.PlanarTilePatch
import Rigidity.Proofs.Dirichlet.PlanarTileSums
import Rigidity.Proofs.Dirichlet.SubcubeMuTest
import Rigidity.Proofs.Regularity.PlanarCoarseBound
import Rigidity.Proofs.Regularity.PlanarCoarseBoundTwo
import Rigidity.Proofs.Regularity.PlanarCoarseComparison
import Rigidity.Proofs.Regularity.PlanarCoarseComparisonTwo
import Rigidity.Proofs.Regularity.PlanarGradNormBound
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationInputs
import Rigidity.Proofs.Regularity.PlanarHarmonicComparison
import Rigidity.Proofs.Regularity.PlanarHarmonicDistTwo
import Rigidity.Proofs.Regularity.PlanarHomogenizedGradient
import Rigidity.Proofs.Regularity.PlanarPartitionSizeScale
import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationHolds
import Rigidity.Proofs.Corrector.DarioBoxMoments
import Rigidity.Proofs.Corrector.DarioCoarsenedFields
import Rigidity.Proofs.Corrector.DarioCoarsenedOs
import Rigidity.Proofs.Corrector.DarioLinftyIteration
import Rigidity.Proofs.Corrector.DarioMoments
import Rigidity.Proofs.Corrector.DarioOptimalCorrector
import Rigidity.Proofs.Corrector.DarioPoincareMoments
import Rigidity.Proofs.Corrector.PlanarCoarseningError
import Rigidity.Proofs.Corrector.PlanarCorrectorLipschitz
import Rigidity.Proofs.Corrector.PlanarDarioCorrector
import Rigidity.Proofs.Corrector.PlanarDarioCorrectorHolds
import Rigidity.Proofs.Corrector.PlanarHeatSmoothing
import Rigidity.Proofs.Corrector.PlanarMeasurableCorrector
import Rigidity.Proofs.Corrector.PlanarPartitionComparison
import Rigidity.Proofs.Corrector.PlanarShiftedAnchor
import Rigidity.Proofs.Corrector.RandomBallSums
import Rigidity.Proofs.Green.LazyHeatMass
import Rigidity.Proofs.Green.DarioGuCorrectorLemma
import Rigidity.Proofs.Green.DarioGuGaussian
import Rigidity.Proofs.Green.DarioGuHeatKernelInputs
import Rigidity.Proofs.Green.DarioGuLatticeSup
import Rigidity.Proofs.Green.DarioGuLevels
import Rigidity.Proofs.Green.DarioGuPhiCalculus
import Rigidity.Proofs.Green.DarioGuPhiConvolution
import Rigidity.Proofs.Green.DarioGuPointwise
import Rigidity.Proofs.Green.DarioGuStep
import Rigidity.Proofs.Green.DarioGuStepEstimates
import Rigidity.Proofs.Green.DarioGuTail
import Rigidity.Proofs.Green.DarioGuTheoremOne
import Rigidity.Proofs.Green.DarioGuTheoremOneCorrector
import Rigidity.Proofs.Green.DarioGuTheoremOneReduced
import Rigidity.Proofs.Green.DarioGuTwoScaleInitial
import Rigidity.Proofs.Green.DarioGuWeightedL2
import Rigidity.Proofs.Green.OpenHeatSemigroup
import Rigidity.Proofs.Corrector.DarioPropThreeOne

/-! The axiom report of every numbered result of the paper and of the further proved results: the
slab connectivity theorem of Grimmett and Marstrand, Proposition 2.3 and the decay of finite
clusters for `d ≥ 3`, Proposition 2.3 in every dimension, Proposition 2.3 and the density
concentration for `d = 2`, Theorem 6.5 with every literature input proved, Theorem 1.3 from its
dimension-two inputs, the density concentration in every dimension with Proposition 2.6 and
Theorem 1.3 without it as a hypothesis, the existence of planar Green columns with Theorem 1.3
from five dimension-two inputs, the Green columns for `d ≥ 3` with the Green-column input from the
planar order-zero estimate and the heat kernel and Green column bounds, the multiscale Poincaré
inequality of Armstrong and Dario (Proposition A.2) with its affine form, and the partition into
good cubes and the functional and elliptic inequalities on the cluster of Armstrong and Dario
(§§2–3) with the Sobolev inequality of the lattice, the localization of the planar subadditive quantities with the limits of their
expectations and the homogenized matrix (§4.3 and the start of §5, `d = 2`), the convergence of
the finite-volume matrices and the energy defects of the planar subadditive quantities with the
identification of the limit from the decay of `ω` (§5, `d = 2`), and the deterministic
steps of the homogenization of the Dirichlet problem and of the excess-decay iteration (§§6–7),
and Lemma 7.3 at `k = 2` with Theorem 2(iii) at `k = 1` in dimension two (§7);
`scripts/check_axioms.py` checks it.

Each proved result is reported through its Lean theorem. A result cited from the literature is
reported through the proposition that states it; the theorems that use it take that proposition
as an explicit hypothesis. Lemma 2.13 (Remark 14.20 of Rudin's *Real and Complex Analysis*) is
cited in the paper and used by no Lean proof, so it has no Lean declaration. -/

-- Section 1
#print axioms Rigidity.Assembly.Main.lipschitz                        -- Theorem 1.1
#print axioms Rigidity.Assembly.Main.integerValuedLinearGrowth        -- Theorem 1.2
#print axioms Rigidity.Assembly.Main.fastDecay                        -- Theorem 1.3

-- Section 2
#print axioms Rigidity.finite_flip_full_measure                       -- Lemma 2.1
#print axioms Rigidity.External.WellConnectedInput                    -- Proposition 2.3 (cited)
#print axioms LatticeProb.External.ArmstrongDarioOrderZero            -- Theorem 2.4 (cited)
#print axioms Rigidity.External.ArmstrongDarioOrderOneOrigin          -- Theorem 2.4 (cited)
#print axioms LatticeProb.External.SupercriticalBondCorrectorInput    -- Theorem 2.5 (cited)
#print axioms Rigidity.External.CorrectorQuantitativeInput            -- Theorem 2.5 (cited)
#print axioms Rigidity.Assembly.Main.greenGradientHomogenization      -- Proposition 2.6
#print axioms Rigidity.mixed_green                                    -- Proposition 2.8
#print axioms Rigidity.External.JordanCurveTheoremSphere              -- Lemma 2.14 (cited)
#print axioms Rigidity.Assembly.jordanCurves                          -- Lemma 2.16

-- Section 3
#print axioms Rigidity.Assembly.reductionToSlopeE1                    -- Lemma 3.1
#print axioms Rigidity.Assembly.Main.notLipschitz                     -- Proposition 3.2
#print axioms Rigidity.Assembly.compareDifferentPlanes                -- Lemma 3.3

-- Section 4
#print axioms Rigidity.OpenGadget.exponential_growth_on_ambient_open_gadget  -- Proposition 4.1
#print axioms Rigidity.Assembly.effectiveResistanceRecurrence         -- Lemma 4.2
#print axioms Rigidity.Assembly.reducedRationalRecursion              -- Lemma 4.3
#print axioms Rigidity.Gadget.numDenomRecs                            -- Lemma 4.4
#print axioms Rigidity.Gadget.reducedRational                         -- Lemma 4.5
#print axioms Rigidity.Gadget.exponentialGrowth                       -- Lemma 4.6
#print axioms Rigidity.Assembly.detSlope                              -- Lemma 4.7
#print axioms Rigidity.Assembly.Main.nonConstantOnGadget              -- Lemma 4.8
#print axioms Rigidity.Assembly.ergodicityLipschitz                   -- Lemma 4.9
#print axioms Rigidity.Assembly.rationalMatrix                        -- Proposition 4.10

-- Section 5
#print axioms Rigidity.Assembly.Main.fastDecayDichotomy               -- Theorem 5.1
#print axioms Rigidity.Assembly.Main.fastDecayPotential               -- Proposition 5.3
#print axioms Rigidity.Assembly.logGrowth                             -- Proposition 5.5
#print axioms Rigidity.Assembly.meanZeroRepresentation                -- Lemma 5.6
#print axioms Rigidity.Assembly.Main.gradientTrichotomy               -- Proposition 5.7
#print axioms Rigidity.Assembly.Main.twoScaleExpansion                -- Proposition 5.8
#print axioms Rigidity.Assembly.Main.levelSetDensity                  -- Proposition 5.11
#print axioms Rigidity.Assembly.infiniteDisjointPaths                 -- Proposition 5.12
#print axioms Rigidity.Assembly.loopsAroundAnnuli                     -- Lemma 5.14
#print axioms Rigidity.Assembly.strongMaxPrinciple                    -- Lemma 5.16
#print axioms Rigidity.Assembly.polesSuperLevelSets                   -- Lemma 5.17
#print axioms Rigidity.Assembly.longNonzeroPaths                      -- Lemma 5.18
#print axioms Rigidity.Assembly.noThickPaths                          -- Lemma 5.19
#print axioms Rigidity.Assembly.boundarySize                          -- Proposition 5.20
#print axioms Rigidity.Assembly.disjointPathsToInfinity               -- Proposition 5.21
#print axioms Rigidity.Assembly.renormalizedDomination                -- Lemma 5.23
#print axioms Rigidity.Assembly.longPathRenormalized                  -- Proposition 5.24
#print axioms Rigidity.Assembly.Main.goodEventLowerBound              -- Lemma 5.25
#print axioms Rigidity.Assembly.Main.goodEventLowerBoundDirectional   -- Lemma 5.25 (as printed)
#print axioms Rigidity.Assembly.Main.goodEventDensity                 -- Lemma 5.26
#print axioms Rigidity.Assembly.Main.largeGradientSensitive           -- Lemma 5.27
#print axioms Rigidity.Assembly.finiteBranches                        -- Lemma 5.28

-- Section 6
#print axioms Rigidity.integer_valued_compact_support                 -- Proposition 6.4
#print axioms Rigidity.Assembly.Main.slowMixing                       -- Theorem 6.5

-- Slab connectivity above the critical point (Grimmett and Marstrand, d ≥ 3)
#print axioms Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt

-- Proposition 2.3 for d ≥ 3, its reduction to d = 2, and finite clusters for d ≥ 3
#print axioms Rigidity.Percolation.wellConnected_of_three_le
#print axioms Rigidity.Percolation.wellConnectedInput_of_planar
#print axioms Rigidity.Percolation.exists_finite_cluster_radius_le
#print axioms Rigidity.Percolation.exists_finite_cluster_card_le

-- Proposition 2.3 in every dimension, and Proposition 2.3 and the density concentration for d = 2
#print axioms Rigidity.Percolation.wellConnected_input
#print axioms Rigidity.Percolation.wellConnected_input_two
#print axioms Rigidity.Proofs.S2.planar_cluster_density_concentration

-- Theorem 6.5 with every literature input proved
#print axioms Rigidity.Assembly.Unconditional.slow_mixing

-- Theorem 1.3 from its dimension-two literature inputs
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay_of_green_exists

-- The density concentration in every dimension, and Proposition 2.6 and Theorem 1.3 without it
#print axioms Rigidity.Proofs.S2.cluster_density_concentration
#print axioms Rigidity.Assembly.WithProvedDensity.green_gradient_homogenization
#print axioms Rigidity.Assembly.WithProvedDensity.fast_decay

-- Existence of planar Green columns, and Theorem 1.3 from five dimension-two literature inputs
#print axioms Rigidity.Proofs.Section5.planar_greenColumn_exists
#print axioms Rigidity.Assembly.WithPlanarInputs.supercriticalBondGreenColumnExistenceTwo_of_orderZero
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay_of_planar_estimates

-- Green columns for d ≥ 3, the Green-column input from the planar order-zero estimate, and the
-- heat kernel and Green column bounds
#print axioms Rigidity.Green.latticeIsoperimetry
#print axioms Rigidity.Green.greenColumnExistence_of_three_le
#print axioms Rigidity.Green.supercriticalBondGreenColumnExistence_of_two
#print axioms Rigidity.Green.supercriticalBondGreenColumnExistence_of_orderZeroTwo
#print axioms Rigidity.Green.heat_le_of_two_le
#print axioms Rigidity.Green.greenColumn_le_rpow_of_three_le
#print axioms Rigidity.Green.greenColumn_le_one_add_rpow_of_three_le

-- The multiscale Poincaré inequality of Armstrong and Dario (Proposition A.2) and its affine form
#print axioms Rigidity.Proofs.Multiscale.multiscalePoincare_holds
#print axioms Rigidity.Proofs.Multiscale.exists_multiscalePoincare_affine

-- The partition into good cubes of Armstrong and Dario (Propositions 2.1 and 2.4, Lemmas 2.7 and 2.8,
-- Corollary 2.10) and the inequalities on the cluster (Lemmas 3.2, 3.3, 3.5 and 3.6, Proposition 3.4,
-- a Gehring lemma on triadic cubes and Proposition 3.8)
#print axioms Rigidity.Percolation.partition_estimates
#print axioms Rigidity.Percolation.partition_estimates_general
#print axioms Rigidity.Percolation.exists_minimalScale
#print axioms Rigidity.Percolation.exists_minimalScale_general
#print axioms Rigidity.Percolation.exists_measure_not_mem_goodCubes_le
#print axioms Rigidity.Percolation.TriadicCube.reachable_of_mem_goodCubes
#print axioms Rigidity.Percolation.reachable_partitionAnchor_of_walk
#print axioms Rigidity.Percolation.partition_sum_abs_sub_coarseAnchor_rpow_le
#print axioms Rigidity.Percolation.partition_sum_gradNormIn_coarseAnchor_rpow_le
#print axioms Rigidity.Percolation.exists_partition_sum_rpow_le_of_latticeSobolevOn
#print axioms Rigidity.Percolation.exists_partition_sum_sq_le_two
#print axioms Rigidity.Proofs.Cluster.caccioppoli_cluster
#print axioms Rigidity.Proofs.Cluster.reverse_holder_partition_cube
#print axioms Rigidity.Proofs.Cluster.gehring_triadic
#print axioms Rigidity.Proofs.Cluster.meyers_cluster

-- The localization and stationarity of the planar subadditive quantities of Armstrong and Dario
-- (Propositions 4.9 and 4.10, (4.40)), the limits of their expectations and the homogenized matrix
-- (Definition 5.1, (5.1)), for d = 2
#print axioms Rigidity.Percolation.exists_measure_planarCappedDiscrepancy_le
#print axioms Rigidity.Percolation.exists_planarNuLoc_localization
#print axioms Rigidity.Percolation.exists_planarMuLoc_localization
#print axioms Rigidity.Percolation.map_planarNuStat_shift
#print axioms Rigidity.Percolation.map_planarMuStat_shift
#print axioms Rigidity.Percolation.exists_tendsto_planarNuMean
#print axioms Rigidity.Percolation.exists_tendsto_planarMuMean
#print axioms Rigidity.Percolation.planarNuLimit_eq_planarAhom
#print axioms Rigidity.Percolation.exists_planarAhom_bounds
#print axioms Rigidity.Percolation.exists_planarMuLimit_two_sided
#print axioms Rigidity.Percolation.sum_mul_le_planarMuLimit_add_planarNuLimit

-- The deterministic steps of the homogenization of the Dirichlet problem of Armstrong and Dario
-- (Lemmas 6.2, 6.3 and 6.4, Proposition 6.1) and the excess-decay iteration (Lemmas 7.2 and 7.3)
#print axioms Rigidity.Dirichlet.innerEdgeEnergy_dirichletSolution_div_le_of_coarse
#print axioms Rigidity.Dirichlet.patch_cubeCutoff_of_not_mem
#print axioms Rigidity.Dirichlet.innerEdgeEnergy_patch_div_le_of_coarse
#print axioms Rigidity.Dirichlet.exists_sum_sq_patch_sub_div_le_of_coarse
#print axioms Rigidity.Dirichlet.sum_abs_grad_boundaryInterpolation_rpow_div_le
#print axioms Rigidity.Dirichlet.sum_sq_sub_le_of_inner_energy_chain
#print axioms Rigidity.Dirichlet.sum_energy_cubeLayer_div_le
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one
#print axioms Rigidity.Proofs.Regularity.harmonicRegularity_latticeHarmonicClass
#print axioms Rigidity.Proofs.Regularity.harmonicRegularity_planarHarmonicClass
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_latticeHarmonic
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_latticeHarmonic
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_zero_planar
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_one_planar
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_zero_planar
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_one_planar
#print axioms Rigidity.Proofs.Regularity.armstrongDario_orderZero_origin_planar

-- The Sobolev inequality of the lattice and Proposition 3.4 of Armstrong and Dario in every dimension
#print axioms Rigidity.Percolation.IntegerCube.exists_latticeSobolevOn
#print axioms Rigidity.Percolation.exists_sum_rpow_le_of_eq_zero_on_boundary
#print axioms Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_eq_zero
#print axioms Rigidity.Percolation.exists_partition_sum_rpow_le_of_sum_coarsen_eq_zero
#print axioms Rigidity.Percolation.exists_partition_sum_rpow_le_of_coarsen_eq_zero
#print axioms Rigidity.Percolation.exists_clusterSobolevTwo

-- The energy defects, the finite-volume matrices, the solenoidal field and the identification of the
-- limit from the decay of omega in Section 5 of Armstrong and Dario, for d = 2
#print axioms Rigidity.Percolation.sum_clusterForm_sub_add_sum_planarMu_subcubes_le
#print axioms Rigidity.Percolation.sum_clusterForm_sub_add_planarNu_le_sum_subcubes
#print axioms Rigidity.Percolation.exists_lintegral_planarMuDefect_le
#print axioms Rigidity.Percolation.exists_lintegral_planarNuDefect_le
#print axioms Rigidity.Percolation.exists_planarMuDefect_le_planarMuTau
#print axioms Rigidity.Percolation.exists_planarNuDefect_le_planarNuTau
#print axioms Rigidity.Percolation.summable_planarTau
#print axioms Rigidity.Percolation.exists_planarMuDefect_le_tendsto
#print axioms Rigidity.Percolation.exists_planarNuDefect_le_tendsto
#print axioms Rigidity.Percolation.planarMuLimit_eq_iff_planarOmegaLimit_eq_zero
#print axioms Rigidity.Percolation.forall_planarOmegaLimit_eq_zero_iff
#print axioms Rigidity.Percolation.coarsePairing_planarMuMinimizer
#print axioms Rigidity.Percolation.integral_coarsePairing_planarMuMinimizer
#print axioms Rigidity.Percolation.tendsto_planarAhomInvFinite
#print axioms Rigidity.Percolation.planarMuLimit_eq_planarAhomInvLimit
#print axioms Rigidity.Percolation.exists_planarAhomInvFinite_bounds
#print axioms Rigidity.Percolation.exists_abs_planarAhomInvFinite_sub_le
#print axioms Rigidity.Percolation.sum_solenoidalField_sub_eq_zero
#print axioms Rigidity.Percolation.solenoidalField_eq
#print axioms Rigidity.Percolation.abs_solenoidalField_le
#print axioms Rigidity.Percolation.tsum_sum_grad_mul_solenoidalField
#print axioms Rigidity.Percolation.exists_abs_planarNu_sub_planarMu_sub_le
#print axioms Rigidity.Percolation.exists_planarOmegaD_succ_le
#print axioms Rigidity.Percolation.exists_neg_le_planarOmegaD
#print axioms Rigidity.Percolation.exists_le_mul_pow_of_omega_iteration
#print axioms Rigidity.Percolation.exists_le_mul_pow_of_omega_iteration_of_ge
#print axioms Rigidity.Percolation.exists_planarOmegaD_le_pow_of_decay
#print axioms Rigidity.Percolation.exists_planarTau_le_pow_of_decay
#print axioms Rigidity.Percolation.exists_abs_planarAhomInvLimit_sub_le_of_decay
#print axioms Rigidity.Percolation.planarAhomInvLimit_det_ne_zero
#print axioms Rigidity.Percolation.tendsto_planarAhomFinite
#print axioms Rigidity.Percolation.tendsto_planarOmegaD
#print axioms Rigidity.Percolation.dotProduct_inv_planarAhomInvLimit_le
#print axioms Rigidity.Percolation.planarMuLimit_eq_of_limit_planarOmegaD_nonpos
#print axioms Rigidity.Percolation.planarMuLimit_eq_of_decay

-- The reverse Hölder inequality, the Meyers estimate and the Sobolev inequality on the clusters of integer cubes
-- (Armstrong and Dario, Lemma 3.6, Propositions 3.4 and 3.8)
#print axioms Rigidity.Proofs.Cluster.exists_latticeSobolevOn_two
#print axioms Rigidity.Proofs.Cluster.reverse_holder_partition_cube_of_moment
#print axioms Rigidity.Proofs.Cluster.reverse_holder_partition_of_moment
#print axioms Rigidity.Proofs.Cluster.lowerSobolevTwo_two
#print axioms Rigidity.Proofs.Cluster.mem_clusterVertices_of_adj_mem
#print axioms Rigidity.Proofs.Cluster.planar_reverse_holder_cube_of_moment
#print axioms Rigidity.Proofs.Cluster.reverse_holder_clusterEnergy_local
#print axioms Rigidity.Proofs.Cluster.meyers_cluster_of_local
#print axioms Rigidity.Proofs.Cluster.mem_boxClusterVertices_of_mem_cube
#print axioms Rigidity.Proofs.Cluster.planar_meyers
#print axioms Rigidity.Proofs.Cluster.mem_partitionBoxCluster_of_mem_cube
#print axioms Rigidity.Proofs.Cluster.partition_meyers
#print axioms Rigidity.Percolation.TriadicCube.reachIn_boxWindow_of_reachIn
#print axioms Rigidity.Percolation.TriadicCube.reachIn_planarAnchor_boxPairWindow
#print axioms Rigidity.Percolation.reachIn_planarAnchor_of_boxResolved
#print axioms Rigidity.Percolation.planarBoxCoarseData
#print axioms Rigidity.Percolation.planarBox_sum_abs_sub_coarseAnchor_rpow_le
#print axioms Rigidity.Percolation.planarBox_sum_gradNormIn_coarseAnchor_rpow_le
#print axioms Rigidity.Percolation.exists_planarBox_sum_sq_le
#print axioms Rigidity.Percolation.three_pow_reachScale_le_planarReach_box
#print axioms Rigidity.Percolation.three_pow_pairReachScale_le_planarReach_box
#print axioms Rigidity.Proofs.Cluster.openLaplacian_clusterExtend
#print axioms Rigidity.Proofs.Cluster.openLaplacian_clusterExtend_eq_zero
#print axioms Rigidity.Proofs.Cluster.planar_meyers_clusterHarmonic
#print axioms Rigidity.Percolation.reachable_partitionAnchor_of_reachable_box
#print axioms Rigidity.Percolation.IntegerCube.exists_walk
#print axioms Rigidity.Percolation.partitionBoxCoarseData
#print axioms Rigidity.Percolation.exists_partitionBox_sum_rpow_le_of_latticeSobolevOn
#print axioms Rigidity.Percolation.exists_clusterSobolevTwo_box
#print axioms Rigidity.Percolation.three_pow_reachScale_le_partitionReach_box

-- The coarse energy, the pairings with bounded fields and the restriction defect (Armstrong and Dario,
-- display (4.24), Lemmas 5.5 and 5.7, d = 2)
#print axioms Rigidity.Proofs.Cluster.sum_gradNormIn_coarse_sq_le_clusterForm
#print axioms Rigidity.Proofs.Cluster.edgePairing_clusterExtend_sq_le_clusterForm
#print axioms Rigidity.Proofs.Cluster.sup_planarReach_pow_seven_le
#print axioms Rigidity.Proofs.Cluster.ofReal_coarse_minimizer_le_reachSum
#print axioms Rigidity.Proofs.Cluster.exists_lintegral_coarse_minimizer_le
#print axioms Rigidity.Proofs.Cluster.exists_lintegral_coarse_minimizer_sq_le
#print axioms Rigidity.Proofs.Cluster.sum_rpow_le_of_meyers_cells
#print axioms Rigidity.Proofs.Cluster.sum_mul_le_of_meyers_cells
#print axioms Rigidity.Proofs.Cluster.planarBox_sum_gradNormIn_sq_le_clusterGradSq
#print axioms Rigidity.Proofs.Cluster.planarBox_coarse_energy_le_of_meyers
#print axioms Rigidity.Proofs.Cluster.sum_gradNormIn_coarse_sq_le_sup
#print axioms Rigidity.Proofs.Cluster.three_pow_sup_pairReachScale_le
#print axioms Rigidity.Proofs.Cluster.ofReal_sum_gradNormIn_coarse_sq_le
#print axioms Rigidity.Proofs.Cluster.ofReal_sum_gradNormIn_coarse_planarMuMinimizer_le
#print axioms Rigidity.Percolation.edgePairing
#print axioms Rigidity.Percolation.coarsePairing_eq_edgePairing
#print axioms Rigidity.Percolation.edgeEnergy_le_two_mul_sum_gradNormIn_sq
#print axioms Rigidity.Percolation.edgePairing_sq_le
#print axioms Rigidity.Percolation.card_layer_edges_le
#print axioms Rigidity.Percolation.edgePairing_sq_le_of_subset
#print axioms Rigidity.Proofs.Cluster.exists_lintegral_edgePairing_sub_sum_subcubes_le
#print axioms Rigidity.Proofs.Cluster.TriadicCube.subset_innerSquare
#print axioms Rigidity.Proofs.Cluster.enl_subset_of_mem_innerSquare
#print axioms Rigidity.Proofs.Cluster.card_innerCells_filter_le
#print axioms Rigidity.Proofs.Cluster.edgePairing_innerCells_sq_le
#print axioms Rigidity.Proofs.Cluster.innerSquare
#print axioms Rigidity.Proofs.Cluster.innerSquare_subset
#print axioms Rigidity.Proofs.Cluster.card_sdiff_innerSquare_le
#print axioms Rigidity.Proofs.Cluster.planarBoxResolved_innerSquare
#print axioms Rigidity.Percolation.exists_measure_partitionScale_gt_le
#print axioms Rigidity.Proofs.Cluster.edgePairing_coarse_sq_le_of_meyers
#print axioms Rigidity.Proofs.Cluster.sum_edgePairing_sq_le_planarMuDefect
#print axioms Rigidity.Proofs.Cluster.sum_clusterGradSq_eq_clusterForm
#print axioms Rigidity.Proofs.Cluster.edgePairing_clusterExtend_sq_le_of_meyers
#print axioms Rigidity.Percolation.edgePairing_sub_sum_subcubes_sq_le

-- The subadditive quantities on the clusters of triadic cubes of Z^d (Armstrong and Dario, Section 4 and
-- Definition 5.1, every d >= 2)
#print axioms Rigidity.Percolation.exists_cubeHarmonic_minimizer
#print axioms Rigidity.Percolation.exists_cubeMu_minimizer
#print axioms Rigidity.Percolation.exists_cubeNu_maximizer
#print axioms Rigidity.Percolation.cubeMu
#print axioms Rigidity.Percolation.cubeNu
#print axioms Rigidity.Percolation.cubeMu_nonpos
#print axioms Rigidity.Percolation.cubeNu_nonneg
#print axioms Rigidity.Percolation.cubeNu_le
#print axioms Rigidity.Percolation.cubeMu_mul_latticeVolume_add_cubeForm_sub
#print axioms Rigidity.Percolation.cubeMu_mul_latticeVolume_eq
#print axioms Rigidity.Percolation.cubeFluxPairing_sub_add_cubeForm_sub
#print axioms Rigidity.Percolation.cubeNu_mul_latticeVolume_eq
#print axioms Rigidity.Percolation.cubeNu_sub_cubeMu_eq
#print axioms Rigidity.Percolation.cubeMu_smul_add_smul
#print axioms Rigidity.Percolation.cubeNu_smul_add_smul
#print axioms Rigidity.Percolation.crossingClusterVertices_subset_of_resolved
#print axioms Rigidity.Percolation.cubeRestrictExt_mem_cubeHarmonic
#print axioms Rigidity.Percolation.sum_cubeForm_restrictExt_le
#print axioms Rigidity.Percolation.sum_cubeMu_subcubes_le
#print axioms Rigidity.Percolation.cubeNu_le_sum_subcubes
#print axioms Rigidity.Percolation.sum_cubeForm_sub_add_sum_cubeMu_subcubes_le
#print axioms Rigidity.Percolation.sum_cubeForm_sub_add_cubeNu_le_sum_subcubes
#print axioms Rigidity.Percolation.exists_cubeHarmonic_eq_on_boundary
#print axioms Rigidity.Percolation.exists_cubeNu_maximizer_affine
#print axioms Rigidity.Percolation.cubeNu_le_of_affine_boundary
#print axioms Rigidity.Percolation.exists_cubeNu_eq_of_affine_boundary
#print axioms Rigidity.Percolation.cubeCoarsePairing_eq_faces
#print axioms Rigidity.Percolation.abs_cubeCoarsePairing_sub_le
#print axioms Rigidity.Percolation.cubeBoundaryError_le
#print axioms Rigidity.Percolation.cubeBoundaryWeight_le
#print axioms Rigidity.Percolation.neg_cubeMu_le
#print axioms Rigidity.Percolation.exists_abs_cubeNu_sub_cubeMu_sub_le
#print axioms Rigidity.Percolation.exists_cubeMu_le_cubeNu_sub
#print axioms Rigidity.Percolation.exists_cubeMu_le_neg_sum_sq
#print axioms Rigidity.Percolation.le_cubeNu_add_of_resolved
#print axioms Rigidity.Percolation.exists_le_integral_cubeNu
#print axioms Rigidity.Percolation.exists_cubeAhom_lower_bound
#print axioms Rigidity.Percolation.exists_integral_sum_faces_le
#print axioms Rigidity.Percolation.exists_integral_sum_margin_le
#print axioms Rigidity.Percolation.exists_lintegral_neg_cubeMu_le
#print axioms Rigidity.Percolation.cubeNu_eq_of_equiv
#print axioms Rigidity.Percolation.measurable_cubeNu
#print axioms Rigidity.Percolation.integral_cubeNu_eq_of_scale_eq
#print axioms Rigidity.Percolation.integrable_cubeNu
#print axioms Rigidity.Percolation.flux_error_le
#print axioms Rigidity.Percolation.cubeNu_mul_latticeVolume_le_sum_add
#print axioms Rigidity.Percolation.sum_exp_neg_margin_le
#print axioms Rigidity.Percolation.exists_integral_cubeNu_le_of_scale_le
#print axioms Rigidity.Percolation.cubeNu_eq_sum_polarization
#print axioms Rigidity.Percolation.exists_tendsto_cubeNuMean
#print axioms Rigidity.Percolation.tendsto_cubeNuLimit
#print axioms Rigidity.Percolation.cubeAhom
#print axioms Rigidity.Percolation.cubeNuLimit_eq_cubeAhom
#print axioms Rigidity.Percolation.cubeAhom_symm
#print axioms Rigidity.Percolation.cubeAhom_bounds
#print axioms Rigidity.Percolation.cubeNuDefect_add_le
#print axioms Rigidity.Percolation.exists_lintegral_cubeNuDefect_le

-- The flatness of the coarsened minimizers, the decay of omega and the qualitative part of Proposition 5.2
-- (Armstrong and Dario, Lemmas 5.8 and 5.9, d = 2)
#print axioms Rigidity.Percolation.PlanarWeakConvergence
#print axioms Rigidity.Percolation.PlanarRestrictQuadCoarsenMu
#print axioms Rigidity.Percolation.PlanarRestrictQuadCoarsenNu
#print axioms Rigidity.Percolation.exists_coarseEnergyMu_majorant
#print axioms Rigidity.Percolation.exists_coarseEnergyNu_majorant
#print axioms Rigidity.Percolation.exists_flatness_le_multiscale
#print axioms Rigidity.Percolation.exists_planarMuFlatness_majorant
#print axioms Rigidity.Percolation.exists_lintegral_planarMuFlatness_le
#print axioms Rigidity.Percolation.exists_planarNuFlatness_majorant
#print axioms Rigidity.Percolation.exists_lintegral_planarNuFlatness_le
#print axioms Rigidity.Percolation.exists_planarMuFlatness_majorant_ae
#print axioms Rigidity.Percolation.exists_planarNuFlatness_majorant_ae
#print axioms Rigidity.Percolation.sum_sq_planarNuGradAvg_sub_le
#print axioms Rigidity.Percolation.exists_lintegral_planarNuGradAvg_sub_le
#print axioms Rigidity.Percolation.caccioppoli_dist
#print axioms Rigidity.Percolation.clusterForm_restrict_le_caccioppoli
#print axioms Rigidity.Percolation.planarNu_sub_planarMu_sub_le
#print axioms Rigidity.Percolation.planarOmega_chain
#print axioms Rigidity.Percolation.planarOmega_real_le
#print axioms Rigidity.Percolation.planarOmega_integral_le
#print axioms Rigidity.Percolation.exists_boundaryMajorant
#print axioms Rigidity.Percolation.exists_lintegral_not_resolved_le
#print axioms Rigidity.Percolation.exists_badMajorant
#print axioms Rigidity.Percolation.exists_lintegral_subMuSum_le
#print axioms Rigidity.Percolation.exists_lintegral_subNuSum_le
#print axioms Rigidity.Percolation.exists_lintegral_nuSubGap_le
#print axioms Rigidity.Percolation.exists_muSubGap_majorant
#print axioms Rigidity.Percolation.exists_subadditivityMajorant
#print axioms Rigidity.Percolation.exists_coarseError_majorant
#print axioms Rigidity.Percolation.planarTau_le_weighted
#print axioms Rigidity.Percolation.exists_planarOmegaD_le_of_inputs
#print axioms Rigidity.Percolation.exists_planarOmegaD_decay
#print axioms Rigidity.Percolation.planarMuLimit_eq_of_inputs

-- Theorem 2(iii) at k = 1 from the mesoscopic regularity of degree two (Armstrong and Dario, Lemma 7.3 and Theorem 2)
#print axioms Rigidity.Proofs.Regularity.ArmstrongDarioMesoscopicDegreeTwo
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderOneOrigin_of_mesoscopicDegreeTwo
#print axioms Rigidity.Proofs.Regularity.ballExcess_le_of_clusterBallVolumeL2
#print axioms Rigidity.Proofs.Regularity.weighted_endpoint_step
#print axioms Rigidity.Proofs.Regularity.orderOneEndpoint_step
#print axioms Rigidity.Proofs.Regularity.orderOneEndpoint_iterate
#print axioms Rigidity.Proofs.Regularity.orderOneEndpoint_fit
#print axioms Rigidity.Proofs.Regularity.exists_forall_le_of_orderOneEndpoint
#print axioms Rigidity.Proofs.Regularity.orderOneEndpointData_cluster
#print axioms Rigidity.Proofs.Regularity.clusterLiftMap_mem_harmonicGrowthSpace
-- The partition of Definition 3.7 of Armstrong and Dario from the local family of reverse Hoelder
-- cubes, and Lemmas 5.5 and 5.7 and Proposition 5.2, qualitative part, for p > p_c (d = 2)
#print axioms Rigidity.Proofs.Cluster.measurableSet_not_mem_planarRHGood_local
#print axioms Rigidity.Proofs.Cluster.planar_meyers_rh_uniform
#print axioms Rigidity.Proofs.Cluster.planarRHPartition_of_failureBound
#print axioms Rigidity.Proofs.Cluster.planarRHCube_of_scales
#print axioms Rigidity.Proofs.Cluster.planarRHFailureBound_holds
#print axioms Rigidity.Proofs.Cluster.planarRHPartition_holds
#print axioms Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenMu_holds
#print axioms Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenNu_holds
#print axioms Rigidity.Proofs.Cluster.planarWeakConvergence_holds
#print axioms Rigidity.Proofs.Cluster.planarMuLimit_eq

-- The inputs of Lemmas 5.5 and 5.7 in dimension two from the partition hypothesis PlanarGehringPartition (the earlier
-- form of Lemmas 5.5 and 5.7 and of the qualitative part of Proposition 5.2, d = 2)
#print axioms Rigidity.Proofs.Cluster.PlanarGehringPartition
#print axioms Rigidity.Proofs.Cluster.PlanarReachConcentration
#print axioms Rigidity.Proofs.Cluster.planarReachConcentration_holds
#print axioms Rigidity.Proofs.Cluster.meyers_triadic_uniform
#print axioms Rigidity.Proofs.Cluster.meyers_cluster_of_local_uniform
#print axioms Rigidity.Proofs.Cluster.planar_meyers_uniform
#print axioms Rigidity.Proofs.Cluster.planar_meyers_clusterHarmonic_uniform
#print axioms Rigidity.Proofs.Cluster.partition_meyers_uniform
#print axioms Rigidity.Proofs.Cluster.measure_restrictBad_le
#print axioms Rigidity.Proofs.Cluster.exists_planarMuRestrictError_majorant
#print axioms Rigidity.Proofs.Cluster.exists_planarNuRestrictError_majorant
#print axioms Rigidity.Proofs.Cluster.exists_lintegral_planarMuRestrictFieldError_le
#print axioms Rigidity.Proofs.Cluster.exists_lintegral_sum_subcube_solenoidal_sq_le
#print axioms Rigidity.Proofs.Cluster.exists_lintegral_sq_sub_switchLoc_le
#print axioms Rigidity.Proofs.Cluster.exists_measure_not_planarCapGood_le
#print axioms Rigidity.Proofs.Cluster.exists_variance_planarMuGradAvg_origin_le
#print axioms Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenMu_of_inputs
#print axioms Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenNu_of_inputs
#print axioms Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenMu_of_gehring
#print axioms Rigidity.Proofs.Cluster.planarRestrictQuadCoarsenNu_of_gehring
#print axioms Rigidity.Proofs.Cluster.planarMuLimit_eq_of_gehring
#print axioms Rigidity.Proofs.Cluster.planarWeakConvergence_of_gehring
#print axioms Rigidity.Proofs.Cluster.planarMuLimit_eq_of_gehring_partition
#print axioms Rigidity.Percolation.exists_lintegral_planarMuDefect_le_tau
#print axioms Rigidity.Percolation.exists_lintegral_planarNuDefect_le_tau
#print axioms Rigidity.Percolation.exists_measure_not_mem_planarCoarseGood_le
#print axioms Rigidity.Percolation.planarReach_le_stoppingSize
#print axioms Rigidity.Percolation.measurable_planarMuRestrictError
#print axioms Rigidity.Percolation.measurable_planarNuRestrictError
#print axioms Rigidity.Percolation.measurable_planarMuGen_indicator

-- The rate of Proposition 5.2 and Lemmas 5.3, 5.10 and 5.11 (Step 2) in dimension two
#print axioms Rigidity.Proofs.Cluster.exists_planarOmegaD_decay_holds
#print axioms Rigidity.Proofs.Cluster.exists_planarOmegaD_le_geometric
#print axioms Rigidity.Proofs.Cluster.exists_planarTau_le_geometric
#print axioms Rigidity.Proofs.Cluster.planarAhomInvLimit_eq_inv
#print axioms Rigidity.Proofs.Cluster.exists_abs_planarAhom_inv_sub_planarAhomInvFinite_le
#print axioms Rigidity.Proofs.Cluster.planar_convexp
#print axioms Rigidity.Proofs.Cluster.planar_omegadecayrate
#print axioms Rigidity.Proofs.Cluster.exists_integral_min_planarRhoStat_le
#print axioms Rigidity.Proofs.Cluster.measureReal_sum_ge_le_of_bounded
#print axioms Rigidity.Proofs.Cluster.planar_SIupgrade_step2
#print axioms Rigidity.Proofs.Cluster.abs_quadratic_sub_half_le
#print axioms Rigidity.Proofs.Cluster.planar_minimalset

-- Propositions 5.2 and 5.13, Lemma 5.11 and the minimal scales in dimension two (Armstrong and Dario)
#print axioms Rigidity.Proofs.Cluster.planarMinimalScales_holds
#print axioms Rigidity.Proofs.Cluster.exists_planar_minimalScale
#print axioms Rigidity.Proofs.Cluster.exists_measure_not_planarReachLe_le
#print axioms Rigidity.Proofs.Cluster.reachSum_le_of_planarReach_le
#print axioms Rigidity.Proofs.Cluster.planarRho_le_avg_of_planarReachLe
#print axioms Rigidity.Proofs.Cluster.planarComparisonError_le_of_planarReachLe
#print axioms Rigidity.Proofs.Cluster.sum_subcubesAt_eq_sum_sum
#print axioms Rigidity.Proofs.Cluster.exists_planarRho_tail
#print axioms Rigidity.Proofs.Cluster.planarSubaddGood_of_event
#print axioms Rigidity.Proofs.Cluster.exists_planarSubaddGood_tail
#print axioms Rigidity.Proofs.Cluster.exists_planarSubaddGood_tail_cube
#print axioms Rigidity.Proofs.Cluster.exists_planarBoundN_general
#print axioms Rigidity.Proofs.Cluster.planarBoundN_holds
#print axioms Rigidity.Proofs.Cluster.planarMinimalScales_partition_holds
#print axioms Rigidity.Proofs.Cluster.planarMesoscopicConvergence_holds
#print axioms Rigidity.Proofs.Cluster.planar_subadd_os
#print axioms Rigidity.Proofs.Cluster.osBound_coarse_bound
#print axioms Rigidity.Proofs.Cluster.OsBound.mul
#print axioms Rigidity.Proofs.Cluster.OsBound.add
#print axioms Rigidity.Proofs.Cluster.osBound_indicator
#print axioms Rigidity.Proofs.Cluster.isOsBond_of_osBound
#print axioms Rigidity.Proofs.Cluster.planar_SIupgrade_os
#print axioms Rigidity.Proofs.Cluster.planar_muupbound_os

-- The corrector estimate, the Green column and the Green function estimate in dimension two (Dario, Dario and Gu)
#print axioms Rigidity.Green.hasSublinearLiouville_of_existsUnique_correctedPlane
#print axioms Rigidity.Green.sublinearLiouville_two_of_correctorInput
#print axioms Rigidity.Green.supercriticalBondGreenColumnExistenceTwo_of_correctorInput
#print axioms Rigidity.Corrector.isOsBond_triadicScale_of_tail
#print axioms Rigidity.Corrector.isOsBond_triadicScale
#print axioms Rigidity.Corrector.correctedPlane_sub_eq
#print axioms Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario
#print axioms Rigidity.Green.hasDerivAt_vsrwHeat
#print axioms Rigidity.Green.vsrwHeat_le_one
#print axioms Rigidity.Green.measurable_openHeat
#print axioms Rigidity.Green.frullani
#print axioms Rigidity.Green.integral_gaussianHeat_sub
#print axioms Rigidity.Green.integral_rpow_neg_mul_exp_neg_div
#print axioms Rigidity.Green.HeatBounds.laplacian_timeGreen
#print axioms Rigidity.Green.HeatBounds.abs_timeGreen_sub_le
#print axioms Rigidity.Green.measurable_greenConstant
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_heatKernel
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_heatKernel_of_correctorInput
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_heatKernel_of_orderZero
#print axioms Rigidity.Green.lazyPow_le_carneVaropoulos
#print axioms Rigidity.Green.openHeat_le_exp_of_le_norm
#print axioms Rigidity.Green.heatSmallTimeTwo
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_smallTime
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_darioGu
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_darioGu_of_correctorInput
#print axioms Rigidity.Green.supercriticalBondGreenQuantitativeTwo_of_darioGu_of_orderZero
#print axioms Rigidity.Corrector.isOsBond_triadicScale_shift

-- Lemma 7.1, the order-zero regularity and the corrector input in dimension two (Armstrong and Dario)
#print axioms Rigidity.Proofs.Regularity.componentBallL2_le_squareL2
#print axioms Rigidity.Proofs.Regularity.squareL2_le_componentBallL2
#print axioms Rigidity.Proofs.Regularity.ballDist_le_squareHarmonicDist
#print axioms Rigidity.Proofs.Regularity.squareOsc_le_ballExcess
#print axioms Rigidity.Proofs.Regularity.le_sum_squareIterCoeff
#print axioms Rigidity.Proofs.Regularity.harmonicApproximation_of_squares
#print axioms Rigidity.Proofs.Regularity.le_sum_prod_of_step
#print axioms Rigidity.Proofs.Regularity.le_of_geometric_step
#print axioms Rigidity.Proofs.Regularity.exists_planarOrderZeroDecay
#print axioms Rigidity.Proofs.Regularity.card_ball_ge_of_clusterCubeDensity
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation
#print axioms Rigidity.Proofs.Regularity.planarHarmonicApproximationAt_of_squareEstimates
#print axioms Rigidity.Proofs.Regularity.mem_supp_of_mem_clusterVertices
#print axioms Rigidity.Proofs.Regularity.mem_clusterVertices_succ
#print axioms Rigidity.Proofs.Regularity.planarHarmonicApproximationTwo_of_squareEstimates
#print axioms Rigidity.Proofs.Regularity.eq_zero_of_slopeAsymptotics_zero
#print axioms Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_of_orderOne
#print axioms Rigidity.Proofs.Regularity.clusterRestrictTo_mem_clusterHarmonic
#print axioms Rigidity.Proofs.Regularity.clusterForm_clusterRestrictTo_le

-- Lemma 7.3, (7.18) at k = 2, and Theorem 2(iii) at k = 1 in dimension two (Armstrong and Dario)
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_two_planar
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_two_planar
#print axioms Rigidity.Proofs.Regularity.harmonicRegularity_three_latticeHarmonicClass
#print axioms Rigidity.Proofs.Regularity.polynomialComparison_latticeHarmonicCubic
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_2_two_latticeHarmonic
#print axioms Rigidity.Proofs.Regularity.armstrongDario_lemma_7_3_two_latticeHarmonic
#print axioms Rigidity.Proofs.Regularity.componentBallL2_le_sum_abs_of_latticeHarmonic
#print axioms Rigidity.Proofs.Regularity.coarse_top_bounds
#print axioms Rigidity.Proofs.Regularity.harmonicApproximation_error_le
#print axioms Rigidity.Proofs.Regularity.mesoscopicDegreeTwo_core
#print axioms Rigidity.Proofs.Regularity.mesoscopicDegreeTwoAt_of_inputs
#print axioms Rigidity.Proofs.Regularity.armstrongDarioMesoscopicDegreeTwoPlanar_of_inputs
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_inputs
#print axioms Rigidity.Proofs.Regularity.orderOneOrigin_of_mesoscopicDegreeTwoAt
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_mesoscopicDegreeTwoPlanar
#print axioms Rigidity.Proofs.Regularity.planarCoarseHarmonicApproximationTwo_iff
#print axioms Rigidity.Proofs.Regularity.planarPartCubeMoments_holds
#print axioms Rigidity.Proofs.Regularity.planarPartitionSizeScale_of_partCubeMoments
#print axioms Rigidity.Proofs.Regularity.planarHarmonicApproximationTwo_of_squareEstimates_holds
#print axioms Rigidity.Proofs.Regularity.armstrongDarioMesoscopicDegreeTwoPlanar_of_squareEstimates
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_squareEstimates

-- Theorem 1 of Armstrong and Dario in dimension two (the homogenization error for the Dirichlet problem)
#print axioms Rigidity.Percolation.exists_planarAhom_eq_smul_one
#print axioms Rigidity.Percolation.planarNuLimit_signedPermSlope
#print axioms Rigidity.Percolation.planarPartitionEvent_configurationMap_iff
#print axioms Rigidity.Dirichlet.exists_mu_test_of_subcubes
#print axioms Rigidity.Dirichlet.abs_cubeEdgeSlope_sub_sum_tiles_le
#print axioms Rigidity.Dirichlet.sum_subcube_errors_le
#print axioms Rigidity.Dirichlet.planar_lemmaSixTwo
#print axioms Rigidity.Dirichlet.exists_planar_sum_sq_le_of_eq_zero
#print axioms Rigidity.Dirichlet.planar_sum_abs_grad_boundaryInterpolation_rpow_div_le
#print axioms Rigidity.Dirichlet.sum_three_pow_pairReachScale_rpow_le
#print axioms Rigidity.Dirichlet.planarMu_le_test
#print axioms Rigidity.Dirichlet.planar_lemmaSixThree
#print axioms Rigidity.Dirichlet.planar_sum_sq_sub_uhom_le
#print axioms Rigidity.Dirichlet.planar_error_chain
#print axioms Rigidity.Dirichlet.chain_le
#print axioms Rigidity.Dirichlet.planarHomogenizationError_of_inputs
#print axioms Rigidity.Dirichlet.planarHomogenizationError_holds

-- Lemma 7.1 and the order-zero regularity in dimension two from Theorem 1 (Armstrong and Dario)
#print axioms Rigidity.Proofs.Regularity.planarPartitionSizeScale_of_minimalScales
#print axioms Rigidity.Proofs.Regularity.coarseComparison_on_square
#print axioms Rigidity.Proofs.Regularity.planarCoarseComparisonTwo_of_minimalScales
#print axioms Rigidity.Proofs.Regularity.sum_sq_coarse_sub_mean_le
#print axioms Rigidity.Proofs.Regularity.squareL2_coarse_sub_le
#print axioms Rigidity.Proofs.Regularity.planarCoarseBoundTwo_of_minimalScales
#print axioms Rigidity.Proofs.Regularity.planarHarmonicDistTwo_of_homogenizationError
#print axioms Rigidity.Proofs.Regularity.planarSquareEstimatesTwo_of_parts
#print axioms Rigidity.Proofs.Regularity.planarHarmonicApproximationTwo_of_inputs
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_of_inputs
#print axioms Rigidity.Proofs.Regularity.planarMinimalScalesTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarHomogenizationErrorTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarSquareEstimatesTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarHarmonicApproximationTwo_holds
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_dario

-- Theorem 1 of Dario in dimension two and the quantitative corrector input
#print axioms Rigidity.Corrector.IsOsBond.integral_rpow_le
#print axioms Rigidity.Corrector.isOsBond_of_moment_le
#print axioms Rigidity.Corrector.LinftyIterationData.mom_sub_le
#print axioms Rigidity.Corrector.isOsBond_sub_of_linftyIterationData
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_coarsened
#print axioms Rigidity.Corrector.lintegral_le_of_isOsBond_rpow_inv
#print axioms Rigidity.Corrector.CoarsenedOsData.linftyIterationData
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_coarsenedOs
#print axioms Rigidity.Corrector.lintegral_rpow_heatSquare_le
#print axioms Rigidity.Corrector.tsum_poincareWeight_le
#print axioms Rigidity.Corrector.lintegral_boxOsc_le_of_poincare
#print axioms Rigidity.Corrector.PoincareCoarsenedData.linftyIterationData
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_poincare
#print axioms Rigidity.Corrector.correctorDiff_translation
#print axioms Rigidity.Corrector.measurable_guardAnchor
#print axioms Rigidity.Corrector.infinite_planarCoarseAnchor
#print axioms Rigidity.Corrector.darioCoarsenedCorrectorTwo_of_base
#print axioms Rigidity.Corrector.lipschitz_correctedPlane_origin
#print axioms Rigidity.Corrector.lintegral_randomBallSum_le
#print axioms Rigidity.Corrector.baseCoarseningError
#print axioms Rigidity.Corrector.baseComparison
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_orderZero
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_poincareInputs
#print axioms Rigidity.Corrector.heatGradient_coarseField_isOsBond
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_prop31
#print axioms Rigidity.Green.tsum_ofReal_vsrwHeat
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_inputs
#print axioms Rigidity.Corrector.ae_summable_heat_coarseField
#print axioms Rigidity.Corrector.lintegral_abs_sub_integral_rpow_le
#print axioms Rigidity.Corrector.darioPropThreeOneTwo_of_lemmas
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_lemmas
#print axioms Rigidity.Corrector.correctorQuantitativeInputTwo_of_inputs

-- Theorem 1 of Dario and Gu in dimension two from Lemma 4.1, Proposition 4.3 and Proposition A.7
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_sections
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_reduced
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_reduced_dario
#print axioms Rigidity.Green.darioGuCorrectorLemmaTwo_of_inputs
#print axioms Rigidity.Green.darioGuTwoScaleInitialTwo_of_correctorQuantitative
#print axioms Rigidity.Green.heatLevel_step
#print axioms Rigidity.Green.pointwise_of_weightedL2
#print axioms Rigidity.Green.hasSum_vsrwHeat_mul
#print axioms Rigidity.Green.sum_dgPhi_mul_dgPhi_le
#print axioms Rigidity.Green.hasTail_latticeSup
