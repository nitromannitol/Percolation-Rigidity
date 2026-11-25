import Rigidity
import Rigidity.Proofs.Assembly.Main
import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section4
import Rigidity.Proofs.Assembly.Section5
import Rigidity.Proofs.Assembly.Section5b
import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Assembly.Section5e
import PercolationClusterHomogenization.Percolation.Blocks.SlabConnectivity
import PercolationClusterHomogenization.Percolation.Pisztora.FiniteClusters
import Rigidity.Proofs.Assembly.PlanarInputs
import Rigidity.Proofs.Assembly.Unconditional
import Rigidity.Proofs.Assembly.ProvedDensity
import Rigidity.Proofs.Assembly.ProvedOrderZero
import Rigidity.Proofs.Assembly.ProvedGreenColumn
import Rigidity.Proofs.Assembly.PlanarGreenInputs
import Rigidity.Proofs.Green.SupercriticalGreenColumn
import Rigidity.Proofs.Green.SupercriticalGreenBounds
import PercolationClusterHomogenization.Proofs.Multiscale.Affine
import PercolationClusterHomogenization.Proofs.Partition.AlmostSure
import PercolationClusterHomogenization.Proofs.Partition.GeneralPartition
import PercolationClusterHomogenization.Proofs.Partition.MinimalScaleCombined
import PercolationClusterHomogenization.Proofs.Partition.Paths
import PercolationClusterHomogenization.Proofs.Cluster.PartitionCoarseData
import PercolationClusterHomogenization.Proofs.Cluster.PartitionSobolev
import PercolationClusterHomogenization.Proofs.Cluster.PartitionSobolevTwo
import PercolationClusterHomogenization.Proofs.Cluster.Caccioppoli
import PercolationClusterHomogenization.Proofs.Cluster.ReverseHolderPartition
import PercolationClusterHomogenization.Proofs.Cluster.Gehring
import PercolationClusterHomogenization.Proofs.Cluster.MeyersCluster
import PercolationClusterHomogenization.Proofs.Cluster.SobolevCube
import PercolationClusterHomogenization.Proofs.Cluster.SobolevZero
import PercolationClusterHomogenization.Proofs.Cluster.SobolevPartition
import PercolationClusterHomogenization.Proofs.Cluster.SobolevCoarseZero
import PercolationClusterHomogenization.Proofs.Cluster.SobolevReverseHolder
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuStationarity
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuLocal
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuLocal
import PercolationClusterHomogenization.Proofs.Percolation.PlanarLocalStationary
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuConvergence
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuConvergence
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuQuadratic
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuLimitBounds
import PercolationClusterHomogenization.Proofs.Percolation.PlanarDuality
import PercolationClusterHomogenization.Proofs.Dirichlet.LemmaSixTwoCoarse
import PercolationClusterHomogenization.Proofs.Dirichlet.CutoffRegions
import PercolationClusterHomogenization.Proofs.Dirichlet.LemmaSixThreeCoarse
import PercolationClusterHomogenization.Proofs.Dirichlet.Interpolation
import PercolationClusterHomogenization.Proofs.Dirichlet.PropSixOne
import PercolationClusterHomogenization.Proofs.Dirichlet.LayerEnergyBound
import PercolationClusterHomogenization.Proofs.Regularity.KIterationGeneral
import PercolationClusterHomogenization.Proofs.Regularity.KIteration
import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcess
import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcessTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicRegularity
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicRegularityTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicRegularity
import PercolationClusterHomogenization.Proofs.Percolation.PlanarCoarseGradientMean
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFiniteVolumeBounds
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFiniteVolumeClose
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFiniteVolumeInverseLimit
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFiniteVolumeMatrix
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFiniteVolumeRate
import PercolationClusterHomogenization.Proofs.Percolation.PlanarIdentification
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuEnergyDefect
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuIncrements
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuDefectTau
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuEnergyDefect
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaDBounds
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaDecayIteration
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaDLimit
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaIteration
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaLimit
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaMatrix
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaStepOne
import PercolationClusterHomogenization.Proofs.Percolation.PlanarQuadraticResponse
import PercolationClusterHomogenization.Proofs.Percolation.PlanarSecondVariation
import PercolationClusterHomogenization.Proofs.Percolation.PlanarSolenoidalField
import PercolationClusterHomogenization.Proofs.Percolation.PlanarSolenoidalPairing
import PercolationClusterHomogenization.Proofs.Percolation.PlanarTauSummable
import PercolationClusterHomogenization.Proofs.Cluster.MeyersPartitionBox
import PercolationClusterHomogenization.Proofs.Cluster.MeyersPlanarBox
import PercolationClusterHomogenization.Proofs.Cluster.PartitionBoxCluster
import PercolationClusterHomogenization.Proofs.Cluster.PartitionBoxPaths
import PercolationClusterHomogenization.Proofs.Cluster.PartitionBoxSobolev
import PercolationClusterHomogenization.Proofs.Cluster.PlanarBoxCluster
import PercolationClusterHomogenization.Proofs.Cluster.PlanarBoxSobolev
import PercolationClusterHomogenization.Proofs.Cluster.PlanarBoxWindows
import PercolationClusterHomogenization.Proofs.Cluster.PlanarCoarseEnergy
import PercolationClusterHomogenization.Proofs.Cluster.PlanarCoarseEnergyMoments
import PercolationClusterHomogenization.Proofs.Cluster.PlanarCoarseEnergySecondMoment
import PercolationClusterHomogenization.Proofs.Cluster.PlanarCoarseMeyers
import PercolationClusterHomogenization.Proofs.Cluster.PlanarCoarseMinimizer
import PercolationClusterHomogenization.Proofs.Cluster.PlanarEdgePairing
import PercolationClusterHomogenization.Proofs.Cluster.PlanarHolderAway
import PercolationClusterHomogenization.Proofs.Cluster.PlanarInnerCells
import PercolationClusterHomogenization.Proofs.Cluster.PlanarInnerSquare
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMeyersHarmonic
import PercolationClusterHomogenization.Proofs.Cluster.PlanarPartitionScaleTail
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictCoarse
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictDefect
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictQuad
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubcubePairing
import PercolationClusterHomogenization.Proofs.Cluster.ReverseHolderMoment
import PercolationClusterHomogenization.Proofs.Cluster.ReverseHolderPlanar
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeBoundaryErrorBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeBoundaryWeightBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeEnergy
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeEnergyBounds
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeExceptionalTail
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeMuLowerBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeMuMoment
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeMuNuComparison
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeMuUpperBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNablaAffine
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuDirichlet
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuEnergyDefect
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuLimit
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuLocal
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuLowerBound
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuLowerBoundMean
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuMonotone
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeNuSubadditiveError
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSecondVariation
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSizeMoments
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeStokes
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSubadditive
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeSubcubes
import PercolationClusterHomogenization.Proofs.Percolation.GeneralDim.CubeVariations
import PercolationClusterHomogenization.Proofs.Percolation.PlanarCoarseEnergyMajorant
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessAE
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessBound
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessInputs
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessMu
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessNu
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFlatnessTools
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNablaAffineMoments
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNablaAffineSq
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaAssembly
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaBad
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaCaccioppoli
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaChain
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaDecay
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaIntegrals
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaMajorants
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaPointwise
import PercolationClusterHomogenization.Proofs.Percolation.PlanarOmegaRates
import PercolationClusterHomogenization.Proofs.Regularity.ClusterOrderOne
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneEndpoint
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneOrigin
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHLocal
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHMeyers
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHPartition
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHEvent
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHProb
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHRestrictGood
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHRestrictQuad
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRHWeakConv
import PercolationClusterHomogenization.Proofs.Cluster.MeyersUniform
import PercolationClusterHomogenization.Proofs.Cluster.PlanarGehringInputs
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMidCells
import PercolationClusterHomogenization.Proofs.Cluster.PlanarOneVarEst
import PercolationClusterHomogenization.Proofs.Cluster.PlanarOneVarEstBound
import PercolationClusterHomogenization.Proofs.Cluster.PlanarReachConcentrationHolds
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictBad
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictErrorGood
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictErrorMajorant
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictField
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictFieldCoarsen
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictFieldQuad
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictQuadCoarsen
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictQuadGehring
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRestrictQuadGood
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSwitchLocCompare
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSwitchLocCore
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSwitchLocGeom
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSwitchLocLocal
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSwitchLocProb
import PercolationClusterHomogenization.Proofs.Cluster.PlanarWeakConvHolds
import PercolationClusterHomogenization.Proofs.Cluster.PlanarWeakConvOrigin
import PercolationClusterHomogenization.Proofs.Cluster.PlanarWeakConvVariance
import PercolationClusterHomogenization.Proofs.Percolation.PlanarDefectTauCube
import PercolationClusterHomogenization.Proofs.Percolation.PlanarMuGeneral
import PercolationClusterHomogenization.Proofs.Percolation.PlanarNuDefectTauCube
import PercolationClusterHomogenization.Proofs.Percolation.PlanarReachDomination
import PercolationClusterHomogenization.Proofs.Percolation.PlanarRestrictErrorMeasurable
import PercolationClusterHomogenization.Proofs.Cluster.BoundedChernoff
import PercolationClusterHomogenization.Proofs.Cluster.PlanarConvergenceRate
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMinimalSet
import PercolationClusterHomogenization.Proofs.Cluster.PlanarOmegaSupRate
import PercolationClusterHomogenization.Proofs.Cluster.PlanarRhoLocal
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSIStepTwo
import PercolationClusterHomogenization.Proofs.Cluster.OsTailCalculus
import PercolationClusterHomogenization.Proofs.Cluster.PlanarBoundN
import PercolationClusterHomogenization.Proofs.Cluster.PlanarMinimalScales
import PercolationClusterHomogenization.Proofs.Cluster.PlanarReachErrors
import PercolationClusterHomogenization.Proofs.Cluster.PlanarReachEvent
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSIUpgrade
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSIUpgradeOs
import PercolationClusterHomogenization.Proofs.Cluster.PlanarScaleForms
import PercolationClusterHomogenization.Proofs.Cluster.PlanarScaleStatements
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubaddOs
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubaddOsMain
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubaddTail
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubcubeIndex
import Rigidity.Proofs.Corrector.OsCalculus
import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative
import Rigidity.Proofs.Corrector.CorrectorQuantitative
import Rigidity.Proofs.Corrector.Concentration
import Rigidity.Proofs.Green.FrullaniGaussian
import Rigidity.Proofs.Green.HeatTimeIntegrals
import Rigidity.Proofs.Green.LazyCarneVaropoulos
import Rigidity.Proofs.Green.LazyHeatKernel
import Rigidity.Proofs.Green.PlanarGreenColumnCorrector
import Rigidity.Proofs.Green.PlanarGreenDeterministic
import Rigidity.Proofs.Green.PlanarGreenQuantitative
import Rigidity.Proofs.Green.PlanarHeatKernelInputs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarClusterInclusions
import PercolationClusterHomogenization.Proofs.Regularity.PlanarClusterRestriction
import Rigidity.Proofs.Regularity.PlanarCorrectorReduction
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximation
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationBalls
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationSquares
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderZero
import PercolationClusterHomogenization.Proofs.Regularity.PlanarOrderZeroInput
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicRegularityThree
import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicExcessThree
import PercolationClusterHomogenization.Proofs.Regularity.LatticeCubicComparison
import PercolationClusterHomogenization.Proofs.Regularity.LatticeKIterationTwo
import PercolationClusterHomogenization.Proofs.Regularity.LatticeHarmonicMeanValue
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicTwoTopBounds
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicTwoMain
import PercolationClusterHomogenization.Proofs.Regularity.PlanarMesoscopicDegreeTwo
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneOriginTwo
import Rigidity.Proofs.Regularity.PlanarOrderOneOriginInputs
import PercolationClusterHomogenization.Proofs.Cluster.PlanarAhomIsotropic
import PercolationClusterHomogenization.Proofs.Cluster.PlanarReflectionMesh
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSignedPermCluster
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSignedPermMesh
import PercolationClusterHomogenization.Proofs.Cluster.TriadicSignedPerm
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarBlockGeometry
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarChainBound
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarClusterEdges
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarClusterTiles
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarDatumBounds
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarErrorChain
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarErrorTerms
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarInterpolation
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarLemmaSixThree
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarLemmaSixTwo
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarMuTest
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarPoincareZero
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarPropSixOne
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarStatements
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarTheoremOne
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarTheoremOneHolds
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarTilePatch
import PercolationClusterHomogenization.Proofs.Dirichlet.PlanarTileSums
import PercolationClusterHomogenization.Proofs.Dirichlet.SubcubeMuTest
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseBound
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseBoundTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseComparison
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCoarseComparisonTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarGradNormBound
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicApproximationInputs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicComparison
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHarmonicDistTwo
import PercolationClusterHomogenization.Proofs.Regularity.PlanarHomogenizedGradient
import PercolationClusterHomogenization.Proofs.Regularity.PlanarPartitionSizeScale
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
import PercolationClusterHomogenization.Proofs.Cluster.GeneralAhomIsotropic
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHEvent
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHExit
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHLocal
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHMeyers
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHPartition
import PercolationClusterHomogenization.Proofs.Cluster.GeneralRHProb
import PercolationClusterHomogenization.Proofs.Cluster.GeneralReachDomination
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMeyersPartition
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuConvergence
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuDuality
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLimits
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLocal
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuLocality
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuMeasurable
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuQuadratic
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuStationary
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuSubadditiveError
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuSubadditiveMoments
import Rigidity.Proofs.Corrector.DarioStationaryPartition
import Rigidity.Proofs.Corrector.ConcentrationTwoHolds
import Rigidity.Proofs.Corrector.DarioCorrectorConcentration
import Rigidity.Proofs.Probability.BregmanConvex
import Rigidity.Proofs.Probability.BernoulliCube
import Rigidity.Proofs.Probability.CubeMoments
import Rigidity.Proofs.Probability.CubeMomentBound
import Rigidity.Proofs.Probability.StretchedExponential
import Rigidity.Proofs.Probability.BernoulliProduct
import Rigidity.Proofs.Probability.BernoulliCylinder
import Rigidity.Proofs.Probability.BernoulliMoments
import Rigidity.Proofs.Poincare.LatticeHeatKernel
import Rigidity.Proofs.Poincare.HeatKernelBounds
import Rigidity.Proofs.Poincare.BoxMaximal
import Rigidity.Proofs.Poincare.HeatMaximal
import Rigidity.Proofs.Poincare.SteinScalar
import Rigidity.Proofs.Poincare.LatticeHeatFlow
import Rigidity.Proofs.Poincare.SteinSquareFunction
import Rigidity.Proofs.Poincare.SteinWeighted
import Rigidity.Proofs.Poincare.SteinBound
import Rigidity.Proofs.Poincare.SteinFinal
import Rigidity.Proofs.Poincare.SteinSigned
import Rigidity.Proofs.Poincare.HeatGradient
import Rigidity.Proofs.Poincare.HeatDuality
import Rigidity.Proofs.Poincare.BoxField
import Rigidity.Proofs.Poincare.DualityBilinear
import Rigidity.Proofs.Poincare.DualityLowFreq
import Rigidity.Proofs.Poincare.DualTestFunction
import Rigidity.Proofs.Poincare.DualityTerms
import Rigidity.Proofs.Poincare.MultiscalePoincareHolds
import Rigidity.Proofs.Poincare.DarioCorrectorPoincare
import Rigidity.Proofs.Poincare.DarioCorrectorBridges
import Rigidity.Proofs.Corrector.DarioBondResampling
import Rigidity.Proofs.Corrector.DarioCaseOneTwo
import Rigidity.Proofs.Corrector.DarioCaseThree
import Rigidity.Proofs.Corrector.DarioCaseThreeAe
import Rigidity.Proofs.Corrector.DarioCaseThreeClosed
import Rigidity.Proofs.Corrector.DarioCaseThreeCorrector
import Rigidity.Proofs.Corrector.DarioCaseThreePairing
import Rigidity.Proofs.Corrector.DarioClusterGreen
import Rigidity.Proofs.Corrector.DarioCoarseHeatField
import Rigidity.Proofs.Corrector.DarioFiniteEnergyGrowth
import Rigidity.Proofs.Corrector.DarioFiniteEnergySublinear
import Rigidity.Proofs.Corrector.DarioFlipCluster
import Rigidity.Proofs.Corrector.DarioLemmaThreeThreeFlip
import Rigidity.Proofs.Corrector.DarioHeatSquareSum
import Rigidity.Proofs.Corrector.DarioFlipTermTwoSummable
import Rigidity.Proofs.Corrector.DarioStepOneSum
import Rigidity.Proofs.Corrector.DarioStepOneHolds
import Rigidity.Proofs.Corrector.PeriodicHeatDecay
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorL2
import PercolationClusterHomogenization.Proofs.Regularity.PlanarScaleMaxima
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorSupNorm
import Rigidity.Proofs.Regularity.PlanarCorrectedPlaneExistence
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorConstruction
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorFromApproximation
import PercolationClusterHomogenization.Proofs.Regularity.PlanarNuEnergy
import PercolationClusterHomogenization.Proofs.Regularity.PlanarAffineApproximationNu
import PercolationClusterHomogenization.Proofs.Regularity.PlanarNuFlatnessAS
import PercolationClusterHomogenization.Proofs.Regularity.PlanarAffineApproximationHolds
import PercolationClusterHomogenization.Proofs.Regularity.OrderOneLift
import Rigidity.Proofs.Regularity.PlanarOrderOneDimension
import Rigidity.Proofs.Regularity.PlanarCorrectorHolds
import Rigidity.Proofs.Corrector.DarioStationaryCoarsening
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoMoments
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoStepTwo
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoMean
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoProof
import PercolationClusterHomogenization.Proofs.Regularity.PlanarStretchedScales
import PercolationClusterHomogenization.Proofs.Regularity.PlanarRestrictBadOs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarRestrictErrorOs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarFlatnessPathwise
import PercolationClusterHomogenization.Proofs.Regularity.PlanarFlatnessDecay
import PercolationClusterHomogenization.Proofs.Regularity.PlanarFlatnessOs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarAffineApproximationOs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarLocalScalesOs
import PercolationClusterHomogenization.Proofs.Regularity.PlanarCorrectorSupOs
import Rigidity.Proofs.Regularity.PlanarCorrectorOsc
import Rigidity.Proofs.Regularity.PlanarCorrectorOscHolds
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoHolds
import PercolationClusterHomogenization.Proofs.Cluster.GeneralSlopeQuadratic
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMinimalSet
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMuEnergyDefect
import PercolationClusterHomogenization.Proofs.Cluster.GeneralTauIncrements
import PercolationClusterHomogenization.Proofs.Cluster.GeneralFiniteVolumeMatrix
import Rigidity.Proofs.Green.PlanarCarneVaropoulos
import Rigidity.Proofs.Green.DarioGuDensityGaussian
import Rigidity.Proofs.Green.DarioGuPoincareHolds
import Rigidity.Proofs.Green.DarioGuApproxLemma
import Rigidity.Proofs.Green.DarioGuTheoremOneDensity
import Rigidity.Proofs.Green.DarioGuTheoremOneApprox
import Rigidity.Proofs.Green.DarioGuTheoremOneCarne
import Rigidity.Proofs.Green.DarioGuTheoremOnePoincare
import Rigidity.Proofs.Poincare.DarioGuBridges
import Rigidity.Proofs.Poincare.DarioGuFluxBridges
import Rigidity.Proofs.Corrector.DarioResamplePartitionHolds
import Rigidity.Proofs.Poincare.DarioStepTwoBridges
import Rigidity.Proofs.Corrector.DarioMeyersSource
import Rigidity.Proofs.Corrector.DarioStepTwoSum
import Rigidity.Proofs.Corrector.DarioStepTwoReduce
import Rigidity.Proofs.Corrector.DarioLocalGradientMoments
import Rigidity.Proofs.Corrector.DarioStepTwoFiniteWeight
import Rigidity.Proofs.Corrector.DarioStepTwoWeightMeas
import Rigidity.Proofs.Corrector.DarioStepTwoPartition
import Rigidity.Proofs.Poincare.DarioStepTwoHolds
import Rigidity.Proofs.Assembly.PlanarDarioGu
import Rigidity.Proofs.Green.DarioGuTwoScaleFluxTerm
import Rigidity.Proofs.Green.DarioGuTwoScaleAssembly
import Rigidity.Proofs.Green.DarioGuTwoScaleErrorFromSource
import Rigidity.Proofs.Green.DarioGuFluxTranslateHolds
import Rigidity.Proofs.Green.DarioGuDirichletSteps
import Rigidity.Proofs.Green.DarioGuDiscreteDivergence
import Rigidity.Proofs.Green.DarioGuGradientFromLipschitz
import Rigidity.Proofs.Green.DarioGuParabolicTimeslice

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

-- The order-zero regularity of Armstrong and Dario in every dimension, and the main theorems without it
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderZero_holds
#print axioms Rigidity.Assembly.WithProvedOrderZero.lipschitz
#print axioms Rigidity.Assembly.WithProvedOrderZero.fastDecay
#print axioms Rigidity.Assembly.WithProvedOrderZero.notLipschitz
#print axioms Rigidity.Assembly.WithProvedOrderZero.nonConstantOnGadget
#print axioms Rigidity.Assembly.WithProvedOrderZero.fastDecayDichotomy
#print axioms Rigidity.Assembly.WithProvedOrderZero.fastDecayPotential
#print axioms Rigidity.Assembly.WithProvedOrderZero.gradientTrichotomy
#print axioms Rigidity.Assembly.WithProvedOrderZero.levelSetDensity
#print axioms Rigidity.Assembly.WithProvedOrderZero.goodEventLowerBound
#print axioms Rigidity.Assembly.WithProvedOrderZero.largeGradientSensitive
#print axioms Rigidity.Assembly.WithProvedOrderZero.goodEventLowerBoundDirectional
#print axioms Rigidity.Assembly.WithProvedOrderZero.fastDecayWithProvedDensity

-- The Green-column input in every dimension, and the main theorems with every proved input supplied
#print axioms Rigidity.Green.supercriticalBondGreenColumnExistence_holds
#print axioms Rigidity.Assembly.WithProvedGreenColumn.lipschitz
#print axioms Rigidity.Assembly.WithProvedGreenColumn.fast_decay
#print axioms Rigidity.Assembly.WithProvedGreenColumn.notLipschitz
#print axioms Rigidity.Assembly.WithProvedGreenColumn.fastDecayDichotomy
#print axioms Rigidity.Assembly.WithProvedGreenColumn.fastDecayPotential
#print axioms Rigidity.Assembly.WithProvedGreenColumn.gradientTrichotomy
#print axioms Rigidity.Assembly.WithProvedGreenColumn.levelSetDensity
#print axioms Rigidity.Assembly.WithProvedGreenColumn.goodEventLowerBound
#print axioms Rigidity.Assembly.WithProvedGreenColumn.largeGradientSensitive
#print axioms Rigidity.Assembly.WithProvedGreenColumn.goodEventLowerBoundDirectional

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

-- Section 3 and the isotropy of the homogenized matrix in every dimension (Armstrong and Dario), and (3.3) and Step 3 of Lemma 3.2 of Dario
#print axioms Rigidity.Proofs.Cluster.GeneralDim.measurableSet_not_mem_rhGood_local
#print axioms Rigidity.Proofs.Cluster.GeneralDim.meyers_rh_uniform
#print axioms Rigidity.Proofs.Cluster.GeneralDim.mem_partitionBoxCluster_of_exit
#print axioms Rigidity.Proofs.Cluster.GeneralDim.rhCube_of_scales
#print axioms Rigidity.Proofs.Cluster.GeneralDim.exists_measure_sum_reach_enl_gt_le
#print axioms Rigidity.Proofs.Cluster.GeneralDim.rhFailureBound_holds
#print axioms Rigidity.Proofs.Cluster.GeneralDim.rhPartition_holds
#print axioms Rigidity.Percolation.reachable_partitionAnchor_of_exit
#print axioms Rigidity.Percolation.partitionReach_le_stoppingSize_coarseGood
#print axioms Rigidity.Percolation.exists_measure_not_mem_coarseGood_le
#print axioms Rigidity.Percolation.cubeNu_signedPerm
#print axioms Rigidity.Percolation.cubeNuLimit_signedPermSlope
#print axioms Rigidity.Percolation.exists_cubeAhom_eq_smul_one
#print axioms Rigidity.Corrector.abs_tsum_openHeat_mul_le
#print axioms Rigidity.Corrector.abs_tsum_openHeat_mul_periodic_le_exp
#print axioms Rigidity.Percolation.dario_errorstatpart

-- The corrected planes, the dimension of the harmonic functions of linear growth and the corrector input in dimension two (Armstrong and Dario, (1.18), Lemma 7.3), with no hypothesis
#print axioms Rigidity.Proofs.Regularity.exists_planar_all_centres_constant_approximation
#print axioms Rigidity.Proofs.Regularity.ae_eventually_scale_le_three
#print axioms Rigidity.Proofs.Regularity.abs_corrector_le_at_scale
#print axioms Rigidity.Proofs.Regularity.componentSlopeAsymptotics_of_scales
#print axioms Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_of_sublinearL2
#print axioms Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_of_sublinearL2
#print axioms Rigidity.Proofs.Regularity.exists_harmonic_of_approximations
#print axioms Rigidity.Proofs.Regularity.planarCorrectorSublinearL2Two_of_affineApproximation
#print axioms Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_of_affineApproximation
#print axioms Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_of_affineApproximationAe
#print axioms Rigidity.Proofs.Regularity.clusterForm_planarNuSolution_le
#print axioms Rigidity.Proofs.Regularity.sum_sq_extend_sub_coarsen_le
#print axioms Rigidity.Proofs.Regularity.sum_sq_coarsen_combo_le
#print axioms Rigidity.Proofs.Regularity.affineApproximation_at_scale
#print axioms Rigidity.Proofs.Regularity.radicand_le
#print axioms Rigidity.Proofs.Regularity.ae_eventually_planarNuFlatness_le
#print axioms Rigidity.Proofs.Regularity.planarAffineApproximationAeTwo_of_nuFlatness
#print axioms Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_of_nuFlatness
#print axioms Rigidity.Proofs.Regularity.planarAffineApproximationAeTwo_of_minimalScales
#print axioms Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_of_minimalScales
#print axioms Rigidity.Proofs.Regularity.eq_clusterLiftMap_of_orderOne
#print axioms Rigidity.Proofs.Regularity.planarOrderOneDimensionTwo_of_mesoscopic
#print axioms Rigidity.Proofs.Regularity.planarOrderOneDimensionTwo_of_minimalScales
#print axioms Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_of_mesoscopic
#print axioms Rigidity.Proofs.Regularity.mesoscopicDegreeTwoPlanarInput_iff
#print axioms Rigidity.Proofs.Regularity.mesoscopicDegreeTwoPlanarInput_holds
#print axioms Rigidity.Proofs.Regularity.supercriticalBondCorrectorInputTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarCorrectedPlaneExistenceTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarOrderOneDimensionTwo_holds
#print axioms Rigidity.Proofs.Regularity.supercriticalBondGreenColumnExistenceTwo_holds
#print axioms Rigidity.Proofs.Regularity.armstrongDarioOrderOneOriginTwo_of_darioOptimalCorrector
#print axioms Rigidity.Proofs.Regularity.darioOptimalCorrectorTwo_of_oscillation

-- Lemma 3.2 of Dario in dimension two from the quantitative sublinearity (1.22), Steps 1 and 2, and Theorem 1 of Dario from it
#print axioms Rigidity.Corrector.measurable_statAnchor
#print axioms Rigidity.Corrector.statGrad_translation
#print axioms Rigidity.Corrector.exists_lintegral_abs_statDiscrepancy_le
#print axioms Rigidity.Corrector.exists_lintegral_abs_statSegment_le
#print axioms Rigidity.Corrector.sum_statMean_period_eq_zero
#print axioms Rigidity.Corrector.darioLemmaThreeTwo_of_osc
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_osc

-- (1.18) and (1.22) in dimension two with minimal scales of class O_s (Armstrong and Dario, Lemma 5.8, (5.33)), and Lemma 3.2 of Dario with no hypothesis
#print axioms Rigidity.Proofs.Regularity.exists_isOsBond_of_events
#print axioms Rigidity.Proofs.Regularity.exists_restrictBad_os
#print axioms Rigidity.Proofs.Regularity.planarNuDefect_le_of_errors
#print axioms Rigidity.Proofs.Regularity.exists_planarFlatness_le_of_reach
#print axioms Rigidity.Proofs.Regularity.exists_flatnessBound_le
#print axioms Rigidity.Proofs.Regularity.exists_measure_flatnessBad_le
#print axioms Rigidity.Proofs.Regularity.exists_planarNuFlatness_os
#print axioms Rigidity.Proofs.Regularity.planarAffineApproximationTwo_of_subaddOs
#print axioms Rigidity.Proofs.Regularity.planarCorrectorSublinearL2Two_of_subaddOs
#print axioms Rigidity.Proofs.Regularity.exists_isOsBond_scale_le_three
#print axioms Rigidity.Proofs.Regularity.exists_corrector_sup_os
#print axioms Rigidity.Proofs.Regularity.eq_add_of_isCorrectedPlane
#print axioms Rigidity.Proofs.Regularity.planarCorrectorOscSublinearTwo_of_sublinearL2
#print axioms Rigidity.Proofs.Regularity.planarCorrectorOscSublinearTwo_of_subaddOs
#print axioms Rigidity.Proofs.Regularity.planarNuSubaddOsTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarCorrectorOscSublinearTwo_iff
#print axioms Rigidity.Proofs.Regularity.planarAffineApproximationTwo_holds
#print axioms Rigidity.Proofs.Regularity.planarCorrectorSublinearL2Two_holds
#print axioms Rigidity.Proofs.Regularity.planarCorrectorOscSublinearTwo_holds
#print axioms Rigidity.Corrector.correctorOscSublinearTwo_holds
#print axioms Rigidity.Corrector.darioLemmaThreeTwo_holds
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_lemmaThreeThree
#print axioms Rigidity.Corrector.correctorQuantitativeInputTwo_of_lemmaThreeThree

-- Localization, stationarity and limits of the subadditive quantity mu in every dimension, and the partition of Definition 3.9 (Armstrong and Dario, Section 4, Definition 3.9)
#print axioms Rigidity.Percolation.cubeMu_eq_of_equiv
#print axioms Rigidity.Percolation.cubeMu_eq_of_adj_iff_of_anchor_eq
#print axioms Rigidity.Percolation.cubeMu_shift_translation_of_partition
#print axioms Rigidity.Percolation.cappedCube_goodCubes_eq_of_localBonds
#print axioms Rigidity.Percolation.anchor_cappedCube_goodCubes_eq_of_localBonds
#print axioms Rigidity.Percolation.exists_measure_ne_cappedCube_goodCubes_le
#print axioms Rigidity.Percolation.exists_measure_cubeCappedDiscrepancy_le
#print axioms Rigidity.Percolation.exists_measure_not_cubeLocalGood_le
#print axioms Rigidity.Percolation.neg_cubeMu_le_latticeVolume_sq
#print axioms Rigidity.Percolation.cubeMuLoc_eq_of_good
#print axioms Rigidity.Percolation.measurable_cubeMuLoc_localBondSigma
#print axioms Rigidity.Percolation.indepFun_cubeMuLoc
#print axioms Rigidity.Percolation.exists_cubeMuLoc_localization
#print axioms Rigidity.Percolation.measurable_cubeNu_localBondSigma
#print axioms Rigidity.Percolation.indepFun_cubeNu
#print axioms Rigidity.Percolation.map_cubeMuStat_shift
#print axioms Rigidity.Percolation.indepFun_cubeMuStat
#print axioms Rigidity.Percolation.cubeMuStat_eq_of_good
#print axioms Rigidity.Percolation.exists_cubeMuStat_localization
#print axioms Rigidity.Percolation.exists_lintegral_neg_cubeMu_le_of_scale_eq
#print axioms Rigidity.Percolation.tendsto_lintegral_cubeMuLoc_of_tendsto
#print axioms Rigidity.Percolation.tendsto_lintegral_neg_cubeMu_of_tendsto
#print axioms Rigidity.Percolation.measurable_cubeMu_indicator
#print axioms Rigidity.Percolation.exceptionalMajorant_of_isExceptionalEdge
#print axioms Rigidity.Percolation.exceptionalEdgeCount_le
#print axioms Rigidity.Percolation.sum_cubeMu_subcubes_sub_le
#print axioms Rigidity.Percolation.exists_lintegral_sum_cubeMu_subcubes_sub_le
#print axioms Rigidity.Percolation.exists_lintegral_neg_cubeMu_le_of_scale_le
#print axioms Rigidity.Percolation.exists_tendsto_cubeMuMean
#print axioms Rigidity.Percolation.tendsto_lintegral_neg_cubeMu_of_scale
#print axioms Rigidity.Percolation.tendsto_lintegral_cubeMuLoc_of_scale
#print axioms Rigidity.Percolation.tendsto_lintegral_cubeMuStat_of_scale
#print axioms Rigidity.Proofs.Cluster.GeneralDim.exists_measure_stoppingScale_large_le
#print axioms Rigidity.Proofs.Cluster.GeneralDim.measurableSet_not_mem_meyersGood_local
#print axioms Rigidity.Proofs.Cluster.GeneralDim.exists_meyersFailureBound
#print axioms Rigidity.Proofs.Cluster.GeneralDim.meyersPartition_holds
#print axioms Rigidity.Percolation.cubeMuLimit_smul_add_smul
#print axioms Rigidity.Percolation.exists_cubeMuLimit_bounds
#print axioms Rigidity.Percolation.sum_mul_le_neg_cubeMu_add_cubeNu
#print axioms Rigidity.Percolation.exists_sum_mul_le_cubeMuMean_add_cubeNuMean
#print axioms Rigidity.Percolation.sum_mul_le_cubeMuLimit_add_cubeNuLimit
#print axioms Rigidity.Percolation.cubeMuLimit_ge_of_cubeAhom_eq_smul_one
#print axioms Rigidity.Percolation.exists_cubeMuLimit_two_sided

-- Lemma 3.3 of Dario in dimension two: the flip form of (3.13), Propositions 2.11 and 2.12 as an orthogonal projection, (3.22), (3.26), (3.27), and Cases 1 to 3 of Step 2
#print axioms Rigidity.Corrector.condExp_bondsExcept_ae_eq
#print axioms Rigidity.Corrector.ae_resampleVar_le_tsum_bondFlipDiff
#print axioms Rigidity.Corrector.lintegral_eq_setBond
#print axioms Rigidity.Corrector.IsOsBond.comp_setBond
#print axioms Rigidity.Corrector.darioLemmaThreeThree_of_flipSum
#print axioms Rigidity.Corrector.edgeDiv_greenProj
#print axioms Rigidity.Corrector.eq_greenProj_of_edgeDiv_eq
#print axioms Rigidity.Corrector.exists_isGradOf_greenProj
#print axioms Rigidity.Corrector.norm_greenProj_le
#print axioms Rigidity.Corrector.inner_greenProj_comm
#print axioms Rigidity.Corrector.greenProj_apply_eq_tsum
#print axioms Rigidity.Corrector.heatComp_coarse_eq_inner
#print axioms Rigidity.Corrector.abs_coarseHeatField_apply_le
#print axioms Rigidity.Corrector.abs_sub_coarseAnchor_zero_le
#print axioms Rigidity.Corrector.ae_abs_sub_coarseAnchor_le_of_finiteEnergy
#print axioms Rigidity.Corrector.laplacian_openGraph_eq_edgeDiv
#print axioms Rigidity.Corrector.localEnergy_le_of_isGradOf
#print axioms Rigidity.Corrector.edgeGrad_eq_smul_greenProj_of_div
#print axioms Rigidity.Corrector.ae_sublinearOn_of_isGradOf
#print axioms Rigidity.Corrector.ae_edgeGrad_eq_smul_greenProj_of_div
#print axioms Rigidity.Corrector.ae_edgeGrad_eq_smul_greenProj
#print axioms Rigidity.Corrector.edgeDiv_edgeGrad_setBond
#print axioms Rigidity.Corrector.ae_setBond
#print axioms Rigidity.Corrector.mem_supp_iff_of_mem_supp_setBond_false
#print axioms Rigidity.Corrector.ae_correctedPlane_sub_eq_smul_greenProj
#print axioms Rigidity.Corrector.heatComp_coarse_eq_smul_greenProj
#print axioms Rigidity.Corrector.ae_heatComp_coarse_sub_eq_smul_greenProj
#print axioms Rigidity.Corrector.abs_sub_le_two_mul_edgeVariation
#print axioms Rigidity.Corrector.heatComp_coarse_eq_smul_inner_greenProj
#print axioms Rigidity.Corrector.edgeDiv_pathField
#print axioms Rigidity.Corrector.ae_correctedPlane_sub_eq_smul_greenProj_closed
#print axioms Rigidity.Corrector.ae_heatComp_coarse_sub_eq_walkSum_closed
#print axioms Rigidity.Corrector.isCorrectedPlane_of_harmonic
#print axioms Rigidity.Corrector.le_of_finite_piece
#print axioms Rigidity.Corrector.ae_exists_correctedPlane_eq_add_const

-- The multiscale Poincare inequality (2.26) on the square lattice and Theorem 1 of Dario and its consequences from Lemma 3.3 alone
#print axioms Rigidity.Poincare.multiscalePoincareTwo_holds
#print axioms Rigidity.Poincare.exists_multiscalePoincare_box
#print axioms Rigidity.Poincare.exists_steinSigned
#print axioms Rigidity.Poincare.tsum_boxMax_rpow_le
#print axioms Rigidity.Poincare.tsum_mul_eq_add_integral
#print axioms Rigidity.Poincare.exists_ofReal_sq_heatGrad_le
#print axioms Rigidity.Poincare.ofReal_abs_integral_le
#print axioms Rigidity.Poincare.darioOptimalCorrectorTwo_of_concentration
#print axioms Rigidity.Poincare.darioOptimalCorrectorTwo_of_threeThree
#print axioms Rigidity.Poincare.darioOptimalCorrectorTwo_of_flipSum
#print axioms Rigidity.Poincare.correctorQuantitativeInputTwo_of_threeThree
#print axioms Rigidity.Poincare.correctorQuantitativeInputTwo_of_flipSum
#print axioms Rigidity.Poincare.armstrongDarioOrderOneOriginTwo_of_threeThree
#print axioms Rigidity.Poincare.armstrongDarioOrderOneOriginTwo_of_flipSum
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_reduced_threeThree
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_reduced_flipSum

-- The concentration inequality (Proposition 2.17 of Dario; Armstrong and Lin, Proposition 2.2)
#print axioms Rigidity.Corrector.concentrationTwo_holds
#print axioms Rigidity.Probability.lintegral_abs_sub_rpow_le_vertSum
#print axioms Rigidity.Probability.lintegral_exp_rpow_le_of_moments
#print axioms Rigidity.Probability.cubeExp_abs_sub_rpow_le
#print axioms Rigidity.Probability.rpowEntropy_le_sum_coordEntropy
#print axioms Rigidity.Probability.bregmanRpow_convex
#print axioms Rigidity.Probability.condExp_allExcept_ae_eq
#print axioms Rigidity.Probability.vertical_condExp_ae_eq
#print axioms Rigidity.Corrector.darioOptimalCorrectorTwo_of_poincare_osc

-- Lemmas 5.3 and 5.4, (5.21)-(5.24) and Step 1(a) of Lemma 5.10 of Armstrong and Dario in every dimension
#print axioms Rigidity.Percolation.abs_slopeQuadratic_sub_half_le
#print axioms Rigidity.Percolation.isSlopeQuadratic_of_eq_dotProduct
#print axioms Rigidity.Percolation.IsSlopeQuadratic.comp_mulVec
#print axioms Rigidity.Percolation.cubeMu_eq_sum_polarization
#print axioms Rigidity.Percolation.sum_mul_le_neg_cubeMu_add_cubeNu_add_mul
#print axioms Rigidity.Percolation.neg_cubeMu_le_cubeMuBound_mul
#print axioms Rigidity.Percolation.cubeOmega_le_cubeRho_mul
#print axioms Rigidity.Percolation.neg_le_cubeOmega
#print axioms Rigidity.Percolation.cube_minimalset
#print axioms Rigidity.Percolation.exceptionalPairing_le
#print axioms Rigidity.Percolation.cubeMuDefect_add_sum_sub_le
#print axioms Rigidity.Percolation.exists_integral_subaddBound_le
#print axioms Rigidity.Percolation.exists_integral_neg_cubeMu_le_of_scale_eq
#print axioms Rigidity.Percolation.exists_lintegral_cubeMuDefect_le
#print axioms Rigidity.Percolation.IsSlopeQuadratic.le_of_nonneg
#print axioms Rigidity.Percolation.isSlopeQuadratic_integral
#print axioms Rigidity.Percolation.isSlopeQuadratic_cubeMuMean
#print axioms Rigidity.Percolation.exists_cubeMuIncrement_le
#print axioms Rigidity.Percolation.exists_cubeNuIncrement_le
#print axioms Rigidity.Percolation.exists_lintegral_cubeMuDefect_le_tau
#print axioms Rigidity.Percolation.exists_lintegral_cubeNuDefect_le_tau
#print axioms Rigidity.Percolation.half_sum_mul_cubeAhomInvFinite_eq
#print axioms Rigidity.Percolation.exists_abs_cubeMuMean_sub_le
#print axioms Rigidity.Percolation.exists_abs_cubeAhomInvFinite_sub_le
#print axioms Rigidity.Percolation.summable_cubeTau
#print axioms Rigidity.Percolation.tendsto_cubeAhomInvFinite
#print axioms Rigidity.Percolation.exists_abs_cubeAhomInvLimit_sub_le
#print axioms Rigidity.Percolation.isSlopeQuadratic_cubeMuLimit
#print axioms Rigidity.Percolation.exists_cubeAhomInvFinite_bounds
#print axioms Rigidity.Percolation.IsSlopeQuadratic.add_sub_sub_eq
#print axioms Rigidity.Percolation.cubeCoarsePairing_cubeMuMinimizer_div
#print axioms Rigidity.Percolation.integral_cubeCoarsePairing_cubeMuMinimizer
#print axioms Rigidity.Percolation.exists_cubeAhomInvFinite_mul_cubeAhomFinite
#print axioms Rigidity.Percolation.cubeMuMean_cubeAhomFinite_sub_le
#print axioms Rigidity.Percolation.cubeOmegaD_succ_le

-- Propositions A.7, 2.15 and 2.7 (weak form) of Dario and Gu, Lemma 4.1 from Theorem 3, and Theorem 1 in dimension two from Propositions 4.3, Theorem 3, Theorem 4 and Lemma 3.3
#print axioms Rigidity.Green.darioGuDensityGaussianTwo_holds
#print axioms Rigidity.Green.carneVaropoulosTwo_holds
#print axioms Rigidity.Green.clusterPoincareTwo_holds
#print axioms Rigidity.Green.darioGuApproxLemmaTwo_of_inputs
#print axioms Rigidity.Green.darioGuApproxLemmaTwo_of_gradient
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_approx_twoScale
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_approx_twoScale_dario
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_twoScale_gradient
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_twoScale_gradient_dario
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_twoScale_gradient_barlow
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_twoScale_gradient_barlow_dario
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_twoScale_gradient_barlow_poincare
#print axioms Rigidity.Green.darioGuHeatKernelTwo_of_twoScale_gradient_barlow_poincare_dario
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_twoScale_gradient_barlow_threeThree
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_twoScale_gradient_barlow_flipSum

-- Lemma 3.3 of Dario in dimension two: the heat square sum, Lemma 3.5 for the planar partition, the split (3.15), Steps 1 and 2 and the reduction of (3.13) to Lemma 3.5 and the Step 2 sum
#print axioms Rigidity.Corrector.exists_tsum_latticeHeat_sq_le
#print axioms Rigidity.Percolation.TriadicCube.planarAnchor_eq_of_agree_off
#print axioms Rigidity.Corrector.planarPartCube_eq_and_anchor_eq_of_resample
#print axioms Rigidity.Corrector.resampleLocal_of_bound
#print axioms Rigidity.Corrector.sq_tsum_partitionChange_le
#print axioms Rigidity.Corrector.bondFlipDiff_heatCoarseComp_eq
#print axioms Rigidity.Corrector.sq_bondFlipDiff_heatCoarseComp_le
#print axioms Rigidity.Corrector.ae_heatComp_coarse_sub_eq_zero
#print axioms Rigidity.Corrector.bondFlipDiff_eq_flipTermOne_add_flipTermTwo
#print axioms Rigidity.Corrector.flipTermOne_eq_tsum_partitionChange
#print axioms Rigidity.Corrector.darioFlipSumBound_of_terms
#print axioms Rigidity.Corrector.ae_flipSeries_summable
#print axioms Rigidity.Corrector.darioFlipSumBound_of_sums
#print axioms Rigidity.Corrector.ae_summable_heat_stepRegion
#print axioms Rigidity.Corrector.summable_heat_coarse_of_le
#print axioms Rigidity.Corrector.ae_flipTermTwoSummable
#print axioms Rigidity.Corrector.darioFlipSumBound_of_stepSums
#print axioms Rigidity.Corrector.flipTermOne_sq_le
#print axioms Rigidity.Corrector.isOsBond_heatSqSum_of_moments
#print axioms Rigidity.Corrector.flipTermOne_sq_le_of_bound
#print axioms Rigidity.Corrector.ae_flipSumOne_le
#print axioms Rigidity.Corrector.flipSumOne_isOsBond_of_moments
#print axioms Rigidity.Corrector.lintegral_tsum_rpow_le_of_decay
#print axioms Rigidity.Corrector.tsum_exp_neg_norm_bondBase_le
#print axioms Rigidity.Corrector.measure_le_mul_stoppingSize_le
#print axioms Rigidity.Corrector.lintegral_indicator_rpow_le
#print axioms Rigidity.Corrector.lintegral_randomBallSum_rpow_le_of_growth
#print axioms Rigidity.Corrector.stepOne_lipschitz_data
#print axioms Rigidity.Corrector.stepOneFactor_eq_self
#print axioms Rigidity.Corrector.measurable_stepOneFactorSelf
#print axioms Rigidity.Corrector.stepOneFactorSelf_le
#print axioms Rigidity.Corrector.stepOneW_moments
#print axioms Rigidity.Corrector.flipSumOne_isOsBond_of_resample
#print axioms Rigidity.Corrector.darioFlipSumBound_of_resample

-- Proposition 4.3 of Dario and Gu in dimension two from the weak norm of the flux (Proposition 2.13) and the quantitative corrector estimate, and Theorem 1 of Dario and Gu from these
#print axioms Rigidity.Green.weakNormLe_translatedFlux
#print axioms Rigidity.Green.darioGuTranslatedFluxTwo_of_inputs
#print axioms Rigidity.Green.dgWeight_bound
#print axioms Rigidity.Green.dgWeightTrunc_edgeKappa_bound
#print axioms Rigidity.Green.openLaplacian_twoScale
#print axioms Rigidity.Green.openLaplacian_twoScale_of_corrector
#print axioms Rigidity.Green.hasDerivAt_dgTwoScale_eq
#print axioms Rigidity.Green.tsum_energy_deriv_le
#print axioms Rigidity.Green.energy_first_pass
#print axioms Rigidity.Green.energy_second_pass
#print axioms Rigidity.Green.clusterW_first_pass
#print axioms Rigidity.Green.clusterW_second_pass
#print axioms Rigidity.Green.dgW_weightedL2Le_of_sourceBound
#print axioms Rigidity.Green.darioGuTwoScaleErrorTwo_of_sourceBound
#print axioms Rigidity.Green.abs_fwdDiff_fwdDiff_latticeGaussian_le
#print axioms Rigidity.Green.abs_fwdDiff_latticeGaussianTimeDeriv_le
#print axioms Rigidity.Green.abs_fwdDiff_fwdDiff_fwdDiff_latticeGaussian_le
#print axioms Rigidity.Green.tsum_weightGauss_le
#print axioms Rigidity.Green.tsum_sq_clusterF_le
#print axioms Rigidity.Green.tsum_sq_clusterFlux_le
#print axioms Rigidity.Green.tsum_source_le_of_split
#print axioms Rigidity.Green.neg_sum_le_of_weakNormLe
#print axioms Rigidity.Green.neg_tsum_le_of_weakNormLe_coeff
#print axioms Rigidity.Green.neg_tsum_le_of_pieces
#print axioms Rigidity.Green.neg_tsum_flux_le
#print axioms Rigidity.Green.darioGuTwoScaleSourceBoundTwo_of_fluxTerm
#print axioms Rigidity.Green.darioGuTwoScaleErrorTwo_of_fluxTerm
#print axioms Rigidity.Green.darioGuTwoScaleFluxTermTwo_of_inputs
#print axioms Rigidity.Green.darioGuTwoScaleErrorTwo_of_inputs
#print axioms Rigidity.Green.exists_darioGuTwoScaleErrorTwo_of_inputs
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow_threeThree
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow_flipSum
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow_resample

-- Lemma 3.5 of Dario for the planar partition, and Theorem 1 of Dario, Proposition 2.12 of Dario and Gu, Theorem 2 (iii) at k = 1 and Theorem 1 of Dario and Gu in dimension two from the Step 2 sum of Lemma 3.3
#print axioms Rigidity.Corrector.resamplePartitionBound_holds
#print axioms Rigidity.Corrector.darioResamplePartitionTwo_holds
#print axioms Rigidity.Poincare.darioFlipSumBound_of_stepTwo
#print axioms Rigidity.Poincare.darioOptimalCorrectorTwo_of_stepTwo
#print axioms Rigidity.Poincare.correctorQuantitativeInputTwo_of_stepTwo
#print axioms Rigidity.Poincare.armstrongDarioOrderOneOriginTwo_of_stepTwo
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_reduced_stepTwo
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow_stepTwo

-- The Meyers estimate with a divergence source on a cube of the cluster, in place of Proposition 3.6 of Dario (d = 2)
#print axioms Rigidity.Corrector.openGraph_restrictConfig_adj
#print axioms Rigidity.Corrector.greenProj_apply_of_not_open
#print axioms Rigidity.Corrector.norm_greenProj_le_restrictField
#print axioms Rigidity.Corrector.openLaplacian_localSolution
#print axioms Rigidity.Corrector.openLaplacian_sub_eq_zero
#print axioms Rigidity.Corrector.sum_clusterEnergy_localSolution_le
#print axioms Rigidity.Corrector.meyers_source

-- The Step 2 sum of Lemma 3.3 of Dario bounded by a weighted energy (d = 2)
#print axioms Rigidity.Corrector.ae_flipTermTwo_eq_walkSum
#print axioms Rigidity.Corrector.ae_flipTermTwo_eq_zero
#print axioms Rigidity.Corrector.ae_flipTermTwo_eq_open
#print axioms Rigidity.Corrector.ae_dipoleCoeff_eq
#print axioms Rigidity.Corrector.ae_flipTermTwo_sq_le_closed
#print axioms Rigidity.Corrector.ae_flipTermTwo_sq_le_open
#print axioms Rigidity.Corrector.ae_flipTermTwo_sq_le_weight
#print axioms Rigidity.Corrector.ae_flipSumTwo_le

-- The summation of estimate (2) over a partition with comparable neighbours (d = 2)
#print axioms Rigidity.Corrector.IsCellScale.le_of_mem_enl
#print axioms Rigidity.Corrector.IsCellScale.tsum_enl_le
#print axioms Rigidity.Corrector.IsCellScale.tsum_eq_tsum_avg
#print axioms Rigidity.Corrector.sum_weight_energy_le_of_meyersCube
#print axioms Rigidity.Corrector.tsum_weight_energy_le
#print axioms Rigidity.Corrector.openLaplacian_clusterPot
#print axioms Rigidity.Corrector.tsum_clusterOpenEnergy_le
#print axioms Rigidity.Corrector.tsum_mul_edgeSq_le
#print axioms Rigidity.Corrector.isCellScale_partScale
#print axioms Rigidity.Corrector.flipSumTwo_le_of_partition

-- A local bound for the gradients of harmonic functions on the planar cluster
#print axioms Rigidity.Corrector.localGrad_le
#print axioms Rigidity.Corrector.abs_sub_le_localGrad
#print axioms Rigidity.Corrector.localGrad_eq_of_adj_iff
#print axioms Rigidity.Corrector.measurable_localGrad
#print axioms Rigidity.Corrector.mem_localCluster_of_infinite
#print axioms Rigidity.Corrector.abs_correctorDiff_le_localGrad
#print axioms Rigidity.Corrector.planeGrad_le_localGrad
#print axioms Rigidity.Corrector.measure_not_localGradGood_le
#print axioms Rigidity.Corrector.localGrad_le_of_orderZero
#print axioms Rigidity.Corrector.ae_localGrad_le
#print axioms Rigidity.Corrector.growthMoments_localGrad

-- The weight of the Step 2 sum: majorant, moments and finite-range approximation (d = 2)
#print axioms Rigidity.Corrector.growthMoments_weightMajorant
#print axioms Rigidity.Corrector.stepTwoWeight_le_weightMajorant
#print axioms Rigidity.Corrector.planarSide_eq_cappedSide
#print axioms Rigidity.Corrector.cappedSide_eq_of_localBonds
#print axioms Rigidity.Corrector.measure_exists_planarCappedDiscrepancy_le
#print axioms Rigidity.Corrector.planeGrad_translation
#print axioms Rigidity.Corrector.siteGrad_eq_of_localBonds
#print axioms Rigidity.Corrector.planeGrad_le_siteGrad
#print axioms Rigidity.Corrector.stepTwoFactor_le_of_bound
#print axioms Rigidity.Corrector.finiteWeight_le
#print axioms Rigidity.Corrector.finiteWeight_eq_of_localBonds
#print axioms Rigidity.Corrector.stepTwoWeight_le_finiteWeight

-- The finite-range weight: good events, uniform moments and concentration over a cube (d = 2)
#print axioms Rigidity.Corrector.measure_not_farGood_le
#print axioms Rigidity.Corrector.measure_not_sideGood_le
#print axioms Rigidity.Corrector.measure_not_gradGood_le
#print axioms Rigidity.Corrector.growthMoments_weightMajorant_uniform
#print axioms Rigidity.Corrector.growthMoments_siteLambda
#print axioms Rigidity.Corrector.finiteWeight_le_weightMajorant
#print axioms Rigidity.Corrector.exists_lintegral_finiteWeight_rpow_le
#print axioms Rigidity.Corrector.indepFun_sum_of_local
#print axioms Rigidity.Corrector.sum_vertices_add_smul_eq
#print axioms Rigidity.Corrector.measureReal_sum_cube_gt_le
#print axioms Rigidity.Corrector.measurable_stepTwoWeight
#print axioms Rigidity.Corrector.measurableSet_mem_stepTwoGood

-- The partition of the good cubes of the summation of estimate (2) (d = 2)
#print axioms Rigidity.Corrector.measure_not_domGood_le
#print axioms Rigidity.Corrector.weightGood_of_domGood
#print axioms Rigidity.Corrector.measure_not_weightGood_le_of_bounds
#print axioms Rigidity.Corrector.exists_measure_not_weightGood_le
#print axioms Rigidity.Corrector.exists_measure_not_mem_stepTwoGood_le
#print axioms Rigidity.Corrector.exists_stepTwoGood_partition

-- The Step 2 sum of Lemma 3.3 of Dario and Theorem 1 of Dario (d = 2)
#print axioms Rigidity.Corrector.GrowthMoments.mul
#print axioms Rigidity.Corrector.growthMoments_of_exp_moment
#print axioms Rigidity.Corrector.pathWeight_le_ballSum
#print axioms Rigidity.Corrector.planeGrad_le_of_lipschitz
#print axioms Rigidity.Corrector.growthMoments_planarBallSum
#print axioms Rigidity.Poincare.exists_stepTwo_weight_data
#print axioms Rigidity.Poincare.darioStepTwoSumBound_holds
#print axioms Rigidity.Poincare.darioOptimalCorrectorTwo_holds
#print axioms Rigidity.Poincare.correctorQuantitativeInputTwo_holds
#print axioms Rigidity.Poincare.armstrongDarioOrderOneOriginTwo_holds
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_sections_barlow
#print axioms Rigidity.Poincare.darioGuHeatKernelTwo_of_flux_gradient_barlow

-- Theorem 1.3 from the quantitative Green estimate of Dario and Gu (d = 2)
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay_of_greenQuantitative
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay_of_darioGu
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay_of_sections_barlow
#print axioms Rigidity.Assembly.WithPlanarInputs.fast_decay_of_flux_gradient_barlow

-- Proposition 2.12 of Dario and Gu in every dimension from Theorem 1 of Dario in dimension d >= 3
#print axioms Rigidity.Corrector.GeneralDim.correctorQuantitativeInput_of_dario

-- The concentration inequality of Dario (Proposition 2.17) in every dimension
#print axioms Rigidity.Corrector.GeneralDim.concentration_holds

-- Proposition 2.7 (second part) of Dario and Gu in dimension two and Steps 1, 2, 3 and 5 of the proof of Theorem 5
#print axioms Rigidity.Green.sum_neg_openLaplacian_mul
#print axioms Rigidity.Green.sum_mul_le_of_weakNormLe
#print axioms Rigidity.Green.integral_sum_sq_le_of_energy
#print axioms Rigidity.Green.weakNormLe_sqrt_sum_sq
#print axioms Rigidity.Green.WeakNormLe.mul_right
#print axioms Rigidity.Green.weakNormLe_sum_antisymm
#print axioms Rigidity.Green.openLaplacian_cutoffTwoScale
#print axioms Rigidity.Green.openLaplacian_cutoffTwoScale_of_corrector
#print axioms Rigidity.Green.timeDeriv_sub_openLaplacian_cutoffTwoScale
#print axioms Rigidity.Green.weakNormLe_div_field
#print axioms Rigidity.Green.weakNormLe_time_term
#print axioms Rigidity.Green.weakNormLe_flux_term
#print axioms Rigidity.Green.weakNormLe_twoScale_equation
#print axioms Rigidity.Green.clusterDirichletPoincareTwo_holds
#print axioms Rigidity.Green.sum_sq_le_of_weakPoincare
#print axioms Rigidity.Green.sum_sq_twoScale_sub_le
#print axioms Rigidity.Green.integral_sum_sq_le_of_dirichletPoincare
#print axioms Rigidity.Green.dgStepFive
#print axioms Rigidity.Green.abs_discrete_div_sub_le
#print axioms Rigidity.Green.weakNormLe_term_a

-- Theorem 3 of Dario and Gu (Remark 1.3) from Proposition 3.9 and Theorem 4, and Proposition 2.9 and Lemma 2.10 (unnormalized), in dimension two
#print axioms Rigidity.Green.darioGuGradientBoundTwo_of_lipschitz
#print axioms Rigidity.Green.goodTimes_anchorDist
#print axioms Rigidity.Green.abs_coarsenPar_openHeat_le
#print axioms Rigidity.Green.darioGuCaccioppoliTwo_holds
#print axioms Rigidity.Green.parabolic_caccioppoli_of_cutoff
#print axioms Rigidity.Green.darioGuTimesliceTwo_holds
#print axioms Rigidity.Green.timeslice_of_cutoff
