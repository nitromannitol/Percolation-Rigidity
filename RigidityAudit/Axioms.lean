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
steps of the homogenization of the Dirichlet problem and of the excess-decay iteration (§§6–7);
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
