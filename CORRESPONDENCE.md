# Correspondence with the cited works

This file maps the numbered results of the works cited below, which this repository states or proves, to
its Lean declarations, and records where the Lean proofs depart from the paper or from the cited source.
The paper is

> Ahmed Bou-Rabee, William Cooperman and Paul Dario, *Rigidity of harmonic functions on the supercritical
> percolation cluster*, Transactions of the American Mathematical Society 378(6) (2025), 3823–3896;
> [arXiv:2303.04736](https://arxiv.org/abs/2303.04736)

and the statements follow a corrected draft of its arXiv v2 source. The changes to the statements of the paper
are the corrections C1–C39 of [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md), which are not repeated here;
the same file lists the three places where the Lean proofs do not follow the printed argument of the paper.
The numbered results of the paper are mapped in [All numbered results](README.md#all-numbered-results).

The cited works whose results are formalized here are

> P. Dario, *Optimal corrector estimates on percolation clusters*, Ann. Appl. Probab. 31 (2021), 377–431;
> [arXiv:1805.00902](https://arxiv.org/abs/1805.00902)

> P. Dario and C. Gu, *Quantitative homogenization of the parabolic and elliptic Green's functions on
> percolation clusters*, Ann. Probab. 49 (2021); [arXiv:1909.10439v4](https://arxiv.org/abs/1909.10439)

and, with the citations given in the README, the Gaussian upper bound of M. T. Barlow, *Random walks on
supercritical percolation clusters*, Ann. Probab. 32 (2004), and Proposition 1.1 of Gu, *An efficient algorithm
for solving elliptic problems on percolation clusters*, arXiv:1907.13571. "Dario" and "DG" below are the first two
works. The numbering of Dario and of DG is that of their arXiv sources as compiled, which counts every numbered
equation, and `Dario18.tex:n` and `DG21.tex:n` are line numbers in those sources; the numbering of Barlow is
the one used in the sections of the [README](README.md) on his Gaussian upper bound. The results of S. Armstrong and
P. Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*, Comm. Pure Appl. Math.
71 (2018), arXiv:1609.09431, are formalized in
[Percolation-Cluster-Homogenization](https://github.com/nitromannitol/Percolation-Cluster-Homogenization), on
which this library is built; their correspondence is in its
[`CORRESPONDENCE.md`](https://github.com/nitromannitol/Percolation-Cluster-Homogenization/blob/main/CORRESPONDENCE.md),
and the results of the three works above use them as stated there.

Throughout, `d ≥ 2`, each edge of `ℤᵈ` is open independently with probability `p ∈ (𝔭_c(d), 1)`, and the law
is `LatticeProb.Percolation.latticeBondLaw d p`. "No hypothesis" in the last column means that the declaration
assumes only this regime. A declaration whose name ends in `Two` is the statement or theorem for `d = 2`, one
ending in `Three` for `d ≥ 3`, and one ending in `D` for a general `d`; `CorrectorQuantitativeInput`,
`SupercriticalBondGreenQuantitative` and the planar statements `CorrectorQuantitativeInputTwo` and
`SupercriticalBondGreenQuantitativeTwo` are stated in Percolation-Cluster-Homogenization and Lattice-Probability.
`X ≤ O_s(C)` is the stretched exponential integrability of the sources. The named hypotheses that
remain open for `d ≥ 3` are collected in the last section. Each declaration is linked to its file; the axiom
report of the library is [`RigidityAudit/Axioms.lean`](RigidityAudit/Axioms.lean).

## Dario

| Dario | Lean declaration | Form |
| --- | --- | --- |
| Theorem 1, (1.2) | [`Rigidity.Poincare.darioOptimalCorrectorTwo_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean); [`Rigidity.Corrector.GeneralDim.darioOptimalCorrectorThree_of_varianceBound`](Rigidity/Proofs/Corrector/GeneralLemmaThreeTwoProof.lean), [`Rigidity.Corrector.GeneralDim.darioOptimalCorrectorThree_of_prop31`](Rigidity/Proofs/Corrector/GeneralHeatSmoothing.lean), [`Rigidity.Corrector.GeneralDim.darioOptimalCorrectorThree_of_baseTheorem`](Rigidity/Proofs/Corrector/GeneralPartitionComparison.lean), [`Rigidity.Corrector.GeneralDim.darioOptimalCorrectorThree_of_coarsened`](Rigidity/Proofs/Corrector/GeneralDarioOptimalCorrector.lean) | `d = 2`: `DarioOptimalCorrectorTwo`, `\|χ_q(x) − χ_q(y)\| 1_{x,y ∈ 𝒞_∞} ≤ O_s(C ‖q‖₁ √(log(2 + ‖x − y‖)))`, no hypothesis. `d ≥ 3`: `DarioOptimalCorrectorThree`, `\|χ_q(x) − χ_q(y)\| ≤ O_s(C\|q\|)`, from Lemma 3.3 (`DarioVarianceBoundThree`), from Proposition 3.1 (`DarioPropThreeOneThree`), from (5.5) alone, or from the coarsened corrector data; hypotheses of Lemma 3.3 for `d ≥ 3`: `DarioResamplePartitionThree`, `DarioStepTwoWeightThree` |
| Section 5, Steps 1–6 of the proof of Theorem 1; (5.1) | [`Rigidity.Corrector.LinftyIterationData.mom_sub_le`](Rigidity/Proofs/Corrector/DarioLinftyIteration.lean) (Steps 1–4), [`Rigidity.Corrector.isOsBond_of_moment_le`](Rigidity/Proofs/Corrector/DarioMoments.lean) (Step 5), [`Rigidity.Corrector.IsOsBond.integral_rpow_le`](Rigidity/Proofs/Corrector/DarioMoments.lean) ((5.1)), [`Rigidity.Corrector.darioOptimalCorrectorTwo_of_coarsened`](Rigidity/Proofs/Corrector/DarioOptimalCorrector.lean) (Step 6); [`Rigidity.Corrector.GeneralDim.LinftyIterationData.mom_sub_le`](Rigidity/Proofs/Corrector/GeneralLinftyIteration.lean), `GeneralDim.darioOptimalCorrectorThree_of_coarsened` | moment form of the iteration; `d = 2` and `d ≥ 3`, no hypothesis beyond the coarsened corrector data |
| (5.7), (5.10) | [`Rigidity.Corrector.baseComparison`](Rigidity/Proofs/Corrector/PlanarPartitionComparison.lean), [`Rigidity.Corrector.baseCoarseningError`](Rigidity/Proofs/Corrector/PlanarCoarseningError.lean); [`Rigidity.Corrector.GeneralDim.baseComparison`](Rigidity/Proofs/Corrector/GeneralPartitionComparison.lean), [`Rigidity.Corrector.GeneralDim.baseCoarseningError`](Rigidity/Proofs/Corrector/GeneralCoarseningError.lean) | the comparison of the translated partitions and the coarsening error, `d = 2` and every `d ≥ 2`; no hypothesis |
| (2.3) | [`Rigidity.Corrector.correctorDiff_translation`](Rigidity/Proofs/Corrector/PlanarMeasurableCorrector.lean) | stationarity of the measurable corrector increments, `d = 2` |
| Theorem 2, Step 1 of its proof (Section 4), (5.4), (5.5) | [`Rigidity.Corrector.lintegral_boxOsc_le_of_poincare`](Rigidity/Proofs/Corrector/DarioPoincareMoments.lean); [`Rigidity.Corrector.GeneralDim.lintegral_boxOsc_le_of_poincare_three`](Rigidity/Proofs/Corrector/GeneralPoincareMoments.lean) | moment form, from (2.26) (`PoincareCube`), Proposition 3.1 (for `r ≥ 1`) and (2.22) (for `r ≤ 1`); `d = 2` and `d ≥ 3` |
| Propositions 2.11 and 2.12, (2.14), (2.15), (2.17) | [`Rigidity.Corrector.greenProj`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`Rigidity.Corrector.edgeDiv_greenProj`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`Rigidity.Corrector.norm_greenProj_le`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`Rigidity.Corrector.inner_greenProj_comm`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`Rigidity.Corrector.greenProj_apply_eq_tsum`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean); [`Rigidity.Corrector.GeneralDim.greenProj`](Rigidity/Proofs/Corrector/GeneralClusterGreen.lean), [`Rigidity.Corrector.GeneralDim.edgeDiv_greenProj`](Rigidity/Proofs/Corrector/GeneralClusterGreen.lean), [`Rigidity.Corrector.GeneralDim.norm_greenProj_le`](Rigidity/Proofs/Corrector/GeneralClusterGreen.lean) | the gradient of the Green function of the open graph as an orthogonal projection, with `C = 1` in (2.14); `d = 2` and every `d ≥ 2`; no hypothesis |
| Proposition 2.14 | the order-zero regularity of Armstrong and Dario, Theorem 2 (iii) at `k = 0`, in Percolation-Cluster-Homogenization | every `d ≥ 2`, no hypothesis; used by the Lipschitz bound below |
| Proposition 2.15, (2.20)–(2.22) | [`Rigidity.Corrector.lipschitz_correctedPlane_origin`](Rigidity/Proofs/Corrector/PlanarCorrectorLipschitz.lean); [`Rigidity.Corrector.GeneralDim.lipschitz_correctedPlane_origin`](Rigidity/Proofs/Corrector/GeneralCorrectorLipschitz.lean) | at the origin, `d = 2` and every `d ≥ 2`, from the order-zero regularity |
| Proposition 2.17 | [`Rigidity.Corrector.concentrationTwo_holds`](Rigidity/Proofs/Corrector/ConcentrationTwoHolds.lean); [`Rigidity.Corrector.GeneralDim.concentration_holds`](Rigidity/Proofs/Corrector/Concentration.lean); [`Rigidity.Probability.lintegral_abs_sub_rpow_le_vertSum`](Rigidity/Proofs/Probability/BernoulliMoments.lean), [`Rigidity.Probability.lintegral_exp_rpow_le_of_moments`](Rigidity/Proofs/Probability/StretchedExponential.lean) | `d = 2` and every `d ≥ 2`; `p ∈ (0, 1)`, `β ∈ (0, 2)`, `C = C(p, β)`; no hypothesis |
| Proposition 2.19, (2.26) | [`Rigidity.Poincare.multiscalePoincareTwo_holds`](Rigidity/Proofs/Poincare/MultiscalePoincareHolds.lean); [`Rigidity.Poincare.GeneralDim.multiscalePoincare_holds`](Rigidity/Proofs/Poincare/GeneralMultiscalePoincare.lean) | the lattice inequality in the cube form, `d = 2` and every `d ≥ 2`; no hypothesis |
| Proposition 3.1 | [`Rigidity.Corrector.darioPropThreeOneTwo_of_lemmas`](Rigidity/Proofs/Corrector/DarioPropThreeOne.lean); `GeneralDim.darioOptimalCorrectorThree_of_prop31` | `d = 2` from Lemmas 3.2 and 3.3 and the concentration inequality; `d ≥ 3` as `DarioPropThreeOneThree` |
| Lemma 3.2, (3.3) | [`Rigidity.Corrector.darioLemmaThreeTwo_holds`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean); [`Rigidity.Corrector.GeneralDim.darioMeanBound`](Rigidity/Proofs/Corrector/GeneralLemmaThreeTwoProof.lean); [`Rigidity.Percolation.dario_errorstatpart`](Rigidity/Proofs/Corrector/DarioStationaryPartition.lean), [`Rigidity.Corrector.GeneralDim.dario_errorstatpart`](Rigidity/Proofs/Corrector/GeneralStationaryCoarsening.lean) | `d = 2` and every `d ≥ 2`, from (1.22) of Armstrong and Dario; no hypothesis |
| Lemma 3.3, (3.12)–(3.15) | [`Rigidity.Corrector.darioLemmaThreeThree_of_flipSum`](Rigidity/Proofs/Corrector/DarioLemmaThreeThreeFlip.lean), [`Rigidity.Corrector.darioFlipSumBound_of_resample`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean), [`Rigidity.Corrector.ae_resampleVar_le_tsum_bondFlipDiff`](Rigidity/Proofs/Corrector/DarioBondResampling.lean), [`Rigidity.Corrector.bondFlipDiff_eq_flipTermOne_add_flipTermTwo`](Rigidity/Proofs/Corrector/DarioFlipSumTerms.lean); [`Rigidity.Corrector.GeneralDim.darioVarianceBoundThree_of_weight`](Rigidity/Proofs/Corrector/GeneralStepTwoReduce.lean), [`Rigidity.Corrector.GeneralDim.darioVarianceBoundThree_of_sums`](Rigidity/Proofs/Corrector/GeneralVarianceSums.lean) | `d = 2`: no hypothesis, from the flip form `DarioFlipSumBound` with Lemma 3.5 for the planar partition and the Step 2 sum `DarioStepTwoSumBound`, which is proved. `d ≥ 3`: `DarioVarianceBoundThree` from the sums of Steps 1 and 2, under `DarioResamplePartitionThree` and `DarioStepTwoWeightThree` |
| Lemma 3.3, Step 1, (3.16)–(3.19) | [`Rigidity.Corrector.resampleLocal_of_bound`](Rigidity/Proofs/Corrector/DarioStepOneLocal.lean), [`Rigidity.Corrector.flipTermOne_sq_le`](Rigidity/Proofs/Corrector/DarioStepOneLipschitz.lean), [`Rigidity.Corrector.flipSumOne_isOsBond_of_resample`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean), [`Rigidity.Corrector.stepOneW_moments`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean); [`Rigidity.Corrector.GeneralDim.darioStepOneSumBoundThree_of_resample`](Rigidity/Proofs/Corrector/GeneralStepOneHolds.lean) | the sum `Σ_e T₁(e)²` is `O_s(C/r²)` given Lemma 3.5 in the form `ResamplePartitionBound` (`d = 2`) or `DarioResamplePartitionThree` (`d ≥ 3`) |
| Lemma 3.3, Step 2, Cases 1–3, (3.22), (3.24), (3.26), (3.27) | [`Rigidity.Corrector.ae_heatComp_coarse_sub_eq_zero`](Rigidity/Proofs/Corrector/DarioStepTwoCases.lean), [`Rigidity.Corrector.ae_correctedPlane_sub_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreeCorrector.lean), [`Rigidity.Corrector.ae_edgeGrad_eq_smul_greenProj_of_div`](Rigidity/Proofs/Corrector/DarioCaseThreeAe.lean), [`Rigidity.Corrector.heatComp_coarse_eq_inner`](Rigidity/Proofs/Corrector/DarioCoarseHeatField.lean), [`Rigidity.Corrector.abs_coarseHeatField_apply_le`](Rigidity/Proofs/Corrector/DarioCoarseHeatField.lean), [`Rigidity.Corrector.ae_flipSumTwo_le`](Rigidity/Proofs/Corrector/DarioStepTwoSum.lean), [`Rigidity.Poincare.darioStepTwoSumBound_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean); [`Rigidity.Corrector.GeneralDim.ae_flipSumTwo_le`](Rigidity/Proofs/Corrector/GeneralStepTwoSum.lean) | `d = 2`: the Step 2 sum is `O_s(C/r²)`, no hypothesis. `d ≥ 3`: the sum is bounded by a weighted energy and through a partition of good cubes; the moments of the weight are `DarioStepTwoWeightThree` |
| Lemma 3.5 | [`Rigidity.Corrector.darioResamplePartitionTwo_holds`](Rigidity/Proofs/Corrector/DarioResamplePartitionHolds.lean), [`Rigidity.Corrector.resamplePartitionBound_holds`](Rigidity/Proofs/Corrector/DarioResamplePartitionHolds.lean); [`Rigidity.Corrector.GeneralDim.resamplePartition_max_bound`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean), [`Rigidity.Corrector.GeneralDim.goodCubes_iff_of_flip`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean), [`Rigidity.Corrector.GeneralDim.mem_stableGood_of_mem_centeredTriple`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean), [`Rigidity.Corrector.GeneralDim.scale_partitionCube_le_of_near`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean), [`Rigidity.Percolation.TriadicCube.eq_of_isMaximalStopping_of_agree`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean) | `d = 2`: `DarioResamplePartitionTwo` for the planar partition, with `C₀ = 4747`, `C = 14244`, no hypothesis. Every `d ≥ 2`: the corrected form with `S = max(side □_{𝒫(ω)}(x), side □_{𝒫(ω')}(x))`, `C₀ = 81`, `C = 243`, no hypothesis (see Departures). `d ≥ 3`: `DarioResamplePartitionThree` is the printed form |
| Proposition 3.6, (3.30); Lemma 3.7, (3.31); Definition 3.8 | [`Rigidity.Corrector.meyers_source`](Rigidity/Proofs/Corrector/DarioMeyersSource.lean), [`Rigidity.Corrector.exists_stepTwoGood_partition`](Rigidity/Proofs/Corrector/DarioStepTwoPartition.lean), [`Rigidity.Corrector.tsum_weight_energy_le`](Rigidity/Proofs/Corrector/DarioCellSum.lean); [`Rigidity.Corrector.GeneralDim.meyers_source`](Rigidity/Proofs/Corrector/GeneralMeyersSource.lean), [`Rigidity.Corrector.GeneralDim.stepTwoGood`](Rigidity/Proofs/Corrector/GeneralStepTwoDefs.lean) | the Meyers estimate with a divergence source in a different form, and the partition of the good cubes of the Step 2 sum (see Departures); `d = 2` no hypothesis, `d ≥ 3` as `DarioStepTwoWeightThree` |
| Lemma C.3 | [`Rigidity.Corrector.isOsBond_triadicScale_shift`](Rigidity/Proofs/Corrector/OsCalculus.lean) | for `X_n ≤ K + O_s(K 3^{−nβ})`, the scale `sup {3ⁿ : X_n ≥ K + 1}` is `O_{βs}(C)`; every `d`, no hypothesis |

## Dario and Gu

| DG | Lean declaration | Form |
| --- | --- | --- |
| Theorem 1, (1.7) | [`Rigidity.Assembly.ProvedFluxWeakNorm.darioGuHeatKernelTwo_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean); [`Rigidity.Green.darioGuHeatKernelD_of_gaussianFlow`](Rigidity/Proofs/Green/HeatKernelHoldsD.lean), [`Rigidity.Green.GeneralDim.darioGuGaussianFlowD_of_inputs`](Rigidity/Proofs/Green/GeneralTwoScaleFlow.lean) | `d = 2`: `DarioGuHeatKernelTwo`, for `t ≥ 1`, no hypothesis. `d ≥ 3`: `DarioGuHeatKernelD d` from the whole-cluster estimate (4.40) (`DarioGuGaussianFlowD`), which follows from Propositions 2.12 and 2.13; hypotheses `CorrectorQuantitativeInput` and `FluxVarianceBoundD d p` |
| Theorem 2, (1.10), (1.11), Section 5 | [`Rigidity.Assembly.ProvedFluxWeakNorm.supercriticalBondGreenQuantitativeTwo_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean); [`Rigidity.Green.supercriticalBondGreenQuantitativeThree_of_heatKernel`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean), [`Rigidity.Assembly.WithProvedBarlow.supercriticalBondGreenQuantitative_of_flux_heatKernel`](Rigidity/Proofs/Assembly/GreenQuantitativeEveryDim.lean), [`Rigidity.Assembly.ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_corrector_flux`](Rigidity/Proofs/Assembly/GreenQuantitativeFromFlux.lean), [`Rigidity.Assembly.ProvedFluxWeakNorm.supercriticalBondGreenQuantitative_of_corrector_fluxVariance`](Rigidity/Proofs/Assembly/GreenQuantitativeFromFluxVariance.lean) | `d = 2`: no hypothesis. Every `d`: `SupercriticalBondGreenQuantitative` from Proposition 2.12 (`CorrectorQuantitativeInput`) and `FluxVarianceBoundThree` |
| Green columns (DG, p. 4 and p. 58, stated without proof) | [`Rigidity.Proofs.Section5.planar_greenColumn_exists`](Rigidity/Proofs/Section5/PlanarGreenExistence.lean), [`Rigidity.Green.greenColumnExistence_of_three_le`](Rigidity/Proofs/Green/SupercriticalGreenColumn.lean), [`Rigidity.Green.supercriticalBondGreenColumnExistence_holds`](Rigidity/Proofs/Green/GreenColumnHolds.lean) | existence (`d = 2`), existence and uniqueness (`d ≥ 3`, and every `d ≥ 2`); no hypothesis |
| Remark 1.3, Theorem 3 | [`Rigidity.Green.darioGuGradientBoundTwo_holds`](Rigidity/Proofs/Green/DarioGuGradientHolds.lean), [`Rigidity.Green.darioGuGradientBoundTwo_of_barlow`](Rigidity/Proofs/Green/DarioGuGradientDirect.lean), [`Rigidity.Green.darioGuGradientBoundTwo_of_lipschitz`](Rigidity/Proofs/Green/DarioGuGradientFromLipschitz.lean) | `d = 2` only, in the form of Remark 1.3 (the gradient on the edges inside the ball); no hypothesis |
| Theorem 4 | [`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean); [`Rigidity.BarlowLattice.barlowGaussianUpperBound_holds`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean) | the Gaussian upper bound of Barlow, `d = 2` and every `d ≥ 2`; no hypothesis (table of Barlow) |
| Theorem 5, Steps 1, 2, 3, 5 | [`Rigidity.Green.sum_sq_twoScale_sub_le`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean), [`Rigidity.Green.integral_sum_sq_le_of_dirichletPoincare`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean), [`Rigidity.Green.weakNormLe_twoScale_equation`](Rigidity/Proofs/Green/ClusterTwoScaleTerms.lean), [`Rigidity.Green.dgStepFive`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean) | the steps in the forms stated, `d = 2`, unit conductances; Theorem 5 itself is not formalized (see Departures) |
| Lemma 1.6 | [`Rigidity.Corrector.isOsBond_triadicScale`](Rigidity/Proofs/Corrector/OsCalculus.lean) | the triadic minimal scale of `O_s` variables, every `d`; no hypothesis |
| Proposition 2.7 | [`Rigidity.Green.clusterPoincareTwo_holds`](Rigidity/Proofs/Green/DarioGuPoincareHolds.lean), [`Rigidity.Green.clusterDirichletPoincareTwo_holds`](Rigidity/Proofs/Green/ClusterDirichletPoincare.lean); [`Rigidity.WeakPoincare.clusterPoincare_holds`](Rigidity/Proofs/WeakPoincare/VeryGood.lean) | `p = 2`, in the weak form with the gradient on the larger ball (see Departures); `d = 2`, the part for functions vanishing on the boundary, and every `d ≥ 2`; no hypothesis |
| Proposition 2.9 | [`Rigidity.Green.darioGuCaccioppoliTwo_holds`](Rigidity/Proofs/Green/DarioGuParabolicCaccioppoli.lean) | parabolic Caccioppoli inequality, `C = 128`, every open component; no hypothesis |
| Lemma 2.10 | [`Rigidity.Green.darioGuTimesliceTwo_holds`](Rigidity/Proofs/Green/DarioGuParabolicTimeslice.lean) | the time-slice gradient estimate in the unnormalized form, `C = 4096` (see Departures); no hypothesis |
| Proposition 2.12, (2.10)–(2.12) | [`Rigidity.Poincare.correctorQuantitativeInputTwo_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean); [`Rigidity.Corrector.GeneralDim.correctorQuantitativeInput_of_dario`](Rigidity/Proofs/Corrector/CorrectorQuantitative.lean), [`Rigidity.Assembly.WithProvedCorrector.correctorQuantitativeInput_of_darioThree`](Rigidity/Proofs/Assembly/ProvedCorrector.lean) | the oscillation bound `osc_{𝒞_∞ ∩ B_r(y)} χ_p ≤ C\|p\| r^α` above a minimal scale `M_corr,α(y) ≤ O_s(C)` (`CorrectorQuantitativeInput`), derived from Theorem 1 of Dario and Lemma 1.6. `d = 2`: no hypothesis. Every `d`: from `DarioOptimalCorrectorThree` and the qualitative corrector input |
| Proposition 2.13 = Proposition B.1, (1.33), (B.2) | [`Rigidity.Green.darioGuFluxWeakNormTwo_holds`](Rigidity/Proofs/Green/DarioGuFluxWeakNormHolds.lean); [`Rigidity.Green.GeneralFlux.darioGuFluxWeakNormD_of_variance`](Rigidity/Proofs/Green/GeneralFluxHolds.lean), [`Rigidity.Green.GeneralFlux.darioGuFluxWeakNormD_two_holds`](Rigidity/Proofs/Green/GeneralFluxHolds.lean) | `d = 2`: `DarioGuFluxWeakNormTwo`, no hypothesis. Every `d ≥ 2`: `DarioGuFluxWeakNormD d p σ` from `FluxVarianceBoundD d p`; `FluxVarianceBoundD 2 p` is proved |
| Proposition 2.15 | [`Rigidity.Green.carneVaropoulosTwo_holds`](Rigidity/Proofs/Green/PlanarCarneVaropoulos.lean); [`Rigidity.Green.carneVaropoulos_holds`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean), [`Rigidity.Green.heatSmallTimeD_holds`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean) | the Carne–Varopoulos bound, `C = 200` for `d = 2` and `C = 100 d²` for every `d ≥ 2`; no hypothesis |
| Proposition 3.9 | [`Rigidity.Green.DarioGuLipschitzTwo`](Rigidity/Proofs/Green/DarioGuParabolicInputs.lean), [`Rigidity.Green.darioGuGradientBoundTwo_of_lipschitz`](Rigidity/Proofs/Green/DarioGuGradientFromLipschitz.lean) | a named statement, in the range `2r ≤ R` (see Departures); Theorem 3 is derived from it with Theorem 4 and, independently, without it |
| Lemma 3.11 | [`Rigidity.Green.AKMLemmaEightNineTwo`](Rigidity/Proofs/Green/DarioGuHeatKernelInputs.lean) | stated (Lemma 8.9 of Armstrong, Kuusi and Mourrat), `d = 2`, since it is used in the source proof of Proposition 3.9; not proved |
| Section 4.3, (4.43)–(4.50); (3.2), (3.52) | [`Rigidity.Green.darioGuHeatKernelTwo_of_reduced`](Rigidity/Proofs/Green/DarioGuTheoremOneReduced.lean), [`Rigidity.Green.heatLevel_step`](Rigidity/Proofs/Green/DarioGuStep.lean), [`Rigidity.Green.pointwise_of_weightedL2`](Rigidity/Proofs/Green/DarioGuPointwise.lean), [`Rigidity.Green.sum_dgPhi_mul_dgPhi_le`](Rigidity/Proofs/Green/DarioGuPhiConvolution.lean), [`Rigidity.Green.hasTail_latticeSup`](Rigidity/Proofs/Green/DarioGuLatticeSup.lean) | the induction over the exponents, `d = 2`; (3.2) the semigroup bound of `Φ_C`; (3.52), (4.44) the tail of the lattice minimal time |
| Lemma 4.1 | [`Rigidity.Green.darioGuApproxLemmaTwo_of_gradient`](Rigidity/Proofs/Green/DarioGuTheoremOnePoincare.lean) | `d = 2`, from Theorem 3 (Remark 1.3) and Theorem 4; no hypothesis |
| Lemma 4.2 | [`Rigidity.Green.darioGuCorrectorLemmaTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuCorrectorLemma.lean) | `d = 2`, from Proposition 2.12, Theorem 4, Proposition 2.15 and (3.2) |
| Proposition 4.3, (4.40) | [`Rigidity.Green.darioGuTwoScaleErrorTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxTerm.lean), [`Rigidity.Assembly.ProvedFluxWeakNorm.exists_darioGuTwoScaleErrorTwo_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean); [`Rigidity.Green.GeneralDim.tsum_sq_clusterWD_le`](Rigidity/Proofs/Green/GeneralTwoScaleError.lean) | `d = 2`: the two-scale error, no hypothesis. Every `d ≥ 2`: the bound (4.40) of one configuration |
| Proposition A.1 | `Rigidity.Proofs.S2.cluster_density_concentration` and `Rigidity.Proofs.S2.planar_cluster_density_concentration`, in Percolation-Cluster-Homogenization | every `d ≥ 2` and `d = 2`; no hypothesis (see its `CORRESPONDENCE.md`) |
| Proposition A.7, (A.13) | [`Rigidity.Green.darioGuDensityGaussianTwo_holds`](Rigidity/Proofs/Green/DarioGuDensityGaussian.lean); [`Rigidity.Green.darioGuDensityGaussianD_holds`](Rigidity/Proofs/Green/DensityGaussianD.lean) | the second part, `d = 2` and every `d ≥ 2`; the first part (A.12) is not formalized; no hypothesis |
| Remark B.3 | [`Rigidity.Green.darioGuTranslatedFluxTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuFluxTranslateHolds.lean), [`Rigidity.Assembly.ProvedFluxWeakNorm.exists_darioGuTranslatedFluxTwo_holds`](Rigidity/Proofs/Assembly/ProvedFluxWeakNorm.lean) | the weak norm of the translated flux, `d = 2`; no hypothesis |

## Gu

| Gu | Lean declaration | Form |
| --- | --- | --- |
| Proposition 1.1, (3.4) | [`Rigidity.Green.exists_fluxSpatialAverage_two`](Rigidity/Proofs/Green/DarioGuFluxSpatialAverage.lean); [`Rigidity.Green.GeneralFlux.exists_fluxSpatialAverageD`](Rigidity/Proofs/Green/GeneralFluxSpatialAverage.lean), [`Rigidity.Green.GeneralFlux.fluxVarianceBoundD_two`](Rigidity/Proofs/Green/GeneralFluxVarianceTwo.lean) | `\|Φ_{r²} ⋆ g(x)\| ≤ O_s(C r^{−d/2})` (DG (B.8)). `d = 2`: no hypothesis. Every `d ≥ 2`: from the variance bound `FluxVarianceBoundD d p`, which is proved for `d = 2` |
| Steps 1–4, Lemma 3.2 | [`Rigidity.Green.fluxFlipSum_isOsBond`](Rigidity/Proofs/Green/DarioGuFluxFlipMoments.lean), [`Rigidity.Green.GeneralFlux.ae_planeFluxD_setBond_eq`](Rigidity/Proofs/Green/GeneralFluxFlip.lean), [`Rigidity.Green.GeneralFlux.fluxPairingOpenD_holds`](Rigidity/Proofs/Green/GeneralFluxPairing.lean), [`Rigidity.Green.GeneralFlux.fluxPairingClosedD_holds`](Rigidity/Proofs/Green/GeneralFluxPairing.lean), [`Rigidity.Green.GeneralFlux.fluxPairingZeroD_holds`](Rigidity/Proofs/Green/GeneralFluxPairing.lean), [`Rigidity.Green.GeneralFlux.fluxFlipSumPartitionD_holds`](Rigidity/Proofs/Green/GeneralFluxFlipSum.lean) | the flip differences of the heat average of the flux and their sum, `d = 2` and every `d ≥ 2`; the bound of each squared flip difference by the Step 2 factor (`FluxFlipWeightBoundD`) is not proved |

## Barlow

| Barlow | Lean declaration | Form |
| --- | --- | --- |
| Theorem 1, (0.4), (0.5); Proposition 6.1 | [`Rigidity.Barlow.barlowGaussianUpperBoundTwo_of_veryGood`](Rigidity/Proofs/Barlow/GaussianHolds.lean), [`Rigidity.Barlow.clusterVeryGoodBallsTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean), [`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean); [`Rigidity.BarlowLattice.barlowGaussianUpperBound_of_veryGood`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean), [`Rigidity.BarlowLattice.barlowGaussianUpperBound_holds`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean) | the Gaussian upper bound in the form of DG Theorem 4, `d = 2` and every `d ≥ 2`; no hypothesis |
| Lemma 1.1 | [`Rigidity.Green.carneVaropoulosTwo_holds`](Rigidity/Proofs/Green/PlanarCarneVaropoulos.lean), [`Rigidity.Green.carneVaropoulos_holds`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean) | the Carne–Varopoulos bound for the variable-speed walk, `d = 2` and every `d ≥ 2`; no hypothesis |
| Lemma 1.6 | [`Rigidity.Barlow.tsum_mul_openLaplacian`](Rigidity/Proofs/Barlow/HeatEnergy.lean); [`Rigidity.BarlowLattice.tsum_mul_openLaplacian`](Rigidity/Proofs/BarlowLattice/HeatEnergy.lean) | the discrete Gauss–Green formula and the energy identity of the proof of Proposition 3.1, `d = 2` and every `d` |
| Definition 1.7, Theorem 2.18 (a)–(c), Lemma 2.19 | [`Rigidity.WeakPoincare.clusterGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/GoodBallsHolds.lean), [`Rigidity.WeakPoincare.clusterVeryGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/VeryGood.lean), [`Rigidity.WeakPoincare.planarVeryGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/PlanarVeryGood.lean) | good and very good balls of the infinite cluster, every `d ≥ 2`; no hypothesis (see Departures) |
| Proposition 3.1, Corollary 3.2 | [`Rigidity.Barlow.openHeat_diag_le_of_good`](Rigidity/Proofs/Barlow/OnDiagonal.lean), [`Rigidity.Barlow.openHeat_le_of_good`](Rigidity/Proofs/Barlow/OnDiagonal.lean); [`Rigidity.BarlowLattice.bondHeat_diag_le_of_good`](Rigidity/Proofs/BarlowLattice/OnDiagonal.lean), [`Rigidity.BarlowLattice.bondHeat_le_of_good`](Rigidity/Proofs/BarlowLattice/OnDiagonal.lean) | on-diagonal bound from good balls, `d = 2` and every `d` |
| Lemma 3.3, Proposition 3.4 | [`Rigidity.Barlow.neg_log_le_heatEntropy`](Rigidity/Proofs/Barlow/MeanDisplacement.lean), [`Rigidity.Barlow.meanDist_le_of_entropy`](Rigidity/Proofs/Barlow/MeanDisplacement.lean); [`Rigidity.BarlowLattice.neg_log_le_heatEntropy`](Rigidity/Proofs/BarlowLattice/MeanDisplacement.lean), [`Rigidity.BarlowLattice.meanDist_le_of_entropy`](Rigidity/Proofs/BarlowLattice/MeanDisplacement.lean) | entropy and mean displacement; only the upper bound of Proposition 3.4 |
| Lemmas 3.5, 3.6, Proposition 3.7 | [`Rigidity.Barlow.exitProb_clBall_le`](Rigidity/Proofs/Barlow/ExitTail.lean), [`Rigidity.Barlow.BarlowRegion.tsum_far_le`](Rigidity/Proofs/Barlow/GaussianTail.lean); [`Rigidity.BarlowLattice.exitProb_clBall_le`](Rigidity/Proofs/BarlowLattice/ExitTail.lean), [`Rigidity.BarlowLattice.BarlowRegion.tsum_far_le`](Rigidity/Proofs/BarlowLattice/GaussianTail.lean) | exit-time estimates for the lazy jump chain and the continuous-time walk |
| Theorem 3.8 | [`Rigidity.Barlow.BarlowRegion.openHeat_le_gauss`](Rigidity/Proofs/Barlow/GaussianBound.lean); [`Rigidity.BarlowLattice.BarlowRegion.bondHeat_le_gauss`](Rigidity/Proofs/BarlowLattice/GaussianBound.lean) | `p_t(x, y) ≤ C_G t^{−d/2} e^{−c_G \|x − y\|²/t}` in a region of good balls, `d = 2` and every `d` |

## Other cited results

| Source | Lean declaration | Form |
| --- | --- | --- |
| Proposition 2.3 of the paper (quoted from the literature) | [`Rigidity.Percolation.wellConnected_input_two`](Rigidity/Proofs/Percolation/PlanarWellConnected.lean), [`Rigidity.Percolation.wellConnected_input`](Rigidity/Proofs/Percolation/WellConnected.lean) | `d = 2` with `s = 1/800`, and every `d ≥ 2`; no hypothesis (see Departures) |
| Lemma 2.14 of the paper (Hatcher, Proposition 2B.1) | [`Rigidity.Topology.jordan_curve_theorem_sphere`](Rigidity/Proofs/Topology/JordanCurveSphere.lean) | the Jordan curve theorem on `S²` for simple loops; no hypothesis |
| Micciancio and Regev, Lemma 3.3 | [`Rigidity.Smoothing.micciancio_regev_smoothing`](Rigidity/Proofs/Smoothing/MicciancioRegev.lean) | the bound of the smoothing parameter of a lattice; no hypothesis |
| Lemma 2.13 of the paper (Rudin, Remark 14.20) | [`Rigidity.Assembly.polyominoJordan`](Rigidity/Proofs/Assembly/Section2Polyomino.lean) | the case of the interior of a finite union of lattice squares; the general lemma is not formalized |
| Antal and Pisztora, Theorem 1.1 | [`Rigidity.External.AntalPisztoraChemicalDistance`](Rigidity/External/ChemicalDistance.lean) | stated as a proposition; no numbered result uses it |

## Departures

### Dario

- **Lemma 3.5 (cited in the proof of Lemma 3.3; Dario18.tex lines 1179-1201).** As printed, with the scale
  `s` = size of the partition cube of an endpoint `x` of the resampled bond in the old environment, the lemma
  fails in dimension `d ≥ 3` for the partition into good cubes (Definition 2.6, from the good cubes of Definition 2.3): a single bond change, by
  opening or by closing, can destroy property (ii) of good cubes of arbitrarily large side while the old
  partition has side 27 everywhere. The printed proof asserts the large-scale stability of good cubes
  (ingredients 3 and 4) without argument. Formalized: the corrected form with
  `S = max(size of P_w(x), size of P_w'(x))`: [`Rigidity.Corrector.GeneralDim.resamplePartition_max_bound`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean)
  (`C₀ = 81`, `C = 243`: new partition sides `≤ 243 S` on the ball of radius `81 S`; outside it the partition
  cubes and their anchors agree), [`Rigidity.Corrector.GeneralDim.goodCubes_iff_of_flip`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean) (goodness unchanged
  at side `≥ 9S`), [`Rigidity.Corrector.GeneralDim.mem_stableGood_of_mem_centeredTriple`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean) (cubes of side
  `≥ 9 size(P(x))` near `x` are stable), [`Rigidity.Corrector.GeneralDim.scale_partitionCube_le_of_near`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean)
  (ingredient 5), [`Rigidity.Percolation.TriadicCube.eq_of_isMaximalStopping_of_agree`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean) (partitions agree where
  the good cubes agree), all with no hypothesis
  ([`GeneralResamplePartitionHolds.lean`](Rigidity/Proofs/Corrector/GeneralResamplePartitionHolds.lean)). `S`
  has the same stretched-exponential tail as `s`, so the conclusion of Dario's Theorem 1 is unchanged. The
  declarations of Steps 1 and 2 for `d ≥ 3` (`darioStepOneSumBoundThree_of_resample`,
  `darioStepTwoSumBoundThree_of_weight`) take as hypothesis `DarioResamplePartitionThree`, which is Lemma 3.5
  in the printed form with the scale `s`, and do not use the corrected form.
- **Lemma 3.5 for the planar partition (Dario18.tex:1179-1201).** Dario states the second clause for the sizes
  of the partition cubes; the coarsenings of Steps 1 and 2 also use the anchors, which for the planar partition
  depend on the bonds of the square of side nine times the side of the cube. `DarioResamplePartitionTwo` states
  the second clause for the cube and for its anchor; for a meshed partition cube of side at least 1000 the anchor
  depends only on the bonds inside the cube, and the statement is then Lemma 3.5 as printed, for this partition.
  The printed proof uses large cubes crossable by clusters avoiding a cube, which the strip meshes of the planar
  partition do not provide. In the Lean proof, with `s` the side of the partition cube of an endpoint `x` of
  the bond, the square of side `s` around `x` is tested in the mesh of that cube, and by planar duality a
  change of a crossing of a strip of width at least `s + 2` would give a walk of faces through closed edges from
  the bond leaving that square, which its outer strip crossings block. So the meshed cubes change only for cubes
  of side below `101 s` near `x`, the stopping cubes only near `x`, and the partition cubes agree at distance at
  least `4747 s` and have side at most `14244 s` closer to `x`. Declarations:
  [`Rigidity.Corrector.darioResamplePartitionTwo_holds`](Rigidity/Proofs/Corrector/DarioResamplePartitionHolds.lean), [`Rigidity.Corrector.resamplePartitionBound_holds`](Rigidity/Proofs/Corrector/DarioResamplePartitionHolds.lean),
  [`Rigidity.Percolation.TriadicCube.planarAnchor_eq_of_agree_off`](Rigidity/Proofs/Corrector/DarioResamplePartition.lean),
  [`Rigidity.Corrector.planarPartCube_eq_and_anchor_eq_of_resample`](Rigidity/Proofs/Corrector/DarioResamplePartition.lean).
- **Theorem 1 (Dario18.tex:212-225), the logarithm.** Dario18.tex:216, and the quotation of Theorem 1 at
  DG21.tex:1094 in the proof of Proposition 2.12, print `log^{1/2}|x − y|`, which vanishes at `|x − y| = 1`. The
  statement `DarioOptimalCorrectorTwo` has `log^{1/2}(2 + |x − y|)` and `‖q‖₁`.
  Declaration: [`Rigidity.Poincare.darioOptimalCorrectorTwo_holds`](Rigidity/Proofs/Poincare/DarioStepTwoHolds.lean).
- **(1.12), (1.14), (5.1) (Dario18.tex:444, 462, 1727): moments in place of the `O_s` calculus.** Dario averages
  `O_s` variables by (1.12) and (1.14). The Lean proof bounds moments instead: Jensen's inequality in `r` for the
  measure `min(r, 1/r) dr`, Tonelli's theorem and lattice sums of exponential weights; the sums over balls of
  random radius of (2.24), (5.7) and (5.10) are bounded by `lintegral_randomBallSum_le`. The exponent of the
  moments is `k = 3/2 + 1/s`, and the exponential moment (5.1) is proved with the factor `e^{−q/s}`, where
  (5.1) prints `e^{q/s}`, which is weaker. Declarations: [`Rigidity.Corrector.IsOsBond.integral_rpow_le`](Rigidity/Proofs/Corrector/DarioMoments.lean),
  [`Rigidity.Corrector.isOsBond_of_moment_le`](Rigidity/Proofs/Corrector/DarioMoments.lean), [`Rigidity.Corrector.lintegral_randomBallSum_le`](Rigidity/Proofs/Corrector/RandomBallSums.lean).
- **Section 5 (Dario18.tex:1699-2031), Step 6 and the translated partitions.** The coarsening error (5.10) is
  stated for the increment between two points. The partition `𝒫_y = y + 𝒫(τ_{−y} a)` is built from the anchors
  of the partition of the repository (the planar partition for `d = 2`, the partition into good cubes for
  `d ≥ 3`), and the bounds of the partition sizes are those of that partition.
  Declarations: [`Rigidity.Corrector.baseCoarseningError`](Rigidity/Proofs/Corrector/PlanarCoarseningError.lean), [`Rigidity.Corrector.baseComparison`](Rigidity/Proofs/Corrector/PlanarPartitionComparison.lean).
- **Proposition 2.15 (Dario18.tex:821-834), at the origin.** Dario bounds the gradient by `X^{d/2}`. The Lean
  bound is `L max(X, 2)²` in `d = 2` and `L max(X, 2)^d` in every `d ≥ 2`, because the cluster ball `B_{4r}`
  is bounded by the lattice ball `B_{5r}`; it is again `O_{s/2}(C)`, respectively `O_{s/d}(C)`. Declarations:
  [`Rigidity.Corrector.lipschitz_correctedPlane_origin`](Rigidity/Proofs/Corrector/PlanarCorrectorLipschitz.lean), [`Rigidity.Corrector.GeneralDim.lipschitz_correctedPlane_origin`](Rigidity/Proofs/Corrector/GeneralCorrectorLipschitz.lean).
- **Propositions 2.11 and 2.12 (Dario18.tex:739-769).** The gradient of the Green function is the orthogonal
  projection onto the closed span of the gradients of point masses, which gives (2.14) with `C = 1`, (2.15) and
  (2.17) at once; potentials are built by sums along walks from the roots of the components. Declarations:
  [`Rigidity.Corrector.greenProj`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean), [`Rigidity.Corrector.norm_greenProj_le`](Rigidity/Proofs/Corrector/DarioClusterGreen.lean).
- **Proposition 2.17 (Dario18.tex:867-876).** (a) Dario cites the proposition to Armstrong and Lin (*Optimal
  quantitative estimates in stochastic homogenization for elliptic equations in nondivergence form*, Arch.
  Ration. Mech. Anal. 225 (2017), Proposition 2.2, with the proof of its Appendix A); it is not a result of
  Armstrong, Kuusi and Mourrat. (b) Armstrong and Lin cite the moment inequality of Boucheron, Bousquet, Lugosi
  and Massart (Ann. Probab. 33 (2005), Theorem 2) with the variance proxy defined through conditional
  expectations; Boucheron, Bousquet, Lugosi and Massart prove it with the resampled quantity `V⁺`. For
  Bernoulli bonds `(X − X'_e)² ≥ min(p, 1 − p)² (X(ω^{e,1}) − X(ω^{e,0}))²`, and their argument (tensorization
  of `φ`-entropies, the two-point bound, induction on the moments) is carried out here with the flip
  differences directly, with the factor `min(p, 1 − p)`; the constant `C` depends on `p` and `β`, where Dario
  has `C(d, β)`. (c) Armstrong and Lin sketch the passage from the moments to the exponential ("Combining ...
  yields"), which leaves `exp(𝔼[V]^{β/2})` to be absorbed; it is written out: the terms of the series with
  `βn < 2` are bounded through the second moment (`|Z|^{βn} ≤ 1 + Z²`), the others by Young's inequality
  termwise, and the exponent `(2 − β)/β < 1` for `β > 1` by Jensen's inequality, in place of Hölder's
  inequality across the series. (d) For `p ∈ {0, 1}` the law is a point mass and the inequality holds with
  `C = 1`; the Efron–Stein and moment inequalities on infinitely many bonds are obtained from the finite cube
  through `𝔼[X | ℱ_S]`, the Lévy upward theorem and Fatou's lemma. Declarations:
  [`Rigidity.Corrector.concentrationTwo_holds`](Rigidity/Proofs/Corrector/ConcentrationTwoHolds.lean), [`Rigidity.Corrector.GeneralDim.concentration_holds`](Rigidity/Proofs/Corrector/Concentration.lean),
  [`Rigidity.Probability.lintegral_abs_sub_rpow_le_vertSum`](Rigidity/Proofs/Probability/BernoulliMoments.lean), [`Rigidity.Probability.lintegral_exp_rpow_le_of_moments`](Rigidity/Proofs/Probability/StretchedExponential.lean).
- **Proposition 2.19, (2.26) (Dario18.tex:901-912; proof in Appendix A, Dario18.tex:2035-2279).** Dario proves
  (2.26) for balls in the continuum, from Proposition D.1 of Armstrong, Kuusi and Mourrat (with Remark D.6) on
  the dual norm `W^{−1,q}` through the Nečas inequality (Bogovskii operator, Newtonian potential and the
  Calderón–Zygmund estimate), Lemma 7.12 and Proposition 9.9 of Gilbarg and Trudinger, and a rescaling, and
  states the version on the lattice by "standard arguments". The Lean proof is for the lattice and the cubes of
  side `R = 3^m`, the form in which (5.4) is applied, with the constant `A₀ q^{3/2}` and the absolute
  convergence of the convolutions `Φ_{r²} * ∇u` required; the exponents `1 ≤ q < 2` are reduced to `q = 2` by
  Jensen's inequality. It is proved directly by the duality argument of Proposition D.1: the `L^q` oscillation
  of `u` on the cube is paired with an extremal test function of mean zero, the pairing is written through the
  heat flow of the test function and one summation by parts, the bilinear term is bounded by Hölder's
  inequality with weights, and the weighted square function of the dual data by Stein's argument and the
  maximal function; the weight `e^{|x|/2R}` is handled by the product of the hyperbolic cosines of the
  coordinates, an eigenfunction of the heat semigroup. The Nečas inequality and the Calderón–Zygmund theory are
  not used. Declarations: [`Rigidity.Poincare.multiscalePoincareTwo_holds`](Rigidity/Proofs/Poincare/MultiscalePoincareHolds.lean),
  [`Rigidity.Poincare.GeneralDim.multiscalePoincare_holds`](Rigidity/Proofs/Poincare/GeneralMultiscalePoincare.lean).
- **Lemma 3.2 (Dario18.tex:934-939; proof 953-1166).** (a) The stationary anchor `z̄_stat` (Dario18.tex:976-982)
  is the first point of `𝒞_∞` in the anchor order of the partition (distance in `ℓ∞` to the centre, then
  lexicographic order), where Dario takes the point of `𝒞_∞` nearest to the cube with lexicographic ties. (b)
  In Step 2 the increments are telescoped along lines in each coordinate direction, in place of the Stokes
  formula on `□_{nk}`. (c) In Step 1 the discrepancy is bounded vertex by vertex through the anchor discrepancy,
  with second moments and the inequality of the arithmetic and geometric means, in place of the sets `U`, the
  `O_s` bound and the Cauchy–Schwarz inequality. The stationary partition is the planar partition capped at the
  scale `k`, and (3.3) is proved from the localization of the planar partition. Declarations:
  [`Rigidity.Corrector.darioLemmaThreeTwo_holds`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoHolds.lean), [`Rigidity.Corrector.exists_lintegral_abs_statSegment_le`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoStepTwo.lean),
  [`Rigidity.Corrector.sum_statMean_line_eq_zero`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoMean.lean), [`Rigidity.Corrector.exists_lintegral_abs_statDiscrepancy_le`](Rigidity/Proofs/Corrector/DarioLemmaThreeTwoMoments.lean).
- **Lemmas 3.2 and 3.3 (Dario18.tex:934-948), translated partitions.** Dario takes `x = 0` by stationarity,
  which does not hold for the partition `𝒫` itself. `DarioLemmaThreeTwo` and `DarioLemmaThreeThree` state the
  bounds `|E[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)]| ≤ C/r` and `𝕍[Φ_{r²} * ∇_j[χ_{e_i}]_𝒫(x)] ≤ O_s(C/r²)` for `r ≥ 1` at
  every point `x`, that is for the translated partitions `𝒫_y`. Declarations: [`Rigidity.Corrector.DarioLemmaThreeTwo`](Rigidity/Proofs/Corrector/DarioPropThreeOne.lean),
  [`Rigidity.Corrector.DarioLemmaThreeThree`](Rigidity/Proofs/Corrector/DarioPropThreeOne.lean).
- **Lemma 3.3, Section 3.2 (Dario18.tex:1168-1531), (3.11)–(3.15): flips in place of a doubled probability
  space.** For the Bernoulli law the variable `a_e` takes the values 0 and 1, so the conditional expectation
  given the other bonds is a two-point average, and the resampled configuration is replaced by the
  configurations `ω^{e,1}` and `ω^{e,0}` with the bond `e` open and closed: `𝕍[X] ≤ Σ_e (D_e X)²` with
  `D_e X = X(ω^{e,1}) − X(ω^{e,0})`. Step 1 and the split (3.15) are proved for them, and the expectation under a
  flip is bounded by `p^{−1}` times the expectation (the form of (3.12)). Declarations:
  [`Rigidity.Corrector.ae_resampleVar_le_tsum_bondFlipDiff`](Rigidity/Proofs/Corrector/DarioBondResampling.lean), [`Rigidity.Corrector.IsOsBond.comp_setBond`](Rigidity/Proofs/Corrector/DarioBondResampling.lean),
  [`Rigidity.Corrector.bondFlipDiff_eq_flipTermOne_add_flipTermTwo`](Rigidity/Proofs/Corrector/DarioFlipSumTerms.lean).
- **Lemma 3.3, Step 1, (3.16)–(3.19) (Dario18.tex:1287-1315).** The bounds by the supremum and infimum of the
  weights `ζ_r` and the calculus of the random radii `O_s` are replaced by the moments of the sums (3.18): the
  Lipschitz bounds of the corrector, with `E[(1 + Λ)^q] ≤ (B q^κ)^q`, a bound of the local factor by the cube of a
  sum over a ball, Jensen's inequality over the bonds with weights decaying exponentially in the distance, and
  moments of order `q` of the sums over balls. Only the bound `Σ_y Φ_{r²}(x, y)² ≤ C/r²` of the weights is
  used. The square of the sum over the box of radius `C₀ s₀` is bounded by Cauchy–Schwarz, by the number of
  points of the box times the sum of the squares. Declarations:
  [`Rigidity.Corrector.exists_tsum_latticeHeat_sq_le`](Rigidity/Proofs/Corrector/DarioHeatSquareSum.lean), [`Rigidity.Corrector.sq_tsum_partitionChange_le`](Rigidity/Proofs/Corrector/DarioStepOneLocal.lean),
  [`Rigidity.Corrector.stepOneW_moments`](Rigidity/Proofs/Corrector/DarioStepOneHolds.lean).
- **Lemma 3.3, Step 2, (3.22), (3.24), (3.26) (Dario18.tex:1355, 1370, 1383).** (3.22) is proved in flip form,
  for the corrected planes of `ω^{e,1}` and `ω^{e,0}`, with the sublinear growth of the potential of the
  gradient of the Green function obtained from the partition chains and the minimal scales with exponent `1/16`,
  and the increment (3.24) is proved through the partition of `ω^{e,0}`, without Lemma 3.5. In (3.26) the
  paths `γ_r` joining the anchors of neighbouring partition cubes are taken in the ninefold square of the
  smaller cube, in place of `□_𝒫(z) ∪ □_𝒫(z')`. Declarations:
  [`Rigidity.Corrector.ae_edgeGrad_eq_smul_greenProj_of_div`](Rigidity/Proofs/Corrector/DarioCaseThreeAe.lean), [`Rigidity.Corrector.ae_correctedPlane_sub_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreeCorrector.lean),
  [`Rigidity.Corrector.ae_heatComp_coarse_sub_eq_smul_greenProj`](Rigidity/Proofs/Corrector/DarioCaseThreePairing.lean), [`Rigidity.Corrector.abs_sub_le_two_mul_edgeVariation`](Rigidity/Proofs/Corrector/DarioCaseThreePairing.lean),
  [`Rigidity.Corrector.heatComp_coarse_eq_inner`](Rigidity/Proofs/Corrector/DarioCoarseHeatField.lean).
- **Proposition 3.6, Lemma 3.7, Definition 3.8 (Dario18.tex:1472-1506; Appendix B, Dario18.tex:2280-2328).**
  Dario derives the Step 2 sum from Proposition 3.6 (the Meyers estimate with a divergence source, with the same
  exponent on the source and on the gradient, of which Appendix B gives a sketch), Lemma 3.7 and Definition 3.8.
  That form of Proposition 3.6 fails on Bernoulli clusters. The Lean proof uses the Meyers estimate with a
  divergence source in the form `avg_□ \|∇v\|^{2p} ≤ K ((avg_{3□} \|∇v\|²)^p + (S/\|3□\|)^p + S^p/\|□\|)`,
  `p = 1 + ε/2`, `S` the squared norm of the source on the open edges inside `U₀` (the estimate replacing
  (3.30)), summed over the almost sure partition into cubes whose children carry the Meyers estimate and whose
  weights `W` of the Step 2 sum are bounded on average, which takes the role of Lemma 3.7 and Definition 3.8.
  Declarations: [`Rigidity.Corrector.meyers_source`](Rigidity/Proofs/Corrector/DarioMeyersSource.lean), [`Rigidity.Corrector.exists_stepTwoGood_partition`](Rigidity/Proofs/Corrector/DarioStepTwoPartition.lean),
  [`Rigidity.Corrector.flipSumTwo_le_of_partition`](Rigidity/Proofs/Corrector/DarioStepTwoReduce.lean), [`Rigidity.Corrector.GeneralDim.meyers_source`](Rigidity/Proofs/Corrector/GeneralMeyersSource.lean),
  [`Rigidity.Corrector.GeneralDim.flipSumTwo_le_of_partition`](Rigidity/Proofs/Corrector/GeneralStepTwoReduce.lean).

### Dario and Gu

- **Proposition 2.12 (DG21.tex:1078-1110), pairs of points.** Theorem 1 of Dario is applied to the pairs of
  points in the ball around `x`, with a union bound over the pairs, in the passage to `CorrectorQuantitativeInputTwo`.
  Declaration: [`Rigidity.Corrector.correctorQuantitativeInputTwo_of_dario`](Rigidity/Proofs/Corrector/PlanarCorrectorQuantitative.lean).
- **Theorem 1, small times (DG21.tex:295-304).** The estimate `DarioGuHeatKernelTwo` is stated for `t ≥ 1`; the
  small times are covered by the Carne–Varopoulos bound for the lazy walk. Declarations:
  [`Rigidity.Green.lazyPow_le_carneVaropoulos`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean), [`Rigidity.Green.heatSmallTimeTwo`](Rigidity/Proofs/Green/LazyCarneVaropoulos.lean).
- **Theorem 1, Section 4.3, (4.43)–(4.50) (DG21.tex:2512-2615), the induction.** (a) The functions `q` and `v` are defined by
  the semigroup formula, and the corrector is normalized by `χ(y) = 0` for `y ∈ 𝒞_∞`. (b) Lemma 4.1 is used in
  the input form of the proof of the induction at (4.7) (DG21.tex:2618): `ε Φ_C(τ, ·)` is replaced by
  `C(ε (τ/t)^{1/2} + τ^{−1/2+α}) Φ_C(t, ·)`. (c) The minimal times of the three propositions are merged into one
  `M` with `τ ≥ M` and `t ≥ 3τ`; the sequence `κ_n` starts at `k₀ = 0`, with `k₁` the exponent `κ₀` of DG; the
  scale `T_par` of (4.44) is the lattice supremum of the point times (`hasTail_latticeSup`); and the statement
  is proved for `t ≥ 8`. (d) Proposition A.7, printed for lattice centres `y ∈ ℤ^d`, is used at the centre
  `(x + z)/2` of (4.48) (DG21.tex:2602); here the centre is rounded to a lattice point and the Lipschitz bound
  of the Gaussian kernel summed over the lattice is used. Declarations: [`Rigidity.Green.darioGuHeatKernelTwo_of_reduced`](Rigidity/Proofs/Green/DarioGuTheoremOneReduced.lean),
  [`Rigidity.Green.heatLevel_step`](Rigidity/Proofs/Green/DarioGuStep.lean), [`Rigidity.Green.hasTail_latticeSup`](Rigidity/Proofs/Green/DarioGuLatticeSup.lean).
- **Theorem 1 in every dimension (DG21.tex:295-304).** The proof for `d ≥ 2` goes through the whole-cluster
  estimate (4.40) with initial time `τ` and final time `3τ` and the passage from smooth initial data to a point
  source with the Gaussian upper bound; Lemmas 4.1 and 4.2 and the weighted estimate (4.3) are not used. The radii
  of the pairing are `√s t^{η/(d+2)}` instead of `√s log(2 + t)`; the minimal time of Theorem 1 at `y` is the
  supremum of the thresholds of the inputs over the points `w` with `|w − y| ≤ T(w) + 1` (`latticeSupD`), which
  keeps a stretched exponential tail; the exponent of the error is `1/2 − δ` with the point-source exponent
  `min(δ, 1/2)/2`. Declarations: [`Rigidity.Green.darioGuHeatKernelD_of_gaussianFlow`](Rigidity/Proofs/Green/HeatKernelHoldsD.lean),
  [`Rigidity.Green.GeneralDim.darioGuGaussianFlowD_of_inputs`](Rigidity/Proofs/Green/GeneralTwoScaleFlow.lean).
- **Theorem 2 (DG21.tex:348-373; Section 5, DG21.tex:2639-2748), normalization and the Green function as a time
  integral.** DG normalize the time integral of `p̄` by its mean over the unit ball, which produces the constant
  `K₁`; here it is normalized by `p̄(t, e)` with `|e| = 1`, which gives the homogenized Green function `ḡ`
  without a constant. The identity `g(x, y) = ∫_0^∞ (p(t, x, y) − p(t, y, y)) dt` (DG21.tex:336-338 and display
  (5.4)), which the source states without proof, is proved for planar clusters. For `d ≥ 3` the time integral
  is split at `t = |x − y|`, and the Gaussian kernel at small times is bounded through the Gamma integral
  `∫_0^∞ t^{−d/2} e^{−a/t} dt = a^{1−d/2} Γ(d/2 − 1)` after the factor `e^{−|x−y|/(4σ)}` is taken out; the
  minimal scale is `max(T(y), 1)`. Declarations: [`Rigidity.Green.HeatBounds.laplacian_timeGreen`](Rigidity/Proofs/Green/PlanarGreenDeterministic.lean),
  [`Rigidity.Green.supercriticalBondGreenQuantitativeThree_of_heatKernel`](Rigidity/Proofs/Green/GreenQuantitativeThree.lean).
- **Proposition 2.7 (DG21.tex:979-992).** The printed form, with the gradient on the same ball, fails in every
  dimension. It is proved in a weak form for `p = 2`,
  `‖u − (u)‖_{L̲²(B_R)} ≤ C R ‖∇u‖_{L̲²(𝒞_∞ ∩ B_{LR}(y))}` (`L = 24` in `d = 2`, and `L = 12 d` in every
  `d ≥ 2`), with the constant `C` and the dilation separate. The second part (functions vanishing on the boundary) is proved
  for functions vanishing on `∂_a V`, the points of `V` with an open edge leaving `V`, a subset of the boundary
  `∂(ℤ² ∩ B_R(y)) ∩ 𝒞_∞` of the source; the statement implies the printed one. Declarations:
  [`Rigidity.Green.clusterPoincareTwo_holds`](Rigidity/Proofs/Green/DarioGuPoincareHolds.lean), [`Rigidity.Green.clusterDirichletPoincareTwo_holds`](Rigidity/Proofs/Green/ClusterDirichletPoincare.lean),
  [`Rigidity.WeakPoincare.clusterPoincare_holds`](Rigidity/Proofs/WeakPoincare/VeryGood.lean).
- **Proposition 2.15 (DG21.tex:1147-1162).** The bound is proved for the lazy walk with `C = 200`, by finite
  speed and a Poisson tail at large distances, in place of the argument of Davies cited by DG; for every `d` the
  constant is `100 d²`. Declarations: [`Rigidity.Green.carneVaropoulosTwo_holds`](Rigidity/Proofs/Green/PlanarCarneVaropoulos.lean), [`Rigidity.Green.carneVaropoulos_holds`](Rigidity/Proofs/Green/BondCarneVaropoulos.lean).
- **Propositions 2.9 and 2.11, Lemma 2.10 (DG21.tex:1006-1051).** The printed Lemma 2.10 (DG21.tex:1023-1032),
  with the normalized norms and a constant independent of the configuration, fails: if `𝒞_∞ ∩ B_{R/2}(y)` is a
  path of length of order `R` joining two large clusters of the annulus, a time-independent caloric `u` close to
  `0` on one and to `1` on the other has the square of the left side of order `R^{−2}` and the square of the
  right side of order `R^{−3}`. `DarioGuTimesliceTwo` is the unnormalized form,
  `sup_{t ∈ I_{R/2}} ‖∇u(t)‖²_{L²(𝒞_∞ ∩ B_{R/2})} ≤ C R^{−2} ‖∇u‖²_{L²(I_R × (𝒞_∞ ∩ B_R))}`, which gives the
  printed one where the volumes of `𝒞_∞ ∩ B_R(y)` and `𝒞_∞ ∩ B_{R/2}(y)` are comparable. The source omits the
  proofs of Proposition 2.9 and Lemma 2.10 (DG21.tex:1017-1019 and :1021, the latter by reference to Lemma 8.2
  of Armstrong, Kuusi and Mourrat); they are the standard energy arguments with a spatial cutoff, by summation
  by parts on the cluster, and a time cutoff (Proposition 2.9) or an average over the initial time
  (Lemma 2.10). Declarations: [`Rigidity.Green.darioGuCaccioppoliTwo_holds`](Rigidity/Proofs/Green/DarioGuParabolicCaccioppoli.lean), [`Rigidity.Green.darioGuTimesliceTwo_holds`](Rigidity/Proofs/Green/DarioGuParabolicTimeslice.lean).
- **Theorem 4 (DG21.tex:1220-1229).** Theorem 4 is stated for the constant speed random walk with conductances
  `0` or `1` and is used for the variable speed walk (DG21.tex:1252); the Lean statement
  `BarlowGaussianUpperBoundTwo` is for the variable-speed walk (see the departures from Barlow). Declarations:
  [`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean), [`Rigidity.BarlowLattice.barlowGaussianUpperBound_holds`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean).
- **Theorem 3 (DG21.tex:497-507, Remark 1.3 at DG21.tex:509-514) and Proposition 3.9 (DG21.tex:1690-1703),
  the route.** The source proves Theorem 3 from Proposition 3.9, whose proof goes through Theorem 5. As printed,
  Proposition 3.9 (DG21.tex:1699-1702, `r ∈ [M, R]`) fails at `r = R`: a time-independent `u`, harmonic at the
  interior vertices of `𝒞_∞ ∩ B_R(y)` with values `±1` at the boundary vertices of opposite signs along about
  `cR` open edges between them, has `‖∇u‖²_{L̲²(𝒞_∞ ∩ B_R(y))}` of order `R^{−1}` while the square of the right
  side is at most of order `R^{−2}`; the proof of the source gives the estimate at the radius `r/2` for
  `r ∈ [M, R]` (Step 4), that is for `2r ≤ R`, the range of `DarioGuLipschitzTwo`. Proposition 3.9 remains a
  named statement. Theorem 3 in the form of Remark 1.3 (the gradient on the open edges inside the ball) is proved
  without Proposition 3.9 and without Theorem 5, from Theorem 4, the order-zero regularity of Armstrong and Dario
  and Proposition A.1 by an elliptic estimate for the time slices of the heat kernel: with `D = |x − y| ≤ t` and
  `r ≤ √t/2`, the time slice `v = p(t, x, ·)` is bounded by `U = C t^{−1} e^{−D²/(C t)}` on `B_{3√t}(y)` by
  Theorem 4 and its Laplacian `∂_t p(t, ·, x)` by `F = C t^{−2} e^{−D²/(C t)}`, by Taylor's formula and the bound
  on the second time derivative, and the oscillation estimate at the radius `3r` and the Caccioppoli inequality
  at the radius `r` give `‖∇v‖_{L̲²(𝒞_∞ ∩ B_r(y))} ≤ C t^{−3/2} e^{−D²/(C t)}`. The second time derivative is bounded
  through the signs of `r ↦ p_r(z, z)` and of its first three derivatives, which give
  `∂_r² p_r(z, z) ≤ 8 r^{−2} p_{r/4}(z, z)`, in place of the bound `‖Δ² P_{s/2}‖_{2→2} ≤ C s^{−2}` of the spectral
  theorem, and the bound `sup_z E_z τ_ρ ≤ C ρ²`, obtained in probability by iterating `P_z(τ_ρ > Aρ²) ≤ 1/2`,
  is proved for the exit-time function through the monotonicity of `s ↦ Σ_{w ∈ A} p_s(z, w) e(w) + s`. The
  derivation of Theorem 3 from Proposition 3.9 and Theorem 4 (`darioGuGradientBoundTwo_of_lipschitz`) uses, for
  `2r ≤ R` and `t ≥ 4r²`, the cylinder of top time `t + r²/2` and radius `(7t/8 + r²/2)^{1/2}`, on which the
  times lie in `[t/8, 9t/8]`, in place of the cylinder of the source (`R = √t/2`, top time `t + 1`). The gradient
  on the left of Theorem 3 and Proposition 3.9 is over the open edges inside the ball; the caloric functions are
  functions on `ℝ × ℤ²` constrained on `𝒞_∞ ∩ B_R(y)` (`IsClusterCaloric`), since the coarsening on `B_R(y)`
  reads them at anchors which may lie outside the ball; they are continuous in time at the vertices of the ball
  and solve the equation pointwise in time at its interior vertices. Declarations:
  [`Rigidity.Green.darioGuGradientBoundTwo_holds`](Rigidity/Proofs/Green/DarioGuGradientHolds.lean), [`Rigidity.Green.darioGuGradientBoundTwo_of_barlow`](Rigidity/Proofs/Green/DarioGuGradientDirect.lean),
  [`Rigidity.Green.DarioGuLipschitzTwo`](Rigidity/Proofs/Green/DarioGuParabolicInputs.lean).
- **Theorem 5 (DG21.tex:1280-1311) and its proof (DG21.tex:1280-1684): statements that fail as printed.** With
  all conductances equal to one and `f(t, x) = t`, the right side of (3.11) (DG21.tex:1308) vanishes while the
  solutions `u` and `ū` differ at every large radius, so Theorem 5 fails as printed (entry C40 of
  [`paper/CORRECTIONS.md`](paper/CORRECTIONS.md)); the global Meyers estimate
  (3.19) (DG21.tex:1375) fails for the same data; the interior estimate (3.13) (DG21.tex:1336) fails when the
  radii `r₁` and `r₂` are not comparable (for the time derivatives of the caloric function `exp(x₁ + at)` with
  `r₂` fixed and `r₁` large); and the lattice points in the interior of the convex hull of `ℤ^d ∩ B_r` need
  not be at distance at least `1/√2` from its boundary, as stated in Step 4.1 (DG21.tex:1586; `r² = 26`,
  `x = (4, 2)`), nor at any positive uniform distance. None of these is used. Steps 1, 2, 3 and 5 are proved in
  the forms of the table: in Step 2 the function `w − u` is assumed to vanish on `∂_a V`, which the source
  asserts at DG21.tex:1420 although `w` equals `ū` there, not `f`, at the points of `∂(ℤ² ∩ B_r)` inside the
  convex hull; the decomposition pairs the centered flux `g̃`, not the translated flux `g̃*`, with the forward
  differences `D_i F_k`, the divergence field carries the corrector at the base point of each edge and the extra
  field `−a_i D_i F_i`, and the discrete divergence is `Σ_k D_k F_k`; the left side of (3.25) is printed with
  `∂_t − D*·aD`, while the computation (3.23) is for `∂_t + D*·aD`; (3.26) and (3.27) carry `|V|^{1/2}` in place of
  `r`, and the term a is bounded by the derivatives of `Υ` and of `ū` along the lattice lines separately, in
  place of `‖∇²(Υ∇ū)‖_{L^∞}`. Declarations: [`Rigidity.Green.sum_sq_twoScale_sub_le`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean),
  [`Rigidity.Green.integral_sum_sq_le_of_dirichletPoincare`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean), [`Rigidity.Green.weakNormLe_twoScale_equation`](Rigidity/Proofs/Green/ClusterTwoScaleTerms.lean),
  [`Rigidity.Green.dgStepFive`](Rigidity/Proofs/Green/DarioGuDirichletSteps.lean).
- **Proposition 4.3, (4.27), (4.40), (4.41), (4.47) (DG21.tex:2234-2239).** (a) The
  comparison (4.27) (DG21.tex:2284) of the gradient of the weight at neighbouring points, with a constant `C̃`,
  does not hold for the weight `exp(Ψ_C)` at distances `r ≫ t`. It is replaced by the discrete product rule
  `(q²b − p²a)(b − a) = (qb − pa)² − (q − p)²ab` on the edges and the pointwise bound
  `ψ²(∂_t g/C + A/t) + K max_{|r'−r|≤1}(ψ(r') − ψ(r))² ≤ C₁/t` for `t ≥ 1` and `C ≥ C₀(K)`, which gives (4.41).
  The weight is `exp(dgExponent C t r)`, the exponent of `Φ_C` alone, without the factor `t^{d/2}/C` of `Ψ_C`,
  with which (4.41) fails because of the term `ψ²/t`. (b) Step 3 uses the centered flux of the corrector,
  paired with the forward second differences `D_i D_k P` of the heat kernel, in place of the translated flux and
  the backward differences of the source; the bound for the translated flux follows from Proposition 2.13
  (Remark B.3). (c) The details of (4.26), of the term `Ξ₂` of Step 3 (the bounds of `D³p̄ ψ` and `D²p̄ Dψ`) and
  of the term `F` of Step 4, which the source leaves to the reader (DG21.tex:2274, :2411, :2446), are written
  out; so are the estimate of the term `h − p̄/θ` in the proof of (4.47) (DG21.tex:2556-2562). (d) The times
  satisfy `τ ≥ M` with `M ≥ max(M_flux², M_corr², 1)` and `t ≥ 3τ`, since Step 5 integrates over `[τ, t]`; the
  scale sum of Step 3 is bounded by `Σ_m sup · ‖·‖` without Cauchy–Schwarz, with piecewise linear cutoffs on the
  balls of radius `2^{m+2}√r`, and the truncations are removed by dominated convergence; the bound (4.40) is
  proved for its square root. (e) `DarioGuTwoScaleErrorTwo p σ` is proved for the `σ` of Proposition 2.13
  (`σ = σ̄²`); Theorem 1 uses it for some `σ > 0`. (f) The decomposition (4.47) has `+w` where `w := h − v − q`
  gives `−w` (compare DG21.tex:1944-1948). (g) The weighted `L²` bounds (4.3), (4.24), (4.46) and (4.49), with
  the weight `exp(Ψ_C)`, `Ψ_C = −ln Φ_C` (3.3), carry the normalization `t^{d/2}` differently from the Gaussian
  factor `exp(|x|²/(Ct))` used in (4.48); the Lean weight is `exp(dgExponent)`. Declarations: [`Rigidity.Green.dgWeight_bound`](Rigidity/Proofs/Green/DarioGuTwoScaleWeight.lean), [`Rigidity.Green.dgWeightTrunc_edgeKappa_bound`](Rigidity/Proofs/Green/DarioGuTwoScaleWeightTrunc.lean),
  [`Rigidity.Green.energy_first_pass`](Rigidity/Proofs/Green/DarioGuTwoScaleStepFive.lean), [`Rigidity.Green.energy_second_pass`](Rigidity/Proofs/Green/DarioGuTwoScaleStepFive.lean),
  [`Rigidity.Green.darioGuTwoScaleErrorTwo_of_inputs`](Rigidity/Proofs/Green/DarioGuTwoScaleFluxTerm.lean), [`Rigidity.Green.GeneralDim.tsum_sq_clusterWD_le`](Rigidity/Proofs/Green/GeneralTwoScaleError.lean).
- **Proposition 2.13 = Proposition B.1 (DG21.tex:1128-1137; 2974-2984), Appendix B.** (a) Lattice heat kernel and
  dyadic times: (eq.gsmallH-1) is proved from the heat averages of the flux of `ℤ²` at the dyadic times `4^j ≥ 1`
  against the time increments of the heat flow of the test function, where DG21.tex:3046-3080 use the continuous
  multiscale Poincaré inequality (D.28) of Armstrong, Kuusi and Mourrat and the heat averages at all times
  `t ∈ (0, 1]`; the times below `2` are handled by the moments of the flux itself, the Lipschitz bound of the
  corrector (eq:lip.corr). (b) (B.8), Gu's Proposition 1.1, is used and proved with the heat kernel of `ℤ²`
  on the lattice points in place of a continuous kernel against the piecewise constant extension `[g]`. (c) The
  weak norms on `ℤ²` are stated for test functions vanishing off a finite set `S`, as `Y ‖w‖ + Z ‖∇w‖` with
  explicit moments, which is what the coarsened test functions need; the source writes them as
  `‖·‖_{H̲^{−1}(ℤ^d ∩ B_r)}` with the normalization `r^{−1} ‖φ‖_{L̲²}`. (d) The coarsened function takes `v`
  (extended by zero off `𝒞_∞ ∩ B_r(y)`) at the anchor of the partition cube of the planar partition of the good
  cubes off the cluster (the source chooses the point of `𝒞_*(□)` closest to the centre); the minimal scale
  `M_q(𝒫)` of (eq:Mt) is replaced by the event that every partition cube within `2·3^{n+2} + 2` of `y` has side
  at most `⌊3^{αn/4}⌋`, and the bound of `|ℤ^d ∩ B_r|/|𝒞_∞ ∩ B_r|` used in Step 1 by
  `|𝒞_∞ ∩ B_r(y)| ≥ (2·3^{n−1} + 1)²/L²`. (e) Step 2 is proved on the `3 × 3` triadic cubes of scale `n + 2`
  around the cube of `y`, with the Poincaré inequality on the triadic cubes of
  Percolation-Cluster-Homogenization in the multiscale decomposition; the source passes from `B_r` to the cube
  `□_m ⊇ B_r`. (f) The minimal scale of Lemma 1.6 is the first triadic scale after which every scale is good,
  with `E[exp(M^s)]` bounded uniformly in `y`; for `α > 1` the bound for `min(α, 1)` is used. (g) The bound is
  stated for each component `[g̃_{e_k}]_i`. (h) For every `d ≥ 2` the statement `DarioGuFluxWeakNormD d p σ` has the
  normalized Sobolev norm (1.32) with the factor `|V|^{−1/d}`, bounded below by `|V|^{−1/2}`; the positivity of
  `ā` uses the Lipschitz bound of the corrected planes (Dario, Proposition 2.15) instead of Theorem 2.5; in the
  density bound the term `3^{k+1} 3^{−dk/2}` of each scale is bounded by `3`, so its gradient constant has the
  factor `K + 1` in every dimension (the source has `O_s(C)` for `d ≥ 3`); the cardinality bound
  `|𝒞_∞ ∩ B_r(y)| ≥ (2m + 1)^d/L^d` with `m = 3^{n−d}` replaces the minimal scale of the density. (i) For every
  `d ≥ 2` the proof takes the variance bound (3.4) of Gu's proof of his Proposition 1.1 (`FluxVarianceBoundD d p`)
  as a hypothesis, which is proved for `d = 2`. Declarations: [`Rigidity.Green.darioGuFluxWeakNormTwo_holds`](Rigidity/Proofs/Green/DarioGuFluxWeakNormHolds.lean),
  [`Rigidity.Green.exists_fluxWeakNormBox`](Rigidity/Proofs/Green/DarioGuFluxWeakNormBox.lean), [`Rigidity.Green.exists_densityWeakNorm`](Rigidity/Proofs/Green/DarioGuDensityWeakNorm.lean),
  [`Rigidity.Green.GeneralFlux.darioGuFluxWeakNormD_of_variance`](Rigidity/Proofs/Green/GeneralFluxHolds.lean), [`Rigidity.Green.GeneralFlux.FluxVarianceBoundD`](Rigidity/Proofs/Green/GeneralFluxSpatialAverage.lean).
- **Proposition A.1 and Theorem 6 (DG21.tex:2753-2762, 2842-2847; Proposition A.3 at DG21.tex:2773-2781, Lemma A.4
  at DG21.tex:2810-2827).** DG prove Proposition A.1 with an exponential Efron–Stein inequality (their
  Proposition A.3, from Armstrong and Lin, Proposition 2.2) and the volume tail `exp(−c n^{(d−1)/d})` of finite
  clusters (their Theorem 6, from H. Kesten and Y. Zhang, *The probability of a large finite cluster in
  supercritical Bernoulli percolation*, Ann. Probab. 18 (1990), 537–555). The Lean proof replaces the
  exponential inequality by the iteration of the Efron–Stein variance inequality over the moments, as for
  `d = 2`; for `d ≥ 3` it replaces the tail of Kesten and Zhang by the exponential decay of the radius of finite
  clusters (Grimmett, Theorem (8.21)) and the volume tail `exp(−c n^{1/d})` that follows from it. It obtains
  the scale `3^{−dm/2}` of the source with the exponent `1/(⌊(3d + 3)/2⌋ + 1)` for `d ≥ 3` and `1/7` for `d = 2`,
  which are at least the exponent `2(d − 1)/(3d² + 2d − 1)` of the source, and derives the stated exponent from
  them; for `d = 2` the recursion is
  `E|X|^{2n} ≤ (E|X|ⁿ)² + C n^{14} 3^{−2m} (E|X|^{2n})^{(n−1)/n}` (the exponent `2/15`). Declarations
  (in Percolation-Cluster-Homogenization): `Rigidity.Proofs.S2.cluster_density_concentration`,
  `Rigidity.Proofs.S2.planar_cluster_density_concentration`.
- **Proposition A.7 (DG21.tex:2911-2920).** Only the second part (A.13) is formalized, as printed; the first part
  (A.12), which is stated for every `t > 0` and holds for `t ≥ 1`, is not. The route is the telescoping over
  triadic averages from Proposition A.1, in place of the exponential Efron–Stein inequality (Proposition A.3,
  cited) with (A.5), (A.6) and Lemma A.4; the exponent is `α s₀/2`, `s₀ = 2/15`, with `α > 1/4` reduced to
  `1/4`, and the scale `T_dense = max(81, M^{1/α})`. Declarations: [`Rigidity.Green.darioGuDensityGaussianTwo_holds`](Rigidity/Proofs/Green/DarioGuDensityGaussian.lean),
  [`Rigidity.Green.darioGuDensityGaussianD_holds`](Rigidity/Proofs/Green/DensityGaussianD.lean).
- **Lemma 4.1 (DG21.tex:1977-1990).** It is proved from Theorem 3 in the form of Remark 1.3, used at the radius
  `24R` of the weak Poincaré inequality. The lower bound on the volume of the cluster in balls at the scale `√τ`
  comes from Proposition A.1, and for `|x − y| > t − τ`, where Theorem 3 does not apply,
  `Φ_C(t, r) ≤ C t^{−1/2} Φ_{2C}(t, r)` is used. The minimal time is
  `T = max(M_reg², M_P², M_dens², 2 max(T_dense, 1), T'_NA, 1)` in place of `max(M_reg², T_dense)`. Declaration:
  [`Rigidity.Green.darioGuApproxLemmaTwo_of_gradient`](Rigidity/Proofs/Green/DarioGuTheoremOnePoincare.lean).

### Gu

- **Proposition 1.1 (arXiv:1907.13571), (B.8) of DG.** (B.8) is proved with the heat kernel of `ℤ²` on the lattice
  points in place of a continuous kernel against the piecewise constant extension. The variance bound (3.4) of
  Gu's proof, `𝕍[Φ_{r²} ⋆ flux(x)] ≤ O_s(C r^{−d})`, which in the source follows from `𝕍[X] ≤ Σ_e (D_e X)²` and
  the bound of the vertical derivatives through the Green function of the cluster (the argument of Step 2 of
  Dario's Lemma 3.3), is proved for `d = 2` (`fluxFlipSum_isOsBond`, `fluxVarianceBoundD_two`) and is the named
  hypothesis `FluxVarianceBoundD d p` for `d ≥ 3`. Declarations: [`Rigidity.Green.exists_fluxSpatialAverage_two`](Rigidity/Proofs/Green/DarioGuFluxSpatialAverage.lean),
  [`Rigidity.Green.GeneralFlux.exists_fluxSpatialAverageD`](Rigidity/Proofs/Green/GeneralFluxSpatialAverage.lean).

### Barlow

- **Balls, walk and the proof of Theorem 1.** The balls are the sets `B(z, r) ∩ 𝒞_∞` of the Euclidean distance,
  not the balls of the chemical distance, and the good balls of Definition 1.7 are defined with them, with the
  energy of the Poincaré inequality on the ball of radius `Lr`; the measure is the counting measure (Barlow's
  `μ_x` is the number of open edges at `x`, which changes the constants only, as `1 ≤ μ_x ≤ 2d` on `𝒞_∞`) and
  the centre is any lattice point; the very good balls are stated for all radii `r ≥ R^θ` (Barlow:
  `N_B ≤ r ≤ R`, `N_B ≤ R^{1/(d+2)}`). The Euclidean balls are a different family from Barlow's balls of the
  graph distance, not a change of constants. The Gaussian bound is stated with the Euclidean distance, as DG
  quote it; the step of the proof of Theorem 1 that replaces the chemical distance by `|x − y|₁` is not needed.
  The walk is the variable-speed walk of DG, with rate one on each open edge, in place of the constant-speed
  walk `Y` of the source, whose kernel `q_t` is taken with respect to the degree measure; its heat kernel is
  `p_t(x, y) = E[P^x(X_{N_{4t}} = y)]` (`N_{2dt}` for `ℤ^d`), where `X` is the lazy jump chain that stays put
  with probability `1 − deg(x)/4` (`1 − deg(x)/(2d)`) and `N` is a Poisson clock of rate one. Declarations:
  [`Rigidity.WeakPoincare.clusterGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/GoodBallsHolds.lean), [`Rigidity.WeakPoincare.clusterVeryGoodBalls_holds`](Rigidity/Proofs/WeakPoincare/VeryGood.lean),
  [`Rigidity.Barlow.barlowGaussianUpperBoundTwo_holds`](Rigidity/Proofs/Barlow/UpperBoundHolds.lean), [`Rigidity.BarlowLattice.barlowGaussianUpperBound_holds`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean).
- **Proposition 3.1 and Corollary 3.2.** The bound (1.7) is not used: the comparison argument starts with the
  good balls of radius `N`, and the bounds are proved for `t ≤ R` in place of `t ≤ c R²/log R`, which is enough
  since Proposition 6.1 applies them with `R = 36t`. The bound `p_s(x, y) ≤ ε` at distance `R/18` comes from the
  Carne–Varopoulos bound, in place of Lemma 1.1(b). For `ℤ^d` the covering bound (3.4) reads
  `Σ_{B(x₀, ρ)} f² ≤ 5^d C_P L^d C_V^{−1} r² E(f) + 5^d C_V^{−2} r^{−d}`; the choice `r^d = 4β/ψ` gives
  `ψ' ≤ −c ψ^{1+2/d}`, which is integrated as `(ψ^{2/d})' ≤ −(2c/d)(ψ^{2/d})²`; the initial time is
  `T₀ = C_P L^d C_V N^{d+2}`. Declarations: [`Rigidity.Barlow.openHeat_diag_le_of_good`](Rigidity/Proofs/Barlow/OnDiagonal.lean),
  [`Rigidity.BarlowLattice.bondHeat_diag_le_of_good`](Rigidity/Proofs/BarlowLattice/OnDiagonal.lean).
- **Lemma 3.3 and Proposition 3.4.** The integral argument of Proposition 3.4 is replaced by the monotonicity of
  `M(s) − 4√s − √s (Q(s) − c₁ − log s)` on `[T₀, t]`; only the upper bound of `M(t)` is proved. For `ℤ^d` the
  lattice sum `Σ_y e^{−|y − x|/M} ≤ (6d)^d M^d` gives `Q(t) ≤ K_d + d log M(t)`, and the entropy bound enters
  Proposition 3.4 as `Q(s) ≥ c₁ + (d/2) log s`. Declarations: [`Rigidity.Barlow.meanDist_le_of_entropy`](Rigidity/Proofs/Barlow/MeanDisplacement.lean),
  [`Rigidity.BarlowLattice.meanDist_le_of_entropy`](Rigidity/Proofs/BarlowLattice/MeanDisplacement.lean).
- **Lemmas 3.5, 3.6, Proposition 3.7.** They are proved for the lazy jump chain: the strong Markov property at
  exit times is replaced by first-step recursions for the exit probabilities and the truncated generating
  functions, and optional stopping by backward induction; Lemma 3.6 enters through the submultiplicativity of
  `E^x[s^σ]` along nested balls. The continuous-time walk enters through the Poisson clock: the mean displacement
  of the jump chain is bounded by that of the walk, `E^z\|X_k − z\| ≤ M(z, k/4) + 6√k`, and the clock adds the
  term `e^{−t}` to Proposition 3.7. For `ℤ^d` the rate is `2d`, so that `M(t) ≤ 2dt`, the walk makes at most
  `8dt` steps by time `t` except with probability `e^{−t}`, and Lemma 3.5 is applied for `n ≤ dR` steps.
  Declarations: [`Rigidity.Barlow.exitProb_clBall_le`](Rigidity/Proofs/Barlow/ExitTail.lean), [`Rigidity.Barlow.BarlowRegion.tsum_far_le`](Rigidity/Proofs/Barlow/GaussianTail.lean),
  [`Rigidity.BarlowLattice.exitProb_clBall_le`](Rigidity/Proofs/BarlowLattice/ExitTail.lean).
- **Theorem 3.8.** In place of the decomposition (3.20)–(3.21) at the exit time of `B(x, |x − y|/2)`,
  `p_t(x, y) = Σ_z p_{t/2}(x, z) p_{t/2}(z, y)` is split according to `|z − x| ≥ |x − y|/2` or
  `|z − y| ≥ |x − y|/2`; the factor on the near side is bounded by Corollary 3.2 and the sum on the far side by
  Proposition 3.7. At distances `|x − y| > κt/r₁` the Carne–Varopoulos bound is used directly. Declarations:
  [`Rigidity.Barlow.BarlowRegion.openHeat_le_gauss`](Rigidity/Proofs/Barlow/GaussianBound.lean), [`Rigidity.BarlowLattice.BarlowRegion.bondHeat_le_gauss`](Rigidity/Proofs/BarlowLattice/GaussianBound.lean).
- **Proposition 6.1.** The ball is `B(y, R)` with `R = 36t` and `N = R^{1/64}` (`N = R^{1/K}`, `K = 4d + 12`,
  for `ℤ^d`); the times of Section 3 are polynomial in `N` (`T_G ≤ c_T N^{16}`, respectively
  `T_G ≤ c_T N^{4(d+2)}`), so the hypotheses of Section 3 hold for `t ≥ max(S_y/36, k₀)`; for `|x − y| > t` the
  bound is the Carne–Varopoulos bound, and for `ℤ^d` the factor `t^{−d/2}` comes from
  `e^{−t/(2C)} ≤ d! (2C)^d t^{−d}` and `t ≥ 1`. Declarations: [`Rigidity.Barlow.barlowGaussianUpperBoundTwo_of_veryGood`](Rigidity/Proofs/Barlow/GaussianHolds.lean),
  [`Rigidity.BarlowLattice.barlowGaussianUpperBound_of_veryGood`](Rigidity/Proofs/BarlowLattice/GaussianHolds.lean).

### Other cited results

- **Proposition 2.3 of the paper.** For `d = 2` it is proved from Kesten's rectangle-crossing estimate, in place
  of the estimate of Couronné and Messikh, with `s = 1/800 = 1/(d(10d)²)`: in the square `z + Q_M`, `M ≥ 10⁴`,
  with `w = ⌊√M⌋/100`, outside an event of probability at most a polynomial in `M` times `exp(−c w)`, every
  horizontal and vertical strip of width `w` has an open crossing in its long direction and the square has a
  unique crossing cluster, so the square is good, and a union bound over the subcubes gives the statement. For
  `d ≥ 3` the statement is proved, with Pisztora's box estimate replaced by crossing estimates from slab
  connectivity, in Percolation-Cluster-Homogenization. Declarations: [`Rigidity.Percolation.wellConnected_input_two`](Rigidity/Proofs/Percolation/PlanarWellConnected.lean),
  [`Rigidity.Percolation.wellConnected_input`](Rigidity/Proofs/Percolation/WellConnected.lean).
- **Lemma 2.14 of the paper.** Printed for a continuous loop; the theorem is for simple loops, and the Lean
  statement is for simple loops (correction C38). Declaration: [`Rigidity.Topology.jordan_curve_theorem_sphere`](Rigidity/Proofs/Topology/JordanCurveSphere.lean).

## Hypotheses that remain open for `d ≥ 3`

- `DarioResamplePartitionThree` ([`Rigidity.Corrector.GeneralDim.DarioResamplePartitionThree`](Rigidity/Proofs/Corrector/GeneralResamplePartition.lean)): Lemma 3.5 of Dario
  in the printed form; see the first entry of the departures from Dario.
- `DarioStepTwoWeightThree` ([`Rigidity.Corrector.GeneralDim.DarioStepTwoWeightThree`](Rigidity/Proofs/Corrector/GeneralStepTwoReduce.lean)): the probabilistic part of
  Step 2 of Lemma 3.3 of Dario, the partition of the good cubes of Step 2 and the moments of the weight.
  With the previous hypothesis it gives Lemma 3.3 (`DarioVarianceBoundThree`), Theorem 1 of Dario
  (`DarioOptimalCorrectorThree`) and, with the qualitative corrector input, `CorrectorQuantitativeInput`
  (Proposition 2.12 of DG).
- `FluxVarianceBoundD d p` ([`Rigidity.Green.GeneralFlux.FluxVarianceBoundD`](Rigidity/Proofs/Green/GeneralFluxSpatialAverage.lean)), and for all `d ≥ 3`
  `FluxVarianceBoundThree` ([`Rigidity.Green.GeneralFlux.FluxVarianceBoundThree`](Rigidity/Proofs/Green/GeneralFluxStepTwoInput.lean)): the variance bound (3.4) of Gu's
  proof of his Proposition 1.1. With it Proposition 2.13 of DG holds on `ℤ^d`, and with `CorrectorQuantitativeInput`
  it gives `DarioGuHeatKernelD d` (Theorem 1 of DG) and `SupercriticalBondGreenQuantitative` (Theorem 2 of DG).

Not formalized: Theorem 5 and Theorem 6 of DG, the first part (A.12) of Proposition A.7, Theorem 3 of DG for
`d ≥ 3`, and Proposition 3.9 beyond its statement `DarioGuLipschitzTwo`.
