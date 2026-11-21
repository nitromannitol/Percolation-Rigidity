#!/usr/bin/env python3
"""Require one axiom report for each declaration of RigidityAudit/Axioms.lean, listing no axiom
other than propext, Classical.choice and Quot.sound: the numbered results of the paper and the
further proved results listed below.

    lake env lean RigidityAudit/Axioms.lean 2>&1 | tee axioms-audit.log
    python3 scripts/check_axioms.py axioms-audit.log

The literature inputs are hypotheses of the theorems, not axioms. Lean may wrap a long report over
several lines; each report is joined before it is read.
"""
import re
import sys

# Numbered result -> its Lean declarations. A proved result is reported through its theorem, a
# cited result through the proposition that states it; Lemma 2.13 is cited and used by no proof.
results = {
    'Theorem 1.1': ['Rigidity.Assembly.Main.lipschitz'],
    'Theorem 1.2': ['Rigidity.Assembly.Main.integerValuedLinearGrowth'],
    'Theorem 1.3': ['Rigidity.Assembly.Main.fastDecay'],
    'Lemma 2.1': ['Rigidity.finite_flip_full_measure'],
    'Proposition 2.3': ['Rigidity.External.WellConnectedInput'],
    'Theorem 2.4': ['LatticeProb.External.ArmstrongDarioOrderZero',
                    'Rigidity.External.ArmstrongDarioOrderOneOrigin'],
    'Theorem 2.5': ['LatticeProb.External.SupercriticalBondCorrectorInput',
                    'Rigidity.External.CorrectorQuantitativeInput'],
    'Proposition 2.6': ['Rigidity.Assembly.Main.greenGradientHomogenization'],
    'Proposition 2.8': ['Rigidity.mixed_green'],
    'Lemma 2.13': [],
    'Lemma 2.14': ['Rigidity.External.JordanCurveTheoremSphere'],
    'Lemma 2.16': ['Rigidity.Assembly.jordanCurves'],
    'Lemma 3.1': ['Rigidity.Assembly.reductionToSlopeE1'],
    'Proposition 3.2': ['Rigidity.Assembly.Main.notLipschitz'],
    'Lemma 3.3': ['Rigidity.Assembly.compareDifferentPlanes'],
    'Proposition 4.1': ['Rigidity.OpenGadget.exponential_growth_on_ambient_open_gadget'],
    'Lemma 4.2': ['Rigidity.Assembly.effectiveResistanceRecurrence'],
    'Lemma 4.3': ['Rigidity.Assembly.reducedRationalRecursion'],
    'Lemma 4.4': ['Rigidity.Gadget.numDenomRecs'],
    'Lemma 4.5': ['Rigidity.Gadget.reducedRational'],
    'Lemma 4.6': ['Rigidity.Gadget.exponentialGrowth'],
    'Lemma 4.7': ['Rigidity.Assembly.detSlope'],
    'Lemma 4.8': ['Rigidity.Assembly.Main.nonConstantOnGadget'],
    'Lemma 4.9': ['Rigidity.Assembly.ergodicityLipschitz'],
    'Proposition 4.10': ['Rigidity.Assembly.rationalMatrix'],
    'Theorem 5.1': ['Rigidity.Assembly.Main.fastDecayDichotomy'],
    'Proposition 5.3': ['Rigidity.Assembly.Main.fastDecayPotential'],
    'Proposition 5.5': ['Rigidity.Assembly.logGrowth'],
    'Lemma 5.6': ['Rigidity.Assembly.meanZeroRepresentation'],
    'Proposition 5.7': ['Rigidity.Assembly.Main.gradientTrichotomy'],
    'Proposition 5.8': ['Rigidity.Assembly.Main.twoScaleExpansion'],
    'Proposition 5.11': ['Rigidity.Assembly.Main.levelSetDensity'],
    'Proposition 5.12': ['Rigidity.Assembly.infiniteDisjointPaths'],
    'Lemma 5.14': ['Rigidity.Assembly.loopsAroundAnnuli'],
    'Lemma 5.16': ['Rigidity.Assembly.strongMaxPrinciple'],
    'Lemma 5.17': ['Rigidity.Assembly.polesSuperLevelSets'],
    'Lemma 5.18': ['Rigidity.Assembly.longNonzeroPaths'],
    'Lemma 5.19': ['Rigidity.Assembly.noThickPaths'],
    'Proposition 5.20': ['Rigidity.Assembly.boundarySize'],
    'Proposition 5.21': ['Rigidity.Assembly.disjointPathsToInfinity'],
    'Lemma 5.23': ['Rigidity.Assembly.renormalizedDomination'],
    'Proposition 5.24': ['Rigidity.Assembly.longPathRenormalized'],
    'Lemma 5.25': ['Rigidity.Assembly.Main.goodEventLowerBound',
                   'Rigidity.Assembly.Main.goodEventLowerBoundDirectional'],
    'Lemma 5.26': ['Rigidity.Assembly.Main.goodEventDensity'],
    'Lemma 5.27': ['Rigidity.Assembly.Main.largeGradientSensitive'],
    'Lemma 5.28': ['Rigidity.Assembly.finiteBranches'],
    'Proposition 6.4': ['Rigidity.integer_valued_compact_support'],
    'Theorem 6.5': ['Rigidity.Assembly.Main.slowMixing'],
}
cited = {'Proposition 2.3', 'Theorem 2.4', 'Theorem 2.5', 'Lemma 2.13', 'Lemma 2.14'}
# Further proved results: results that are not numbered results of the paper, proofs of literature
# inputs, and forms of the main theorems with fewer hypotheses.
further = {
    'Slab connectivity (Grimmett and Marstrand, d >= 3)':
        ['Rigidity.Percolation.uniformCubeSlabConnectivity_of_criticalProbability_lt'],
    'Proposition 2.3 for d >= 3 and its reduction to d = 2':
        ['Rigidity.Percolation.wellConnected_of_three_le',
         'Rigidity.Percolation.wellConnectedInput_of_planar'],
    'Finite clusters (d >= 3)':
        ['Rigidity.Percolation.exists_finite_cluster_radius_le',
         'Rigidity.Percolation.exists_finite_cluster_card_le'],
    'Proposition 2.3 in every dimension':
        ['Rigidity.Percolation.wellConnected_input'],
    'Proposition 2.3 and the density concentration (d = 2)':
        ['Rigidity.Percolation.wellConnected_input_two',
         'Rigidity.Proofs.S2.planar_cluster_density_concentration'],
    'Theorem 6.5 with every literature input proved':
        ['Rigidity.Assembly.Unconditional.slow_mixing'],
    'Theorem 1.3 from its dimension-two inputs':
        ['Rigidity.Assembly.WithPlanarInputs.fast_decay',
         'Rigidity.Assembly.WithPlanarInputs.fast_decay_of_green_exists'],
    'Density concentration in every dimension':
        ['Rigidity.Proofs.S2.cluster_density_concentration',
         'Rigidity.Assembly.WithProvedDensity.green_gradient_homogenization',
         'Rigidity.Assembly.WithProvedDensity.fast_decay'],
    'Planar Green-column existence and Theorem 1.3 from five dimension-two inputs':
        ['Rigidity.Proofs.Section5.planar_greenColumn_exists',
         'Rigidity.Assembly.WithPlanarInputs.supercriticalBondGreenColumnExistenceTwo_of_orderZero',
         'Rigidity.Assembly.WithPlanarInputs.fast_decay_of_planar_estimates'],
    'Green columns for d >= 3, the Green-column input from the planar order-zero estimate, '
    'and the heat kernel and Green column bounds':
        ['Rigidity.Green.latticeIsoperimetry',
         'Rigidity.Green.greenColumnExistence_of_three_le',
         'Rigidity.Green.supercriticalBondGreenColumnExistence_of_two',
         'Rigidity.Green.supercriticalBondGreenColumnExistence_of_orderZeroTwo',
         'Rigidity.Green.heat_le_of_two_le',
         'Rigidity.Green.greenColumn_le_rpow_of_three_le',
         'Rigidity.Green.greenColumn_le_one_add_rpow_of_three_le'],
    'the multiscale Poincare inequality of Armstrong and Dario (Proposition A.2) and its affine form':
        ['Rigidity.Proofs.Multiscale.multiscalePoincare_holds',
         'Rigidity.Proofs.Multiscale.exists_multiscalePoincare_affine'],
}
standard = {'propext', 'Classical.choice', 'Quot.sound'}

if len(results) != 48:
    raise SystemExit(f'The list must have the 48 numbered results, not {len(results)}')
expected = [name for names in list(results.values()) + list(further.values()) for name in names]
if len(set(expected)) != len(expected):
    raise SystemExit('A declaration is listed twice')
if len(sys.argv) != 2:
    raise SystemExit('Usage: check_axioms.py <log of RigidityAudit/Axioms.lean>')
with open(sys.argv[1], encoding='utf-8') as handle:
    log = handle.read()
if re.search(r'(^|[\s:])error:|warning:|sorryAx|declaration uses .sorry', log, re.IGNORECASE | re.MULTILINE):
    raise SystemExit('The axiom audit emitted an error or a warning, or reported sorryAx')
reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",
                     log, re.S)
seen = set()
for name, axioms, _ in reports:
    if name not in expected or name in seen:
        raise SystemExit('Unexpected or repeated axiom report: ' + name)
    actual = {a.strip() for a in axioms.split(',') if a.strip()}
    if not actual <= standard:
        raise SystemExit('Nonstandard axioms for ' + name + ': ' + ', '.join(sorted(actual - standard)))
    seen.add(name)
missing = [name for name in expected if name not in seen]
if missing:
    raise SystemExit('Missing axiom reports: ' + ', '.join(missing))
proved = [r for r in results if r not in cited]
print(f'All {len(results)} numbered results checked: the {len(proved)} proved results '
      f'({sum(len(results[r]) for r in proved)} theorems) and the propositions stating '
      f'{len(cited) - 1} cited results ({sum(len(results[r]) for r in cited)} declarations) '
      f'use only propext, Classical.choice and Quot.sound; Lemma 2.13 is cited and used by no '
      f'Lean proof.')
print(f'The {len(further)} further proved result(s) ({", ".join(further)}) use only propext, '
      f'Classical.choice and Quot.sound.')
