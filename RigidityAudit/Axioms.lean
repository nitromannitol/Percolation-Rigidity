import Rigidity
import Rigidity.Proofs.Assembly.Main
import Rigidity.Proofs.Assembly.Section2
import Rigidity.Proofs.Assembly.Section3
import Rigidity.Proofs.Assembly.Section4
import Rigidity.Proofs.Assembly.Section5
import Rigidity.Proofs.Assembly.Section5b
import Rigidity.Proofs.Assembly.Section5d
import Rigidity.Proofs.Assembly.Section5e

/-! The axiom report of every numbered result of the paper; `scripts/check_axioms.py` checks it.

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
