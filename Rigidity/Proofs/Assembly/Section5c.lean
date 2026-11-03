import Rigidity.Proofs.Section5.CorrectedPlaneMinimalScale
import Rigidity.Proofs.Section5.RootBlock
import Rigidity.Proofs.Section5.FluxBalance
import Rigidity.Proofs.Section5.FluxGrowth
import Rigidity.Proofs.Section5.ExplorationAssembly

/-! # Section 5: the proved steps of Lemma 5.27 (d = 2)

This module gathers the proved steps of Lemma 5.27 (`lemma:large-gradient-implies-not-in-level-set`,
corrected draft L2413-2419). The composed Lemma 5.27 in draft form (`LargeGradientSensitiveStmt`,
universal `G_1` [C31], direction-free `G_3` [C32]) is `Rigidity.Assembly.largeGradientSensitive`
(`Rigidity/Proofs/Assembly/Section5Decay.lean`), from `largeGradientSensitive_of_steps`
(`Rigidity/Steps/Section5/DirectionFree.lean`). -/
