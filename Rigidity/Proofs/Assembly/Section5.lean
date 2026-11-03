import Rigidity.Proofs.Section5.LogGrowth
import Rigidity.Proofs.Section5.ConnectingSet
import Rigidity.Proofs.Section5.FlowOnConnectedSet
import Rigidity.Proofs.Section5.SummationByParts
import Rigidity.Steps.Section5.MeanZeroRepresentation
import Rigidity.Proofs.Section5.LoopFromCrossings
import Rigidity.Proofs.Section5.RecurrenceBarrier
import Rigidity.Steps.Section5.PolesSuperLevelSets
import Rigidity.Steps.Section5.LongNonzeroPaths
import Rigidity.Proofs.Section5.ManyPaths
import Rigidity.Proofs.Section5.Signs
import Rigidity.Proofs.Section5.Separation
import Rigidity.Steps.Section5.NoThickPaths
import Rigidity.Proofs.Section5.Connector
import Rigidity.Proofs.Section5.JordanLoop
import Rigidity.Proofs.Section5.TraceCrossing
import Rigidity.Steps.Section5.InfiniteDisjointPaths
import Rigidity.Proofs.Section5.VeryGoodProbability
import Rigidity.Proofs.Section5.RenormField
import Rigidity.Proofs.Section5.Peierls
import Rigidity.Proofs.Section5.MengerRays
import Rigidity.Proofs.Section5.KestenChannelCut
import Rigidity.Steps.Section5.DisjointPathsToInfinity
import Rigidity.Proofs.Section5.InfiniteBranches
import Rigidity.Proofs.Section5.LeafSeparator
import Rigidity.Proofs.Section5.NoK33Minor

/-! # Section 5: composed theorems for the finished results (d = 2)

Each theorem below concludes exactly the draft statement `Rigidity.Section5.…Stmt` of a numbered
result of Section 5, under the standing regime `p_c(2) < p < 1` and the literature inputs it uses,
each an explicit hypothesis whose `Prop` lives in `Rigidity.External` or `LatticeProb.External`:

* `LatticeProb.External.SupercriticalBondUniqueness`: almost sure uniqueness of the infinite
  cluster (Grimmett, *Percolation*, Theorems 1.10 and 8.1);
* `LatticeProb.External.SupercriticalBondGreenQuantitative`: the quantitative Green function
  asymptotics on the infinite cluster (Dario–Gu);
* `Rigidity.External.WellConnectedInput`: Proposition 2.3 (well-connected cubes);
* `Rigidity.External.KestenRectangleCrossing`: Kesten's rectangle crossing estimate (Theorem 11.1);
* `Rigidity.External.JordanCurveTheoremSphere`: the Jordan curve theorem on the sphere.

The homogenized coefficient `ā` does not enter any of these results, so the local
`HomogenizedCoefficientProposed` of `Rigidity/Proofs/S3/FluxEvent.lean` is not used here.

Every proof applies the reduction `…_of_steps` of `Rigidity/Steps/Section5` to the proved step
theorems of `Rigidity/Proofs/Section5`; the upstream results it consumes (Lemmas 5.14, 5.16 and
5.19) are the composed theorems of this file. Proposition 5.21 follows the Peierls route
(`disjointPathsToInfinity_of_peierls`), which does not use Proposition 5.22.

Lemma 5.28 (`FiniteBranchesStmt`) composes `finiteBranches_of_steps` with the steps proved in
`Rigidity/Proofs/Section5/InfiniteBranches.lean`, `LeafExit.lean`, `LeafSeparator.lean` and
`NoK33Minor.lean`, and with Lemma 5.16 and Proposition 5.12 of this file. -/

namespace Rigidity.Assembly

open LatticeProb.Percolation LatticeProb.Lattice Rigidity.Section5 Rigidity.Steps.Section5

/-- **Proposition 5.5** (`LogGrowthStmt`): for `p_c(2) < p < 1` and finitely supported `f`, almost
surely, if `Σ f ≠ 0` then `u_f = Θ(log |x|)`. Inputs: uniqueness of the infinite cluster and the
quantitative Green function asymptotics. -/
theorem logGrowth (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    LogGrowthStmt p f :=
  logGrowth_of_steps (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    (Proofs.Section5.potentialAsymptotic hGQ hp hp1)
    (Proofs.Section5.asymptoticLogBounds_of_logNormComparison
      (Proofs.Section5.logNormComparison_of_normComparison Proofs.Section5.normComparison)) f

/-- **Lemma 5.6** (`MeanZeroRepresentationStmt`): for `p_c(2) < p < 1` and finitely supported `f`,
on `Σ f = 0` the potential `u_f` is a combination `Σ_e F(e) ∇_y G(x, e)` with a finitely supported
vector field `F` whose support size and `L²` norm are `O_s(C_f)`. Inputs: uniqueness of the
infinite cluster and Proposition 2.3. -/
theorem meanZeroRepresentation (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hW : Rigidity.External.WellConnectedInput) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    MeanZeroRepresentationStmt p f :=
  meanZeroRepresentation_of_steps hp hp1 hW (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    Proofs.Section5.connectingSetStep Proofs.Section5.flowOnConnectedSet
    Proofs.Section5.summationByParts f

/-- **Lemma 5.14** (`LoopsAroundAnnuliStmt`): for `p_c(2) < p < 1`, almost surely the infinite
cluster contains, beyond a random scale, a loop in every annulus `Q_{2R} \ Q_R` winding around
the origin. Inputs: uniqueness of the infinite cluster and Kesten's crossing estimate. -/
theorem loopsAroundAnnuli (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hK : Rigidity.External.KestenRectangleCrossing) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : LoopsAroundAnnuliStmt p :=
  loopsAroundAnnuli_of_steps hK hp (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    Proofs.Section5.crossingProbabilityStep Proofs.Section5.borelCantelliStep
    Proofs.Section5.loopFromCrossingsStep

/-- **Lemma 5.16** (`StrongMaxPrincipleStmt`, the strong maximum principle on the planar infinite
cluster): for `p_c(2) < p < 1`, almost surely a bounded function harmonic on an infinite proper
subset `Ω` of the cluster is bounded on `Ω` by its supremum on the outer boundary of `Ω`. Input:
uniqueness of the infinite cluster. -/
theorem strongMaxPrinciple (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    StrongMaxPrincipleStmt p :=
  strongMaxPrinciple_of_steps (Proofs.Section5.uniqueClusterAe hUq hp hp1)
    Proofs.Section5.finiteMaxPrinciple Proofs.Section5.recurrenceBarrier

/-- **Lemma 5.17** (`PolesSuperLevelSetsStmt`): for `p_c(2) < p < 1` and finitely supported `f`,
almost surely every connected component of a super-level set `{u > a}` of a decaying potential
`u` with infinite support meets `supp f`. Input: uniqueness of the infinite cluster. -/
theorem polesSuperLevelSets (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : PolesSuperLevelSetsStmt p f :=
  polesSuperLevelSets_of_steps Proofs.Section5.finiteMaxPrinciple
    (strongMaxPrinciple hUq hp hp1) f

/-- **Lemma 5.18** (`LongNonzeroPathsStmt`): for `p_c(2) < p < 1` and finitely supported
`f ⊆ Q_R`, almost surely for every `R' > R` some path of the cluster from `Q_R` to the complement
of `Q_{R'}` avoids the zero set of a decaying potential `u` with infinite support. Input:
uniqueness of the infinite cluster. -/
theorem longNonzeroPaths (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    {p : unitInterval} (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (f : Vertex 2 → ℤ) : LongNonzeroPathsStmt p f :=
  longNonzeroPaths_of_steps Proofs.Section5.finiteMaxPrinciple (strongMaxPrinciple hUq hp hp1) f

/-- **Lemma 5.19** (`NoThickPathsStmt`): for `p_c(2) < p < 1` and finitely supported `f`, almost
surely a decaying potential `u` with infinite support has no bi-infinite path in `L_0` one of
whose complementary components has all its cluster points in `L_0`. Inputs: uniqueness of the
infinite cluster, Kesten's crossing estimate (through Lemma 5.14) and the Jordan curve theorem. -/
theorem noThickPaths (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    NoThickPathsStmt p f :=
  noThickPaths_of_steps hJ (strongMaxPrinciple hUq hp hp1) (loopsAroundAnnuli hUq hK hp hp1)
    Proofs.Section5.manyPathsStep Proofs.Section5.signsStep Proofs.Section5.separationStep

/-- **Proposition 5.12** (`InfiniteDisjointPathsStmt`): for `p_c(2) < p < 1` and finitely
supported `f`, almost surely a connected component of the zero level set `L_0` of a decaying
potential with infinite support contains at most `|supp f| + 2` disjoint infinite paths. Inputs:
uniqueness of the infinite cluster, Kesten's crossing estimate (through Lemma 5.19) and the
Jordan curve theorem. -/
theorem infiniteDisjointPaths (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    InfiniteDisjointPathsStmt p f :=
  infiniteDisjointPaths_of_steps hJ (strongMaxPrinciple hUq hp hp1)
    (noThickPaths hUq hK hJ hp hp1 f) Proofs.Section5.connectorStep
    (Proofs.Section5.jordanLoopStep hJ) Proofs.Section5.traceCrossingStep

/-- **Proposition 5.21** (`DisjointPathsToInfinityStmt`): for `p_c(2) < p < 1` there is `s > 0`
such that for every `C_f` the event `E_R(x)` fails with probability at most `C exp(-c R^s)`.
Proved by the Peierls route (`disjointPathsToInfinity_of_peierls`); inputs: Proposition 2.3 and
Kesten's crossing estimate. The hypothesis `p < 1` is not used by this route. -/
theorem disjointPathsToInfinity (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (_hp1 : (p : ℝ) < 1) :
    DisjointPathsToInfinityStmt p :=
  disjointPathsToInfinity_of_peierls hW hK hp Proofs.Section5.veryGoodProbabilityStep
    Proofs.Section5.renormFieldMeasurableStep Proofs.Section5.renormFieldOneDependentStep
    Proofs.Section5.oneDependentPeierlsStep Proofs.Section5.mengerRaysStep
    Proofs.Section5.kestenChannelCutStep

/-- **Lemma 5.28** (`FiniteBranchesStmt`): for `p_c(2) < p < 1` and finitely supported `f`, there is
`C_branches` such that, almost surely, for every decaying potential `u` with infinite support and
every admissible `x₀` in the cone beyond a random scale, the pruned block-cut tree `𝒢_tree` has at
most `C_branches` branches. Inputs: uniqueness of the infinite cluster, the Kesten rectangle
crossing estimate (through Proposition 5.12) and the Jordan curve theorem on the sphere. -/
theorem finiteBranches (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hK : Rigidity.External.KestenRectangleCrossing)
    (hJ : Rigidity.External.JordanCurveTheoremSphere) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    FiniteBranchesStmt p f :=
  finiteBranches_of_steps hJ (strongMaxPrinciple hUq hp hp1)
    (infiniteDisjointPaths hUq hK hJ hp hp1 f) Proofs.Section5.infiniteBranchesStep
    Proofs.Section5.leafExitStep Proofs.Section5.exitsDistinctStep
    Proofs.Section5.leafSeparatorStep Proofs.Section5.noK33MinorStep

end Rigidity.Assembly
