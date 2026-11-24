import Rigidity.Steps.Section5.DisjointPathsToInfinity
import LatticeProb.Prob.Percolation.LSSThinVacuity
import PercolationClusterHomogenization.Proofs.Planar.Peierls

/-!
# Proposition 5.21: the Peierls bounds

This file proves the steps `SiteDensityNearOneStep` (`step:5.21-site-density`) and
`OneDependentPeierlsStep` (`step:5.21-peierls`) of Proposition 5.21
(`Rigidity/Steps/Section5/DisjointPathsToInfinity.lean`; corrected draft L2154-2158,
L2253-2276). The printed proof cites Grimmett, *Percolation*, Theorem 8.92 for the first; both
follow from one Peierls bound, valid for every `1`-dependent site field on `ℤ²` (for the
`ℓ^∞` distance) whose sites are closed with probability at most `ε`:
`P(z is not in an infinite open cluster) ≤ 64⁹ ε` (`measure_not_inInfiniteSiteCluster_le`).

**Duality** (`exists_closedStarWalk`). Let `z` be open with a finite open cluster `C`, and let
`u = z + (k₀, 0)` be the last site of `C` on the horizontal ray from `z`. The lattice edges with
exactly one endpoint in `C` (the edge boundary of `C`) form, with two of them adjacent when
they are edges of a common plaquette, the dual boundary graph (`boundaryGraph`); let `Γ` be the
component of the edge `D₀` from `u` to `u + (1, 0)`. Every plaquette has an even number of edges
in `Γ` (`plaquette_sum_eq_zero`: if it has one, its edges in `Γ` are its boundary edges, and the
four corners of a plaquette change membership in `C` an even number of times). Hence the parity
`F(a)` of the number of edges of `Γ` crossed by the horizontal ray from `a` satisfies
`F(a) + F(b) = 1_{ab ∈ Γ}` for each lattice edge `ab` (`rowCount_succ_fst`,
`rowCount_add_succ_snd`): `F` is constant on `C`, equal to `F(u) = 1`, and vanishes on the
column `x = -B - 2` left of `C`. So `Γ` crosses the ray to the left of `z`. The outer endpoints of
the edges of `Γ` are closed and `*`-connected, which gives a closed self-avoiding `*`-walk from
`z + (k₀ + 1, 0)` to a site of abscissa at most `z.1`, of length at least `k₀ + 1`.

**Counting.** The `*`-walks of length `n` from a site number at most `9ⁿ`
(`card_starWalkLists_le`). Among the `n + 1` sites of a self-avoiding walk, at least
`(n + 1) / 9` lie at pairwise `ℓ^∞` distance at least `2` (`exists_separated_subset`); by
`1`-dependence these are all closed with probability at most `ε^{(n+1)/9}`
(`measure_forall_closed_le`). Summing over `n` and the starting points `z + (k, 0)`, `k ≤ n`,
gives a bound linear in `ε` for `ε ≤ 64⁻⁹`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Steps.Section5

noncomputable section

open Classical

namespace Rigidity.Proofs.Section5

/-! ### Lattice edges, plaquettes and the dual boundary graph -/

variable {C : Set PlanarCarrier} {D₀ : PlanarCarrier × Bool}

/-! ### The parity of the crossings of a horizontal ray -/

/-! ### Closed `*`-walks -/

/-! ### Counting the `*`-walks -/

/-! ### Separated sites and `1`-dependence -/

/-! ### The Peierls bound -/

/-- Step `step:5.21-peierls`, with exponent `a = 1` and `C₀ = 64⁹`. -/
theorem oneDependentPeierlsStep : OneDependentPeierlsStep :=
  ⟨64 ^ 9, 1, by positivity, one_pos, fun _ _ hν _ hε hcl z => by
    rw [Real.rpow_one]
    exact measure_not_inInfiniteSiteCluster_le hν hε hcl z⟩

/-- Step `step:5.21-site-density` (Grimmett, *Percolation*, Theorem 8.92 in the printed proof),
with `C = 64⁹`: Bernoulli site percolation is `1`-dependent. -/
theorem siteDensityNearOneStep : SiteDensityNearOneStep := by
  refine ⟨64 ^ 9, by positivity, fun q hq z => ?_⟩
  refine measure_not_inInfiniteSiteCluster_le (kDependentPlanar_bernoulliFieldPlanar 1 q hq)
    (sub_nonneg.mpr (by exact_mod_cast hq)) (fun s => ?_) z
  have hs : {η : PlanarCarrier → Bool | η s = false} = {η | η s = true}ᶜ := by
    ext η
    simp
  have hm : MeasurableSet {η : PlanarCarrier → Bool | η s = true} := by
    have h := (measurable_pi_apply s : Measurable fun f : PlanarCarrier → Bool => f s)
      (measurableSet_singleton (true : Bool))
    simpa [Set.preimage, Set.mem_singleton_iff] using h
  rw [hs, prob_compl_eq_one_sub hm,
    bernoulliFieldPlanar_oneSite, ENNReal.ofReal_sub _ (NNReal.coe_nonneg q), ENNReal.ofReal_one]

end Rigidity.Proofs.Section5
