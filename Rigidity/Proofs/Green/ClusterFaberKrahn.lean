import Rigidity.Proofs.Green.HeatDomination
import Rigidity.Proofs.Green.ClusterGreenColumn

/-!
# Green columns of the infinite cluster from Faber-Krahn inequalities on growing balls

`ClusterFaberKrahn d p D η` says that, for each fixed pole `y`, almost surely the graph balls of
radius `R ≥ R₀(ω)` around `y` in the infinite cluster satisfy the Faber-Krahn inequality of
dimension `D` with constant `a₀(ω) R^{-η}`. When `(D/2)(1 - η) > 1`, this gives the summable
transition bound `p_n(x, y) ≤ K n^{-(D/2)(1-η)}` into the pole (`HeatDomination.lean`), hence, for
`d ≥ 3`, existence and uniqueness of the Green column with pole `y`: the `d ≥ 3` part of
`LatticeProb.External.SupercriticalBondGreenColumnExistence`.
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Graph
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ}

/-- Almost surely, the graph balls of radius `R ≥ R₀` around a fixed pole of the infinite cluster
satisfy the Faber-Krahn inequality of dimension `D` with constant `a₀ R^{-η}`. -/
def ClusterFaberKrahn (d : ℕ) [NeZero d] (p : unitInterval) (D η : ℝ) : Prop :=
  ∀ y : Vertex d, ∀ᵐ ω ∂latticeBondLaw d p,
    ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        FaberKrahnOn (componentGraph (uniqueInfiniteComponent h))
          {v | (componentGraph (uniqueInfiniteComponent h)).dist ⟨y, hy⟩ v ≤ R} D
          (a₀ * (R : ℝ) ^ (-η))

/-- Faber-Krahn inequalities on growing balls give the summable domination of the transition
probabilities into each pole. -/
theorem clusterHeatDomination_of_clusterFaberKrahn [NeZero d] {p : unitInterval} {D η : ℝ}
    (hD : 0 < D) (hγ : 1 < D / 2 * (1 - η)) (hFK : ClusterFaberKrahn d p D η) :
    ClusterHeatDomination d p := by
  intro y
  filter_upwards [hFK y] with ω hω
  intro h hy
  obtain ⟨a₀, ha₀, R₀, hR⟩ := hω h hy
  letI : Infinite (uniqueInfiniteComponent h) :=
    Set.infinite_coe_iff.mpr (uniqueInfiniteComponent_infinite h)
  obtain ⟨K, hK⟩ := heatDominated_of_faberKrahn_balls
    (uniqueInfiniteComponent h).connected_toSimpleGraph
    (componentGraph_degree_le (uniqueInfiniteComponent h)) hD ha₀ ⟨y, hy⟩ hR
  exact ⟨_, _, summable_rpow_mul K hγ, hK⟩

/-- **Green columns in dimension `d ≥ 3` from Faber-Krahn inequalities on growing balls.** -/
theorem greenColumnExistence_of_clusterFaberKrahn [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (p : unitInterval) {D η : ℝ} (hD : 0 < D) (hγ : 1 < D / 2 * (1 - η))
    (hFK : ClusterFaberKrahn d p D η) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g :=
  greenColumnExistence_of_clusterHeatDomination hd hd2 p
    (clusterHeatDomination_of_clusterFaberKrahn hD hγ hFK) y

end Rigidity.Green
