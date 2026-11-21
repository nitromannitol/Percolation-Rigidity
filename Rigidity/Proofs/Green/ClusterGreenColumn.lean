import Rigidity.Proofs.Green.TransientGreen
import Rigidity.Proofs.S3.ExteriorNetworkDecay
import LatticeProb.Prob.Percolation.GreenColumn
import LatticeProb.Prob.Percolation.LatticeUniqueCluster
import LatticeProb.Prob.Percolation.LatticeBondCritical

/-!
# Green columns of infinite components in dimension at least three

On an infinite open component whose transition probabilities into the pole `y` are dominated at
large times by a summable sequence (`HeatDominated`), the Green function
`g(x) = ∑_n p_n(x, y) / deg(y)` is a Green column in the sense of `IsGreenColumn` for every
`d ≥ 3`: it solves the unit-pole equation, and it exceeds any `ε > 0` at finitely many vertices
only, which is its decay at Euclidean infinity. In dimension `d ≥ 3` a Green column is unique on
any infinite component: the difference of two is harmonic and decays, so it vanishes by the
maximum principle.

Consequently the existence and uniqueness of Green columns of the infinite cluster for `d ≥ 3`,
the `d ≥ 3` part of `LatticeProb.External.SupercriticalBondGreenColumnExistence`, follows from an
almost-sure summable domination of the transition probabilities into each pole
(`ClusterHeatDomination`).
-/

open MeasureTheory LatticeProb.Percolation LatticeProb.Graph
open scoped Classical

namespace Rigidity.Green

variable {d : ℕ} {ω : Configuration d}

/-- Finitely many exceptional vertices leave a function on a component small at Euclidean
infinity. -/
theorem exists_radius_of_finite (C : OpenComponent ω) {u : C → ℝ} {ε : ℝ}
    (hfin : {x | ε < |u x|}.Finite) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ → |u x| ≤ ε := by
  have hnn : 0 ≤ ∑ x ∈ hfin.toFinset, ‖latticeEuclideanEmbedding x.val‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 + ∑ x ∈ hfin.toFinset, ‖latticeEuclideanEmbedding x.val‖, by linarith, ?_⟩
  intro x hx
  by_contra hlt
  have hmem : x ∈ hfin.toFinset := hfin.mem_toFinset.2 (lt_of_not_ge hlt)
  have := Finset.single_le_sum (f := fun x : C => ‖latticeEuclideanEmbedding x.val‖)
    (fun _ _ => norm_nonneg _) hmem
  linarith

/-- Smallness at Euclidean infinity leaves finitely many exceptional vertices. -/
theorem finite_of_exists_radius (C : OpenComponent ω) {u : C → ℝ} {ε : ℝ}
    (h : ∃ R : ℝ, 0 < R ∧ ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ → |u x| ≤ ε) :
    {x | ε < |u x|}.Finite := by
  obtain ⟨R, -, hR⟩ := h
  refine (finite_componentEuclideanBall C 0 R).subset ?_
  intro x hx
  have hx : ε < |u x| := hx
  show dist _ _ < R
  rw [Rigidity.Proofs.S3.NetworkTrace.dist_embedding_zero_eq_norm]
  by_contra hle
  exact absurd (hR x (le_of_not_gt hle)) (not_le.2 hx)

/-- With a summable transition bound into the pole, the Green function of an infinite component
is a Green column in every dimension `d ≥ 3`. -/
theorem isGreenColumn_heatGreen (hd : 3 ≤ d) (hd2 : 2 ≤ d) (C : OpenComponent ω)
    (hC : C.supp.Infinite) (y : C) {N₀ : ℕ} {b : ℕ → ℝ} (hb : Summable b)
    (h : HeatDominated (componentGraph C) y N₀ b) :
    IsGreenColumn d hd2 C y (heatGreen (componentGraph C) y) := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  have hG := C.connected_toSimpleGraph
  refine ⟨fun x => by convert laplacian_heatGreen hG hb h x using 2; rfl, fun h2 => by omega,
    fun _ ε hε => ?_⟩
  refine exists_radius_of_finite C ?_
  simpa only [abs_of_nonneg (heatGreen_nonneg _)] using finite_setOf_lt_heatGreen hG hb h hε

/-- In dimension `d ≥ 3`, two Green columns with the same pole on an infinite component
coincide. -/
theorem eq_of_isGreenColumn_of_three_le (hd : 3 ≤ d) (hd2 : 2 ≤ d) (C : OpenComponent ω)
    (hC : C.supp.Infinite) {y : C} {g g' : C → ℝ} (hg : IsGreenColumn d hd2 C y g)
    (hg' : IsGreenColumn d hd2 C y g') : g = g' := by
  letI : Infinite C := Set.infinite_coe_iff.mpr hC
  have hG := C.connected_toSimpleGraph
  have hΔ : ∀ x, laplacian (componentGraph C) (fun v => g v - g' v) x = 0 := by
    intro x
    have h1 := hg.1 x
    have h2 := hg'.1 x
    have hsub : laplacian (componentGraph C) (fun v => g v - g' v) x =
        componentLaplacian C g x - componentLaplacian C g' x := by
      simp only [laplacian, componentLaplacian, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsub]
    linarith
  have hfin : ∀ ε : ℝ, 0 < ε → {x | ε < |(fun v => g v - g' v) x|}.Finite := by
    intro ε hε
    obtain ⟨R, hR, hRb⟩ := hg.2.2 hd (ε / 2) (by linarith)
    obtain ⟨R', -, hRb'⟩ := hg'.2.2 hd (ε / 2) (by linarith)
    refine finite_of_exists_radius C ⟨max R R', lt_max_of_lt_left hR, fun x hx => ?_⟩
    obtain ⟨a1, a2⟩ := abs_le.1 (hRb x ((le_max_left _ _).trans hx))
    obtain ⟨b1, b2⟩ := abs_le.1 (hRb' x ((le_max_right _ _).trans hx))
    rw [abs_le]
    constructor <;> linarith
  funext x
  have := eq_zero_of_harmonic_of_finite hG hΔ hfin x
  linarith

/-- A summable transition bound into the pole gives a unique Green column for `d ≥ 3`. -/
theorem existsUnique_isGreenColumn_of_heatDominated (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (C : OpenComponent ω) (hC : C.supp.Infinite) (y : C) {N₀ : ℕ} {b : ℕ → ℝ}
    (hb : Summable b) (h : HeatDominated (componentGraph C) y N₀ b) :
    ∃! g, IsGreenColumn d hd2 C y g :=
  ⟨_, isGreenColumn_heatGreen hd hd2 C hC y hb h, fun _ hg' =>
    eq_of_isGreenColumn_of_three_le hd hd2 C hC hg' (isGreenColumn_heatGreen hd hd2 C hC y hb h)⟩

/-- Almost surely, the transition probabilities of the walk on the infinite cluster into each
fixed pole are dominated at large times by a summable sequence. -/
def ClusterHeatDomination (d : ℕ) [NeZero d] (p : unitInterval) : Prop :=
  ∀ y : Vertex d, ∀ᵐ ω ∂latticeBondLaw d p,
    ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
      ∃ (N₀ : ℕ) (b : ℕ → ℝ), Summable b ∧
        HeatDominated (componentGraph (uniqueInfiniteComponent h)) ⟨y, hy⟩ N₀ b

/-- The `d ≥ 3` part of the Green-column input from the summable domination of the transition
probabilities. -/
theorem greenColumnExistence_of_clusterHeatDomination [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    (p : unitInterval) (hH : ClusterHeatDomination d p) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
          ∃! g : uniqueInfiniteComponent h → ℝ,
            IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g := by
  filter_upwards [hH y] with ω hω
  intro h hy
  obtain ⟨N₀, b, hb, hdom⟩ := hω h hy
  exact existsUnique_isGreenColumn_of_heatDominated hd hd2 _
    (uniqueInfiniteComponent_infinite h) _ hb hdom

end Rigidity.Green
