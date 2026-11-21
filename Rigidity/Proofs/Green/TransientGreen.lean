import LatticeProb.Graph.Reach
import LatticeProb.Graph.Odometer

/-!
# Green functions of walks with summable transition bounds

Let `G` be an infinite connected locally finite graph and `y` a vertex. Suppose that the
transition probabilities into `y` are dominated at large times by a summable sequence: there are
`N₀` and a summable `b` with `p_n(x, y) ≤ b n` whenever `n ≥ N₀` and `n` is at least the graph
distance from `x` to `y`. Then the Green function `g(x) = ∑_n p_n(x, y) / deg(y)` is finite and
solves `-Δ g = δ_y`, and it tends to zero at infinity in the strong sense that `{x : ε < g(x)}`
is finite for every `ε > 0`: since `p_n(x, y) = 0` for `n` below the distance, `g(x)` is at most
the tail `∑_{k} b (k + dist(x, y))`.

Conversely, a harmonic function `h` on `G` for which every set `{x : ε < |h x|}` is finite
vanishes identically (maximum principle): otherwise `|h|` attains a positive maximum, and the mean
value property spreads it over the whole infinite graph.
-/

open Filter Topology
open scoped Classical

namespace Rigidity.Green

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The transition probabilities into `y` are dominated by `b n` at the times `n ≥ N₀` that are
at least the graph distance from the starting point. -/
def HeatDominated (G : SimpleGraph V) [G.LocallyFinite] (y : V) (N₀ : ℕ) (b : ℕ → ℝ) : Prop :=
  ∀ x n, N₀ ≤ n → G.dist x y ≤ n → heat G n x y ≤ b n

/-- The Green function with pole `y`: the expected number of visits to `y`, divided by the degree
of `y`. -/
noncomputable def heatGreen (G : SimpleGraph V) [G.LocallyFinite] (y x : V) : ℝ :=
  (∑' n, heat G n x y) / G.degree y

variable {y : V} {N₀ : ℕ} {b : ℕ → ℝ}

theorem summable_heat_of_heatDominated (hb : Summable b) (h : HeatDominated G y N₀ b) (x : V) :
    Summable (fun n => heat G n x y) := by
  refine Summable.of_norm_bounded_eventually_nat hb ?_
  filter_upwards [eventually_ge_atTop (max N₀ (G.dist x y))] with n hn
  rw [Real.norm_of_nonneg (heat_nonneg n x y)]
  exact h x n (le_of_max_le_left hn) (le_of_max_le_right hn)

/-- The visits before the graph distance vanish. -/
theorem tsum_heat_eq_tsum_add_dist (hb : Summable b) (h : HeatDominated G y N₀ b) (x : V) :
    ∑' n, heat G n x y = ∑' k, heat G (k + G.dist x y) x y := by
  rw [← Summable.sum_add_tsum_nat_add (G.dist x y) (summable_heat_of_heatDominated hb h x),
    Finset.sum_eq_zero (fun i hi => heat_eq_zero_of_lt_dist (Finset.mem_range.1 hi)), zero_add]

/-- Beyond distance `N₀` the expected number of visits is bounded by a tail of `b`. -/
theorem tsum_heat_le_tsum_add_dist (hb : Summable b) (h : HeatDominated G y N₀ b) (x : V)
    (hx : N₀ ≤ G.dist x y) :
    ∑' n, heat G n x y ≤ ∑' k, b (k + G.dist x y) := by
  rw [tsum_heat_eq_tsum_add_dist hb h x]
  refine Summable.tsum_le_tsum (fun k => h x _ (by omega) (by omega)) ?_ ?_
  · exact (summable_nat_add_iff _).2 (summable_heat_of_heatDominated hb h x)
  · exact (summable_nat_add_iff _).2 hb

theorem heatGreen_nonneg (x : V) : 0 ≤ heatGreen G y x :=
  div_nonneg (tsum_nonneg fun n => heat_nonneg n x y) (Nat.cast_nonneg _)

/-- The Green function exceeds `ε` at finitely many vertices only. -/
theorem finite_setOf_lt_heatGreen [Infinite V] (hG : G.Connected) (hb : Summable b)
    (h : HeatDominated G y N₀ b) {ε : ℝ} (hε : 0 < ε) :
    {x | ε < heatGreen G y x}.Finite := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 ((tendsto_order.1 (tendsto_sum_nat_add b)).2 ε hε)
  refine (ballFinset G y (max M N₀)).finite_toSet.subset ?_
  intro x hx
  have hx : ε < heatGreen G y x := hx
  refine mem_ballFinset_of_dist_le hG ?_
  rw [SimpleGraph.dist_comm]
  by_contra hlt
  have hle : max M N₀ ≤ G.dist x y := by omega
  have hdeg : (1 : ℝ) ≤ G.degree y := by exact_mod_cast degree_pos hG y
  have hsum := tsum_heat_le_tsum_add_dist hb h x (le_of_max_le_right hle)
  have htail := hM (G.dist x y) (le_of_max_le_left hle)
  have hnn : 0 ≤ ∑' n, heat G n x y := tsum_nonneg fun n => heat_nonneg n x y
  have hg : heatGreen G y x ≤ ∑' n, heat G n x y :=
    div_le_self hnn hdeg
  linarith

/-- The Laplacian of a transition probability is a time difference. -/
theorem laplacian_heat [Infinite V] (hG : G.Connected) (n : ℕ) (x y : V) :
    laplacian G (fun z => heat G n z y) x =
      (G.degree x : ℝ) * (heat G (n + 1) x y - heat G n x y) := by
  have hd : (G.degree x : ℝ) ≠ 0 := by exact_mod_cast (degree_pos hG x).ne'
  rw [heat_succ, walkOp, laplacian]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul]
  field_simp

/-- The Green function solves `-Δ g = δ_y`. -/
theorem laplacian_heatGreen [Infinite V] (hG : G.Connected) (hb : Summable b)
    (h : HeatDominated G y N₀ b) (x : V) :
    -laplacian G (heatGreen G y) x = if x = y then 1 else 0 := by
  set S : ℕ → V → ℝ := fun N z => ∑ n ∈ Finset.range N, heat G n z y / G.degree y with hS
  have hSlim : ∀ z, Tendsto (fun N => S N z) atTop (𝓝 (heatGreen G y z)) := by
    intro z
    have := ((summable_heat_of_heatDominated hb h z).hasSum.tendsto_sum_nat).div_const
      (G.degree y : ℝ)
    simpa only [hS, heatGreen, Finset.sum_div] using this
  have hlap : Tendsto (fun N => laplacian G (S N) x) atTop (𝓝 (laplacian G (heatGreen G y) x)) := by
    unfold laplacian
    exact tendsto_finsetSum _ fun z _ => (hSlim z).sub (hSlim x)
  have hSN : ∀ N, laplacian G (S N) x =
      (G.degree x : ℝ) / G.degree y * (heat G N x y - heat G 0 x y) := by
    intro N
    have hlin : laplacian G (S N) x =
        ∑ n ∈ Finset.range N, laplacian G (fun z => heat G n z y) x / G.degree y := by
      simp only [hS, laplacian, ← Finset.sum_sub_distrib, Finset.sum_div]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => by ring
    rw [hlin]
    simp_rw [laplacian_heat hG]
    rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_range_sub (fun n => heat G n x y)]
    ring
  have hheat : Tendsto (fun N => heat G N x y) atTop (𝓝 0) :=
    (summable_heat_of_heatDominated hb h x).tendsto_atTop_zero
  have hlim : Tendsto (fun N => laplacian G (S N) x) atTop
      (𝓝 ((G.degree x : ℝ) / G.degree y * (0 - heat G 0 x y))) := by
    simp_rw [hSN]
    exact (hheat.sub tendsto_const_nhds).const_mul _
  rw [tendsto_nhds_unique hlap hlim]
  have hdy : (G.degree y : ℝ) ≠ 0 := by exact_mod_cast (degree_pos hG y).ne'
  simp only [heat]
  split_ifs with hxy
  · subst hxy
    field_simp
    ring
  · ring

/-- A vertex where a harmonic function attains its maximum passes the maximum to its
neighbours. -/
theorem eq_of_adj_of_isMax {u : V → ℝ} {z w : V} (hΔ : laplacian G u z = 0)
    (hmax : ∀ v, u v ≤ u z) (hzw : G.Adj z w) : u w = u z := by
  have hnonpos : ∀ v ∈ G.neighborFinset z, u v - u z ≤ 0 := fun v _ => by linarith [hmax v]
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).1 hΔ w
    ((SimpleGraph.mem_neighborFinset _ _ _).2 hzw)
  linarith

/-- On a connected graph, a harmonic function attaining its maximum is constant. -/
theorem eq_of_isMax (hG : G.Connected) {u : V → ℝ} (hΔ : ∀ x, laplacian G u x = 0) {z : V}
    (hmax : ∀ v, u v ≤ u z) (x : V) : u x = u z := by
  have key : ∀ {a b : V} (p : G.Walk a b), u a = u z → u b = u z := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hadj p ih =>
        intro ha
        refine ih ?_
        have hmax' : ∀ v, u v ≤ u _ := fun v => (hmax v).trans_eq ha.symm
        exact (eq_of_adj_of_isMax (hΔ _) hmax' hadj).trans ha
  obtain ⟨p⟩ := hG.preconnected z x
  exact key p rfl

private theorem not_pos_of_harmonic_of_finite [Infinite V] (hG : G.Connected) {u : V → ℝ}
    (hΔ : ∀ x, laplacian G u x = 0) (hfin : ∀ ε : ℝ, 0 < ε → {x | ε < |u x|}.Finite)
    (x₀ : V) : ¬ 0 < u x₀ := by
  intro hx₀
  set S := {x | u x₀ / 2 < |u x|} with hSdef
  have hSfin : S.Finite := hfin _ (by linarith)
  have hx₀S : x₀ ∈ S := by
    show u x₀ / 2 < |u x₀|
    rw [abs_of_pos hx₀]
    linarith
  obtain ⟨z, hzS, hz⟩ := hSfin.toFinset.exists_max_image u ⟨x₀, hSfin.mem_toFinset.2 hx₀S⟩
  have hzx₀ : u x₀ ≤ u z := hz x₀ (hSfin.mem_toFinset.2 hx₀S)
  have hmax : ∀ v, u v ≤ u z := by
    intro v
    by_cases hv : v ∈ S
    · exact hz v (hSfin.mem_toFinset.2 hv)
    · have hv' : |u v| ≤ u x₀ / 2 := le_of_not_gt hv
      linarith [le_abs_self (u v)]
  have hall : S = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    show u x₀ / 2 < |u v|
    rw [eq_of_isMax hG hΔ hmax v, abs_of_pos (hx₀.trans_le hzx₀)]
    linarith
  exact Set.infinite_univ (hall ▸ hSfin)

/-- **Maximum principle.** A harmonic function exceeding each `ε > 0` in absolute value at only
finitely many vertices of an infinite connected graph vanishes. -/
theorem eq_zero_of_harmonic_of_finite [Infinite V] (hG : G.Connected) {u : V → ℝ}
    (hΔ : ∀ x, laplacian G u x = 0) (hfin : ∀ ε : ℝ, 0 < ε → {x | ε < |u x|}.Finite) (x : V) :
    u x = 0 := by
  have h1 := not_pos_of_harmonic_of_finite hG hΔ hfin x
  have hΔ' : ∀ x, laplacian G (fun v => -u v) x = 0 := by
    intro x
    have := hΔ x
    simp only [laplacian] at this ⊢
    rw [← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hfin' : ∀ ε : ℝ, 0 < ε → {x | ε < |(fun v => -u v) x|}.Finite := by
    intro ε hε
    simpa only [abs_neg] using hfin ε hε
  have h2 := not_pos_of_harmonic_of_finite hG hΔ' hfin' x
  simp only [neg_pos, not_lt] at h2
  linarith [not_lt.1 h1]

end Rigidity.Green
