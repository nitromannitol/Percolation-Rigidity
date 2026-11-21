import LatticeProb.Network.LocalCaccioppoli
import LatticeProb.Prob.Percolation.LatticeBondGraph

/-!
# The Caccioppoli inequality on clusters

Armstrong–Dario, *Elliptic regularity and quantitative homogenization on percolation clusters*
(Comm. Pure Appl. Math. 2018), Lemma 3.5: if `U ⊆ ℤ^d` is a cluster, `V ⊆ U` satisfies
`dist(V, ∂_𝐚 U) ≥ r ≥ 1` and `u` is `𝐚`-harmonic in `U`, then

`∫_V |∇u 1_{𝐚 ≠ 0}|² ≤ C r⁻² ∫_{U ∖ int V} |u|²`,

where `|F|(x)² = (1/2) ∑_{y ∈ U, y ∼ x} |F(x, y)|²`.

We prove it in four steps.

* `caccioppoli_of_cutoff`: on a locally finite graph with symmetric conductances in `[λ, 1]` along
  its edges, for a cutoff `η` equal to `1` on `W`, vanishing off the set where `u` is harmonic and
  varying by at most `1/r` along edges, with the constant `4/(λ r²)` in front of the sum of
  `u x² + u y²` over the edges along which `η` changes. The test-function computation is the
  discrete Caccioppoli inequality `LatticeProb.Network.caccioppoli_of_support`.
* `sum_cutoff_change_le`: those edges are counted with the degree bound.
* `caccioppoli_of_distance`: the cutoff `max (1 - ρ/r) 0` built from a function `ρ` vanishing on `W`
  and varying by at most one along edges.
* `caccioppoli_cluster`: the open graph of a bond configuration of `ℤ^d` restricted to a finite set
  `U`, unit conductances on the open edges, `ρ` the sup-norm distance to `V`; the constant is `8d`.
  The distance of Armstrong and Dario is the `ℓ^∞` distance of the coordinates, `supDist`. For
  conductances in `{0} ∪ [λ, 1]`, `caccioppoli_of_distance` (degree `Δ = 2d`) gives the constant
  `C(λ) = 8d/λ`; the open graph has `λ = 1`.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Network
open scoped BigOperators Classical

section Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **Caccioppoli inequality with a cutoff.** Let the conductances `c` of a locally finite graph lie
in `[λ, 1]` along its edges, let `u` be harmonic at every vertex of `B`, whose neighbours lie in `S`,
and let `η` vanish off `B`, equal `1` on `W ⊆ S` and vary by at most `1/r` along edges. Then the
Dirichlet energy of `u` at the vertices of `W` is controlled by the squares of `u` at the endpoints of
the edges along which `η` changes. -/
theorem caccioppoli_of_cutoff {c : V → V → ℝ} (hc : IsCond G c) {lam r : ℝ}
    (hlam : ∀ x y, G.Adj x y → lam ≤ c x y) (hc1 : ∀ x y, c x y ≤ 1) (hr : 0 < r)
    (S B W : Finset V) (u η : V → ℝ) (hu : ∀ x ∈ B, netLaplacian G c u x = 0)
    (hηB : ∀ x, x ∉ B → η x = 0) (hηW : ∀ x ∈ W, η x = 1)
    (hηlip : ∀ x y, G.Adj x y → |η x - η y| ≤ 1 / r) (hBS : B ⊆ S) (hWS : W ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    lam * ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 ≤
      4 / r ^ 2 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        (if η x = η y then 0 else u x ^ 2 + u y ^ 2) := by
  have hmain := caccioppoli_of_support hc S B u η hu
    (fun x hx => by rw [hηB x hx]; ring) hBS hnb
  have hleft : lam * ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 ≤
      ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (u x - u y) ^ 2 * η x ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ x ∈ W, lam * ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2
        ≤ ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, c x y * (u x - u y) ^ 2 * η x ^ 2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun y hy => ?_
          rw [hηW x hx]
          have h1 := hlam x y ((G.mem_neighborFinset x y).1 hy)
          nlinarith [sq_nonneg (u x - u y)]
      _ ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (u x - u y) ^ 2 * η x ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hWS fun x _ _ =>
            Finset.sum_nonneg fun y _ => by
              have := hc.nonneg x y
              positivity
  have hright : 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (u x ^ 2 + u y ^ 2) * (η x - η y) ^ 2 ≤
      4 / r ^ 2 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        (if η x = η y then 0 else u x ^ 2 + u y ^ 2) := by
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    have hadj := (G.mem_neighborFinset x y).1 hy
    split_ifs with h
    · rw [h, sub_self]
      simp
    · have hlip := abs_le.mp (hηlip x y hadj)
      have hr2 : 0 < r ^ 2 := by positivity
      have h1 : (η x - η y) ^ 2 ≤ (r ^ 2)⁻¹ := by
        have h2 : (1 / r) ^ 2 = (r ^ 2)⁻¹ := by rw [one_div, inv_pow]
        rw [← h2]
        nlinarith [hlip.1, hlip.2]
      have hA : 0 ≤ u x ^ 2 + u y ^ 2 := by positivity
      have hc0 := hc.nonneg x y
      calc c x y * (u x ^ 2 + u y ^ 2) * (η x - η y) ^ 2
          ≤ 1 * (u x ^ 2 + u y ^ 2) * (r ^ 2)⁻¹ :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hc1 x y) hA) h1 (sq_nonneg _)
              (by positivity)
        _ = (r ^ 2)⁻¹ * (u x ^ 2 + u y ^ 2) := by ring
  linarith

/-- **Counting the edges along which a cutoff changes.** If every neighbour `y` of a vertex `x ∈ S`
with `η x ≠ η y` lies in `S` and all degrees are at most `Δ`, the sum of `u x² + u y²` over the
edges of `S` along which `η` changes is at most `2Δ` times the sum of `u²` over the vertices of `S`
having such an edge. -/
theorem sum_cutoff_change_le [DecidableEq V] (S : Finset V) (η u : V → ℝ) {Δ : ℕ}
    (hdeg : ∀ x, G.degree x ≤ Δ) (hS : ∀ x ∈ S, ∀ y, G.Adj x y → η x ≠ η y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, (if η x = η y then 0 else u x ^ 2 + u y ^ 2) ≤
      2 * Δ * ∑ x ∈ S.filter (fun x => ∃ y, G.Adj x y ∧ η x ≠ η y), u x ^ 2 := by
  set N : V → Finset V := fun x => (G.neighborFinset x).filter (fun y => η x ≠ η y) with hN
  have hsplit : ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        (if η x = η y then 0 else u x ^ 2 + u y ^ 2) =
      ∑ x ∈ S, ∑ y ∈ N x, u x ^ 2 + ∑ x ∈ S, ∑ y ∈ N x, u y ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, hN, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : η x = η y <;> simp [h]
  have hswap : ∑ x ∈ S, ∑ y ∈ N x, u y ^ 2 = ∑ x ∈ S, ∑ y ∈ N x, u x ^ 2 := by
    refine Finset.sum_comm' fun x y => ?_
    simp only [hN, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hx, hadj, hne⟩
      exact ⟨⟨hadj.symm, Ne.symm hne⟩, hS x hx y hadj hne⟩
    · rintro ⟨⟨hadj, hne⟩, hy⟩
      exact ⟨hS y hy x hadj hne, hadj.symm, Ne.symm hne⟩
  have hcount : ∑ x ∈ S, ∑ y ∈ N x, u x ^ 2 ≤
      Δ * ∑ x ∈ S.filter (fun x => ∃ y, G.Adj x y ∧ η x ≠ η y), u x ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    split_ifs with h
    · have hcard : ((N x).card : ℝ) ≤ Δ := by
        have h1 : (N x).card ≤ G.degree x := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_filter_le _ _
        exact_mod_cast h1.trans (hdeg x)
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    · have hempty : N x = ∅ := by
        rw [hN, Finset.filter_eq_empty_iff]
        intro y hy hne
        exact h ⟨y, (G.mem_neighborFinset x y).1 hy, hne⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
  rw [hsplit, hswap]
  linarith

/-- **Caccioppoli inequality from a distance function.** Let the conductances lie in `[λ, 1]` along
the edges of a graph of degrees at most `Δ`, let `ρ` vanish on `W ⊆ S` and vary by at most one along
edges, and let `u` be harmonic at the vertices `x ∈ S` with `ρ x < r`, whose neighbours lie in `S`.
Then `λ ∑_{x ∈ W} ∑_{y ∼ x} (u x - u y)² ≤ (8Δ/r²) ∑ u²` over the vertices of `S` outside the
interior of `W`. -/
theorem caccioppoli_of_distance [DecidableEq V] {c : V → V → ℝ} (hc : IsCond G c) {lam r : ℝ}
    {Δ : ℕ}
    (hlam : ∀ x y, G.Adj x y → lam ≤ c x y) (hc1 : ∀ x y, c x y ≤ 1) (hr : 0 < r)
    (hdeg : ∀ x, G.degree x ≤ Δ) (S W : Finset V) (u ρ : V → ℝ)
    (hρlip : ∀ x y, G.Adj x y → |ρ x - ρ y| ≤ 1) (hρW : ∀ x ∈ W, ρ x = 0) (hWS : W ⊆ S)
    (hu : ∀ x ∈ S, ρ x < r → netLaplacian G c u x = 0)
    (hnb : ∀ x ∈ S, ρ x < r → ∀ y, G.Adj x y → y ∈ S) :
    lam * ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2 ≤
      8 * Δ / r ^ 2 *
        ∑ x ∈ S.filter (fun x => ¬ (x ∈ W ∧ ∀ y, G.Adj x y → y ∈ W)), u x ^ 2 := by
  set η : V → ℝ := fun x => if x ∈ S then max (1 - ρ x / r) 0 else 0 with hη
  set B : Finset V := S.filter (fun x => ρ x < r) with hB
  have hηzero : ∀ x ∈ S, r ≤ ρ x → η x = 0 := by
    intro x hx hρ
    have h1 : 1 - ρ x / r ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hr, one_mul]
      exact hρ
    simp only [hη, if_pos hx, max_eq_right h1]
  have hηout : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S → η x = 0 := by
    intro x hx y hadj hy
    by_contra hne
    by_cases hρ : ρ x < r
    · exact hy (hnb x hx hρ y hadj)
    · exact hne (hηzero x hx (not_lt.mp hρ))
  have hηB : ∀ x, x ∉ B → η x = 0 := by
    intro x hx
    by_cases hxS : x ∈ S
    · have hρ : r ≤ ρ x := by
        by_contra h
        exact hx (Finset.mem_filter.mpr ⟨hxS, not_le.mp h⟩)
      exact hηzero x hxS hρ
    · simp only [hη, if_neg hxS]
  have hηW : ∀ x ∈ W, η x = 1 := by
    intro x hx
    simp only [hη, if_pos (hWS hx), hρW x hx, zero_div, sub_zero]
    exact max_eq_left zero_le_one
  have hηlip : ∀ x y, G.Adj x y → |η x - η y| ≤ 1 / r := by
    intro x y hadj
    have hr1 : 0 ≤ 1 / r := by positivity
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simp only [hη, if_pos hx, if_pos hy]
      calc |max (1 - ρ x / r) 0 - max (1 - ρ y / r) 0|
          ≤ |(1 - ρ x / r) - (1 - ρ y / r)| := abs_max_sub_max_le_abs _ _ _
        _ = |ρ x - ρ y| / r := by
            rw [show (1 - ρ x / r) - (1 - ρ y / r) = -((ρ x - ρ y) / r) by ring, abs_neg,
              abs_div, abs_of_pos hr]
        _ ≤ 1 / r := div_le_div_of_nonneg_right (hρlip x y hadj) hr.le
    · rw [hηout x hx y hadj hy, show η y = 0 by simp only [hη, if_neg hy], sub_zero, abs_zero]
      exact hr1
    · rw [hηout y hy x hadj.symm hx, show η x = 0 by simp only [hη, if_neg hx], sub_zero,
        abs_zero]
      exact hr1
    · simp only [hη, if_neg hx, if_neg hy, sub_zero, abs_zero]
      exact hr1
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hcac := caccioppoli_of_cutoff hc hlam hc1 hr S B W u η
    (fun x hx => hu x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2) hηB hηW hηlip hBS
    hWS (fun x hx => hnb x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
  have hcount := sum_cutoff_change_le (G := G) S η u hdeg (fun x hx y hadj hne => by
    by_contra hy
    exact hne ((hηout x hx y hadj hy).trans (show η y = 0 by simp only [hη, if_neg hy]).symm))
  have hsub : ∑ x ∈ S.filter (fun x => ∃ y, G.Adj x y ∧ η x ≠ η y), u x ^ 2 ≤
      ∑ x ∈ S.filter (fun x => ¬ (x ∈ W ∧ ∀ y, G.Adj x y → y ∈ W)), u x ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => sq_nonneg _
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, fun hint => ?_⟩
    obtain ⟨y, hadj, hne⟩ := hx.2
    exact hne ((hηW x hint.1).trans (hηW y (hint.2 y hadj)).symm)
  have hr2 : 0 ≤ 4 / r ^ 2 := by positivity
  calc lam * ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - u y) ^ 2
      ≤ 4 / r ^ 2 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (if η x = η y then 0 else u x ^ 2 + u y ^ 2) := hcac
    _ ≤ 4 / r ^ 2 * (2 * Δ *
          ∑ x ∈ S.filter (fun x => ¬ (x ∈ W ∧ ∀ y, G.Adj x y → y ∈ W)), u x ^ 2) := by
        refine mul_le_mul_of_nonneg_left (hcount.trans ?_) hr2
        exact mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = 8 * Δ / r ^ 2 *
          ∑ x ∈ S.filter (fun x => ¬ (x ∈ W ∧ ∀ y, G.Adj x y → y ∈ W)), u x ^ 2 := by ring

end Graph

section Restrict

variable {V : Type*}

/-- The graph keeping the edges of `G` with both endpoints in `U`. -/
def restrictGraph (G : SimpleGraph V) (U : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem restrictGraph_adj {G : SimpleGraph V} {U : Finset V} {x y : V} :
    (restrictGraph G U).Adj x y ↔ G.Adj x y ∧ x ∈ U ∧ y ∈ U := Iff.rfl

theorem restrictGraph_le (G : SimpleGraph V) (U : Finset V) : restrictGraph G U ≤ G :=
  fun _ _ h => h.1

noncomputable instance restrictGraphLocallyFinite (G : SimpleGraph V) [G.LocallyFinite]
    (U : Finset V) : (restrictGraph G U).LocallyFinite :=
  fun x => Set.Finite.fintype ((G.neighborSet x).toFinite.subset fun _ hy => hy.1)

theorem restrictGraph_neighborFinset [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]
    (U : Finset V)
    {x : V} (hx : x ∈ U) :
    (restrictGraph G U).neighborFinset x = (G.neighborFinset x).filter (· ∈ U) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, restrictGraph_adj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hx, h.2⟩⟩

end Restrict

section Lattice

open LatticeProb.Percolation

variable {d : ℕ}

/-- The sup-norm distance between two lattice points. -/
def supDist (x y : Vertex d) : ℕ := Finset.univ.sup fun i => (x i - y i).natAbs

theorem natAbs_le_supDist (x y : Vertex d) (i : Fin d) : (x i - y i).natAbs ≤ supDist x y :=
  Finset.le_sup (f := fun i => (x i - y i).natAbs) (Finset.mem_univ i)

theorem supDist_comm (x y : Vertex d) : supDist x y = supDist y x := by
  unfold supDist
  congr 1
  funext i
  rw [← Int.natAbs_neg, neg_sub]

theorem supDist_self (x : Vertex d) : supDist x x = 0 :=
  le_antisymm (Finset.sup_le fun i _ => by simp) (Nat.zero_le _)

/-- Open neighbours differ by at most one in every coordinate. -/
theorem abs_sub_le_one_of_openGraph_adj {ω : Configuration d} {x y : Vertex d}
    (h : (openGraph ω).Adj x y) (i : Fin d) : |x i - y i| ≤ 1 := by
  have h1 := lattice_adj_iff_l1Dist.mp (openGraph_le ω h)
  unfold latticeL1Dist at h1
  rw [← h1]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j - y j)) (Finset.mem_univ i)

theorem supDist_le_supDist_add_one {ω : Configuration d} {x y : Vertex d}
    (h : (openGraph ω).Adj x y) (w : Vertex d) : supDist x w ≤ supDist y w + 1 := by
  refine Finset.sup_le fun i _ => ?_
  have h1 := abs_sub_le_one_of_openGraph_adj h i
  have h2 : ((y i - w i).natAbs : ℤ) ≤ supDist y w := by exact_mod_cast natAbs_le_supDist y w i
  have h3 : ((x i - w i).natAbs : ℤ) ≤ (supDist y w : ℤ) + 1 := by
    rw [Int.natCast_natAbs] at h2 ⊢
    have h4 := abs_sub_abs_le_abs_sub (x i - w i) (y i - w i)
    rw [show (x i - w i) - (y i - w i) = x i - y i by ring] at h4
    linarith
  exact_mod_cast h3

/-- The open graph of a configuration restricted to `U`: the open edges with both endpoints in
`U`. -/
abbrev clusterGraph (ω : Configuration d) (U : Finset (Vertex d)) : SimpleGraph (Vertex d) :=
  restrictGraph (openGraph ω) U

theorem clusterGraph_neighborFinset (ω : Configuration d) (U : Finset (Vertex d)) {x : Vertex d}
    (hx : x ∈ U) :
    (clusterGraph ω U).neighborFinset x = ((openGraph ω).neighborFinset x).filter (· ∈ U) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, restrictGraph_adj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hx, h.2⟩⟩

/-- The squared gradient `|∇u 1_{𝐚 ≠ 0}|²(x) = (1/2) ∑_{y ∈ U, y ∼ x open} (u x - u y)²` at `x` of a
function on `U`. -/
noncomputable def clusterGradSq (ω : Configuration d) (U : Finset (Vertex d)) (u : Vertex d → ℝ)
    (x : Vertex d) : ℝ :=
  (1 / 2) * ∑ y ∈ ((openGraph ω).neighborFinset x).filter (· ∈ U), (u x - u y) ^ 2

/-- **Caccioppoli inequality on a cluster** (Armstrong–Dario, Lemma 3.5). Let `U` be a finite set
of lattice points, `V ⊆ U`, and let every point of `U` with an open edge leaving `U` be at sup-norm
distance at least `r > 0` from `V`. If `u` is harmonic for the open edges at every point of `U` all
of whose open edges stay in `U`, then
`∑_{x ∈ V} |∇u 1_{𝐚 ≠ 0}|²(x) ≤ (8d/r²) ∑_{x ∈ U ∖ int V} u(x)²`,
`int V` being the set of points of `V` all of whose lattice neighbours lie in `V`. -/
theorem caccioppoli_cluster (ω : Configuration d) (U V : Finset (Vertex d)) (hVU : V ⊆ U)
    {r : ℝ} (hr : 0 < r)
    (hdist : ∀ x ∈ V, ∀ z ∈ U, (∃ y, (openGraph ω).Adj z y ∧ y ∉ U) → r ≤ supDist x z)
    (u : Vertex d → ℝ)
    (hu : ∀ x ∈ U, (∀ y, (openGraph ω).Adj x y → y ∈ U) → openLaplacian ω u x = 0) :
    ∑ x ∈ V, clusterGradSq ω U u x ≤
      8 * d / r ^ 2 *
        ∑ x ∈ U.filter (fun x => ¬ (x ∈ V ∧ ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ V)),
          u x ^ 2 := by
  rcases V.eq_empty_or_nonempty with hV | hV
  · subst hV
    simp only [Finset.sum_empty]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => sq_nonneg _)
  set ρ : Vertex d → ℝ := fun x => V.inf' hV fun w => (supDist x w : ℝ) with hρ
  have hρlip : ∀ x y, (clusterGraph ω U).Adj x y → |ρ x - ρ y| ≤ 1 := by
    intro x y hadj
    have hxy : ∀ a b : Vertex d, (openGraph ω).Adj a b → ρ a ≤ ρ b + 1 := by
      intro a b hab
      obtain ⟨w, hw, hwb⟩ := Finset.exists_mem_eq_inf' hV fun w => (supDist b w : ℝ)
      have h1 : ρ a ≤ supDist a w := Finset.inf'_le _ hw
      have h2 : (supDist a w : ℝ) ≤ supDist b w + 1 := by
        exact_mod_cast supDist_le_supDist_add_one hab w
      have h3 : ρ b = supDist b w := hwb
      linarith
    rw [abs_le]
    constructor
    · linarith [hxy y x hadj.1.symm]
    · linarith [hxy x y hadj.1]
  have hρW : ∀ x ∈ V, ρ x = 0 := by
    intro x hx
    refine le_antisymm ?_ ?_
    · have h1 : ρ x ≤ supDist x x := Finset.inf'_le _ hx
      rwa [supDist_self, Nat.cast_zero] at h1
    · exact Finset.le_inf' hV _ fun w _ => Nat.cast_nonneg _
  have hdeg : ∀ x, (clusterGraph ω U).degree x ≤ 2 * d := fun x =>
    (SimpleGraph.degree_le_of_le (restrictGraph_le _ _)).trans (openGraph_degree_le ω x)
  have hint : ∀ x ∈ U, ρ x < r → ∀ y, (openGraph ω).Adj x y → y ∈ U := by
    intro x hx hρx y hy
    by_contra hyU
    obtain ⟨w, hw, hwx⟩ := Finset.exists_mem_eq_inf' hV fun w => (supDist x w : ℝ)
    have h1 := hdist w hw x hx ⟨y, hy, hyU⟩
    rw [supDist_comm] at h1
    have h2 : ρ x = supDist x w := hwx
    linarith
  have hu' : ∀ x ∈ U, ρ x < r →
      netLaplacian (clusterGraph ω U) (unitCond (clusterGraph ω U)) u x = 0 := by
    intro x hx hρx
    have hall := hint x hx hρx
    rw [netLaplacian_unitCond, LatticeProb.Graph.laplacian, clusterGraph_neighborFinset ω U hx,
      Finset.filter_true_of_mem fun y hy => hall y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)]
    exact hu x hx hall
  have hlam : ∀ x y, (clusterGraph ω U).Adj x y → (1 : ℝ) ≤ unitCond (clusterGraph ω U) x y := by
    intro x y hadj
    simp [unitCond, hadj]
  have hc1 : ∀ x y, unitCond (clusterGraph ω U) x y ≤ 1 := by
    intro x y
    unfold unitCond
    split_ifs <;> norm_num
  have hmain := caccioppoli_of_distance (G := clusterGraph ω U) isCond_unitCond hlam hc1 hr hdeg
    U V u ρ hρlip hρW hVU hu' (fun x _ _ y hadj => hadj.2.2)
  have hleft : ∑ x ∈ V, clusterGradSq ω U u x =
      (1 / 2) * ∑ x ∈ V, ∑ y ∈ (clusterGraph ω U).neighborFinset x, (u x - u y) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [clusterGradSq, clusterGraph_neighborFinset ω U (hVU hx)]
  have hd : (0 : ℝ) ≤ 8 * ((2 * d : ℕ) : ℝ) / r ^ 2 := by positivity
  have hmain' : ∑ x ∈ V, ∑ y ∈ (clusterGraph ω U).neighborFinset x, (u x - u y) ^ 2 ≤
      8 * ((2 * d : ℕ) : ℝ) / r ^ 2 *
        ∑ x ∈ U.filter (fun x => ¬ (x ∈ V ∧ ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ V)),
          u x ^ 2 := by
    have h1 := hmain
    rw [one_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => sq_nonneg _) hd)
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun hlat => hx.2 ⟨hlat.1, fun y hadj => hlat.2 y (openGraph_le ω hadj.1)⟩⟩
  rw [hleft]
  calc (1 / 2 : ℝ) * ∑ x ∈ V, ∑ y ∈ (clusterGraph ω U).neighborFinset x, (u x - u y) ^ 2
      ≤ (1 / 2 : ℝ) * (8 * ((2 * d : ℕ) : ℝ) / r ^ 2 *
          ∑ x ∈ U.filter (fun x => ¬ (x ∈ V ∧ ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ V)),
            u x ^ 2) := mul_le_mul_of_nonneg_left hmain' (by norm_num)
    _ = 8 * d / r ^ 2 *
          ∑ x ∈ U.filter (fun x => ¬ (x ∈ V ∧ ∀ y, (nearestNeighborGraph d).Adj x y → y ∈ V)),
            u x ^ 2 := by
        push_cast
        ring

end Lattice

end Rigidity.Proofs.Cluster
