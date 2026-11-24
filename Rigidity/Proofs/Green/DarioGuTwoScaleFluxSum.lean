import Rigidity.Proofs.Green.DarioGuTwoScaleCutoff
import Rigidity.Proofs.Green.DarioGuTwoScaleFluxScale

/-!
# The sum over the dyadic scales in Step 3 of Proposition 4.3 of Dario–Gu

In Step 3 of the proof of Proposition 4.3 of Dario–Gu (the computation (4.32), lines 2371-2376 of
the source) the test function is split with the partition of unity `1 = Σ_m (η_m - η_{m-1})` and
each piece is estimated separately. `neg_tsum_le_of_pieces` justifies the exchange of the sum
over the scales with the sum over the lattice: if `Σ_x G W` converges absolutely and every piece
satisfies `-Σ_x G (dyPiece r y m) W ≤ c_m` with `Σ_{m ≤ M} c_m ≤ S` for all `M`, then
`-Σ_x G W ≤ S`. The truncations `Σ_x G η_M W` converge to `Σ_x G W` by dominated convergence
(Tannery's theorem), since `η_M = 1` eventually at each point.
-/

open Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem abs_dyEta_le {r : ℝ} (y : Vertex 2) (M : ℕ) (x : Vertex 2) : |dyEta r y M x| ≤ 1 := by
  unfold dyEta
  rw [abs_of_nonneg (dyCut_nonneg _ _ _)]
  exact dyCut_le_one _ _ _

/-- **The exchange of the dyadic sum with the lattice sum.** -/
theorem neg_tsum_le_of_pieces {r S : ℝ} (hr : 0 < r) {y : Vertex 2} {G W : Vertex 2 → ℝ}
    {c : ℕ → ℝ} (hGW : Summable fun x => |G x * W x|)
    (hpiece : ∀ m, Summable fun x => G x * (dyPiece r y m x * W x))
    (hc : ∀ m, -(∑' x, G x * (dyPiece r y m x * W x)) ≤ c m)
    (hS : ∀ M, ∑ m ∈ Finset.range (M + 1), c m ≤ S) :
    -(∑' x, G x * W x) ≤ S := by
  -- the truncated sums
  have htrunc : ∀ M, -(∑' x, G x * (dyEta r y M x * W x)) ≤ S := by
    intro M
    have e : ∑' x, G x * (dyEta r y M x * W x) =
        ∑ m ∈ Finset.range (M + 1), ∑' x, G x * (dyPiece r y m x * W x) := by
      rw [← Summable.tsum_finsetSum fun m _ => hpiece m]
      refine tsum_congr fun x => ?_
      rw [← sum_dyPiece r y M x, Finset.sum_mul, Finset.mul_sum]
    rw [e, ← Finset.sum_neg_distrib]
    exact (Finset.sum_le_sum fun m _ => hc m).trans (hS M)
  -- the limit
  have hlim : Tendsto (fun M => ∑' x, G x * (dyEta r y M x * W x)) atTop
      (𝓝 (∑' x, G x * W x)) := by
    refine tendsto_tsum_of_dominated_convergence hGW (fun x => ?_) (Eventually.of_forall
      fun M x => ?_)
    · obtain ⟨M₀, hM₀⟩ := exists_dyEta_eq_one hr y x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop M₀] with M hM
      rw [hM₀ M hM, one_mul]
    · rw [Real.norm_eq_abs, mul_left_comm, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_dyEta_le y M x)
  have hneg := hlim.neg
  exact le_of_tendsto' hneg htrunc

end Rigidity.Green
