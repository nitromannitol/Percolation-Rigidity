import Rigidity.Proofs.Green.DarioGuTwoScaleWeight
import Rigidity.Proofs.Green.DarioGuTwoScaleEnergy
import Rigidity.Proofs.Green.DarioGuTwoScaleInitial

/-!
# The weight of Proposition 4.3 of Dario–Gu on the lattice

The weight `ψ(x) = exp(g(t, |x - y|)/C)` (`dgWeight`) of the proof of Proposition 4.3 of Dario–Gu
and the coefficient `κ(x)` of `w(x)²` in the error term of the weighted energy
(`edgeKappa`, see `tsum_edge_weight_eq`). The discrete form of (4.41),
`(∂_t ψ) ψ + A ψ²/t + K κ ≤ C₁/t` at every lattice point (`dgWeight_edgeKappa_bound`), follows from
`dgWeight_bound` at the four lattice neighbours of `x`, whose distances to `y` differ from that of
`x` by at most one.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The weight `ψ(x) = exp(g(t, |x - y|)/C)` of Proposition 4.3. -/
noncomputable def dgWeight (C t : ℝ) (y x : Vertex 2) : ℝ :=
  Real.exp (dgShape t (latticeDist x y) / C)

/-- The half sum of the squared differences of `ψ` along the open edges at `x`. -/
noncomputable def edgeKappa (ω : Configuration 2) (ψ : Vertex 2 → ℝ) (x : Vertex 2) : ℝ :=
  ∑ i : Fin 2, (openCond ω i x * (ψ (x + unit i) - ψ x) ^ 2 +
    openCond ω i (x - unit i) * (ψ x - ψ (x - unit i)) ^ 2) / 2

theorem abs_latticeDist_add_unit_sub_le (x y : Vertex 2) (i : Fin 2) :
    |latticeDist (x + unit i) y - latticeDist x y| ≤ 1 := by
  have h1 : latticeDist (x + unit i) x = 1 := latticeDist_add_single x i
  have h2 : latticeDist x (x + unit i) = 1 := by rw [latticeDist_comm]; exact h1
  have t1 := latticeDist_triangle (x + unit i) x y
  have t2 := latticeDist_triangle x (x + unit i) y
  rw [abs_le]
  constructor <;> linarith

theorem abs_latticeDist_sub_unit_sub_le (x y : Vertex 2) (i : Fin 2) :
    |latticeDist (x - unit i) y - latticeDist x y| ≤ 1 := by
  have h := abs_latticeDist_add_unit_sub_le (x - unit i) y i
  rw [sub_add_cancel, abs_sub_comm] at h
  exact h

theorem openCond_nonneg (ω : Configuration 2) (i : Fin 2) (x : Vertex 2) : 0 ≤ openCond ω i x := by
  unfold openCond
  split_ifs <;> norm_num

theorem openCond_le_one (ω : Configuration 2) (i : Fin 2) (x : Vertex 2) : openCond ω i x ≤ 1 := by
  unfold openCond
  split_ifs <;> norm_num

/-- `κ(x)` is at most half the sum of the squared differences of `ψ` at the four neighbours. -/
theorem edgeKappa_le (ω : Configuration 2) (ψ : Vertex 2 → ℝ) (x : Vertex 2) :
    edgeKappa ω ψ x ≤ ∑ i : Fin 2, ((ψ (x + unit i) - ψ x) ^ 2 + (ψ (x - unit i) - ψ x) ^ 2) / 2 := by
  unfold edgeKappa
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := mul_le_of_le_one_left (sq_nonneg (ψ (x + unit i) - ψ x)) (openCond_le_one ω i x)
  have h2 := mul_le_of_le_one_left (sq_nonneg (ψ x - ψ (x - unit i)))
    (openCond_le_one ω i (x - unit i))
  have e : (ψ x - ψ (x - unit i)) ^ 2 = (ψ (x - unit i) - ψ x) ^ 2 := by ring
  rw [e] at h2
  linarith

/-- **The discrete form of (4.41) of Dario–Gu on the lattice**: for every `K > 0` and `A ≥ 0` there
is `C₀` such that for `C ≥ C₀` there is `C₁` with, for `t ≥ 1` and every `x`,
`ψ(x)² (∂_t g(t, |x - y|)/C + A/t) + K κ(x) ≤ C₁/t`, where `ψ = dgWeight C t y`. -/
theorem dgWeight_edgeKappa_bound {K A : ℝ} (hK : 0 < K) (hA : 0 ≤ A) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (ω : Configuration 2) (t : ℝ) (y x : Vertex 2), 1 ≤ t →
        dgWeight C t y x ^ 2 * (dgShapeTimeDeriv t (latticeDist x y) / C + A / t) +
          K * edgeKappa ω (dgWeight C t y) x ≤ C₁ / t := by
  obtain ⟨C₀, hC₀, h⟩ := dgWeight_bound (K := 2 * K) (A := A) (by positivity) hA
  refine ⟨C₀, hC₀, fun C hC => ?_⟩
  obtain ⟨C₁, hC₁, h1⟩ := h C hC
  refine ⟨C₁, hC₁, fun ω t y x ht => ?_⟩
  set ψ := dgWeight C t y with hψ
  set T := dgWeight C t y x ^ 2 * (dgShapeTimeDeriv t (latticeDist x y) / C + A / t) with hT
  have hz : ∀ z : Vertex 2, |latticeDist z y - latticeDist x y| ≤ 1 →
      T + 2 * K * (ψ z - ψ x) ^ 2 ≤ C₁ / t := fun z hzd =>
    h1 t (latticeDist x y) (latticeDist z y) ht (latticeDist_nonneg _ _)
      (latticeDist_nonneg _ _) hzd
  have hk := edgeKappa_le ω ψ x
  simp only [Fin.sum_univ_two] at hk
  have a1 := hz _ (abs_latticeDist_add_unit_sub_le x y 0)
  have a2 := hz _ (abs_latticeDist_sub_unit_sub_le x y 0)
  have a3 := hz _ (abs_latticeDist_add_unit_sub_le x y 1)
  have a4 := hz _ (abs_latticeDist_sub_unit_sub_le x y 1)
  have hKk := mul_le_mul_of_nonneg_left hk hK.le
  nlinarith

end Rigidity.Green
