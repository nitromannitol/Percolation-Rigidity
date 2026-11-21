import Rigidity.Proofs.Cluster.SobolevZero
import Rigidity.Proofs.Cluster.SobolevCubePoincare

/-!
# The `L^p` Poincaré inequality on an integer cube in terms of the gradient magnitude

For an integer cube `B` of side `n ≥ 1`, every real `p ≥ 1` and every `f`,
`∑_{x ∈ B} |f(x) - (f)_B|^p ≤ d^{p-1} d √2^p n^p ∑_{x ∈ B} |∇f|^p(x)`,
with `|∇f|(x)` the magnitude of the lattice gradient on `B`. It follows from the `L^p` Poincaré
inequality on lattice cubes, since the integer cube of side `n` is the lattice cube of side `n - 1`
and each increment along an edge of `B` is at most `√2` times the gradient magnitude.
-/

open LatticeProb.Percolation
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- An integer cube of side `n ≥ 1` is the lattice cube `corner + {0, …, n - 1}^d`. -/
theorem IntegerCube.vertices_eq_latticeCube (B : IntegerCube d) (hB : 0 < B.size) :
    B.vertices = LatticeHC.latticeCube B.corner (B.size - 1) := by
  ext x
  rw [IntegerCube.mem_vertices, LatticeHC.mem_latticeCube_iff_coord]
  refine forall_congr' fun i => ?_
  have : ((B.size - 1 : ℕ) : ℤ) = (B.size : ℤ) - 1 := by omega
  rw [this]
  omega

/-- **The `L^p` Poincaré inequality on an integer cube.** -/
theorem IntegerCube.sum_abs_sub_mean_rpow_le (B : IntegerCube d) (hB : 0 < B.size)
    (f : Vertex d → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ∑ x ∈ B.vertices, |f x - (∑ y ∈ B.vertices, f y) / B.vertices.card| ^ p ≤
      (d : ℝ) ^ (p - 1) * (d * √2 ^ p) * (B.size : ℝ) ^ p *
        ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices f x ^ p := by
  have hP := LatticeHC.sum_abs_sub_avg_rpow_le (d := d) B.corner (B.size - 1) f hp
  rw [← B.vertices_eq_latticeCube hB] at hP
  have hn : ((B.size - 1 : ℕ) : ℝ) + 1 = B.size := by
    rw [Nat.cast_sub hB, Nat.cast_one]
    ring
  rw [hn] at hP
  have hn1 : ((B.size - 1 : ℕ) : ℝ) ≤ B.size := by
    rw [Nat.cast_sub hB, Nat.cast_one]
    linarith
  have hp0 : 0 ≤ p - 1 := by linarith
  have hedge : ∀ x ∈ B.vertices, (∑ i : Fin d, if x + LatticeProb.unit i ∈ B.vertices then
      |f (x + LatticeProb.unit i) - f x| ^ p else 0) ≤
      d * √2 ^ p * gradNormIn (nearestNeighborGraph d) B.vertices f x ^ p := by
    intro x _
    have hterm : ∀ i : Fin d, (if x + LatticeProb.unit i ∈ B.vertices then
        |f (x + LatticeProb.unit i) - f x| ^ p else 0) ≤
        √2 ^ p * gradNormIn (nearestNeighborGraph d) B.vertices f x ^ p := by
      intro i
      split_ifs with hxi
      · rw [← Real.mul_rpow (Real.sqrt_nonneg _) (gradNormIn_nonneg _ _ _ _), abs_sub_comm]
        exact Real.rpow_le_rpow (abs_nonneg _)
          (abs_sub_le_sqrt_two_mul_gradNormIn _ _ _ hxi ⟨i, Or.inl rfl⟩) (by linarith)
      · exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
          (Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _)
    calc _ ≤ ∑ _i : Fin d, √2 ^ p * gradNormIn (nearestNeighborGraph d) B.vertices f x ^ p :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hG0 : 0 ≤ ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices f x ^ p :=
    Finset.sum_nonneg fun x _ => Real.rpow_nonneg (gradNormIn_nonneg _ _ _ _) _
  have hmean : (∑ y ∈ B.vertices, f y) / B.vertices.card =
      (B.vertices.card : ℝ)⁻¹ * ∑ y ∈ B.vertices, f y := by
    rw [div_eq_inv_mul]
  rw [hmean]
  refine hP.trans ?_
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ (p - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsz : ((B.size - 1 : ℕ) : ℝ) ^ (p - 1) * (B.size : ℝ) ≤ (B.size : ℝ) ^ p := by
    have h1 : ((B.size - 1 : ℕ) : ℝ) ^ (p - 1) ≤ (B.size : ℝ) ^ (p - 1) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hn1 hp0
    have h2 : (B.size : ℝ) ^ (p - 1) * (B.size : ℝ) = (B.size : ℝ) ^ p := by
      have hpos : (0 : ℝ) < B.size := by exact_mod_cast hB
      rw [← Real.rpow_add_one hpos.ne']
      ring_nf
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  have hS0 : 0 ≤ ∑ x ∈ B.vertices, ∑ i : Fin d, (if x + LatticeProb.unit i ∈ B.vertices then
      |f (x + LatticeProb.unit i) - f x| ^ p else 0) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact Real.rpow_nonneg (abs_nonneg _) _
      · exact le_rfl
  have hmul := mul_le_mul hsz (Finset.sum_le_sum hedge) hS0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [← Finset.mul_sum] at hmul
  calc (d : ℝ) ^ (p - 1) * ((B.size - 1 : ℕ) : ℝ) ^ (p - 1) * (B.size : ℝ) *
        ∑ x ∈ B.vertices, ∑ i : Fin d, (if x + LatticeProb.unit i ∈ B.vertices then
          |f (x + LatticeProb.unit i) - f x| ^ p else 0)
      = (d : ℝ) ^ (p - 1) * ((((B.size - 1 : ℕ) : ℝ) ^ (p - 1) * (B.size : ℝ)) *
        ∑ x ∈ B.vertices, ∑ i : Fin d, (if x + LatticeProb.unit i ∈ B.vertices then
          |f (x + LatticeProb.unit i) - f x| ^ p else 0)) := by ring
    _ ≤ (d : ℝ) ^ (p - 1) * ((B.size : ℝ) ^ p * ((d * √2 ^ p) *
          ∑ x ∈ B.vertices, gradNormIn (nearestNeighborGraph d) B.vertices f x ^ p)) :=
        mul_le_mul_of_nonneg_left hmul hd0
    _ = _ := by ring

end Rigidity.Percolation
