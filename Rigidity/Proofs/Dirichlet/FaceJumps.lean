import Rigidity.Proofs.Dirichlet.AffinePatch
import Rigidity.Proofs.Dirichlet.MesoscopicAffine

/-!
# Jumps of the patched affine approximations across the faces of a tiling

Sums over the doubled cubes `y_i + {0, …, 2N − 1}^d` of a tiling by cubes of side `N` count every
point at most `2^d` times, so with the face bound `sq_cubeAffine_neighbour_sub_le_secondDiff`
and the convexity of the tile slopes, the squared jumps of the patched affine approximations
across the faces orthogonal to `e_j` satisfy
`Σ_{faces} (ℓ_{y'}(x + e_j) − ℓ_y(x))² ≤ 3 (1 + d) 2^d N³ Σ_k Σ (∇_j∇_k g)² + 3 N⁻¹ Σ (∇_j g)²`.

This is the bound of the energy of `ṽ` on the edges between mesoscopic cubes in the proof of
Armstrong–Dario, Lemma 6.3, Step 2: `C 3^{−n} (|p|² + 3^{4n} ⨍ |∇∇u_hom|²)` after normalization.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Overlap of the doubled tiles**: for `F ≥ 0`,
`Σ_i Σ_{y_i + {0,…,2N−1}^d} F ≤ 2^d Σ_{z + {0,…,(M+1)N−1}^d} F`. -/
theorem sum_tiles_doubled_le {N : ℕ} (hN : 0 < N) (z : Vertex d) (M : ℕ) (F : Vertex d → ℝ)
    (hF : ∀ w, 0 ≤ F w) :
    ∑ i ∈ (cornerCube 0 M).vertices, ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices, F w ≤
      2 ^ d * ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices, F w := by
  classical
  set G : Vertex d → ℝ := fun m => ∑ w ∈ (cornerCube (z + (N : ℤ) • m) N).vertices, F w
  have hG : ∀ m, 0 ≤ G m := fun m => Finset.sum_nonneg fun w _ => hF w
  have h2 : ∀ i, ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices, F w =
      ∑ i' ∈ (cornerCube 0 2).vertices, G (i + i') := by
    intro i
    rw [sum_cornerCube_mul hN (z + (N : ℤ) • i) 2 F]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [G, smul_add, add_assoc]
  simp only [h2]
  rw [Finset.sum_comm, sum_cornerCube_mul hN z (M + 1) F]
  have hcard : ((cornerCube (0 : Vertex d) 2).vertices.card : ℝ) = 2 ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  calc ∑ i' ∈ (cornerCube 0 2).vertices, ∑ i ∈ (cornerCube 0 M).vertices, G (i + i')
      ≤ ∑ _i' ∈ (cornerCube (0 : Vertex d) 2).vertices,
          ∑ m ∈ (cornerCube 0 (M + 1)).vertices, G m := by
        refine Finset.sum_le_sum fun i' hi' => ?_
        calc ∑ i ∈ (cornerCube 0 M).vertices, G (i + i')
            = ∑ m ∈ (cornerCube 0 M).vertices.map (addRightEmbedding i'), G m := by
              rw [Finset.sum_map]
              rfl
          _ ≤ ∑ m ∈ (cornerCube 0 (M + 1)).vertices, G m := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun m _ _ => hG m
              obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hm
              rw [IntegerCube.mem_vertices] at hi hi' ⊢
              intro k
              have h1 := hi k
              have h2 := hi' k
              simp only [cornerCube, Pi.zero_apply, zero_add, addRightEmbedding_apply,
                Pi.add_apply] at h1 h2 ⊢
              push_cast at h1 h2 ⊢
              constructor <;> omega
    _ = 2 ^ d * ∑ m ∈ (cornerCube 0 (M + 1)).vertices, G m := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

end Rigidity.Dirichlet
