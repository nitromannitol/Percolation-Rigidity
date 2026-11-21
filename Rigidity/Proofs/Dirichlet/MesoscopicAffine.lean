import Rigidity.Proofs.Dirichlet.AffineApproximation
import Rigidity.Proofs.Dirichlet.CubeTiling
import Rigidity.Proofs.Dirichlet.Averages

/-!
# Mesoscopic affine approximations on a tiled cube

For the tiling of the cube with corner `z` and side `M N` by the cubes `y_i + □_N`,
`y_i = z + N i`, the affine approximations `ℓ_{y_i}` of `g` on the tiles satisfy
`Σ_i Σ_{x ∈ y_i + □_N} (g(x) − ℓ_{y_i}(x))² ≤ C N⁴ Σ_{x} Σ_{j,k} (∇_k∇_j g(x))²`, the sum on the
right being over the whole cube.

With the interior `H²` estimate for the homogenized solution, this is the bound of
`Σ_y Σ_{y+□_n} |ℓ_y − u_hom|²` by `C 3^{4n} 3^{−2l} Σ |∇u_hom|²` in the proof of Armstrong–Dario,
Lemma 6.3 (iii).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Affine approximation on the tiles of a cube.** -/
theorem exists_sum_tiles_sq_sub_cubeAffine_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vertex d) (M N : ℕ) (g : Vertex d → ℝ), 0 < N →
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (g x - cubeAffine N g (z + (N : ℤ) • i) x) ^ 2 ≤
        C * (N : ℝ) ^ 4 * ∑ x ∈ (cornerCube z (M * N)).vertices, ∑ j : Fin d, ∑ k : Fin d,
          ((g (x + unit k + unit j) - g (x + unit k)) - (g (x + unit j) - g x)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_sum_sq_sub_cubeAffine_le (d := d)
  refine ⟨C, hC, fun z M N g hN => ?_⟩
  set D : Vertex d → ℝ := fun x => ∑ j : Fin d, ∑ k : Fin d,
    ((g (x + unit k + unit j) - g (x + unit k)) - (g (x + unit j) - g x)) ^ 2 with hD
  rw [sum_cornerCube_mul hN z M D, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (h (z + (N : ℤ) • i) N g hN).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  simp only [hD]
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

/-- **Convexity on the tiles** (Armstrong–Dario (6.36), summed over the mesoscopic cubes of
Lemma 6.3): for `a_k ≥ 0`, the quadratic forms of the mesoscopic slopes at the corners of the
tiles, weighted by the tile volume `N^d`, are at most the energy of `g` on the tiled cube:
`Σ_i N^d Σ_k a_k p_k(y_i)² ≤ Σ_{x} Σ_k a_k (∇_k g(x))²`. -/
theorem sum_tiles_cubeSlope_sq_le (a : Fin d → ℝ) (ha : ∀ k, 0 ≤ a k) (z : Vertex d) (M : ℕ)
    {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) :
    ∑ i ∈ (cornerCube 0 M).vertices, (N : ℝ) ^ d *
        ∑ k : Fin d, a k * cubeSlope N g (z + (N : ℤ) • i) k ^ 2 ≤
      ∑ x ∈ (cornerCube z (M * N)).vertices, ∑ k : Fin d, a k * (g (x + unit k) - g x) ^ 2 := by
  rw [sum_cornerCube_mul hN z M]
  refine Finset.sum_le_sum fun i _ => ?_
  set T := (cornerCube (z + (N : ℤ) • i) N).vertices
  have hT : (#T : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  have h := card_mul_sum_quadratic_avg_le T a ha (fun x k => g (x + unit k) - g x)
  rw [hT] at h
  refine le_trans (le_of_eq ?_) h
  congr 1

end Rigidity.Dirichlet
