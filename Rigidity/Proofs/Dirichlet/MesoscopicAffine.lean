import Rigidity.Proofs.Dirichlet.AffineApproximation
import Rigidity.Proofs.Dirichlet.CubeTiling

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

end Rigidity.Dirichlet
