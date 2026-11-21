import Rigidity.Proofs.Dirichlet.CubeStokes
import Rigidity.Vendor.LHCH.Support.Analysis.CubePoincare

/-!
# Affine approximation on a lattice cube

On the cube `Q = y + {0, …, N − 1}^d`, the Poincaré inequality of `LatticeHC` gives
`Σ_Q (g − ⟨g⟩_Q)² ≤ C N² Σ_{edges of Q} (∇g)²`. Applied to `g` minus the affine function with the
mesoscopic average slope `p_j = ⟨∇_j g⟩_Q` and then to each `∇_j g`, it bounds the distance from
`g` to the affine function `ℓ(x) = c + p · (x − y)` (with `c` the average of `g − p · (x − y)`) by
`C N⁴` times the second differences of `g` on the edges of `Q`.

This is the discrete form of the estimate of `u_hom − ℓ_y` on the mesoscopic cubes `y + □_n` in
the proof of Armstrong–Dario, Lemma 6.3 (iii): `|ℓ_y − u_hom|² ≤ C 3^{4n} ⨍ |∇∇u_hom|²`. The
constant of the affine function is the average of `g − p · (x − y)` rather than the average of
`g`, which removes the dependence on the position of `y` in the cube.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The half-open cube of side `N ≥ 1` with corner `z` is the closed cube `z + {0, …, N − 1}^d`. -/
theorem vertices_cornerCube_eq_latticeCube (z : Vertex d) {N : ℕ} (hN : 0 < N) :
    (cornerCube z N).vertices = latticeCube z (N - 1) := by
  ext x
  rw [IntegerCube.mem_vertices, mem_latticeCube_iff_coord]
  simp only [cornerCube]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> omega

/-- **Poincaré inequality on a cube of side `N`**: there is `C(d)` with
`Σ_{x∈Q} (g(x) − N^{-d} Σ_Q g)² ≤ C N² Σ_{x∈Q} Σ_i [x + e_i ∈ Q] (∇_i g(x))²`. -/
theorem exists_sum_sq_sub_cubeAverage_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Vertex d) (N : ℕ) (g : Vertex d → ℝ), 0 < N →
      ∑ x ∈ (cornerCube y N).vertices, (g x - cubeAverage N g y) ^ 2 ≤
        C * (N : ℝ) ^ 2 * ∑ x ∈ (cornerCube y N).vertices, ∑ i : Fin d,
          if x + unit i ∈ (cornerCube y N).vertices then (g (x + unit i) - g x) ^ 2 else 0 := by
  obtain ⟨C, hC, h⟩ := exists_sum_sq_sub_avg_le (d := d)
  refine ⟨C, hC, fun y N g hN => ?_⟩
  have hQ := vertices_cornerCube_eq_latticeCube y hN
  have hcard : ((latticeCube y (N - 1)).card : ℝ) = (N : ℝ) ^ d := by
    rw [← hQ, card_vertices]
    simp [cornerCube]
  have havg : cubeAverage N g y =
      ((latticeCube y (N - 1)).card : ℝ)⁻¹ * ∑ z ∈ latticeCube y (N - 1), g z := by
    rw [cubeAverage, hcard, ← hQ, div_eq_inv_mul]
  rw [havg, hQ]
  refine (h y (N - 1) g).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine mul_le_mul_of_nonneg_left ?_ hC
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by
      rw [Nat.cast_sub hN]
      linarith
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
      split_ifs <;> positivity

/-- The slope `p_j = N^{-d} Σ_{x ∈ y + □} ∇_j g(x)` of the affine approximation. -/
noncomputable def cubeSlope (N : ℕ) (g : Vertex d → ℝ) (y : Vertex d) (j : Fin d) : ℝ :=
  cubeAverage N (fun x => g (x + unit j) - g x) y

/-- The affine approximation `ℓ(x) = c + p · (x − y)` of `g` on `y + □`, with the mesoscopic
slope `p` and `c` the average of `g − p · (x − y)`. -/
noncomputable def cubeAffine (N : ℕ) (g : Vertex d → ℝ) (y x : Vertex d) : ℝ :=
  cubeAverage N (fun z => g z - ∑ j, cubeSlope N g y j * ((z j - y j : ℤ) : ℝ)) y +
    ∑ j, cubeSlope N g y j * ((x j - y j : ℤ) : ℝ)

/-- **Affine approximation on a cube**: there is `C(d)` with
`Σ_{x∈Q} (g(x) − ℓ(x))² ≤ C N⁴ Σ_j Σ_{x∈Q} Σ_i [x + e_i ∈ Q] (∇_i∇_j g(x))²`. -/
theorem exists_sum_sq_sub_cubeAffine_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Vertex d) (N : ℕ) (g : Vertex d → ℝ), 0 < N →
      ∑ x ∈ (cornerCube y N).vertices, (g x - cubeAffine N g y x) ^ 2 ≤
        C * (N : ℝ) ^ 4 * ∑ j : Fin d, ∑ x ∈ (cornerCube y N).vertices, ∑ i : Fin d,
          if x + unit i ∈ (cornerCube y N).vertices then
            ((g (x + unit i + unit j) - g (x + unit i)) - (g (x + unit j) - g x)) ^ 2 else 0 := by
  obtain ⟨C, hC, hP⟩ := exists_sum_sq_sub_cubeAverage_le (d := d)
  refine ⟨C * C, mul_nonneg hC hC, fun y N g hN => ?_⟩
  set Q := (cornerCube y N).vertices
  set p : Fin d → ℝ := cubeSlope N g y
  set h : Vertex d → ℝ := fun z => g z - ∑ j, p j * ((z j - y j : ℤ) : ℝ)
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- `g − ℓ = h − ⟨h⟩`
  have hgl : ∀ x, g x - cubeAffine N g y x = h x - cubeAverage N h y := by
    intro x
    simp only [cubeAffine, h, p]
    ring
  -- the gradient of `h`
  have hgrad : ∀ x (i : Fin d), h (x + unit i) - h x = (g (x + unit i) - g x) - p i := by
    intro x i
    simp only [h]
    have : ∑ j, p j * (((x + unit i) j - y j : ℤ) : ℝ) =
        ∑ j, p j * ((x j - y j : ℤ) : ℝ) + p i := by
      rw [← Finset.sum_add_sum_compl {i}]
      conv_rhs => rw [← Finset.sum_add_sum_compl {i}]
      simp only [Finset.sum_singleton]
      have hrest : ∑ j ∈ ({i} : Finset (Fin d))ᶜ, p j * (((x + unit i) j - y j : ℤ) : ℝ) =
          ∑ j ∈ ({i} : Finset (Fin d))ᶜ, p j * ((x j - y j : ℤ) : ℝ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hji : j ≠ i := by simpa using hj
        rw [add_unit_apply, if_neg hji, add_zero]
      rw [hrest, add_unit_apply, if_pos rfl]
      push_cast
      ring
    rw [this]
    ring
  -- first Poincaré: for `h`
  have h1 := hP y N h hN
  simp only [hgrad] at h1
  -- second Poincaré: for each `∇_i g`
  have h2 : ∀ i : Fin d, ∑ x ∈ Q, (if x + unit i ∈ Q then ((g (x + unit i) - g x) - p i) ^ 2
      else 0) ≤ C * (N : ℝ) ^ 2 * ∑ x ∈ Q, ∑ j : Fin d,
        if x + unit j ∈ Q then ((g (x + unit j + unit i) - g (x + unit j)) -
          (g (x + unit i) - g x)) ^ 2 else 0 := by
    intro i
    have hPi := hP y N (fun x => g (x + unit i) - g x) hN
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) hPi
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  calc ∑ x ∈ Q, (g x - cubeAffine N g y x) ^ 2
      = ∑ x ∈ Q, (h x - cubeAverage N h y) ^ 2 := Finset.sum_congr rfl fun x _ => by rw [hgl]
    _ ≤ C * (N : ℝ) ^ 2 * ∑ x ∈ Q, ∑ i : Fin d,
          if x + unit i ∈ Q then ((g (x + unit i) - g x) - p i) ^ 2 else 0 := h1
    _ = C * (N : ℝ) ^ 2 * ∑ i : Fin d, ∑ x ∈ Q,
          if x + unit i ∈ Q then ((g (x + unit i) - g x) - p i) ^ 2 else 0 := by
        rw [Finset.sum_comm]
    _ ≤ C * (N : ℝ) ^ 2 * ∑ i : Fin d, C * (N : ℝ) ^ 2 * ∑ x ∈ Q, ∑ j : Fin d,
          if x + unit j ∈ Q then ((g (x + unit j + unit i) - g (x + unit j)) -
            (g (x + unit i) - g x)) ^ 2 else 0 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) (by positivity)
    _ = C * C * (N : ℝ) ^ 4 * ∑ j : Fin d, ∑ x ∈ Q, ∑ i : Fin d,
          if x + unit i ∈ Q then
            ((g (x + unit i + unit j) - g (x + unit i)) - (g (x + unit j) - g x)) ^ 2
          else 0 := by
        rw [← Finset.mul_sum]
        ring

end Rigidity.Dirichlet
