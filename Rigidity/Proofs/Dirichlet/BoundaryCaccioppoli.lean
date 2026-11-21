import Rigidity.Proofs.Dirichlet.SecondDifferences

/-!
# Caccioppoli inequality up to the boundary

For nonnegative conductances `c`, a function `u` that is `c`-harmonic on a finite set `U` and
equal to `f` off `U`, and any cutoff `η` (not required to vanish off `U`),
`Σ η(x + e_j)² c (∇_j u)² ≤ 8 Σ c (∇_j η)² ((u − f)(x + e_j)² + (u − f)(x)²) +
  2 Σ c (η(x + e_j)² + (∇_j η)²) (∇_j f)²`:
test the equation with `η² (u − f)`, which vanishes off `U`, and use Young's inequality.

This is the Caccioppoli inequality for the Dirichlet problem near the boundary, the first
ingredient of the boundary reverse Hölder inequality behind the global Meyers estimate for the
homogenized solution (Armstrong–Dario, Proposition 6.5, from [Giu]) and of the energy bounds of
Lemma 6.3, Step 3.
-/

open LatticeProb LatticeHC

namespace Rigidity.Dirichlet

variable {d : ℕ}

/-- The elementary inequality behind the boundary Caccioppoli inequality: with `G = A − B + F`,
`a² G² ≤ (a² A − b² B) G + a² G²/2 + 4 (a − b)² (A² + B²) + (a² + (a − b)²) F²`. -/
theorem sq_mul_sq_le_boundary (a b A B F : ℝ) :
    a ^ 2 * (A - B + F) ^ 2 ≤ (a ^ 2 * A - b ^ 2 * B) * (A - B + F) +
      1 / 2 * (a ^ 2 * (A - B + F) ^ 2) + 4 * ((a - b) ^ 2 * (A ^ 2 + B ^ 2)) +
        (a ^ 2 + (a - b) ^ 2) * F ^ 2 := by
  nlinarith [sq_nonneg (a * (A - B + F) / 2 - a * F),
    sq_nonneg (a * (A - B + F) / 2 + 2 * (a - b) * B),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (A - B)),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (B - F)),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg A), mul_nonneg (sq_nonneg (a - b)) (sq_nonneg B),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg F)]

/-- **Caccioppoli inequality for the Dirichlet problem**: for `c ≥ 0`, `u` `c`-harmonic on `U`
with `u = f` off `U`, any `η` and `S` covering the edges at `U`,
`Σ_{x∈S} Σ_j η(x + e_j)² c(x,j) (∇_j u(x))² ≤
  8 Σ_{x∈S} Σ_j c(x,j) (∇_j η(x))² ((u − f)(x + e_j)² + (u − f)(x)²) +
  2 Σ_{x∈S} Σ_j c(x,j) (η(x + e_j)² + (∇_j η(x))²) (∇_j f(x))²`. -/
theorem sum_cutoff_energy_le_of_eq_off (c : Edge d → ℝ) (hc : ∀ e, 0 ≤ c e)
    {U S : Finset (Site d)} (hS : CoversEdges U S) (u f η : Site d → ℝ)
    (hu : ∀ x ∈ U, condLaplacian c u x = 0) (huf : ∀ x, x ∉ U → u x = f x) :
    ∑ x ∈ S, ∑ j : Fin d, η (x + unit j) ^ 2 * c (x, j) * (u (x + unit j) - u x) ^ 2 ≤
      8 * ∑ x ∈ S, ∑ j : Fin d, c (x, j) * (η (x + unit j) - η x) ^ 2 *
          ((u (x + unit j) - f (x + unit j)) ^ 2 + (u x - f x) ^ 2) +
        2 * ∑ x ∈ S, ∑ j : Fin d, c (x, j) * (η (x + unit j) ^ 2 + (η (x + unit j) - η x) ^ 2) *
          (f (x + unit j) - f x) ^ 2 := by
  have key := sum_mul_condLaplacian_eq_sum_gradient_mul c U S
    (fun x => η x ^ 2 * (u x - f x)) u (fun x hx => by simp [huf x hx]) hS
  rw [Finset.sum_eq_zero fun x hx => by rw [hu x hx, mul_zero]] at key
  have hpt : ∀ x (j : Fin d), η (x + unit j) ^ 2 * c (x, j) * (u (x + unit j) - u x) ^ 2 ≤
      c (x, j) * ((η (x + unit j) ^ 2 * (u (x + unit j) - f (x + unit j)) -
        η x ^ 2 * (u x - f x)) * (u (x + unit j) - u x)) +
      1 / 2 * (η (x + unit j) ^ 2 * c (x, j) * (u (x + unit j) - u x) ^ 2) +
      4 * (c (x, j) * (η (x + unit j) - η x) ^ 2 *
        ((u (x + unit j) - f (x + unit j)) ^ 2 + (u x - f x) ^ 2)) +
      c (x, j) * (η (x + unit j) ^ 2 + (η (x + unit j) - η x) ^ 2) *
        (f (x + unit j) - f x) ^ 2 := by
    intro x j
    have h := sq_mul_sq_le_boundary (η (x + unit j)) (η x) (u (x + unit j) - f (x + unit j))
      (u x - f x) (f (x + unit j) - f x)
    have hG : u (x + unit j) - f (x + unit j) - (u x - f x) + (f (x + unit j) - f x) =
        u (x + unit j) - u x := by ring
    rw [hG] at h
    have := mul_le_mul_of_nonneg_left h (hc (x, j))
    nlinarith [this]
  have h := Finset.sum_le_sum fun x (_ : x ∈ S) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => hpt x j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  linarith

end Rigidity.Dirichlet
