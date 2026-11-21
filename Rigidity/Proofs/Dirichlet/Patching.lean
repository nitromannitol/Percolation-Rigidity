import Rigidity.Proofs.Dirichlet.CubeStokes

/-!
# Patching two functions with a cutoff

For functions `v`, `w` and a cutoff `η` with values in `[0, 1]` and `|∇η| ≤ 1/r`, the patched
function `ũ = η v + (1 − η) w` has, on every edge,
`∇ũ = η(x + e) ∇v + (1 − η(x + e)) ∇w + (v − w)(x) ∇η`, hence
`(∇ũ)² ≤ 3 ((∇v)² + (∇w)² + r^{-2} (v − w)(x)²)`.

This is the pointwise bound behind the energy estimates (6.44)–(6.45) of the proof of
Armstrong–Dario, Lemma 6.3, Step 3, for `ũ_hom = η ṽ + (1 − η) u_hom` in the boundary strip.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The patched function `η v + (1 − η) w`. -/
def patch (η v w : Vertex d → ℝ) (x : Vertex d) : ℝ := η x * v x + (1 - η x) * w x

/-- **Discrete product rule for the patch.** -/
theorem patch_grad (η v w : Vertex d → ℝ) (x y : Vertex d) :
    patch η v w y - patch η v w x =
      η y * (v y - v x) + (1 - η y) * (w y - w x) + (v x - w x) * (η y - η x) := by
  simp only [patch]
  ring

/-- **Pointwise bound for the gradient of the patch**: for `0 ≤ η ≤ 1` and `|η(y) − η(x)| ≤ K`,
`(ũ(y) − ũ(x))² ≤ 3 ((v(y) − v(x))² + (w(y) − w(x))² + K² (v(x) − w(x))²)`. -/
theorem sq_patch_grad_le {η v w : Vertex d → ℝ} {x y : Vertex d} (hη0 : 0 ≤ η y)
    (hη1 : η y ≤ 1) {K : ℝ} (hK : |η y - η x| ≤ K) :
    (patch η v w y - patch η v w x) ^ 2 ≤
      3 * ((v y - v x) ^ 2 + (w y - w x) ^ 2 + K ^ 2 * (v x - w x) ^ 2) := by
  rw [patch_grad]
  set A := η y * (v y - v x)
  set B := (1 - η y) * (w y - w x)
  set C := (v x - w x) * (η y - η x)
  have hA : A ^ 2 ≤ (v y - v x) ^ 2 := by
    simp only [A, mul_pow]
    have : η y ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (v y - v x)]
  have hB : B ^ 2 ≤ (w y - w x) ^ 2 := by
    simp only [B, mul_pow]
    have : (1 - η y) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (w y - w x)]
  have hC : C ^ 2 ≤ K ^ 2 * (v x - w x) ^ 2 := by
    simp only [C, mul_pow]
    have h1 : (η y - η x) ^ 2 ≤ K ^ 2 := by
      have := abs_nonneg (η y - η x)
      nlinarith [sq_abs (η y - η x)]
    nlinarith [sq_nonneg (v x - w x)]
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C)]

end Rigidity.Dirichlet
