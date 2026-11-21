import Rigidity.Proofs.Dirichlet.CubeStokes
import Rigidity.Proofs.Dirichlet.BoundaryData

/-!
# Patching two functions with a cutoff

For functions `v`, `w` and a cutoff `η` with values in `[0, 1]` and `|∇η| ≤ 1/r`, the patched
function `ũ = η v + (1 − η) w` has, on every edge,
`∇ũ = η(x + e) ∇v + (1 − η(x + e)) ∇w + (v − w)(x) ∇η`, hence
`(∇ũ)² ≤ 3 ((∇v)² + (∇w)² + r^{-2} (v − w)(x)²)`.

This is the pointwise bound behind the energy estimates (6.44)–(6.45) of the proof of
Armstrong–Dario, Lemma 6.3, Step 3, for `ũ_hom = η ṽ + (1 − η) u_hom` in the boundary strip.
On the points where `η = 1` (respectively `η = 0`) along all edges the patch has the energy of
`v` (respectively `w`), so the energy of the patch is that of `v` on the interior, that of `w`
outside, and three times the energies of both plus the `L²` difference in the strip
(`edgeEnergy_patch_le`); the patch equals `v − w` times `η` plus `w` (`patch_sub`), which gives the
`L²` estimate (iii) and the boundary condition (i).
-/

open Finset LatticeProb LatticeHC

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

/-- **Energy of the patch on a set**: for `0 ≤ η ≤ 1` and `|∇_j η| ≤ K` at the points of `T`,
`Σ_T Σ_j (∇_j ũ)² ≤ 3 (Σ_T Σ_j (∇_j v)² + Σ_T Σ_j (∇_j w)² + d K² Σ_T (v − w)²)`. -/
theorem sum_sq_patch_grad_le (T : Finset (Vertex d)) {η : Vertex d → ℝ} (v w : Vertex d → ℝ)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1) {K : ℝ}
    (hK : ∀ x ∈ T, ∀ j : Fin d, |η (x + unit j) - η x| ≤ K) :
    ∑ x ∈ T, ∑ j : Fin d, (patch η v w (x + unit j) - patch η v w x) ^ 2 ≤
      3 * (∑ x ∈ T, ∑ j : Fin d, (v (x + unit j) - v x) ^ 2 +
        ∑ x ∈ T, ∑ j : Fin d, (w (x + unit j) - w x) ^ 2 +
          d * K ^ 2 * ∑ x ∈ T, (v x - w x) ^ 2) := by
  have hpt : ∀ x ∈ T, ∑ j : Fin d, (patch η v w (x + unit j) - patch η v w x) ^ 2 ≤
      3 * (∑ j : Fin d, (v (x + unit j) - v x) ^ 2 + ∑ j : Fin d, (w (x + unit j) - w x) ^ 2 +
        d * K ^ 2 * (v x - w x) ^ 2) := by
    intro x hx
    calc ∑ j : Fin d, (patch η v w (x + unit j) - patch η v w x) ^ 2
        ≤ ∑ j : Fin d, 3 * ((v (x + unit j) - v x) ^ 2 + (w (x + unit j) - w x) ^ 2 +
            K ^ 2 * (v x - w x) ^ 2) :=
          Finset.sum_le_sum fun j _ => sq_patch_grad_le (hη0 _) (hη1 _) (hK x hx j)
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The patch minus `w` is `η (v − w)`. -/
theorem patch_sub (η v w : Vertex d → ℝ) (x : Vertex d) :
    patch η v w x - w x = η x * (v x - w x) := by
  simp only [patch]
  ring

/-- The patch equals `w` where `η = 0` and `v` where `η = 1`. -/
theorem patch_of_eq_zero {η : Vertex d → ℝ} (v w : Vertex d → ℝ) {x : Vertex d} (h : η x = 0) :
    patch η v w x = w x := by
  simp only [patch, h]
  ring

theorem patch_of_eq_one {η : Vertex d → ℝ} (v w : Vertex d → ℝ) {x : Vertex d} (h : η x = 1) :
    patch η v w x = v x := by
  simp only [patch, h]
  ring

/-- **Energy of the patch**: let `A`, `B`, `S` be disjoint with union `U`, with `η = 1` along all
edges from `A` and `η = 0` along all edges from `B`, and `|∇_j η| ≤ K` on `S`. For conductances
`0 ≤ c ≤ Λ`, `E_U(ũ) ≤ E_A(v) + E_B(w) + 3 (E_S(v) + E_S(w) + Λ d K² Σ_S (v − w)²)`. -/
theorem edgeEnergy_patch_le (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e) {Λ : ℝ} (hcΛ : ∀ e, c e ≤ Λ)
    {η : Vertex d → ℝ} (v w : Vertex d → ℝ) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (A B S : Finset (Vertex d)) (hAB : Disjoint A B) (hABS : Disjoint (A ∪ B) S)
    (hA : ∀ x ∈ A, ∀ j : Fin d, η x = 1 ∧ η (x + unit j) = 1)
    (hB : ∀ x ∈ B, ∀ j : Fin d, η x = 0 ∧ η (x + unit j) = 0) {K : ℝ}
    (hK : ∀ x ∈ S, ∀ j : Fin d, |η (x + unit j) - η x| ≤ K) :
    edgeEnergy c (A ∪ B ∪ S) (patch η v w) ≤
      edgeEnergy c A v + edgeEnergy c B w +
        3 * (edgeEnergy c S v + edgeEnergy c S w + Λ * (d * K ^ 2 * ∑ x ∈ S, (v x - w x) ^ 2)) := by
  rw [edgeEnergy, Finset.sum_union hABS, Finset.sum_union hAB]
  have hAeq : ∑ x ∈ A, ∑ j : Fin d, c (x, j) * (patch η v w (x + unit j) - patch η v w x) ^ 2 =
      edgeEnergy c A v :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun j _ => by
      rw [patch_of_eq_one v w (hA x hx j).1, patch_of_eq_one v w (hA x hx j).2]
  have hBeq : ∑ x ∈ B, ∑ j : Fin d, c (x, j) * (patch η v w (x + unit j) - patch η v w x) ^ 2 =
      edgeEnergy c B w :=
    Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun j _ => by
      rw [patch_of_eq_zero v w (hB x hx j).1, patch_of_eq_zero v w (hB x hx j).2]
  rw [hAeq, hBeq]
  refine add_le_add le_rfl ?_
  have hpt : ∀ x ∈ S, ∑ j : Fin d, c (x, j) * (patch η v w (x + unit j) - patch η v w x) ^ 2 ≤
      3 * (∑ j : Fin d, c (x, j) * (v (x + unit j) - v x) ^ 2 +
        ∑ j : Fin d, c (x, j) * (w (x + unit j) - w x) ^ 2 +
          Λ * (d * K ^ 2 * (v x - w x) ^ 2)) := by
    intro x hx
    calc ∑ j : Fin d, c (x, j) * (patch η v w (x + unit j) - patch η v w x) ^ 2
        ≤ ∑ j : Fin d, 3 * (c (x, j) * (v (x + unit j) - v x) ^ 2 +
            c (x, j) * (w (x + unit j) - w x) ^ 2 + Λ * (K ^ 2 * (v x - w x) ^ 2)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h := mul_le_mul_of_nonneg_left (sq_patch_grad_le (v := v) (w := w) (hη0 _)
            (hη1 _) (hK x hx j)) (hc0 (x, j))
          have h2 : c (x, j) * (K ^ 2 * (v x - w x) ^ 2) ≤ Λ * (K ^ 2 * (v x - w x) ^ 2) :=
            mul_le_mul_of_nonneg_right (hcΛ _) (by positivity)
          nlinarith
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, edgeEnergy, edgeEnergy]

end Rigidity.Dirichlet
