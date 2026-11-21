import Rigidity.Proofs.Regularity.LatticeHarmonic
import Rigidity.Proofs.Regularity.DiscreteTaylor

/-!
# Second differences of lattice harmonic functions

The forward differences of a lattice harmonic function are harmonic, and the second forward
differences `D_a D_b f` of a function harmonic on the box `Q_{4ρ + 4}(z)`, `ρ = 2 · 4^d m`, are
bounded at the points of `Q_m(z)` by the square sum of `f` on `Q_{4ρ + 6}(z)`, with the factor
`m^{-d} ρ^{-4}` (`sq_fwd_fwd_le`): the interior bound of harmonic functions applied to `D_a D_b f`,
and two Caccioppoli inequalities.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

theorem latticeLaplacian_fwd (i : Fin d) (h : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    latticeLaplacian (fwd i h) x = latticeLaplacian h (x + unit i) - latticeLaplacian h x := by
  have := latticeLaplacian_sub (fun y => h (y + unit i)) h x
  rw [latticeLaplacian_comp_add] at this
  exact this

theorem supDist_add_unit_le' (x z : Fin d → ℤ) (i : Fin d) :
    supDist (x + unit i) z ≤ supDist x z + 1 := by
  have := supDist_add_unit_le x z i 1 (by norm_num)
  rwa [one_smul] at this

/-- Forward differences of a function harmonic on `Q_{L+1}` are harmonic on `Q_L`. -/
theorem latticeLaplacian_fwd_eq_zero {h : (Fin d → ℤ) → ℝ} {z : Fin d → ℤ} {L : ℕ}
    (hh : ∀ x ∈ supBox z (L + 1), latticeLaplacian h x = 0) (i : Fin d) :
    ∀ x ∈ supBox z L, latticeLaplacian (fwd i h) x = 0 := by
  intro x hx
  rw [latticeLaplacian_fwd, hh x (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega),
    hh (x + unit i) (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢
      have := supDist_add_unit_le' x z i; omega), sub_zero]

/-- One forward difference and the Caccioppoli inequality. -/
theorem sum_sq_fwd_le (h : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) {ρ : ℕ} (hρ : 0 < ρ)
    (hh : ∀ x ∈ supBox z (2 * ρ), latticeLaplacian h x = 0) (a : Fin d) :
    ∑ x ∈ supBox z ρ, fwd a h x ^ 2 ≤ 16 * d / (ρ : ℝ) ^ 2 * ∑ x ∈ supBox z (2 * ρ + 2), h x ^ 2 := by
  refine le_trans ?_ (caccioppoli_supBox h z hρ hh)
  refine sum_le_sum fun x _ => ?_
  exact single_le_sum (f := fun i => (h (x + unit i) - h x) ^ 2) (fun i _ => sq_nonneg _)
    (mem_univ a)

/-- **Second differences of lattice harmonic functions.** -/
theorem sq_fwd_fwd_le (f : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) {m : ℕ} (hm : 0 < m)
    (hf : ∀ x ∈ supBox z (4 * (4 ^ d * (2 * m)) + 4), latticeLaplacian f x = 0)
    (a b : Fin d) {x₀ : Fin d → ℤ} (hx₀ : x₀ ∈ supBox z m) :
    fwd a (fwd b f) x₀ ^ 2 ≤
      4 ^ d * (64 * d) ^ d / ((m : ℝ) + 1) ^ d *
        (16 * d / ((4 ^ d * (2 * m) : ℕ) : ℝ) ^ 2 *
          (16 * d / ((2 * (4 ^ d * (2 * m)) + 2 : ℕ) : ℝ) ^ 2 *
            ∑ x ∈ supBox z (2 * (2 * (4 ^ d * (2 * m)) + 2) + 2), f x ^ 2)) := by
  set ρ := 4 ^ d * (2 * m) with hρdef
  have hρ : 0 < ρ := by positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- harmonicity of `f`, `D_b f`, `D_a D_b f`
  have hf1 : ∀ x ∈ supBox z (2 * (2 * ρ + 2)), latticeLaplacian f x = 0 := fun x hx =>
    hf x (by rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)
  have hfb : ∀ x ∈ supBox z (2 * ρ), latticeLaplacian (fwd b f) x = 0 :=
    latticeLaplacian_fwd_eq_zero (fun x hx => hf x (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) b
  have hfab : ∀ x ∈ supBox z ρ, latticeLaplacian (fwd a (fwd b f)) x = 0 :=
    latticeLaplacian_fwd_eq_zero (fun x hx => hfb x (by
      rw [mem_supBox_iff_supDist_le] at hx ⊢; omega)) a
  have h1 := sq_le_of_latticeHarmonic (fwd a (fwd b f)) z hm hfab hx₀
  have h2 := sum_sq_fwd_le (fwd b f) z hρ hfb a
  have h3 := sum_sq_fwd_le f z (by omega : 0 < 2 * ρ + 2) hf1 b
  have hA := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 16 * d / (ρ : ℝ) ^ 2)
  refine h1.trans (mul_le_mul_of_nonneg_left (h2.trans hA) (by positivity))

end Rigidity.Proofs.Regularity
