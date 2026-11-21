import Rigidity.Proofs.Dirichlet.HardyCubeMoments
import Rigidity.Proofs.Dirichlet.Averages

/-!
# Smallness of the energy of the homogenized solution in a boundary layer

For the discrete Dirichlet problem with constant conductances `0 < a_k ≤ Λ` on a cube `Q` of side
`N` (harmonic off the extreme slices, equal to the data `f` there), an exponent `p > 2` with
`q = p/(p − 2)` and `0 < γ ≤ 1/16`, `γ q < 1`, the normalized energy in the boundary layer of
width `ℓ + 1` satisfies
`N^{-d} Σ_{layer} Σ_k a_k (∇_k u)² ≤ 2 N^{-d} Σ_{layer} Σ_k a_k (∇_k f)² +
  88 Λ e^{γ+4γ²} ((2d)^q/(1 − γq))^{1/q} ((ℓ + 1)/N)^γ (N^{-d} Σ_Q |∇f|^p)^{2/p}`.

This is the bound used in the proof of Armstrong–Dario, Lemma 6.3, Step 3, for the homogenized
solution (`3^l ≪ 3^m`): there it is deduced from the global Meyers estimate (Proposition 6.5,
from [Giu]); here it follows from the Hardy-weighted energy estimate on the lattice.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Boundary-layer energy of the homogenized solution.** -/
theorem sum_energy_cubeLayer_div_le {γ p : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 1 / 16) (hp : 2 < p)
    (hγp : γ * (p / (p - 2)) < 1) (hd : 0 < d) (a : Fin d → ℝ) (ha : ∀ k, 0 < a k) {Λ : ℝ}
    (haΛ : ∀ k, a k ≤ Λ) (Q : IntegerCube d) (hN : 0 < Q.size) (u f : Vertex d → ℝ)
    (hu : ∀ x ∈ cubeInterior Q, condLaplacian (constCond a) u x = 0)
    (huf : ∀ x, x ∉ cubeInterior Q → u x = f x) (ℓ : ℕ) :
    (∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2) /
        (Q.size : ℝ) ^ d ≤
      2 * ((∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2) /
          (Q.size : ℝ) ^ d) +
        88 * Λ * Real.exp (γ + 4 * γ ^ 2) *
          ((2 * (d : ℝ)) ^ (p / (p - 2)) / (1 - γ * (p / (p - 2)))) ^ (1 - 2 / p) *
          (((ℓ : ℝ) + 1) / Q.size) ^ γ *
          ((∑ x ∈ Q.vertices, √(∑ k : Fin d, (f (x + unit k) - f x) ^ 2) ^ p) /
            (Q.size : ℝ) ^ d) ^ (2 / p) := by
  have hγ1 : γ < 1 := by linarith
  set q := p / (p - 2) with hq
  have hp2 : 0 < p - 2 := by linarith
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hp2]; linarith
  have hq0 : 0 < q := by linarith
  have hinvq : 1 - 2 / p = 1 / q := by rw [hq]; field_simp
  rw [hinvq]
  set V := (Q.size : ℝ) ^ d with hV
  have hN' : (0 : ℝ) < Q.size := by exact_mod_cast hN
  have hV0 : 0 < V := by positivity
  set W := cubeHardyWeight γ Q with hWdef
  have hW : ∀ x, 0 < W x := cubeHardyWeight_pos hγ1 hd Q
  set g : Vertex d → ℝ := fun x => √(∑ k : Fin d, (f (x + unit k) - f x) ^ 2) with hg
  have hΛ : 0 ≤ Λ := (ha ⟨0, hd⟩).le.trans (haΛ _)
  -- the weighted layer bound
  have hlayer := sum_energy_cubeLayer_le hγ0 hγ hd a ha Q u f hu huf ℓ
  set Y := ∑ x ∈ Q.vertices, ∑ k : Fin d, a k *
    ((W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2) with hY
  -- the weighted energy of the data is at most `2Λ Σ W g²`
  have hYle : Y ≤ 2 * Λ * ∑ x ∈ Q.vertices, W x * |g x| ^ (2 : ℝ) := by
    rw [hY, Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hg2 : |g x| ^ (2 : ℝ) = ∑ k : Fin d, (f (x + unit k) - f x) ^ 2 := by
      rw [Real.rpow_two, sq_abs, hg, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    rw [hg2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hWk : (W x + W (x + unit k)) / 2 ≤ 2 * W x := by
      have := cubeHardyWeight_add_unit_le hγ0.le (by linarith) Q hx k
      have := hW x
      linarith
    have h1 : a k * ((W x + W (x + unit k)) / 2 * (f (x + unit k) - f x) ^ 2) ≤
        Λ * (2 * W x * (f (x + unit k) - f x) ^ 2) :=
      mul_le_mul (haΛ k) (mul_le_mul_of_nonneg_right hWk (sq_nonneg _))
        (mul_nonneg (by have := hW x; have := hW (x + unit k); positivity) (sq_nonneg _)) hΛ
    linarith
  -- Hölder with the moments of the weight
  have hHold := sum_mul_rpow_div_le Q.vertices W g (fun x _ => (hW x).le) (by norm_num : (0:ℝ) < 2)
    hp hV0
  rw [show p / (p - 2) = q from rfl, hinvq] at hHold
  have hmom := sum_cubeHardyWeight_rpow_le hγ0 hγ hq1 hγp hd Q
  have h1γq : (0 : ℝ) < 1 - γ * q := by linarith
  have hmomV : (∑ x ∈ Q.vertices, W x ^ q) / V ≤
      (2 * (d : ℝ)) ^ q / (1 - γ * q) * (Q.size : ℝ) ^ (-(γ * q)) := by
    rw [div_le_iff₀ hV0]
    refine hmom.trans (le_of_eq ?_)
    rw [hV]
    have hpow : (Q.size : ℝ) ^ (d - 1) * (Q.size : ℝ) ^ (1 - γ * q) =
        (Q.size : ℝ) ^ d * (Q.size : ℝ) ^ (-(γ * q)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hN', ← Real.rpow_add hN']
      congr 1
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    calc (2 * (d : ℝ)) ^ q * (Q.size : ℝ) ^ (d - 1) * ((Q.size : ℝ) ^ (1 - γ * q) / (1 - γ * q))
        = (2 * (d : ℝ)) ^ q / (1 - γ * q) *
            ((Q.size : ℝ) ^ (d - 1) * (Q.size : ℝ) ^ (1 - γ * q)) := by ring
      _ = (2 * (d : ℝ)) ^ q / (1 - γ * q) *
            ((Q.size : ℝ) ^ d * (Q.size : ℝ) ^ (-(γ * q))) := by rw [hpow]
      _ = _ := by ring
  have hmom1 : ((∑ x ∈ Q.vertices, W x ^ q) / V) ^ (1 / q) ≤
      ((2 * (d : ℝ)) ^ q / (1 - γ * q)) ^ (1 / q) * (Q.size : ℝ) ^ (-γ) := by
    refine (Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg fun x _ =>
      Real.rpow_nonneg (hW x).le _) hV0.le) hmomV (by positivity)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hN'.le,
      show -(γ * q) * (1 / q) = -γ by field_simp]
  -- the weight at the width of the layer
  have hwℓ := rpow_le_hardyWeight hγ0.le (by linarith) ℓ
  have hwℓ0 := hardyWeight_pos hγ1 ℓ
  have hinvw : 1 / hardyWeight γ ℓ ≤ Real.exp (γ + 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ γ := by
    rw [div_le_iff₀ hwℓ0]
    have hpos : (0 : ℝ) < (ℓ : ℝ) + 1 := by positivity
    calc (1 : ℝ) = Real.exp (γ + 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ γ *
          (Real.exp (-γ - 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ (-γ)) := by
          rw [show Real.exp (γ + 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ γ *
            (Real.exp (-γ - 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ (-γ)) =
            (Real.exp (γ + 4 * γ ^ 2) * Real.exp (-γ - 4 * γ ^ 2)) *
              (((ℓ : ℝ) + 1) ^ γ * ((ℓ : ℝ) + 1) ^ (-γ)) by ring,
            ← Real.exp_add, ← Real.rpow_add hpos]
          simp
      _ ≤ Real.exp (γ + 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ γ * hardyWeight γ ℓ :=
          mul_le_mul_of_nonneg_left hwℓ (by positivity)
  -- assembly
  set L := ((∑ x ∈ Q.vertices, |g x| ^ p) / V) ^ (2 / p) with hL
  have hL0 : 0 ≤ L := by positivity
  set K := ((2 * (d : ℝ)) ^ q / (1 - γ * q)) ^ (1 / q) with hK
  have hK0 : 0 ≤ K := by positivity
  have hYV : Y / V ≤ 2 * Λ * (K * (Q.size : ℝ) ^ (-γ) * L) := by
    have h2Λ : (0 : ℝ) ≤ 2 * Λ := by linarith
    calc Y / V ≤ (2 * Λ * ∑ x ∈ Q.vertices, W x * |g x| ^ (2 : ℝ)) / V :=
          div_le_div_of_nonneg_right hYle hV0.le
      _ = 2 * Λ * ((∑ x ∈ Q.vertices, W x * |g x| ^ (2 : ℝ)) / V) := by ring
      _ ≤ 2 * Λ * (((∑ x ∈ Q.vertices, W x ^ q) / V) ^ (1 / q) * L) :=
          mul_le_mul_of_nonneg_left hHold h2Λ
      _ ≤ 2 * Λ * (K * (Q.size : ℝ) ^ (-γ) * L) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmom1 hL0) h2Λ
  have habs : ∀ x, |g x| ^ p = √(∑ k : Fin d, (f (x + unit k) - f x) ^ 2) ^ p := fun x => by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  simp only [habs] at hL
  have hfrac : ((ℓ : ℝ) + 1) ^ γ * (Q.size : ℝ) ^ (-γ) = (((ℓ : ℝ) + 1) / Q.size) ^ γ := by
    rw [Real.div_rpow (by positivity) hN'.le, Real.rpow_neg hN'.le, div_eq_mul_inv]
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (ha k).le (mul_nonneg (by have := hW x; have := hW (x + unit k); positivity)
      (sq_nonneg _))
  calc (∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2) / V
      ≤ (2 * ∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2 +
          44 / hardyWeight γ ℓ * Y) / V := div_le_div_of_nonneg_right hlayer hV0.le
    _ = 2 * ((∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2) / V) +
          44 * (1 / hardyWeight γ ℓ) * (Y / V) := by ring
    _ ≤ 2 * ((∑ x ∈ cubeLayer Q (ℓ + 1), ∑ k : Fin d, a k * (f (x + unit k) - f x) ^ 2) / V) +
          44 * (Real.exp (γ + 4 * γ ^ 2) * ((ℓ : ℝ) + 1) ^ γ) *
            (2 * Λ * (K * (Q.size : ℝ) ^ (-γ) * L)) := by
        refine add_le_add le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left hinvw (by norm_num)) hYV
          (div_nonneg hY0 hV0.le) (by positivity))
    _ = _ := by
        rw [← hfrac, hL, hK]
        ring

end Rigidity.Dirichlet
