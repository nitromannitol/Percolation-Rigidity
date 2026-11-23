import Rigidity.Proofs.Regularity.PlanarCorrectorScale

/-!
# The uniform sublinearity of the planar correctors

Armstrong and Dario (arXiv:1609.09431v2), Remark after (1.19): the bound (1.18) in `L̲²` upgrades
to the uniform norm, (1.22). At the triadic scale `N = 9 · 3^m`, with the minimal scales of the
Lipschitz estimate at the vertices of `{|z_i| ≤ 3N}` and the sides of the partition cubes of
`{|z_i| ≤ 2N}` at most `y` and `3y`, and `‖χ‖_{L̲²(𝒞_∞ ∩ B_{6N})} ≤ K |q| N y^{-28}`,
`abs_corrector_le_at_scale` gives `|χ(x)| ≤ c₃ y⁷ |q| + c₄ |q| N y^{-7}` for `x ∈ 𝒞_∞`,
`|x_i| ≤ N`: the comparison with the coarsening and the interpolation inequality on the box
`x + [0, t]²`, `t = ⌊N y^{-14}⌋`.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.S2
open Rigidity.External
open scoped Classical

variable {ω : Configuration 2}

/-- The algebra of the two terms of `abs_le_of_scale_bounds` at one scale. -/
theorem scale_terms_le {N y t K CL q L B : ℝ} (hN : 0 < N) (hy : 1 ≤ y) (ht0 : 0 ≤ t)
    (ht : t ≤ N / y ^ 14) (ht1 : N / y ^ 14 ≤ t + 1) (hq : 0 ≤ q)
    (hL : L = CL * y ^ 3 * q) (hB : B = K * q * N / y ^ 28) :
    (81 * (3 * y) ^ 2) ^ 2 * L +
        √(2 / (t + 1) ^ 2 * ((3 * y) ^ 2 * (225 * N ^ 2 * B ^ 2)) +
          8 * t ^ 2 * ((81 * (3 * y) ^ 2) ^ 2 * L) ^ 2) ≤
      729 ^ 2 * CL * y ^ 7 * q + √(4050 * K ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * q * N / y ^ 7 := by
  have hy0 : 0 < y := by linarith
  have hyp : ∀ n : ℕ, 0 < y ^ n := fun n => pow_pos hy0 n
  have hy14 : 1 ≤ y ^ 12 := one_le_pow₀ hy
  have hA : (81 * (3 * y) ^ 2) ^ 2 * L = 729 ^ 2 * CL * y ^ 7 * q := by rw [hL]; ring
  rw [hA]
  gcongr
  have htp : 0 < t + 1 := by linarith
  have h1 : 2 / (t + 1) ^ 2 * ((3 * y) ^ 2 * (225 * N ^ 2 * B ^ 2)) ≤
      4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
    have hinv : 1 / (t + 1) ^ 2 ≤ y ^ 28 / N ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have := pow_le_pow_left₀ (by positivity) ht1 2
      rw [div_pow, div_le_iff₀ (by positivity), ← pow_mul] at this
      norm_num at this
      linarith
    rw [hB]
    calc 2 / (t + 1) ^ 2 * ((3 * y) ^ 2 * (225 * N ^ 2 * (K * q * N / y ^ 28) ^ 2))
        = 2 * (1 / (t + 1) ^ 2) * ((3 * y) ^ 2 * (225 * N ^ 2 * (K * q * N / y ^ 28) ^ 2)) := by
          ring
      _ ≤ 2 * (y ^ 28 / N ^ 2) * ((3 * y) ^ 2 * (225 * N ^ 2 * (K * q * N / y ^ 28) ^ 2)) := by
          gcongr
      _ = 4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 26 := by
          field_simp
          ring
      _ ≤ 4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
          apply div_le_div_of_nonneg_left (by positivity) (hyp 14)
          calc y ^ 14 = y ^ 14 * 1 := (mul_one _).symm
            _ ≤ y ^ 14 * y ^ 12 := mul_le_mul_of_nonneg_left hy14 (hyp 14).le
            _ = y ^ 26 := by ring
  have h2 : 8 * t ^ 2 * (729 ^ 2 * CL * y ^ 7 * q) ^ 2 ≤
      8 * 729 ^ 4 * CL ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
    have ht2 : t ^ 2 ≤ N ^ 2 / y ^ 28 := by
      have := pow_le_pow_left₀ ht0 ht 2
      rw [div_pow, ← pow_mul] at this
      exact this
    calc 8 * t ^ 2 * (729 ^ 2 * CL * y ^ 7 * q) ^ 2
        ≤ 8 * (N ^ 2 / y ^ 28) * (729 ^ 2 * CL * y ^ 7 * q) ^ 2 := by gcongr
      _ = 8 * 729 ^ 4 * CL ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 := by
          field_simp
  have h3 : 4050 * K ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 + 8 * 729 ^ 4 * CL ^ 2 * q ^ 2 * N ^ 2 / y ^ 14 =
      (√(4050 * K ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * q * N / y ^ 7) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
    field_simp
    ring
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ √(4050 * K ^ 2 + 8 * 729 ^ 4 * CL ^ 2) * q * N /
    y ^ 7), ← h3]
  exact Real.sqrt_le_sqrt (add_le_add h1 h2)

end Rigidity.Proofs.Regularity
