import Rigidity.Proofs.Percolation.GeneralDim.CubeMuNuComparison

/-!
# Lower bound for `-μ` on triadic cubes of `ℤ^d`, up to the boundary errors

Comparing `μ(U, q)` with `ν(U, t q)` for `t = 2 / (3^d d)` and using `ν(U, p) ≤ (3^d / 4) |p|₁²`
and `|q|₁² ≤ d |q|²`, on the partition event and for a resolved cube of side `L`,

`μ(U, q) ≤ -|q|² / (3^d d) + t |q|² / L + |q|₁ E_{t q}(v) / |U|`,

where `v` is the maximizer of `ν(U, t q)` and `E` the boundary error of `CubeNablaAffine`
(Armstrong and Dario, Lemma 4.7, (4.30), deterministic form: the boundary error is bounded in
probability in their proof).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- `|q|₁² ≤ d |q|²`. -/
theorem sq_sum_abs_le_mul_sum_sq (q : Fin d → ℝ) :
    (∑ i, |q i|) ^ 2 ≤ d * ∑ i, q i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |q i|)
  rw [Finset.card_univ, Fintype.card_fin] at h
  simpa only [sq_abs] using h

/-- **Lower bound for `-μ`** (Armstrong and Dario, Lemma 4.7, (4.30), deterministic form). -/
theorem exists_cubeMu_le_neg_sum_sq (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (q : Fin d → ℝ) :
    ∃ v ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w v = cubeFluxPairing ω U ((2 / (3 ^ d * d) : ℝ) • q) w) ∧
      cubeMu ω U q ≤ -(∑ i, q i ^ 2) / (3 ^ d * d) +
        (2 / (3 ^ d * d) * (∑ i, q i ^ 2) / (U.toIntegerCube.size : ℝ) +
          (∑ i, |q i|) * cubeBoundaryError ω U ((2 / (3 ^ d * d) : ℝ) • q) v /
            U.latticeVolume) := by
  set t : ℝ := 2 / (3 ^ d * d) with ht
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : (0 : ℝ) < 3 ^ d := by positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  obtain ⟨v, hv, hvar, hle⟩ := exists_cubeMu_le_cubeNu_sub hd hP hU (t • q) q
  refine ⟨v, hv, hvar, ?_⟩
  set S := ∑ i, q i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs : ∑ i, q i * (t • q) i = t * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hs, abs_of_nonneg (by positivity : 0 ≤ t * S)] at hle
  have hν := cubeNu_le (ω := ω) (U := U) (t • q)
  have hp : (∑ i, |(t • q) i|) ^ 2 = t ^ 2 * (∑ i, |q i|) ^ 2 := by
    have : ∑ i, |(t • q) i| = t * ∑ i, |q i| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ht0]
    rw [this]
    ring
  rw [hp] at hν
  have hq := sq_sum_abs_le_mul_sum_sq q
  rw [← hS] at hq
  have hν' : cubeNu ω U (t • q) ≤ 3 ^ d / 4 * t ^ 2 * (d * S) := by
    calc cubeNu ω U (t • q) ≤ 3 ^ d / 4 * (t ^ 2 * (∑ i, |q i|) ^ 2) := hν
      _ ≤ 3 ^ d / 4 * (t ^ 2 * (d * S)) := by gcongr
      _ = 3 ^ d / 4 * t ^ 2 * (d * S) := by ring
  have hval : 3 ^ d / 4 * t ^ 2 * (d * S) - t * S = -S / (3 ^ d * d) := by
    have h3' : (3 : ℝ) ^ d ≠ 0 := h3.ne'
    have hd'' : (d : ℝ) ≠ 0 := hd'.ne'
    rw [ht]
    field_simp
    ring
  have hfinal : cubeNu ω U (t • q) - t * S ≤ -S / (3 ^ d * d) := by linarith
  linarith

end Rigidity.Percolation
