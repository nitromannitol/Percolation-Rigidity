import Rigidity.Proofs.Percolation.PlanarBoundaryWeight
import Rigidity.Proofs.Percolation.PlanarMuNuComparison

/-!
# Lower bound for `-μ` with a quantified error

Combining the comparison of `μ` and `ν` with `p = q / 9`, the bound of the boundary error by
Cauchy–Schwarz and Young with parameter `t = 1 / (|p|₁ √L)`, the energy bound for the `ν`
maximizer and the concentration of the boundary weight, on the partition event and for a resolved
cube `U` of side `L`,

`μ(U, q) + |q|² / 18 ≤ |q|₁² (162001 ∑_{x ∈ ∂U} s_x⁴ / (L √L) + 1 / √L)`,

where `s_x` is the side of the partition cube of `x` and the boundary vertices are counted once per
face (planar form of Armstrong and Dario, Lemma 4.7).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

theorem sum_boundaryIndex_partSide_le (U : TriadicCube 2) :
    ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ≤ ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 :=
  Finset.sum_le_sum fun k _ => by
    have h := one_le_partSide (ω := ω) k.2.2
    calc partSide ω k.2.2 = partSide ω k.2.2 ^ 1 := (pow_one _).symm
      _ ≤ partSide ω k.2.2 ^ 4 := pow_le_pow_right₀ h (by norm_num)

/-- The real-number algebra of the boundary error with `t = 1 / (|p|₁ √L)`. -/
theorem boundary_algebra {Q L S BE : ℝ} (hQ : 0 < Q) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (hBE : BE ≤ (9 * (324000 * S) / (1 / (Q / 9 * Real.sqrt L)) +
      1 / (Q / 9 * Real.sqrt L) * (2 * (9 / 2 * (Q / 9) ^ 2 * (L * L)))) / 2 + Q / 9 * S) :
    Q * BE / (L * L) ≤ Q ^ 2 * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ L by linarith)
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hsqL : Real.sqrt L ≤ L := by nlinarith [Real.sqrt_nonneg L]
  have hLpos : 0 < L := by linarith
  rw [div_le_iff₀ (by positivity)]
  have h1 : Q * BE ≤ Q * ((9 * (324000 * S) / (1 / (Q / 9 * Real.sqrt L)) +
      1 / (Q / 9 * Real.sqrt L) * (2 * (9 / 2 * (Q / 9) ^ 2 * (L * L)))) / 2 + Q / 9 * S) :=
    mul_le_mul_of_nonneg_left hBE hQ.le
  have h2 : Q * ((9 * (324000 * S) / (1 / (Q / 9 * Real.sqrt L)) +
      1 / (Q / 9 * Real.sqrt L) * (2 * (9 / 2 * (Q / 9) ^ 2 * (L * L)))) / 2 + Q / 9 * S) =
      Q ^ 2 * (162000 * S * Real.sqrt L + L * L / (2 * Real.sqrt L) + S / 9) := by
    field_simp
    ring
  have h3 : Q ^ 2 * (162000 * S * Real.sqrt L + L * L / (2 * Real.sqrt L) + S / 9) ≤
      Q ^ 2 * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) * (L * L) := by
    have e : Q ^ 2 * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) * (L * L) =
        Q ^ 2 * (162001 * S * (L / Real.sqrt L) + L * L / (2 * Real.sqrt L)) := by
      field_simp
    rw [e]
    have hLs : L / Real.sqrt L = Real.sqrt L := by
      rw [div_eq_iff hsqpos.ne', ← sq, hsq]
    rw [hLs]
    have hS9 : S / 9 ≤ S * Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]
    have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg Q
    nlinarith [mul_le_mul_of_nonneg_left hS9 hQ2]
  linarith

theorem sq_sum_div_le_aux (a b L : ℝ) (hL : 1 ≤ L) :
    (a ^ 2 + b ^ 2) / 9 / L ≤ (|a| + |b|) ^ 2 * (1 / 2 / Real.sqrt L) := by
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ L by linarith)
  have hqq : a ^ 2 + b ^ 2 ≤ (|a| + |b|) ^ 2 := by
    nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]
  have hLL : Real.sqrt L ≤ L := by nlinarith [Real.sqrt_nonneg L]
  rw [div_div, div_le_iff₀ (by positivity)]
  have e : (|a| + |b|) ^ 2 * (1 / 2 / Real.sqrt L) * (9 * L) =
      (|a| + |b|) ^ 2 * (9 / 2 * (L / Real.sqrt L)) := by ring
  rw [e]
  have hLL' : 1 ≤ 9 / 2 * (L / Real.sqrt L) := by
    have : 1 ≤ L / Real.sqrt L := by
      rw [le_div_iff₀ hsqpos]
      linarith
    linarith
  calc a ^ 2 + b ^ 2 ≤ (|a| + |b|) ^ 2 := hqq
    _ = (|a| + |b|) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (|a| + |b|) ^ 2 * (9 / 2 * (L / Real.sqrt L)) :=
        mul_le_mul_of_nonneg_left hLL' (sq_nonneg _)

/-- **Lower bound for `-μ` with error** (planar form of Armstrong and Dario, Lemma 4.7). -/
theorem planarMu_add_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    planarMu ω U q + (q 0 ^ 2 + q 1 ^ 2) / 18 ≤
      (|q 0| + |q 1|) ^ 2 * (162001 * (∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4) /
        ((U.toIntegerCube.size : ℝ) * Real.sqrt (U.toIntegerCube.size : ℝ)) +
        1 / Real.sqrt (U.toIntegerCube.size : ℝ)) := by
  set Q₁ := |q 0| + |q 1| with hQ₁
  set L : ℝ := (U.toIntegerCube.size : ℝ) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact_mod_cast (show 1 ≤ U.toIntegerCube.size from by
      change 1 ≤ 3 ^ U.scale
      exact Nat.one_le_pow _ _ (by norm_num))
  have hLvol : L * L = U.volume := by
    rw [hL]
    change ((3 ^ U.scale : ℕ) : ℝ) * ((3 ^ U.scale : ℕ) : ℝ) = (9 : ℝ) ^ U.scale
    push_cast
    rw [← mul_pow]
    norm_num
  set S4 := ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun k _ => by
    have := one_le_partSide (ω := ω) k.2.2
    positivity
  have hmu0 := planarMu_nonpos hP hU q
  rcases (show (0 : ℝ) ≤ Q₁ by positivity).eq_or_lt with hQ0 | hQpos
  · have h0 : |q 0| = 0 ∧ |q 1| = 0 := by
      constructor <;> linarith [abs_nonneg (q 0), abs_nonneg (q 1)]
    have hq0 : q 0 = 0 := abs_eq_zero.1 h0.1
    have hq1 : q 1 = 0 := abs_eq_zero.1 h0.2
    rw [← hQ0, hq0, hq1]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_div,
      zero_mul]
    exact hmu0
  obtain ⟨v, hv, hvar, hle⟩ := planarMu_le_neg_sq hP hU q
  set p : Fin 2 → ℝ := fun i => q i / 9 with hp
  have hP₁ : |p 0| + |p 1| = Q₁ / 9 := by
    simp only [hp, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 9)]
    ring
  have hB : clusterForm ω U v v ≤ 9 / 2 * (Q₁ / 9) ^ 2 * (L * L) := by
    have h1 := clusterForm_le_of_variation p hv hvar
    have h2 := planarNu_le (ω := ω) (U := U) p
    rw [hP₁] at h2
    rw [hLvol]
    have hvol := U.volume_pos
    calc clusterForm ω U v v ≤ 2 * U.volume * planarNu ω U p := h1
      _ ≤ 2 * U.volume * (9 / 4 * (Q₁ / 9) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 9 / 2 * (Q₁ / 9) ^ 2 * U.volume := by ring
  set t := 1 / (Q₁ / 9 * Real.sqrt L) with ht
  have htpos : 0 < t := by positivity
  have hbe := boundaryError_le p v htpos
  rw [hP₁] at hbe
  have hW := sum_sq_boundaryWeight_le hP hU
  have hfaces : ∑ i, (∑ x ∈ U.toIntegerCube.upperFace i, (3 : ℝ) ^ (planarPartCube ω x).scale +
      ∑ x ∈ U.toIntegerCube.lowerFace i, (3 : ℝ) ^ (planarPartCube ω x).scale) ≤ S4 := by
    have := sum_boundaryIndex U (fun x => (3 : ℝ) ^ (planarPartCube ω x).scale)
    rw [← this]
    exact sum_boundaryIndex_partSide_le U
  have hBE : boundaryError ω U p v ≤
      (9 * (324000 * S4) / t + t * (2 * (9 / 2 * (Q₁ / 9) ^ 2 * (L * L)))) / 2 +
        Q₁ / 9 * S4 := by
    have h1 : 9 * (∑ x : ↥(clusterVertices ω U), boundaryWeight ω U x.1 ^ 2) / t ≤
        9 * (324000 * S4) / t :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by norm_num)) htpos.le
    have h2 : t * (2 * clusterForm ω U v v) ≤ t * (2 * (9 / 2 * (Q₁ / 9) ^ 2 * (L * L))) :=
      mul_le_mul_of_nonneg_left (by linarith) htpos.le
    have h3 := mul_le_mul_of_nonneg_left hfaces (show (0 : ℝ) ≤ Q₁ / 9 by positivity)
    linarith
  have halg := boundary_algebra hQpos hL1 hS4 hBE
  rw [← hLvol] at hle
  have hq2 : (q 0 ^ 2 + q 1 ^ 2) / 9 / L ≤ Q₁ ^ 2 * (1 / 2 / Real.sqrt L) :=
    sq_sum_div_le_aux (q 0) (q 1) L hL1
  have hsplit : Q₁ ^ 2 * (162001 * S4 / (L * Real.sqrt L) + 1 / Real.sqrt L) =
      Q₁ ^ 2 * (162001 * S4 / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) +
        Q₁ ^ 2 * (1 / 2 / Real.sqrt L) := by ring
  rw [hsplit]
  linarith

end Rigidity.Percolation
