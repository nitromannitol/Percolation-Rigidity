import Rigidity.Proofs.Percolation.PlanarLimitCubes
import Rigidity.Proofs.Percolation.PlanarNuLowerBound

/-!
# The convex duality inequality between the limits of `-μ` and `ν`

On resolved cubes, the comparison of `μ` and `ν` with boundary errors (planar form of Armstrong
and Dario, Corollary 4.6) gives, for all slopes `q` and `ξ ≠ 0`,

`q · ξ ≤ ν(U, ξ) - μ(U, q) + |q|₁ |ξ|₁ (1 / L + 9 (162001 S / (L √L) + 1 / (2 √L)))`,

with `L` the side of `U` and `S` the sum of the fourth powers of the partition sides at the
boundary. Taking expectations and letting the scale tend to infinity,

`q · ξ ≤ lim E[-μ(□_m, q)] + lim E[ν(□_m, ξ)] = lim E[-μ(□_m, q)] + (1/2) ξ · ā ξ`.

This is one of the two inequalities identifying the limit of `-μ` as `(1/2) q · ā⁻¹ q`, the
convex dual of the limit of `ν` (Armstrong and Dario, Section 5, after Definition 5.1, in
dimension two); the other one is the content of Section 5.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

theorem abs_sum_mul_le (q ξ : Fin 2 → ℝ) :
    |∑ i, q i * ξ i| ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) := by
  rw [Fin.sum_univ_two]
  calc |q 0 * ξ 0 + q 1 * ξ 1| ≤ |q 0 * ξ 0| + |q 1 * ξ 1| := abs_add_le _ _
    _ = |q 0| * |ξ 0| + |q 1| * |ξ 1| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by
        nlinarith [mul_nonneg (abs_nonneg (q 0)) (abs_nonneg (ξ 1)),
          mul_nonneg (abs_nonneg (q 1)) (abs_nonneg (ξ 0))]

/-- **Comparison of `μ` and `ν` for arbitrary slopes.** On resolved cubes of side `L` and for
`ξ ≠ 0`, `q · ξ ≤ -μ(U, q) + ν(U, ξ) + X (1 / L + 9 / (2 √L)) + 9 · 162001 X S / (L √L)` with
`X = |q|₁ |ξ|₁` and `S` the sum of the fourth powers of the partition sides at the boundary. -/
theorem sum_mul_le_planarNu_sub_planarMu (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (ξ q : Fin 2 → ℝ) (hξ : 0 < |ξ 0| + |ξ 1|) :
    ∑ i, q i * ξ i ≤ -planarMu ω U q + planarNu ω U ξ +
      (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (1 / (3 : ℝ) ^ U.scale +
        9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale))) +
      9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
        ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale)) *
        ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 := by
  obtain ⟨v, hv, hvar, hle⟩ := planarMu_le_planarNu_sub hP hU ξ q
  have hb := mul_boundaryError_div_le hP hU ξ hv hvar
  have hvol := U.volume_pos
  have habs := abs_sum_mul_le q ξ
  have hsize : ((U.toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ U.scale := by
    rw [show U.toIntegerCube.size = 3 ^ U.scale from rfl]
    push_cast
    ring
  rw [hsize] at hle hb
  set Q := |q 0| + |q 1| with hQ
  set P₁ := |ξ 0| + |ξ 1| with hP₁
  set L : ℝ := (3 : ℝ) ^ U.scale with hL
  set S := ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 with hS
  have hQ0 : 0 ≤ Q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hP0 : P₁ ≠ 0 := hξ.ne'
  have hL0 : 0 < L := pow_pos (by norm_num) _
  have hBE : Q * boundaryError ω U ξ v / U.volume ≤
      9 * Q * P₁ * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) := by
    have e : Q * boundaryError ω U ξ v / U.volume =
        Q / P₁ * (P₁ * boundaryError ω U ξ v / U.volume) := by
      rw [show Q / P₁ * (P₁ * boundaryError ω U ξ v / U.volume) =
        Q * boundaryError ω U ξ v / U.volume * (P₁ / P₁) by ring, div_self hP0, mul_one]
    rw [e]
    calc Q / P₁ * (P₁ * boundaryError ω U ξ v / U.volume) ≤
          Q / P₁ * (9 * P₁ ^ 2 * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left hb (div_nonneg hQ0 hξ.le)
      _ = 9 * Q * P₁ * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) * (P₁ / P₁) := by
          ring
      _ = _ := by rw [div_self hP0, mul_one]
  have hdiv : |∑ i, q i * ξ i| / L ≤ Q * P₁ * (1 / L) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right habs (by positivity)
  have e : Q * P₁ * (1 / L + 9 * (1 / 2 / Real.sqrt L)) +
      9 * 162001 * (Q * P₁) / (L * Real.sqrt L) * S =
      Q * P₁ * (1 / L) + 9 * Q * P₁ * (162001 * S / (L * Real.sqrt L) + 1 / 2 / Real.sqrt L) := by
    ring
  linarith

/-- The pointwise form of the comparison, with the boundary sum bounded by reach sums and an
unresolved cube controlled by the sixth powers of the partition sides. -/
theorem ofReal_sum_mul_le_of_partitionEvent (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (ξ q : Fin 2 → ℝ) (hξ : 0 < |ξ 0| + |ξ 1|) :
    ENNReal.ofReal (∑ i, q i * ξ i) ≤
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (-planarMu ω U q) else 0) +
      (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarNu ω U ξ) else 0) +
      (ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (1 / (3 : ℝ) ^ U.scale +
          9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale)))) +
        ENNReal.ofReal (9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
          ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
          ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2) +
      ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) *
        ∑ z ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z := by
  have hX0 : 0 ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hL0 : (0 : ℝ) < 3 ^ U.scale := pow_pos (by norm_num) _
  have hsL0 : 0 < Real.sqrt ((3 : ℝ) ^ U.scale) := Real.sqrt_pos.2 hL0
  by_cases hres : PlanarResolved ω U
  · rw [if_pos ⟨hP, hres⟩, if_pos ⟨hP, hres⟩]
    refine le_add_right ?_
    have h := sum_mul_le_planarNu_sub_planarMu hP hres ξ q hξ
    have hS0 : 0 ≤ ∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4 :=
      Finset.sum_nonneg fun k _ => pow_nonneg (le_trans zero_le_one (one_le_partSide k.2.2)) _
    have hS : ENNReal.ofReal (∑ k ∈ boundaryIndex U, partSide ω k.2.2 ^ 4) ≤
        ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 := by
      rw [ENNReal.ofReal_sum_of_nonneg fun k _ =>
        pow_nonneg (le_trans zero_le_one (one_le_partSide k.2.2)) _]
      exact Finset.sum_le_sum fun k _ => ofReal_partSide_pow_le hP k.2.2 3
    have hμ0 : 0 ≤ -planarMu ω U q := neg_nonneg.2 (planarMu_nonpos hP hres q)
    have hν0 : 0 ≤ planarNu ω U ξ := planarNu_nonneg ξ
    have hT0 : 0 ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (1 / (3 : ℝ) ^ U.scale +
        9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale))) := mul_nonneg hX0 (by positivity)
    have hb0 : 0 ≤ 9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
        ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale)) :=
      div_nonneg (mul_nonneg (by norm_num) hX0) (mul_nonneg hL0.le hsL0.le)
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hμ0 hν0) hT0) (mul_nonneg hb0 hS0),
      ENNReal.ofReal_add (add_nonneg hμ0 hν0) hT0, ENNReal.ofReal_add hμ0 hν0,
      ENNReal.ofReal_mul hb0, add_assoc (ENNReal.ofReal (-planarMu ω U q) +
        ENNReal.ofReal (planarNu ω U ξ))]
    gcongr
  · rw [if_neg fun h => hres h.2, if_neg fun h => hres h.2, zero_add, zero_add]
    refine le_add_left ?_
    have h1 := one_le_sum_of_not_resolved (ω := ω) hres
    calc ENNReal.ofReal (∑ i, q i * ξ i)
        ≤ ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) * 1 := by
          rw [mul_one]
          exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (abs_sum_mul_le q ξ))
      _ ≤ ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) *
          ENNReal.ofReal (∑ z ∈ U.toIntegerCube.vertices,
            (partSide ω z / 3 ^ (U.scale + 1)) ^ 6) := by
          gcongr
          exact ENNReal.one_le_ofReal.2 h1
      _ ≤ _ := by
          gcongr
          exact ofReal_sum_partSide_div_pow_le hP _ U.scale

/-- The numerical form of the error terms. -/
theorem duality_error_le {X L : ℝ} (hX : 0 ≤ X) (hL : 1 ≤ L) {m : ℕ} (hm : L = 3 ^ m)
    (C₄ C₆ : ℝ≥0∞) :
    ENNReal.ofReal (X * (1 / L + 9 * (1 / 2 / Real.sqrt L))) +
        ENNReal.ofReal (9 * 162001 * X / (L * Real.sqrt L)) * (ENNReal.ofReal (4 * L) * C₄) +
      ENNReal.ofReal X * (ENNReal.ofReal ((9 : ℝ) ^ m) *
        (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (m + 1))) * C₆)) ≤
      (10 + 9 * 162001 * 4 * C₄ + C₆) * ENNReal.ofReal (X / Real.sqrt L) := by
  have hL0 : 0 < L := by linarith
  have hsL0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsLL : Real.sqrt L ≤ L := by
    have := Real.sq_sqrt hL0.le
    nlinarith [Real.sqrt_nonneg L]
  have k1 : ENNReal.ofReal (X * (1 / L + 9 * (1 / 2 / Real.sqrt L))) ≤
      10 * ENNReal.ofReal (X / Real.sqrt L) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 / L ≤ 1 / Real.sqrt L := one_div_le_one_div_of_le hsL0 hsLL
    have h2 : (0 : ℝ) < 1 / Real.sqrt L := by positivity
    have h3 : 9 * (1 / 2 / Real.sqrt L) = 9 / 2 * (1 / Real.sqrt L) := by ring
    calc X * (1 / L + 9 * (1 / 2 / Real.sqrt L)) ≤ X * (10 * (1 / Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left (by rw [h3]; linarith) hX
      _ = 10 * (X / Real.sqrt L) := by ring
  have k2 : ENNReal.ofReal (9 * 162001 * X / (L * Real.sqrt L)) * (ENNReal.ofReal (4 * L) * C₄) =
      9 * 162001 * 4 * C₄ * ENNReal.ofReal (X / Real.sqrt L) := by
    have hb0 : 0 ≤ 9 * 162001 * X / (L * Real.sqrt L) :=
      div_nonneg (mul_nonneg (by norm_num) hX) (mul_nonneg hL0.le (Real.sqrt_nonneg _))
    rw [← mul_assoc, ← ENNReal.ofReal_mul hb0]
    have e : 9 * 162001 * X / (L * Real.sqrt L) * (4 * L) =
        (9 * 162001 * 4) * (X / Real.sqrt L) := by
      calc 9 * 162001 * X / (L * Real.sqrt L) * (4 * L) =
          (9 * 162001 * 4) * (X / Real.sqrt L) * (L / L) := by ring
        _ = _ := by rw [div_self hL0.ne', mul_one]
    rw [e, ENNReal.ofReal_mul (by norm_num),
      show ((9 * 162001 * 4 : ℝ)) = ((9 * 162001 * 4 : ℕ) : ℝ) by norm_num,
      ENNReal.ofReal_natCast]
    push_cast
    ring
  have k3 : ENNReal.ofReal X * (ENNReal.ofReal ((9 : ℝ) ^ m) *
      (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (m + 1))) * C₆)) ≤
      C₆ * ENNReal.ofReal (X / Real.sqrt L) := by
    rw [← mul_assoc (ENNReal.ofReal ((9 : ℝ) ^ m)), ← ENNReal.ofReal_mul (by positivity),
      ← mul_assoc, ← ENNReal.ofReal_mul hX, mul_comm C₆]
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
    have h := nine_pow_div_three_pow_le m
    rw [← hm] at h
    rw [mul_one_div, div_eq_mul_one_div X]
    exact mul_le_mul_of_nonneg_left h hX
  calc _ ≤ 10 * ENNReal.ofReal (X / Real.sqrt L) +
        9 * 162001 * 4 * C₄ * ENNReal.ofReal (X / Real.sqrt L) +
        C₆ * ENNReal.ofReal (X / Real.sqrt L) := by
        rw [k2]
        gcongr
    _ = _ := by ring

/-- **Comparison in expectation.** For `ξ ≠ 0`,
`q · ξ ≤ E[-μ(U, q); P, U res] + E[ν(U, ξ); P, U res] + C |q|₁ |ξ|₁ / √L`. -/
theorem exists_ofReal_sum_mul_le_lintegral {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (ξ q : Fin 2 → ℝ), 0 < |ξ 0| + |ξ 1| →
      ENNReal.ofReal (∑ i, q i * ξ i) ≤
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) +
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNu ω U ξ) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) /
          Real.sqrt ((3 : ℝ) ^ U.scale)) := by
  obtain ⟨C₄, hC₄, h4⟩ := exists_lintegral_tsum_ninefold_le hpc 4
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  refine ⟨10 + 9 * 162001 * 4 * C₄ + C₆, by finiteness, fun U ξ q hξ => ?_⟩
  have hX0 : 0 ≤ (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) :=
    mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hsize : ((U.toIntegerCube.size : ℕ) : ℝ) = (3 : ℝ) ^ U.scale := by
    rw [show U.toIntegerCube.size = 3 ^ U.scale from rfl]
    push_cast
    ring
  have hm4 : Measurable fun ω : Configuration 2 =>
      ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (1 / (3 : ℝ) ^ U.scale +
          9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale)))) +
        ENNReal.ofReal (9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
          ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
          ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2 :=
    measurable_const.add ((Finset.measurable_sum _
      fun (k : Fin 2 × Bool × Vertex 2) _ => measurable_reachSum 4 k.2.2).const_mul _)
  have hm6 : Measurable fun ω : Configuration 2 =>
      ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) *
        ∑ z ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z :=
    (Finset.measurable_sum _ fun z _ => (measurable_reachSum 6 z).const_mul _).const_mul _
  have hcardB : ((boundaryIndex U).card : ℝ≥0∞) ≤ ENNReal.ofReal (4 * (3 : ℝ) ^ U.scale) := by
    rw [← ENNReal.ofReal_natCast, ← hsize]
    exact ENNReal.ofReal_le_ofReal (card_boundaryIndex_le U)
  have e4 : ∫⁻ ω, (ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (1 / (3 : ℝ) ^ U.scale +
          9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale)))) +
        ENNReal.ofReal (9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
          ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
          ∑ k ∈ boundaryIndex U, reachSum ω 4 k.2.2) ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) * (1 / (3 : ℝ) ^ U.scale +
          9 * (1 / 2 / Real.sqrt ((3 : ℝ) ^ U.scale)))) +
        ENNReal.ofReal (9 * 162001 * ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) /
          ((3 : ℝ) ^ U.scale * Real.sqrt ((3 : ℝ) ^ U.scale))) *
          (ENNReal.ofReal (4 * (3 : ℝ) ^ U.scale) * C₄) := by
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum _ fun k _ => measurable_reachSum 4 k.2.2]
    gcongr
    calc ∑ k ∈ boundaryIndex U, ∫⁻ ω, reachSum ω 4 k.2.2 ∂(latticeBondLaw 2 p)
        ≤ ∑ _k ∈ boundaryIndex U, C₄ := Finset.sum_le_sum fun k _ => h4 k.2.2
      _ = ((boundaryIndex U).card : ℝ≥0∞) * C₄ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardB zero_le
  have e6 : ∫⁻ ω, ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) *
        ∑ z ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z
        ∂(latticeBondLaw 2 p) ≤
      ENNReal.ofReal ((|q 0| + |q 1|) * (|ξ 0| + |ξ 1|)) * (ENNReal.ofReal ((9 : ℝ) ^ U.scale) *
        (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * C₆)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum _ fun z _ => (measurable_reachSum 6 z).const_mul _]
    gcongr
    calc ∑ z ∈ U.toIntegerCube.vertices, ∫⁻ ω,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * reachSum ω 6 z
          ∂(latticeBondLaw 2 p)
        ≤ ∑ _z ∈ U.toIntegerCube.vertices,
            ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (U.scale + 1))) * C₆ :=
          Finset.sum_le_sum fun z _ => by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact mul_le_mul_of_nonneg_left (h6 z) zero_le
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices U]; rfl
  have herr := duality_error_le hX0 (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 3 ^ U.scale) rfl C₄ C₆
  calc ENNReal.ofReal (∑ i, q i * ξ i)
      = ∫⁻ _ω, ENNReal.ofReal (∑ i, q i * ξ i) ∂(latticeBondLaw 2 p) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ _ := lintegral_mono_ae (by
        filter_upwards [ae_planarPartitionEvent hpc] with ω hP
        exact ofReal_sum_mul_le_of_partitionEvent hP U ξ q hξ)
    _ = _ := by
        rw [lintegral_add_right _ hm6, lintegral_add_right _ hm4,
          lintegral_add_left (measurable_planarMu_indicator U q)]
    _ ≤ _ := add_le_add (add_le_add le_rfl e4) e6
    _ ≤ _ := by
        rw [add_assoc]
        exact add_le_add le_rfl herr

/-- **Duality of the limits** (Armstrong and Dario, Section 5, in dimension two). For all slopes
`q` and `ξ`, `q · ξ ≤ lim E[-μ(□_m, q)] + lim E[ν(□_m, ξ)]`. -/
theorem sum_mul_le_planarMuLimit_add_planarNuLimit {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (ξ q : Fin 2 → ℝ) :
    ∑ i, q i * ξ i ≤ planarMuLimit p q + planarNuLimit p ξ := by
  have hμ0 := ((exists_planarMuLimit_bounds hpc).choose_spec.2 q).1
  have hν0 : 0 ≤ planarNuLimit p ξ :=
    ge_of_tendsto' (tendsto_planarNuLimit hpc ξ) fun m => ENNReal.toReal_nonneg
  by_cases hξ : 0 < |ξ 0| + |ξ 1|
  · obtain ⟨C, hC, h⟩ := exists_ofReal_sum_mul_le_lintegral hpc
    obtain ⟨C₂, hC₂, hup⟩ := exists_lintegral_neg_planarMu_le hpc
    set X := (|q 0| + |q 1|) * (|ξ 0| + |ξ 1|) with hX
    have hX0 : 0 ≤ X := by positivity
    have hfinμ : ∀ m : ℕ, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        ENNReal.ofReal (-planarMu ω ⟨m, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
      fun m => ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₂ ENNReal.ofReal_ne_top) (hup _ q)
    have hfinν : ∀ m : ℕ, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
        ENNReal.ofReal (planarNu ω ⟨m, 0⟩ ξ) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
      fun m => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p _ ξ)
    have hm : ∀ m : ℕ, ∑ i, q i * ξ i ≤ planarMuMean p m q + planarNuMean p m ξ +
        C.toReal * (X * (1 / Real.sqrt ((3 : ℝ) ^ m))) := by
      intro m
      have h1 := h ⟨m, 0⟩ ξ q hξ
      rw [← hX] at h1
      have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
        ⟨hfinμ m, hfinν m⟩, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top⟩) h1
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfinμ m, hfinν m⟩)
          (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top),
        ENNReal.toReal_add (hfinμ m) (hfinν m), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (div_nonneg hX0 (Real.sqrt_nonneg _))] at h2
      calc ∑ i, q i * ξ i ≤ (ENNReal.ofReal (∑ i, q i * ξ i)).toReal := by
            rw [ENNReal.toReal_ofReal']
            exact le_max_left _ _
        _ ≤ _ := h2
        _ = _ := by
            unfold planarMuMean planarNuMean
            ring
    have hr : Tendsto (fun m : ℕ => C.toReal * (X * (1 / Real.sqrt ((3 : ℝ) ^ m)))) atTop
        (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_one_div_sqrt_three_pow.const_mul X).const_mul C.toReal
    have := ge_of_tendsto' (((tendsto_planarMuLimit hpc q).add (tendsto_planarNuLimit hpc ξ)).add
      hr) hm
    simpa only [add_zero] using this
  · have h0 : ξ 0 = 0 ∧ ξ 1 = 0 := by
      have a0 := abs_nonneg (ξ 0)
      have a1 := abs_nonneg (ξ 1)
      constructor <;> apply abs_eq_zero.1 <;> linarith
    rw [Fin.sum_univ_two, h0.1, h0.2, mul_zero, mul_zero, add_zero]
    linarith

/-- **The limit of `-μ` dominates the convex dual of `(1/2) ξ · ā ξ`.** -/
theorem planarMuLimit_ge_sub_planarAhom {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (ξ q : Fin 2 → ℝ) :
    ∑ i, q i * ξ i - 1 / 2 * ∑ i, ∑ j, ξ i * planarAhom p i j * ξ j ≤ planarMuLimit p q := by
  have h := sum_mul_le_planarMuLimit_add_planarNuLimit hpc ξ q
  rw [planarNuLimit_eq_planarAhom hpc] at h
  linarith

end Rigidity.Percolation
