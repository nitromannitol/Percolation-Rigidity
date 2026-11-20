import Rigidity.Percolation.SlabExponentialAbsorption
import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Polynomial prefactors in cube estimates

The number of roots and possible slab positions in a cube is bounded by a
fixed polynomial in its side length.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- The combinatorial prefactor in the slab crossing estimate is bounded by a
power of the cube's side length. -/
theorem IntegerCube.slab_crossing_prefactor_le {d : ℕ} (Q : IntegerCube d)
    (j : Fin d) (hsize : 1 ≤ Q.size) :
    1 + ((Q.lowerFace j).card : ℝ) +
      ((d * Q.size : ℕ) : ℝ) * (Q.vertices.card : ℝ) ^ 2 ≤
      ((d : ℝ) + 2) * (Q.size : ℝ) ^ (2 * d + 1) := by
  have hf : (Q.lowerFace j).card ≤ Q.vertices.card := by
    exact Finset.card_filter_le _ _
  have hf' : ((Q.lowerFace j).card : ℝ) ≤ (Q.size : ℝ) ^ d := by
    rw [← Nat.cast_pow, ← Q.card_vertices]
    exact_mod_cast hf
  have hs : (1 : ℝ) ≤ Q.size := by exact_mod_cast hsize
  have hpow : (Q.size : ℝ) ^ d ≤ (Q.size : ℝ) ^ (2 * d + 1) :=
    pow_le_pow_right₀ hs (by omega)
  have hone : (1 : ℝ) ≤ (Q.size : ℝ) ^ (2 * d + 1) := one_le_pow₀ hs
  have hidentity : (Q.size : ℝ) * ((Q.size : ℝ) ^ d) ^ 2 =
      (Q.size : ℝ) ^ (2 * d + 1) := by
    rw [pow_add, pow_mul]
    ring
  rw [Q.card_vertices]
  push_cast
  rw [← hidentity]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sub_nonneg.mpr hpow)]

/-- Beyond four slab units, the rounded slab count is at least half of the
unrounded radius-to-width ratio. -/
theorem rounded_slab_count_lower_bound (D radius : ℕ) (hD : 0 < D)
    (hradius : 4 * D ≤ radius) :
    radius ≤ 2 * D * (radius / D - 1) := by
  let K := radius / D
  have hK : 4 ≤ K := (Nat.le_div_iff_mul_le hD).2 hradius
  have hdiv := Nat.mod_add_div radius D
  have hmod := Nat.mod_lt radius hD
  have hupper : radius ≤ (K + 1) * D := by
    dsimp only [K]
    nlinarith
  have hk : K + 1 ≤ 2 * (K - 1) := by omega
  calc
    radius ≤ (K + 1) * D := hupper
    _ ≤ (2 * (K - 1)) * D := Nat.mul_le_mul_right D hk
    _ = 2 * D * (radius / D - 1) := by dsimp only [K]; ring

/-- The rounded exponential slab factor has a linear rate in the radius. -/
theorem exp_neg_rounded_slab_count_le (D radius : ℕ) (hD : 0 < D)
    (hradius : 4 * D ≤ radius) {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-(c * ((radius / D - 1 : ℕ) : ℝ))) ≤
      Real.exp (-((c / (2 * (D : ℝ))) * radius)) := by
  have hbound : (radius : ℝ) ≤ (2 * (D : ℝ)) * ((radius / D - 1 : ℕ) : ℝ) := by
    exact_mod_cast rounded_slab_count_lower_bound D radius hD hradius
  have hD' : 0 < 2 * (D : ℝ) := by exact_mod_cast (show 0 < 2 * D by omega)
  have hratio : (radius : ℝ) / (2 * D) ≤ ((radius / D - 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hD').2 (by simpa only [mul_comm] using hbound)
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hratio hc
  have heq : c / (2 * (D : ℝ)) * radius = c * ((radius : ℝ) / (2 * D)) := by ring
  rw [heq]
  linarith

end Rigidity.Percolation
