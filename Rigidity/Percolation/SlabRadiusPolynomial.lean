import Rigidity.Percolation.SlabExponentialAbsorption
import Rigidity.Percolation.IntegerCubeCoalescenceScales

/-!
# Polynomial prefactors in cube estimates

The number of roots and possible slab positions in a cube is bounded by a
fixed polynomial in its side length.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External Filter
open scoped Topology

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

/-- When cube size is at most a fixed multiple of the radius, the conditional
crossing failure bound has a polynomial prefactor in the radius and a linear
exponential rate. -/
theorem IntegerCube.measureReal_no_crossing_connecting_radius_le_poly_exp {d : ℕ}
    (hd : 0 < d) (Q : IntegerCube d) (j i : Fin d) (hij : i ≠ j)
    (width radius K : ℕ) (hwidth : 0 < width) (hQ : 1 ≤ Q.size)
    (hradius : 4 * (10 * d * width) ≤ radius)
    (hfit : radius < 10 * d * Q.size) (hcomparable : Q.size ≤ K * radius)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ))
    (hprob : ∀ t : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
      ∀ x ∈ Q.slab t width k, ∀ y ∈ Q.slab t width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab t width k)).Reachable x y}) :
    (latticeBondLaw d p).real {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
      (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
      (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
        (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
      (((d : ℝ) + 2) * (K : ℝ) ^ (2 * d + 1)) * (radius : ℝ) ^ (2 * d + 1) *
        Real.exp (-((c / (2 * ((10 * d * width : ℕ) : ℝ))) * radius)) := by
  have hD : 0 < 10 * d * width := by positivity
  have hr : 10 * d * width ≤ radius := by omega
  have hbound := Q.measureReal_no_crossing_connecting_radius_le_scaled_exp hd j i hij
    width radius hwidth hr hfit p ρ c hρ hρ₁ hc hcρ hcroot hctwo hprob
  have hpre := Q.slab_crossing_prefactor_le j hQ
  have hexp := exp_neg_rounded_slab_count_le (10 * d * width) radius hD hradius hc.le
  have hcomp : (Q.size : ℝ) ≤ (K : ℝ) * radius := by exact_mod_cast hcomparable
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ Q.size by positivity) hcomp (2 * d + 1)
  calc
    _ ≤ (1 + ((Q.lowerFace j).card : ℝ) +
        ((d * Q.size : ℕ) : ℝ) * (Q.vertices.card : ℝ) ^ 2) *
        Real.exp (-(c * ((radius / (10 * d * width) - 1 : ℕ) : ℝ))) := hbound
    _ ≤ (((d : ℝ) + 2) * (Q.size : ℝ) ^ (2 * d + 1)) *
        Real.exp (-((c / (2 * ((10 * d * width : ℕ) : ℝ))) * radius)) :=
      mul_le_mul hpre hexp (Real.exp_nonneg _) (by positivity)
    _ ≤ (((d : ℝ) + 2) * ((K : ℝ) * radius) ^ (2 * d + 1)) *
        Real.exp (-((c / (2 * ((10 * d * width : ℕ) : ℝ))) * radius)) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Uniform full-slab two-point estimates give an eventually exponential
radius-crossing bound, uniformly over cubes whose side is comparable to the
radius. -/
theorem eventually_no_crossing_connecting_radius_le_exp {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width K : ℕ) (hwidth : 0 < width)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ)) :
    ∀ᶠ radius : ℕ in atTop, ∀ Q : IntegerCube d, 1 ≤ Q.size →
      radius < 10 * d * Q.size → Q.size ≤ K * radius →
      (∀ t : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
        ∀ x ∈ Q.slab t width k, ∀ y ∈ Q.slab t width k,
          ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab t width k)).Reachable x y}) →
      (latticeBondLaw d p).real {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
        (fun t => ↑(Q.lowerFace t)) (fun t => ↑(Q.upperFace t))
        (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
          (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
        Real.exp (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) * radius)) := by
  have hD : 0 < (2 * ((10 * d * width : ℕ) : ℝ)) := by positivity
  have ha : 0 < c / (2 * ((10 * d * width : ℕ) : ℝ)) := div_pos hc hD
  have hA : 0 ≤ ((d : ℝ) + 2) * (K : ℝ) ^ (2 * d + 1) := by positivity
  have hsmall := eventually_mul_pow_mul_exp_le
    (((d : ℝ) + 2) * (K : ℝ) ^ (2 * d + 1))
    (c / (2 * ((10 * d * width : ℕ) : ℝ))) hA ha (2 * d + 1)
  have hnaturals := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
    atTop atTop).eventually hsmall
  filter_upwards [hnaturals, eventually_ge_atTop (4 * (10 * d * width))] with radius hsmall' hradius
  intro Q hQ hfit hcomparable hprob
  exact (Q.measureReal_no_crossing_connecting_radius_le_poly_exp hd j i hij width radius K
    hwidth hQ hradius hfit hcomparable p ρ c hρ hρ₁ hc hcρ hcroot hctwo hprob).trans hsmall'

end Rigidity.Percolation
