import Rigidity.Percolation.SlabRadiusPolynomial
import Rigidity.Percolation.TriadicCoalescenceRadius

/-!
# Slab bounds at compatible cube scales

Uniform slab connectivity supplies radius-crossing estimates for integer
cubes whose side and radius scales grow linearly together.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External Filter
open scoped Topology ENNReal

/-- At linearly related cube and radius scales, uniform full-slab two-point
bounds imply an eventual exponential radius-crossing bound. -/
theorem eventually_scaled_radius_crossing_le_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width sideScale radiusScale : ℕ)
    (hwidth : 0 < width) (hradius : 0 < radiusScale)
    (hscales : radiusScale ≤ 10 * d * sideScale)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ)) :
    ∀ᶠ t : ℕ in atTop, ∀ Q : IntegerCube d, Q.size = sideScale * t + 1 →
      (∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ Q.size →
        ∀ x ∈ Q.slab a width k, ∀ y ∈ Q.slab a width k,
          ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (Q.slab a width k)).Reachable x y}) →
      (latticeBondLaw d p) {ω | ¬ HasCrossingComponentConnectingPaths ω Q.vertices
        (fun a => ↑(Q.lowerFace a)) (fun a => ↑(Q.upperFace a))
        (fun n γ => ∀ z : Vertex d, ∃ b : Fin (n + 1),
          ((radiusScale * t : ℕ) : ℤ) < 10 * ∑ k, |γ b k - z k|)} ≤
        ENNReal.ofReal (Real.exp (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) *
          ((radiusScale * t : ℕ) : ℝ)))) := by
  have hscale : Tendsto (fun t : ℕ => radiusScale * t) atTop atTop := by
    apply tendsto_atTop_mono (fun t => ?_) tendsto_id
    change t ≤ radiusScale * t
    nlinarith
  have hmain := eventually_no_crossing_connecting_radius_le_exp hd j i hij width (sideScale + 1)
    hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo
  filter_upwards [hscale.eventually hmain, eventually_ge_atTop 1] with t ht htpos
  intro Q hQ hprob
  have hQpos : 1 ≤ Q.size := by omega
  have hfit : radiusScale * t < 10 * d * Q.size := by
    rw [hQ]
    have hmul := Nat.mul_le_mul_right t hscales
    nlinarith
  have hcomp : Q.size ≤ (sideScale + 1) * (radiusScale * t) := by
    rw [hQ]
    nlinarith
  have hreal := ht Q hQpos hfit hcomp hprob
  rw [← ENNReal.ofReal_toReal (measure_ne_top (latticeBondLaw d p) _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Uniform slab bounds on subcubes supply the two radius estimates required
for the coalescence bound in each triadic test cube. -/
theorem TriadicCube.measure_testCube_not_coalesces_le_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width : ℕ) (hwidth : 0 < width)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ)) :
    ∃ t₀ : ℕ, ∀ (Q : TriadicCube d) {interior : Set (Vertex d)}
      (T : IntegerCube d), T ∈ Q.testCubes interior → 61 ≤ T.size →
      (∀ U : IntegerCube d, (↑U.vertices : Set (Vertex d)) ⊆ T.vertices →
        ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
          ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
            ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}) →
      ∃ t : ℕ, 3 ≤ t ∧ T.size ≤ 20 * t + 20 ∧
        (latticeBondLaw d p) {ω | ¬ LargePathsCoalesce ω (↑T.vertices) Q.largePath} ≤
          (T.size ^ d : ℕ) *
            ((if t < t₀ then 1 else ENNReal.ofReal (Real.exp
              (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) * ((4 * t : ℕ) : ℝ))))) +
             (if t < t₀ then 1 else ENNReal.ofReal (Real.exp
              (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) * ((4 * t : ℕ) : ℝ)))))) := by
  have hscale₈ : 8 ≤ 10 * d * 20 := by nlinarith
  have hscale₄ : 4 ≤ 10 * d * 10 := by nlinarith
  have h₈ := eventually_scaled_radius_crossing_le_of_twoPoint_slabs hd j i hij width 20 8
    hwidth (by omega) hscale₈ p ρ c hρ hρ₁ hc hcρ hcroot hctwo
  have h₄ := eventually_scaled_radius_crossing_le_of_twoPoint_slabs hd j i hij width 10 4
    hwidth (by omega) hscale₄ p ρ c hρ hρ₁ hc hcρ hcroot hctwo
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (h₈.and h₄)
  refine ⟨t₀, ?_⟩
  intro Q interior T hT hsize hslab
  let f : ℕ → ℝ≥0∞ := fun t => if t < t₀ then 1 else ENNReal.ofReal (Real.exp
    (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) * ((4 * t : ℕ) : ℝ))))
  have hrate : 0 ≤ (c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2 := by positivity
  have hone (s : Set (Configuration d)) : (latticeBondLaw d p) s ≤ 1 := by
    simpa using measure_mono (μ := latticeBondLaw d p) (Set.subset_univ s)
  apply Q.measure_testCube_not_coalesces_le_of_radius hd T hT hsize (latticeBondLaw d p) f f
  · intro t _ U hU hUT
    by_cases ht : t < t₀
    · simpa only [f, if_pos ht] using (hone (
        {ω | ¬ HasCrossingComponentConnectingPaths ω U.vertices
          (fun a => ↑(U.lowerFace a)) (fun a => ↑(U.upperFace a))
          (fun n γ => ∀ z : Vertex d, ∃ b : Fin (n + 1),
            8 * (t : ℤ) < 10 * ∑ k, |γ b k - z k|)}))
    · have h₈' := (ht₀ t (by omega)).1 U hU (hslab U hUT)
      have hreal : Real.exp (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) *
          ((8 * t : ℕ) : ℝ))) ≤ Real.exp (-(((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) *
          ((4 * t : ℕ) : ℝ))) := by
        apply Real.exp_le_exp.mpr
        push_cast at hrate ⊢
        nlinarith [show (0 : ℝ) ≤ t by positivity]
      simpa only [f, if_neg ht, Nat.cast_mul, Nat.cast_ofNat] using
        h₈'.trans (ENNReal.ofReal_le_ofReal hreal)
  · intro t _ U hU hUT
    by_cases ht : t < t₀
    · simpa only [f, if_pos ht] using (hone (
        {ω | ¬ HasCrossingComponentConnectingPaths ω U.vertices
          (fun a => ↑(U.lowerFace a)) (fun a => ↑(U.upperFace a))
          (fun n γ => ∀ z : Vertex d, ∃ b : Fin (n + 1),
            4 * (t : ℤ) < 10 * ∑ k, |γ b k - z k|)}))
    · simpa only [f, if_neg ht, Nat.cast_mul, Nat.cast_ofNat] using
        (ht₀ t (by omega)).2 U hU (hslab U hUT)

/-- Uniform full-slab two-point estimates on subcubes yield an exponential
coalescence tail for sufficiently large triadic test cubes. -/
theorem TriadicCube.eventually_measure_testCube_not_coalesces_le_exp_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width : ℕ) (hwidth : 0 < width)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ)) :
    ∃ M : ℕ, ∀ (Q : TriadicCube d) {interior : Set (Vertex d)}
      (T : IntegerCube d), T ∈ Q.testCubes interior → M ≤ T.size →
      (∀ U : IntegerCube d, (↑U.vertices : Set (Vertex d)) ⊆ T.vertices →
        ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
          ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
            ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}) →
      (latticeBondLaw d p) {ω | ¬ LargePathsCoalesce ω (↑T.vertices) Q.largePath} ≤
        ENNReal.ofReal (Real.exp (-((((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) / 20) *
          (T.size : ℝ)))) := by
  obtain ⟨t₀, hcoal⟩ := TriadicCube.measure_testCube_not_coalesces_le_of_twoPoint_slabs
    hd j i hij width hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo
  let rate : ℝ := (c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  have hsmall := eventually_mul_pow_mul_exp_le 2 (rate / 10) (by norm_num) (by positivity) d
  have hsmallNat := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
    atTop atTop).eventually hsmall
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp hsmallNat
  refine ⟨max 61 (max (20 * t₀ + 40) M₀), ?_⟩
  intro Q interior T hT hTsize hslab
  have hsize : 61 ≤ T.size := le_trans (le_max_left _ _) hTsize
  have hcut : 20 * t₀ + 40 ≤ T.size :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTsize
  have hM : M₀ ≤ T.size := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTsize
  obtain ⟨t, ht, hTt, hbound⟩ := hcoal Q T hT hsize hslab
  have ht₀ : ¬ t < t₀ := by omega
  have hsize40 : 40 ≤ T.size := by omega
  have hlin : T.size ≤ 40 * t := by omega
  have hlin' : (T.size : ℝ) ≤ 40 * (t : ℝ) := by exact_mod_cast hlin
  have htail : ENNReal.ofReal (Real.exp (-(rate * ((4 * t : ℕ) : ℝ)))) ≤
      ENNReal.ofReal (Real.exp (-((rate / 10) * T.size))) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hbound' : (latticeBondLaw d p) {ω | ¬ LargePathsCoalesce ω (↑T.vertices) Q.largePath} ≤
      (T.size ^ d : ℕ) *
        (ENNReal.ofReal (Real.exp (-(rate * ((4 * t : ℕ) : ℝ)))) +
         ENNReal.ofReal (Real.exp (-(rate * ((4 * t : ℕ) : ℝ))))) := by
    simpa only [if_neg ht₀, rate] using hbound
  have heq : (T.size ^ d : ℝ≥0∞) *
      (ENNReal.ofReal (Real.exp (-((rate / 10) * T.size))) +
       ENNReal.ofReal (Real.exp (-((rate / 10) * T.size)))) =
      ENNReal.ofReal (2 * (T.size : ℝ) ^ d * Real.exp (-((rate / 10) * T.size))) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (T.size : ℝ) ^ d),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ T.size), ENNReal.ofReal_natCast]
    ring
  calc
    _ ≤ (T.size ^ d : ℕ) *
        (ENNReal.ofReal (Real.exp (-(rate * ((4 * t : ℕ) : ℝ)))) +
         ENNReal.ofReal (Real.exp (-(rate * ((4 * t : ℕ) : ℝ))))) := hbound'
    _ ≤ (T.size ^ d : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (-((rate / 10) * T.size))) +
         ENNReal.ofReal (Real.exp (-((rate / 10) * T.size)))) := by
      rw [Nat.cast_pow]
      gcongr
    _ = ENNReal.ofReal (2 * (T.size : ℝ) ^ d *
        Real.exp (-((rate / 10) * T.size))) := heq
    _ ≤ ENNReal.ofReal (Real.exp (-((rate / 10 / 2) * T.size))) :=
      ENNReal.ofReal_le_ofReal (hM₀ T.size hM)
    _ = _ := by congr 2; dsimp only [rate]; ring

end Rigidity.Percolation
