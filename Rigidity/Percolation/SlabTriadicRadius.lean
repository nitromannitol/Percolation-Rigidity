import Rigidity.Percolation.SlabRadiusPolynomial
import Rigidity.Percolation.TriadicCoalescenceRadius

/-!
# Slab bounds at compatible cube scales

Uniform slab connectivity supplies radius-crossing estimates for integer
cubes whose side and radius scales grow linearly together.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External Filter
open scoped Topology

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

end Rigidity.Percolation
