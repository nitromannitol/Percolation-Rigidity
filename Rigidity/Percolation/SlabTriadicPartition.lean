import Rigidity.Percolation.SlabTriadicOverlap
import Rigidity.Percolation.TriadicLargeScaleDecay

/-!
# Triadic partitions from slab connectivity

Uniform two-point connectivity in complete slabs yields the stopping partition,
its size moment, and its localization bound through the well-connected-cube
construction.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

/-- Uniform full-slab two-point connectivity implies the triadic stopping
partition, exponential size moment, and localization estimate for the rounded
three-quarter interior. -/
theorem triadic_partition_estimates_of_twoPoint_slabs {d : ℕ}
    (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) (width : ℕ) (hwidth : 0 < width)
    (p : unitInterval) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hc : 0 < c)
    (hcρ : c ≤ ρ) (hcroot : c ≤ (p : ℝ) * ρ ^ (2 * d))
    (hctwo : c ≤ (p : ℝ) * ((p : ℝ) * ρ))
    (hslab : ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
      ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}) :
    let G : Configuration d → Set (TriadicCube d) := fun ω =>
      TriadicCube.goodOfWellConnected (TriadicCube.wellConnectedFamily
        (fun Q => Q.threeQuarterCube.vertices) ω)
    (∀ᵐ ω ∂(latticeBondLaw d p), ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ x : Vertex d,
      Integrable (fun ω => Real.exp (TriadicCube.stoppingSize (G ω) x / θ)) (latticeBondLaw d p) ∧
      (∫ ω, Real.exp (TriadicCube.stoppingSize (G ω) x / θ) ∂(latticeBondLaw d p)) ≤ 2) ∧
    (∃ K k : ℝ, 0 < K ∧ 0 < k ∧ ∀ (A : TriadicCube d) (n : ℕ),
      (latticeBondLaw d p) {ω | ∃ x ∈ A.boundaryInterior n, ∃ Q R : TriadicCube d,
        x ∈ Q.vertices ∧ x ∈ R.vertices ∧ Q.IsMaximalStopping (G ω) ∧
          R.IsMaximalStopping (TriadicCube.localGoodCentered (G ω) A.vertices) ∧ Q ≠ R} ≤
        ENNReal.ofReal (K * (3 : ℝ) ^ ((A.scale : ℝ) - n) *
          Real.exp (-k * (3 : ℝ) ^ n))) := by
  obtain ⟨M, hM⟩ :=
    TriadicCube.eventually_measure_not_wellConnectedIn_threeQuarter_le_of_twoPoint_slabs
      hd j i hij width hwidth p ρ c hρ hρ₁ hc hcρ hcroot hctwo hslab
  let rate : ℝ := ((c / (2 * ((10 * d * width : ℕ) : ℝ))) / 2) / 40
  let C : ℝ := 1 + 4 * 7 ^ d * ((d + 1).factorial : ℝ) / (rate / 2) ^ (d + 1)
  have hrate : 0 < rate := by dsimp only [rate]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlarge : ∀ Q : TriadicCube d, M ≤ Q.scale →
      (latticeBondLaw d p) {ω | ¬ Q.wellConnectedIn Q.threeQuarterCube.vertices ω} ≤
        ENNReal.ofReal (C * Real.exp (-(rate / 2) * (3 : ℝ) ^ Q.scale)) := by
    intro Q hscale
    have hpow : M ≤ 3 ^ Q.scale := by
      calc
        M ≤ 2 ^ M := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ 3 ^ M := by gcongr; omega
        _ ≤ 3 ^ Q.scale := pow_le_pow_right₀ (by omega) hscale
    exact hM Q hpow
  exact TriadicCube.partition_estimates_of_large_scale hd (latticeBondLaw d p)
    (fun Q => Q.threeQuarterCube.vertices) M C (rate / 2) hC (by positivity) hlarge

end Rigidity.Percolation
