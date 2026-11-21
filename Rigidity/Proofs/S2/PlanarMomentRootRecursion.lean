import Rigidity.Proofs.S2.PlanarMomentRecursion
import Rigidity.Proofs.S2.PowerRecursionAlgebra

/-!
# Root recursion for planar density moments

Taking roots of the spectral-gap recursion gives an additive bound on the squared moment
norms at successive dyadic orders.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.External

/-- The squared `Lⁿ` moment norm of the centered planar density. -/
noncomputable def planarDensityMomentRoot (p : unitInterval) (m : ℕ) (k : Vertex 2) (n : ℕ) : ℝ :=
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  (∫ ω, |planarDensityRealObservable p m k ω| ^ n ∂P) ^ (2 / (n : ℝ))

/-- Consecutive dyadic moment roots differ by at most the influence-moment bound. -/
theorem planar_density_moment_root_recursion (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m : ℕ) (k : Vertex 2),
      planarDensityMomentRoot p m k (2 * n) ≤ planarDensityMomentRoot p m k n +
        C * (n : ℝ) ^ 14 / (((3 ^ m : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C, hC, hrec⟩ := planar_density_moment_recursion p hp
  refine ⟨C, hC, fun n hn m k => ?_⟩
  let P := Measure.infinitePi (fun _ : Bond 2 => bernoulliMeasure (1 : ℝ) 0 p)
  let X := planarDensityRealObservable p m k
  let A : ℝ := ∫ ω, |X ω| ^ (2 * n) ∂P
  let B : ℝ := ∫ ω, |X ω| ^ n ∂P
  let a : ℝ := A ^ (1 / (n : ℝ))
  let b : ℝ := B ^ (2 / (n : ℝ))
  let c : ℝ := C * (n : ℝ) ^ 14 / (((3 ^ m : ℕ) : ℝ) ^ 2)
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hA : 0 ≤ A := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ B := integral_nonneg fun _ => by positivity
  have hb : 0 ≤ b := Real.rpow_nonneg hB _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have haN : a ^ n = A := by
    dsimp only [a]
    simpa only [one_div] using Real.rpow_inv_natCast_pow hA hn0
  have hbN : b ^ n = B ^ 2 := by
    dsimp only [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    have h : (2 / (n : ℝ)) * n = 2 := by field_simp
    rw [h, Real.rpow_two]
  have haPred : a ^ (n - 1) = A ^ (((n : ℝ) - 1) / n) := by
    dsimp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    congr 1
    ring
  have hpow : a ^ n ≤ b ^ n + c * a ^ (n - 1) := by
    rw [haN, hbN, haPred]
    exact hrec n hn m k
  have hroot := le_add_of_pow_le_pow_add_mul hb hc n (by omega) hpow
  have heq : planarDensityMomentRoot p m k (2 * n) = a := by
    dsimp only [planarDensityMomentRoot, a, A, X, P]
    congr 1
    push_cast
    field_simp
  change planarDensityMomentRoot p m k (2 * n) ≤ b + c
  rw [heq]
  exact hroot

end Rigidity.Proofs.S2
