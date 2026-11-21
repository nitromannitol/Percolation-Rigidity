import Rigidity.Proofs.S2.FiniteClusterMoment

/-!
# Polynomial moments of planar finite clusters

The stretched-exponential finite-cluster estimate controls every integer moment uniformly over
vertices. The factorial growth records the dependence on the moment order.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation

/-- An exponential square-root bound controls integer powers. -/
theorem pow_le_factorial_mul_exp_sqrt {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (r : ℕ) :
    x ^ r ≤ ((2 * r).factorial : ℝ) / a ^ (2 * r) * Real.exp (a * Real.sqrt x) := by
  have hf : (0 : ℝ) < ((2 * r).factorial : ℝ) := by positivity
  have hpow : 0 < a ^ (2 * r) := pow_pos ha _
  have h := Real.pow_div_factorial_le_exp (a * Real.sqrt x) (by positivity) (2 * r)
  have hs : (a * Real.sqrt x) ^ (2 * r) = a ^ (2 * r) * x ^ r := by
    rw [mul_pow]
    congr 1
    rw [pow_mul, Real.sq_sqrt hx]
  rw [hs] at h
  have h' : a ^ (2 * r) * x ^ r ≤ Real.exp (a * Real.sqrt x) * ((2 * r).factorial : ℝ) :=
    (div_le_iff₀ hf).1 h
  calc
    x ^ r ≤ (Real.exp (a * Real.sqrt x) * ((2 * r).factorial : ℝ)) / a ^ (2 * r) :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using h')
    _ = _ := by ring

/-- All integer moments of a planar finite component satisfy a uniform factorial bound. -/
theorem planar_finiteComponent_polynomial_moment (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ r : ℕ, ∀ x : Vertex 2,
      Integrable (fun ω => ((finiteComponentVertices ω x).card : ℝ) ^ r)
          (latticeBondLaw 2 p) ∧
      (∫ ω, ((finiteComponentVertices ω x).card : ℝ) ^ r ∂latticeBondLaw 2 p) ≤
        ((2 * r).factorial : ℝ) / a ^ (2 * r) * C := by
  obtain ⟨a, C, ha, hC, hmoment⟩ := planar_finiteComponent_exp_sqrt_moment p hp
  refine ⟨a, C, ha, hC, fun r x => ?_⟩
  obtain ⟨hExp, hExpBound⟩ := hmoment x
  let K : ℝ := ((2 * r).factorial : ℝ) / a ^ (2 * r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hBound (ω : Configuration 2) :
      ((finiteComponentVertices ω x).card : ℝ) ^ r ≤
        K * Real.exp (a * Real.sqrt ((finiteComponentVertices ω x).card : ℝ)) :=
    pow_le_factorial_mul_exp_sqrt ha (Nat.cast_nonneg _) r
  have hMaj : Integrable
      (fun ω => K * Real.exp (a * Real.sqrt ((finiteComponentVertices ω x).card : ℝ)))
      (latticeBondLaw 2 p) := hExp.const_mul K
  have hInt : Integrable (fun ω => ((finiteComponentVertices ω x).card : ℝ) ^ r)
      (latticeBondLaw 2 p) := by
    refine hMaj.mono' (((measurable_from_nat (f := fun n : ℕ => (n : ℝ) ^ r)).comp
      (measurable_finiteComponent_size x)).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact hBound ω
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ ω, K * Real.exp (a * Real.sqrt ((finiteComponentVertices ω x).card : ℝ))
        ∂latticeBondLaw 2 p := integral_mono hInt hMaj hBound
    _ = K * ∫ ω, Real.exp (a * Real.sqrt ((finiteComponentVertices ω x).card : ℝ))
        ∂latticeBondLaw 2 p := integral_const_mul _ _
    _ ≤ K * C := mul_le_mul_of_nonneg_left hExpBound hK

end Rigidity.Proofs.S2
