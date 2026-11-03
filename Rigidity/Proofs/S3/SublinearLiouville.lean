import Rigidity.Steps.S3.CompareDifferentPlanes
import LatticeProb.Prob.Percolation.LatticeOrderZeroApproximation

/-!
# Lemma 3.3: the Liouville theorem at order zero

Step `step:3.3-liouville` of Lemma 3.3 (paper L889, L896 of the corrected draft). By the
order-zero large-scale regularity of Armstrong–Dario (Theorem 2.4 at order zero, the cited input
`LatticeProb.External.ArmstrongDarioOrderZero`), almost surely the space `𝒜₀(C_∞)` of harmonic
functions on the infinite cluster whose normalized `L²` norm on the ball of radius `R` is `o(R)`
has dimension one, so it consists of the constants. A harmonic function with slope asymptotics of
slope zero is uniformly `o(R)` on the ball of radius `R`, hence lies in `𝒜₀(C_∞)`.
-/

namespace Rigidity.Proofs.S3

open Filter MeasureTheory LatticeProb.Percolation Rigidity.Steps.S3

variable {d : ℕ}

/-- A function with slope asymptotics of slope zero has the growth of order zero: its normalized
`L²` norm on the Euclidean ball of radius `R` is `o(R)`. -/
theorem componentL2Subpolynomial_zero_of_slope_asymptotics {ω : Configuration d}
    (C : OpenComponent ω) (u : C → ℝ) (hu : componentSlopeAsymptotics C 0 u) :
    componentL2Subpolynomial C 0 u := by
  rw [componentL2Subpolynomial, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₀, hR₀, htail⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨R₀, fun R hR => ?_⟩
  have hRp : 0 < R := hR₀.trans_le hR
  have hball : componentBallL2 C 0 R u ≤ ε / 2 * R := by
    apply componentBallL2_le_of_abs_le C 0 R u (by positivity)
    intro x hx
    simpa [componentSlope] using htail R hR x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (componentL2_scaled_nonneg C 0 u hRp.le)]
  calc
    (R ^ (0 + 1))⁻¹ * componentBallL2 C 0 R u ≤ (R ^ (0 + 1))⁻¹ * (ε / 2 * R) :=
      mul_le_mul_of_nonneg_left hball (by positivity)
    _ = ε / 2 := by rw [zero_add, pow_one]; field_simp
    _ < ε := half_lt_self hε

/-- Step `step:3.3-liouville`: almost surely, every harmonic function on the infinite cluster with
slope asymptotics of slope zero is constant. -/
theorem sublinearLiouvilleStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (input : LatticeProb.External.ArmstrongDarioOrderZero) :
    SublinearLiouvilleStep d p := by
  obtain ⟨_, _, _, _, _, _, X, _, _, _, _, hae⟩ := input d hd p hpc hp1
  filter_upwards [hae] with ω hω
  intro h v hharm hsub
  obtain ⟨-, hω⟩ := hω
  obtain ⟨hfin, hrank, -⟩ := hω h
  have hv : v ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 0 :=
    ⟨hharm, componentL2Subpolynomial_zero_of_slope_asymptotics _ v hsub⟩
  obtain ⟨c, hc⟩ := harmonicGrowthSpace_zero_eq_const _ hfin hrank v hv
  exact ⟨c, fun x => congrFun hc x⟩

end Rigidity.Proofs.S3
