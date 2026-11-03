import Rigidity.Steps.Section5.Common
import Rigidity.Proofs.S3.SublinearLiouville

/-!
# Section 5: the Liouville theorem at order zero in the plane

Step `step:5.1-liouville` (paper L1526-1531 of the corrected draft): almost surely, a harmonic
function on the infinite cluster of `ℤ²` with `|v(x)| ≤ ε |x|` far from the origin, for every
`ε > 0`, is constant. This is the order-zero Liouville theorem of Armstrong–Dario (the cited input
`LatticeProb.External.ArmstrongDarioOrderZero`), obtained from the general-dimension step
`Rigidity.Proofs.S3.sublinearLiouvilleStep`: pointwise sublinear growth at infinity gives the
slope asymptotics of slope zero, since the cluster meets each Euclidean ball in finitely many
vertices.
-/

namespace Rigidity.Proofs.Section5

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

/-- The Euclidean distance of a lattice vertex to the origin is its Euclidean norm. -/
theorem dist_latticeEuclideanEmbedding_zero (x : Vertex 2) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding 0) = eucl x := by
  have h0 : latticeEuclideanEmbedding (0 : Vertex 2) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    simp
  rw [h0, dist_zero_right, eucl]

/-- Pointwise sublinear growth at infinity gives the slope asymptotics of slope zero. -/
theorem componentSlopeAsymptotics_zero_of_sublinear {ω : Configuration 2} (C : OpenComponent ω)
    (v : C → ℝ)
    (hv : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : C, R ≤ eucl x.val → |v x| ≤ ε * eucl x.val) :
    componentSlopeAsymptotics C 0 v := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := hv ε hε
  set M := ∑ y ∈ componentEuclideanBall C 0 R₁, |v y|
  refine ⟨max R₁ (M / ε) + 1, by positivity, fun R hR x hx => ?_⟩
  have hR₁R : R₁ ≤ R := (le_max_left _ _).trans (by linarith)
  have hMR : M ≤ ε * R := by
    have : M / ε ≤ R := (le_max_right _ _).trans (by linarith)
    rwa [div_le_iff₀ hε, mul_comm] at this
  have hxR : eucl x.val < R := by
    rw [← dist_latticeEuclideanEmbedding_zero]
    exact (mem_componentEuclideanBall C 0 R x).mp hx
  simp only [componentSlope, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
  by_cases hfar : R₁ ≤ eucl x.val
  · exact (hR₁ x hfar).trans (mul_le_mul_of_nonneg_left hxR.le hε.le)
  · have hmem : x ∈ componentEuclideanBall C 0 R₁ := by
      rw [mem_componentEuclideanBall, dist_latticeEuclideanEmbedding_zero]
      exact lt_of_not_ge hfar
    exact (Finset.single_le_sum (f := fun y => |v y|) (fun y _ => abs_nonneg (v y)) hmem).trans
      hMR

/-- Step `step:5.1-liouville`: almost surely, every harmonic function of sublinear growth on the
infinite cluster of `ℤ²` is constant (Armstrong–Dario, order zero). -/
theorem sublinearLiouville (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (input : LatticeProb.External.ArmstrongDarioOrderZero) :
    SublinearLiouville p := by
  filter_upwards [Rigidity.Proofs.S3.sublinearLiouvilleStep le_rfl p hpc hp1 input] with ω hω
  intro h v hharm hsub
  exact hω h v hharm (componentSlopeAsymptotics_zero_of_sublinear _ v hsub)

end Rigidity.Proofs.Section5
