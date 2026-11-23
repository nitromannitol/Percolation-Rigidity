import Rigidity.Proofs.Regularity.PlanarCorrectorConstruction

/-!
# (1.18) in dimension two from the approximation of affine functions on growing balls

`PlanarAffineApproximationTwo` is the input of Step 3 of the proof of Proposition 3.1 of
Armstrong, Kuusi and Mourrat (arXiv:1602.00512v1), for `k = 1`, on the planar cluster: almost
surely, for every slope `q` and every `m` with `3^m ≥ 𝒳`, a function harmonic on `𝒞_∞ ∩ B_{3^m}`
within `K |q| 3^{m(1-δ)}` of `q · x` in `L̲²(𝒞_∞ ∩ B_{3^m})`. In AKM2 it comes from the error
estimate for the Dirichlet problem with affine data (their Proposition 3.2); Armstrong and Dario
(arXiv:1609.09431v2, proof of Theorem 2) use their Theorem 1 in its place.

`planarCorrectorSublinearL2Two_of_affineApproximation` proves (1.18)
(`PlanarCorrectorSublinearL2Two`) from it, the order-zero regularity of Theorem 2 (iii) and the
density of the cluster, by the construction of Step 3 (`exists_harmonic_of_approximations`).
-/

namespace Rigidity.Proofs.Regularity

open Finset Filter Topology MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation
open Rigidity.External Rigidity.Proofs.S2

/-- The approximation of affine functions by harmonic functions on growing balls of the planar
cluster (the input of AKM2, Proposition 3.1, Step 3, for `k = 1`). -/
def PlanarAffineApproximationTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s δ θ K : ℝ, 0 < s ∧ 0 < δ ∧ 0 < θ ∧ 0 ≤ K ∧
      ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ q : Fin 2 → ℝ,
          ∀ m : ℕ, X ω ≤ 3 ^ m → ∃ v : uniqueInfiniteComponent h → ℝ,
            HarmonicOnBall (uniqueInfiniteComponent h) v (3 ^ m) ∧
            componentBallL2 (uniqueInfiniteComponent h) 0 (3 ^ m)
                (fun x => v x - componentSlope (uniqueInfiniteComponent h) q x) ≤
              K * (|q 0| + |q 1|) * ((3 : ℝ) ^ m) ^ (1 - δ)

theorem three_pow_rpow_eq {m : ℕ} (δ : ℝ) :
    ((3 : ℝ) ^ m) ^ (1 - δ) = 3 ^ m * ((3 : ℝ) ^ (-δ)) ^ m := by
  rw [Real.rpow_sub (by positivity), Real.rpow_one, Real.rpow_neg (by norm_num), inv_pow]
  have e : ((3 : ℝ) ^ m) ^ δ = ((3 : ℝ) ^ δ) ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [e, div_eq_mul_inv]

theorem abs_componentSlope_le {ω : Configuration 2} (C : OpenComponent ω) (q : Fin 2 → ℝ) {R : ℝ}
    {x : C} (hx : x ∈ componentEuclideanBall C 0 R) :
    |componentSlope C q x| ≤ (|q 0| + |q 1|) * R := by
  rw [mem_componentEuclideanBall] at hx
  unfold componentSlope
  rw [Fin.sum_univ_two]
  have h0 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) 0
  have h1 := abs_sub_le_dist_latticeEuclideanEmbedding x.val (0 : Vertex 2) 1
  simp only [Pi.zero_apply, Int.cast_zero, sub_zero] at h0 h1
  calc |q 0 * (x.val 0 : ℝ) + q 1 * (x.val 1 : ℝ)| ≤ |q 0| * |(x.val 0 : ℝ)| + |q 1| * |(x.val 1 : ℝ)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |q 0| * R + |q 1| * R := by gcongr <;> linarith
    _ = (|q 0| + |q 1|) * R := by ring

end Rigidity.Proofs.Regularity
