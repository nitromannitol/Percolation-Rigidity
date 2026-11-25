import Rigidity.Proofs.WeakPoincare.Balls
import PercolationClusterHomogenization.Proofs.Cluster.PartitionBoxSobolev

/-!
# The Sobolev inequality on a cluster as a Poincaré inequality

The Sobolev inequality of Armstrong–Dario (Proposition 3.4 with `s = 2`) on a cluster `U`, in the
form `ClusterSobolevTwo` of Percolation-Cluster-Homogenization,
`Σ_U w² ≤ K (Σ_U size^{2d} |∇w|^{2_*})^{2/2_*}` for `Σ_U w = 0`, `2_* = 2d/(d+2)`, gives with
Hölder's inequality for the exponents `(d+2)/2` and `(d+2)/d`

`Σ_U w² ≤ K (Σ_U size^{d(d+2)})^{2/d} Σ_U |∇w|²`

(`sum_sq_le_of_clusterSobolevTwo`). When `Σ_U size^{d(d+2)} ≤ C 3^{md}` this is the Poincaré
inequality with the factor `C^{2/d} 9^m`, of order the square of the radius.
-/

open Finset LatticeProb.Percolation Rigidity.Proofs.Cluster

namespace Rigidity.WeakPoincare

variable {d : ℕ}

/-- **The Sobolev inequality on a cluster as a Poincaré inequality.** If `ClusterSobolevTwo` holds
on `U` with the weight `size ≥ 0` and the constant `K ≥ 0`, and `Σ_U size^{d(d+2)} ≤ A`, then every
`w` with `Σ_U w = 0` satisfies `Σ_U w² ≤ K A^{2/d} Σ_U |∇w|²`. -/
theorem sum_sq_le_of_clusterSobolevTwo (hd : 0 < d) {ω : Configuration d}
    {U : Finset (Vertex d)} {size : Vertex d → ℝ} (hsize : ∀ x, 0 ≤ size x) {K A : ℝ}
    (hK : 0 ≤ K) (hSob : ClusterSobolevTwo ω U size K)
    (hA : ∑ x ∈ U, size x ^ (d * (d + 2)) ≤ A) (w : Vertex d → ℝ) (hw : ∑ x ∈ U, w x = 0) :
    ∑ x ∈ U, w x ^ 2 ≤ K * A ^ (2 / (d : ℝ)) * ∑ x ∈ U, clusterGradSq ω U w x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0' : (d : ℝ) ≠ 0 := hd0.ne'
  have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
  set q := lowerSobolevTwo d with hq
  have hq' : q = 2 * d / (d + 2) := by rw [hq, lowerSobolevTwo]
  have hqpos : 0 < q := lowerSobolevTwo_pos hd
  set s : ℝ := ((d : ℝ) + 2) / 2 with hs
  set t : ℝ := ((d : ℝ) + 2) / d with ht
  have hs1 : 1 < s := by rw [hs]; linarith
  have hst : s.HolderConjugate t := by
    refine (Real.holderConjugate_iff_eq_conjExponent hs1).2 ?_
    rw [hs, ht]
    have e : ((d : ℝ) + 2) / 2 - 1 = d / 2 := by ring
    rw [e, div_div_div_cancel_right₀ two_ne_zero]
  set g : Vertex d → ℝ := fun x => clusterGradSq ω U w x ^ (q / 2) with hg
  set X : ℝ := ∑ x ∈ U, size x ^ (2 * (d : ℝ)) * g x with hX
  set Y : ℝ := ∑ x ∈ U, clusterGradSq ω U w x with hY
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun x _ =>
    mul_nonneg (Real.rpow_nonneg (hsize x) _) (Real.rpow_nonneg (clusterGradSq_nonneg ω U w x) _)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun x _ => clusterGradSq_nonneg ω U w x
  have hA0 : 0 ≤ ∑ x ∈ U, size x ^ (d * (d + 2)) :=
    Finset.sum_nonneg fun x _ => pow_nonneg (hsize x) _
  have hA' : 0 ≤ A := hA0.trans hA
  have hHold : X ≤ A ^ (1 / s) * Y ^ (1 / t) := by
    have h1 := Real.inner_le_Lp_mul_Lq_of_nonneg U hst
      (f := fun x => size x ^ (2 * (d : ℝ))) (g := g)
      (fun x _ => Real.rpow_nonneg (hsize x) _)
      (fun x _ => Real.rpow_nonneg (clusterGradSq_nonneg ω U w x) _)
    have h2 : ∑ x ∈ U, (size x ^ (2 * (d : ℝ))) ^ s = ∑ x ∈ U, size x ^ (d * (d + 2)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Real.rpow_mul (hsize x), ← Real.rpow_natCast]
      congr 1
      rw [hs]
      push_cast
      ring
    have h3 : ∑ x ∈ U, g x ^ t = Y := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hg, ← Real.rpow_mul (clusterGradSq_nonneg ω U w x)]
      have e : q / 2 * t = 1 := by
        rw [hq', ht]
        field_simp
      rw [e, Real.rpow_one]
    rw [h2, h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hA0 hA (by rw [hs]; positivity)) (Real.rpow_nonneg hY0 _))
  have hHoldPow : X ^ (2 / q) ≤ A ^ (2 / (d : ℝ)) * Y := by
    have h1 := Real.rpow_le_rpow hX0 hHold (by positivity : (0 : ℝ) ≤ 2 / q)
    rw [Real.mul_rpow (Real.rpow_nonneg hA' _) (Real.rpow_nonneg hY0 _), ← Real.rpow_mul hA',
      ← Real.rpow_mul hY0] at h1
    have e1 : 1 / s * (2 / q) = 2 / d := by
      rw [hs, hq']
      field_simp
    have e2 : 1 / t * (2 / q) = 1 := by
      rw [ht, hq']
      field_simp
    rw [e1, e2, Real.rpow_one] at h1
    exact h1
  calc ∑ x ∈ U, w x ^ 2 ≤ K * X ^ (2 / q) := hSob w hw
    _ ≤ K * (A ^ (2 / (d : ℝ)) * Y) := mul_le_mul_of_nonneg_left hHoldPow hK
    _ = K * A ^ (2 / (d : ℝ)) * Y := by ring

end Rigidity.WeakPoincare
