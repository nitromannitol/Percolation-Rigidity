import Rigidity.Proofs.Smoothing.GaussianDiscrete
import Rigidity.Proofs.Smoothing.SliceGeometry

/-!
# Gaussian mass of an integer slice

The Gaussian mass of a slice with integer coordinate `n` is at most the mass of its zero slice
multiplied by `exp (-a n² / ‖b‖²)`. This is the slice estimate in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3, obtained from their Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- A translated integer slice has Gaussian mass bounded by the zero slice times a Gaussian factor. -/
theorem gaussian_integer_slice_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℤ E) [DiscreteTopology K] (b v : E) (hb : b ≠ 0)
    (hv : inner ℝ v b = 1) (hK : ∀ k : K, inner ℝ (k : E) b = 0)
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    Summable (fun k : K => Real.exp (-a * ‖n • v + (k : E)‖ ^ 2)) ∧
    Summable (fun k : K => Real.exp (-a * ‖(k : E)‖ ^ 2)) ∧
    (∑' k : K, Real.exp (-a * ‖n • v + (k : E)‖ ^ 2)) ≤
      Real.exp (-a * ((n : ℝ) ^ 2 / ‖b‖ ^ 2)) *
        ∑' k : K, Real.exp (-a * ‖(k : E)‖ ^ 2) := by
  let x : E := (n : ℝ) • (v - (1 / ‖b‖ ^ 2) • b)
  let A : ℝ := Real.exp (-a * ((n : ℝ) ^ 2 / ‖b‖ ^ 2))
  have hshift := gaussian_shift_le_of_discrete K ha x
  have hpoint (k : K) : Real.exp (-a * ‖n • v + (k : E)‖ ^ 2) =
      A * Real.exp (-a * ‖(k : E) + x‖ ^ 2) := by
    rw [norm_sq_zsmul_add_of_orthogonal b v (k : E) hb hv (hK k) n]
    dsimp only [A, x]
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Summable (fun k : K => Real.exp (-a * ‖n • v + (k : E)‖ ^ 2)) :=
    (hshift.1.mul_left A).congr fun k => (hpoint k).symm
  refine ⟨hs, hshift.2.1, ?_⟩
  simp_rw [hpoint, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hshift.2.2 (Real.exp_pos _).le

end Rigidity.Smoothing
