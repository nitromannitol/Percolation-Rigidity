import Rigidity.Proofs.Poincare.HeatKernelBounds
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoProof

/-!
# The square sum of the heat kernel of `ℤ²`

In the proof of Lemma 3.3 of Dario, the bound `O_s'(C r^{-d})` comes from the heat kernel through
`Σ_y ζ_r(y)² ≤ C r^{-d}`, with `ζ_r` the polynomial majorant (3.17) of `Φ_{r²}`. In dimension two
the square sum of the heat kernel itself is enough:

* `exists_latticeHeat_le_div_sq`: `Φ_{r²}(x, y) ≤ C/r²` for `r ≥ 1`, the on-diagonal bound, from the
  tilted bound `exists_openHeat_mul_exp_le` (local limit theorem of Lattice-Probability) with
  tilt `0`;
* `summable_latticeHeat_sq`, `tsum_latticeHeat_sq_le`: `Σ_y Φ_t(x, y)² ≤ M` when `Φ_t(x, ·) ≤ M`,
  since `Σ_y Φ_t(x, y) = 1`;
* `exists_tsum_latticeHeat_sq_le`: `Σ_y Φ_{r²}(x, y)² ≤ C/r²` for `r ≥ 1`.
-/

namespace Rigidity.Corrector

open LatticeProb.Percolation

/-- **The on-diagonal bound of the heat kernel of `ℤ²`**: `Φ_{r²}(x, y) ≤ C/r²` for `r ≥ 1`. -/
theorem exists_latticeHeat_le_div_sq :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x y : Vertex 2, latticeHeat (r ^ 2) x y ≤ C / r ^ 2 := by
  obtain ⟨C, hC, h⟩ := Rigidity.Poincare.exists_openHeat_mul_exp_le
  refine ⟨C, hC, fun r hr x y => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  have hσ : max (Real.sqrt (r ^ 2)) 1 = r := by
    rw [Real.sqrt_sq hr0]
    exact max_eq_left hr
  have h1 := h (r ^ 2) (by positivity) 0 le_rfl (by norm_num) (by simp) x y
  rw [zero_mul, Real.exp_zero, mul_one, hσ] at h1
  have key : ∀ A : ℝ, 0 ≤ A → C / r ^ 2 * Real.exp (-A / r) ≤ C / r ^ 2 := fun A hA => by
    have he : Real.exp (-A / r) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hr0)
    calc C / r ^ 2 * Real.exp (-A / r) ≤ C / r ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = C / r ^ 2 := mul_one _
  exact h1.trans (key _ (by positivity))

theorem latticeHeat_le_one {t : ℝ} (ht : 0 ≤ t) (x y : Vertex 2) : latticeHeat t x y ≤ 1 :=
  Rigidity.Green.openHeat_le_one _ ht x y

theorem summable_latticeHeat_sq {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    Summable fun y => latticeHeat t x y ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun y => by
      have h0 := latticeHeat_nonneg ht x y
      have h1 := latticeHeat_le_one ht x y
      nlinarith)
    (summable_latticeHeat ht x)

/-- `Σ_y Φ_t(x, y)² ≤ M` when `Φ_t(x, ·) ≤ M`, since the heat kernel sums to one. -/
theorem tsum_latticeHeat_sq_le {t M : ℝ} (ht : 0 ≤ t) {x : Vertex 2}
    (hM : ∀ y, latticeHeat t x y ≤ M) : ∑' y, latticeHeat t x y ^ 2 ≤ M := by
  calc ∑' y, latticeHeat t x y ^ 2 ≤ ∑' y, M * latticeHeat t x y :=
        Summable.tsum_le_tsum (fun y => by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hM y) (latticeHeat_nonneg ht x y))
          (summable_latticeHeat_sq ht x) ((summable_latticeHeat ht x).mul_left M)
    _ = M * ∑' y, latticeHeat t x y := tsum_mul_left
    _ = M := by rw [tsum_latticeHeat ht x, mul_one]

/-- **The square sum of the heat kernel of `ℤ²`**: `Σ_y Φ_{r²}(x, y)² ≤ C/r²` for `r ≥ 1`, the
two-dimensional form of `Σ_y ζ_r(y)² ≤ C r^{-d}` in the proof of Lemma 3.3 of Dario. -/
theorem exists_tsum_latticeHeat_sq_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex 2,
      ∑' y, latticeHeat (r ^ 2) x y ^ 2 ≤ C / r ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_latticeHeat_le_div_sq
  exact ⟨C, hC, fun r hr x => tsum_latticeHeat_sq_le (by positivity) (h r hr x)⟩

end Rigidity.Corrector
