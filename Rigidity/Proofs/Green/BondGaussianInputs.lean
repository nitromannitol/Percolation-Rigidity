import Rigidity.Proofs.Green.BondHeat
import Rigidity.Proofs.Green.DarioGuPhiCalculus
import Rigidity.Proofs.WeakPoincare.Balls

/-!
# The Gaussian upper bound of Barlow on `ℤ^d`: the statement

`dgPhiDim d C t r` is `Φ_C(t, x)` of Dario–Gu, (3.1), at `|x| = r` in dimension `d`:
`C t^{-d/2} exp(-r²/(C t))` if `r ≤ t` and `C t^{-d/2} exp(-r/C (1 + ln(r/t)))` if `r > t`; the
prefactor `t^{-d/2}` is written `(√t)^{-d}` (`dgPhiDim_eq_rpow`). In dimension two it is the planar
`dgPhi` (`dgPhiDim_two`).

`BarlowGaussianUpperBound d` is Theorem 4 of Dario–Gu (Barlow 2004, Theorem 1 and Lemma 1.1) in
dimension `d`, for the heat kernel `bondHeat` of the variable speed random walk on the open graph:
the `d`-dimensional form of `BarlowGaussianUpperBoundTwo`, which it implies for `d = 2`
(`barlowGaussianUpperBoundTwo_of_dim`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- **Dario–Gu, (3.1)** in dimension `d`: `Φ_C(t, x) = C t^{-d/2} exp(-|x|²/(C t))` if `|x| ≤ t`
and `C t^{-d/2} exp(-|x|/C (1 + ln(|x|/t)))` if `|x| ≥ t`, at `|x| = r`. -/
noncomputable def dgPhiDim (d : ℕ) (C t r : ℝ) : ℝ :=
  C * (Real.sqrt t ^ d)⁻¹ * Real.exp (-dgExponent C t r)

theorem dgPhiDim_eq_rpow (d : ℕ) {C t r : ℝ} (ht : 0 ≤ t) :
    dgPhiDim d C t r = C * t ^ (-((d : ℝ) / 2)) * Real.exp (-dgExponent C t r) := by
  rw [dgPhiDim, Real.rpow_neg ht, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 4
  ring

/-- In dimension two `Φ_C` is the planar `dgPhi`. -/
theorem dgPhiDim_two {C t r : ℝ} (ht : 0 ≤ t) : dgPhiDim 2 C t r = dgPhi C t r := by
  rw [dgPhiDim, dgPhi, Real.sq_sqrt ht]

theorem dgPhiDim_eq_mul_dgPhi (d : ℕ) {C t r : ℝ} (ht : 0 < t) :
    dgPhiDim d C t r = t * (Real.sqrt t ^ d)⁻¹ * dgPhi C t r := by
  rw [dgPhiDim, dgPhi]
  field_simp

theorem dgPhiDim_mono (d : ℕ) {C C' t r : ℝ} (hC : 0 < C) (hCC : C ≤ C') (ht : 0 < t)
    (hr : 0 ≤ r) : dgPhiDim d C t r ≤ dgPhiDim d C' t r := by
  rw [dgPhiDim_eq_mul_dgPhi d ht, dgPhiDim_eq_mul_dgPhi d ht]
  have : 0 < Real.sqrt t ^ d := by positivity
  exact mul_le_mul_of_nonneg_left (dgPhi_mono hC hCC ht hr) (by positivity)

/-- **Dario–Gu, Theorem 4** (Gaussian upper bound; Barlow, *Random walks on supercritical
percolation clusters*, Ann. Probab. 2004, Theorem 1 and Lemma 1.1), in dimension `d`.

Printed statement (lines 1220-1228 of the source): *There exist an exponent `s > 0`, a positive
constant `C < ∞` such that for each `y`, there exists a random time `T_NA(y)` satisfying
`T_NA(y) ≤ O_s(C)`, such that, on the event `{y ∈ 𝒞_∞}`, for every time `t ∈ (0, ∞)` satisfying
`t ≥ T_NA(y)`, and every point `x ∈ 𝒞_∞`, `p(t, x, y) ≤ Φ_C(t, x - y)`.* Here `p = bondHeat` is the
heat kernel of the variable speed walk with unit conductances (see `BarlowGaussianUpperBoundTwo`
for the citing lines and the change from the constant speed walk of the source). -/
def BarlowGaussianUpperBound (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ y : Vertex d,
      ∃ T : Configuration d → ℝ, Measurable T ∧ (∀ ω, 0 ≤ T ω) ∧ IsOsBond d p T s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          y ∈ (uniqueInfiniteComponent h).supp → ∀ t : ℝ, 0 < t → T ω ≤ t →
            ∀ x ∈ (uniqueInfiniteComponent h).supp,
              bondHeat ω t x y ≤ dgPhiDim d C t (WeakPoincare.latticeDist x y)

/-- The planar Gaussian upper bound is the case `d = 2`. -/
theorem barlowGaussianUpperBoundTwo_of_dim (h : BarlowGaussianUpperBound 2) :
    BarlowGaussianUpperBoundTwo := by
  intro p hpc hp1
  obtain ⟨s, C, hs, hC, hy⟩ := h p hpc hp1
  refine ⟨s, C, hs, hC, fun y => ?_⟩
  obtain ⟨T, hTm, hT0, hTos, hae⟩ := hy y
  refine ⟨T, hTm, hT0, hTos, ?_⟩
  filter_upwards [hae] with ω hω
  intro hu hyK t ht hTt x hx
  have h1 := hω hu hyK t ht hTt x hx
  rw [dgPhiDim_two ht.le] at h1
  exact h1

end Rigidity.Green
