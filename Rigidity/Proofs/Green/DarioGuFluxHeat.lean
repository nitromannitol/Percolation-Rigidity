import Rigidity.Proofs.Green.DarioGuFluxFlip
import Rigidity.Proofs.Corrector.RandomBallSums
import Rigidity.Proofs.Corrector.DarioOptimalCorrector
import Rigidity.Proofs.Corrector.PlanarHeatSmoothing

/-!
# Heat averages of the flux of the corrected planes

The spatial average of the flux of Gu's Proposition 1.1 with the heat kernel of `ℤ²` as kernel,
`Σ_z Φ_{r²}(x, z) planeFlux(z, i)`, is a convergent series for every corrected plane
(`summable_heat_planeFlux`): the flux grows at most linearly (`exists_abs_planeFlux_le`) and the
heat kernel decays exponentially (`latticeHeat_le_exp`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Green

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Corrector
open scoped Classical ENNReal

/-- `Σ_{z ∈ ℤ²} e^{-|z - y|/κ}` converges. -/
theorem summable_exp_neg_norm_sub (y : Vertex 2) {κ : ℝ} (hκ : 0 < κ) :
    Summable fun z : Vertex 2 => Real.exp (-‖latticeEuclideanEmbedding (z - y)‖ / κ) := by
  have h := tsum_exp_neg_norm_sub_le y hκ
  have hne : ∑' z : Vertex 2,
      ENNReal.ofReal (Real.exp (-‖latticeEuclideanEmbedding (z - y)‖ / κ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have := ENNReal.summable_toReal hne
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this

theorem one_add_mul_exp_le (d : ℝ) :
    (1 + d) * Real.exp (-d / 18) ≤ 36 * Real.exp (-d / 36) := by
  have h1 : 1 + d / 36 ≤ Real.exp (d / 36) := by
    have := Real.add_one_le_exp (d / 36)
    linarith
  have h2 : 1 + d ≤ 36 * Real.exp (d / 36) := by linarith
  calc (1 + d) * Real.exp (-d / 18) ≤ 36 * Real.exp (d / 36) * Real.exp (-d / 18) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 36 * Real.exp (-d / 36) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The heat average of a function of linear growth converges.** -/
theorem summable_latticeHeat_mul_of_abs_le {r : ℝ} (hr : 0 < r) (x : Vertex 2)
    {f : Vertex 2 → ℝ} {A : ℝ}
    (hf : ∀ z, |f z| ≤ A * (1 + ‖latticeEuclideanEmbedding z‖)) :
    Summable fun z => latticeHeat (r ^ 2) x z * f z := by
  have hr2 : 0 < r ^ 2 := by positivity
  set K : ℝ := 108 * Real.exp (r ^ 2 / 18) * |A| * (1 + ‖latticeEuclideanEmbedding x‖)
  refine Summable.of_norm_bounded
    ((summable_exp_neg_norm_sub x (by norm_num : (0 : ℝ) < 36)).mul_left K) fun z => ?_
  set d := ‖latticeEuclideanEmbedding (z - x)‖
  have hΦ := latticeHeat_le_exp hr2 le_rfl x z
  have hΦ0 := latticeHeat_nonneg hr2.le x z
  have hz : 1 + ‖latticeEuclideanEmbedding z‖ ≤ (1 + ‖latticeEuclideanEmbedding x‖) * (1 + d) := by
    have : ‖latticeEuclideanEmbedding z‖ ≤ ‖latticeEuclideanEmbedding x‖ + d := by
      have e : latticeEuclideanEmbedding z =
          latticeEuclideanEmbedding x + latticeEuclideanEmbedding (z - x) := by
        rw [Rigidity.Corrector.latticeEuclideanEmbedding_sub]; abel
      rw [e]
      exact norm_add_le _ _
    nlinarith [norm_nonneg (latticeEuclideanEmbedding x), norm_nonneg (latticeEuclideanEmbedding (z - x))]
  have hfz : |f z| ≤ |A| * ((1 + ‖latticeEuclideanEmbedding x‖) * (1 + d)) :=
    (hf z).trans (by
      calc A * (1 + ‖latticeEuclideanEmbedding z‖) ≤ |A| * (1 + ‖latticeEuclideanEmbedding z‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * ((1 + ‖latticeEuclideanEmbedding x‖) * (1 + d)) :=
            mul_le_mul_of_nonneg_left hz (abs_nonneg A))
  have hexp := one_add_mul_exp_le d
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΦ0]
  calc latticeHeat (r ^ 2) x z * |f z|
      ≤ (3 * Real.exp (r ^ 2 / 18) * Real.exp (-d / 18)) *
          (|A| * ((1 + ‖latticeEuclideanEmbedding x‖) * (1 + d))) :=
        mul_le_mul hΦ hfz (abs_nonneg _) (by positivity)
    _ = 3 * Real.exp (r ^ 2 / 18) * |A| * (1 + ‖latticeEuclideanEmbedding x‖) *
          ((1 + d) * Real.exp (-d / 18)) := by ring
    _ ≤ 3 * Real.exp (r ^ 2 / 18) * |A| * (1 + ‖latticeEuclideanEmbedding x‖) *
          (36 * Real.exp (-d / 36)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = K * Real.exp (-d / 36) := by ring

theorem abs_coord_le_norm (z : Vertex 2) (i : Fin 2) :
    |(z i : ℝ)| ≤ ‖latticeEuclideanEmbedding z‖ := by
  have h := PiLp.norm_apply_le (latticeEuclideanEmbedding z) i
  rwa [Real.norm_eq_abs] at h

/-- **A corrected plane grows at most linearly.** -/
theorem exists_abs_le_of_isCorrectedPlane {ω : Configuration 2} {C : OpenComponent ω}
    {q : Fin 2 → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : C, |ℓ z| ≤ B * (1 + ‖latticeEuclideanEmbedding z.val‖) := by
  obtain ⟨R₀, hR₀, hR⟩ := hℓ.2 1 one_pos
  refine ⟨∑ i, |q i| + R₀ + 1, by positivity, fun z => ?_⟩
  set n := ‖latticeEuclideanEmbedding z.val‖
  have hn : 0 ≤ n := norm_nonneg _
  have hz : z ∈ componentEuclideanBall C 0 (R₀ + n + 1) := by
    rw [mem_componentEuclideanBall]
    have : dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding (0 : Vertex 2)) = n := by
      rw [dist_eq_norm, ← Rigidity.Corrector.latticeEuclideanEmbedding_sub, sub_zero]
    rw [this]
    linarith
  have h1 := hR (R₀ + n + 1) (by linarith) z hz
  rw [one_mul] at h1
  have hslope : |componentSlope C q z| ≤ (∑ i, |q i|) * n := by
    unfold componentSlope
    calc |∑ i, q i * (z.val i : ℝ)| ≤ ∑ i, |q i * (z.val i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |q i| * n := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_coord_le_norm z.val i) (abs_nonneg _)
      _ = (∑ i, |q i|) * n := by rw [Finset.sum_mul]
  have hq0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc |ℓ z| ≤ |ℓ z - componentSlope C q z| + |componentSlope C q z| := by
        have := abs_add_le (ℓ z - componentSlope C q z) (componentSlope C q z)
        rwa [sub_add_cancel] at this
    _ ≤ (R₀ + n + 1) + (∑ i, |q i|) * n := add_le_add h1 hslope
    _ ≤ (∑ i, |q i| + R₀ + 1) * (1 + n) := by nlinarith

/-- **The flux of a corrected plane grows at most linearly.** -/
theorem exists_abs_planeFlux_le {ω : Configuration 2} {C : OpenComponent ω}
    {q : Fin 2 → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) (i : Fin 2) :
    ∃ A : ℝ, ∀ z : Vertex 2, |planeFlux C ℓ (z, i)| ≤ A * (1 + ‖latticeEuclideanEmbedding z‖) := by
  obtain ⟨B, hB, hBℓ⟩ := exists_abs_le_of_isCorrectedPlane hℓ
  refine ⟨3 * B, fun z => ?_⟩
  have hext : ∀ w : Vertex 2, |extendComp C ℓ w| ≤ B * (1 + ‖latticeEuclideanEmbedding w‖) := by
    intro w
    by_cases hw : w ∈ C.supp
    · rw [extendComp_of_mem _ _ hw]
      exact hBℓ ⟨w, hw⟩
    · rw [extendComp_of_not_mem _ _ hw, abs_zero]
      positivity
  have hhead : ‖latticeEuclideanEmbedding (edgeHead (z, i))‖ ≤
      ‖latticeEuclideanEmbedding z‖ + 1 := by
    have e : latticeEuclideanEmbedding (edgeHead (z, i)) =
        latticeEuclideanEmbedding z + latticeEuclideanEmbedding (LatticeProb.unit i) := by
      have := Rigidity.Corrector.latticeEuclideanEmbedding_sub (edgeHead (z, i)) z
      rw [show edgeHead (z, i) - z = LatticeProb.unit i by simp [edgeHead]] at this
      rw [this]; abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl (le_of_eq ?_))
    rw [EuclideanSpace.norm_eq]
    fin_cases i <;> simp [latticeEuclideanEmbedding, LatticeProb.unit, Fin.sum_univ_two]
  unfold planeFlux
  split_ifs
  · calc |extendComp C ℓ (edgeHead (z, i)) - extendComp C ℓ (z, i).1|
        ≤ |extendComp C ℓ (edgeHead (z, i))| + |extendComp C ℓ z| := by
          have := abs_add_le (extendComp C ℓ (edgeHead (z, i))) (-extendComp C ℓ z)
          rwa [abs_neg, ← sub_eq_add_neg] at this
      _ ≤ B * (1 + ‖latticeEuclideanEmbedding (edgeHead (z, i))‖) +
          B * (1 + ‖latticeEuclideanEmbedding z‖) := add_le_add (hext _) (hext _)
      _ ≤ 3 * B * (1 + ‖latticeEuclideanEmbedding z‖) := by
          nlinarith [norm_nonneg (latticeEuclideanEmbedding z)]
  · rw [abs_zero]
    positivity

/-- **The heat average of the flux of a corrected plane converges.** -/
theorem summable_heat_planeFlux {ω : Configuration 2} {C : OpenComponent ω}
    {q : Fin 2 → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) (i : Fin 2) {r : ℝ}
    (hr : 0 < r) (x : Vertex 2) :
    Summable fun z => latticeHeat (r ^ 2) x z * planeFlux C ℓ (z, i) := by
  obtain ⟨A, hA⟩ := exists_abs_planeFlux_le hℓ i
  exact summable_latticeHeat_mul_of_abs_le hr x hA

end Rigidity.Green
