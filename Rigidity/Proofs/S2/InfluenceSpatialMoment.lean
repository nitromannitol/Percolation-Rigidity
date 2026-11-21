import Rigidity.Proofs.S2.InfluenceMoment
import Rigidity.Proofs.S2.PlanarInfluenceTail
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Spatial decay of density influence moments

Cauchy–Schwarz combines a uniform higher-moment estimate with the probability that a distant
bond changes the cluster count.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Moments of single-bond influences decay with the bond's distance from the counting cube. -/
theorem planar_density_influence_spatial_moment (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ a A b B : ℝ, 0 < a ∧ 0 < A ∧ 0 < b ∧ 0 < B ∧
      ∀ (m : ℕ) (k : Vertex 2) (e : Bond 2) (r : ℕ), 1 ≤ r →
      ∀ (i : Fin 2) (n : ℕ), 1 ≤ n →
      (∀ x ∈ triadicCube 2 m k, ∀ y ∈ e.val, (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)|) →
      Integrable (fun q : Configuration 2 × Configuration 2 =>
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r)
        ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p)) ∧
      (∫ q : Configuration 2 × Configuration 2,
        |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r
        ∂((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))) ≤
        Real.sqrt ((4 : ℝ) ^ (2 * r + 1) *
          (((2 * (2 * r)).factorial : ℝ) / a ^ (2 * (2 * r))) * A) *
        Real.sqrt (B * Real.exp (-(b * Real.sqrt n))) := by
  classical
  obtain ⟨a, A, ha, hA, hmoment⟩ := planar_density_influence_polynomial_moment p hp
  obtain ⟨B, b, hB, hb, htail⟩ := planar_density_influence_spatial_tail p hp
  refine ⟨a, A, b, B, ha, hA, hb, hB, fun m k e r hr i n hn hsep => ?_⟩
  let μ := (latticeBondLaw 2 p).prod (latticeBondLaw 2 p)
  let X (q : Configuration 2 × Configuration 2) : ℝ :=
    |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)|
  let F (q : Configuration 2 × Configuration 2) : ℝ := X q ^ r
  let S : Set (Configuration 2 × Configuration 2) := {q | 0 < X q}
  let G : Configuration 2 × Configuration 2 → ℝ := S.indicator 1
  have hXm : Measurable X := measurable_count_influence m k e
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hXm
  have hFm : Measurable F := hXm.pow_const r
  have hFint : Integrable F μ := (hmoment m k e r hr).1
  have hF2int : Integrable (fun q => F q ^ 2) μ := by
    have h := (hmoment m k e (2 * r) (by omega)).1
    simpa only [F, ← pow_mul, mul_comm] using h
  have hF2bound : (∫ q, F q ^ 2 ∂μ) ≤
      (4 : ℝ) ^ (2 * r + 1) *
        (((2 * (2 * r)).factorial : ℝ) / a ^ (2 * (2 * r))) * A := by
    have h := (hmoment m k e (2 * r) (by omega)).2
    simpa only [F, ← pow_mul, mul_comm] using h
  have hGm : Measurable G := measurable_const.indicator hSm
  have hG2eq (q) : G q ^ 2 = G q := by
    by_cases hq : q ∈ S <;> simp [G, hq]
  have hGint : Integrable G μ := (integrable_const (1 : ℝ)).indicator hSm
  have hG2int : Integrable (fun q => G q ^ 2) μ := by simpa only [hG2eq] using hGint
  have hFmem : MemLp F 2 μ := (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 hF2int
  have hGmem : MemLp G 2 μ := (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2 hG2int
  have hSprob : μ S ≤ ENNReal.ofReal (B * Real.exp (-(b * Real.sqrt n))) := by
    have heq : S = {q | infiniteClusterCount (triadicCube 2 m k) q.1 ≠
        infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e)} := by
      ext q
      simp only [S, X, Set.mem_setOf_eq, abs_pos, sub_ne_zero]
      constructor <;> intro h hn <;> apply h <;> exact_mod_cast hn
    rw [heq]
    exact htail m k e i n hn hsep
  have hSreal : μ.real S ≤ B * Real.exp (-(b * Real.sqrt n)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSprob
    have hnonneg : 0 ≤ B * Real.exp (-(b * Real.sqrt n)) :=
      mul_nonneg hB.le (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal hnonneg] at h
    exact h
  have hFG (q) : F q * G q = F q := by
    by_cases hq : q ∈ S
    · simp [G, hq]
    · have hX0 : X q = 0 := le_antisymm (le_of_not_gt hq) (abs_nonneg _)
      simp [G, hq, F, hX0, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hr)]
  have hGintegral : (∫ q, G q ^ 2 ∂μ) = μ.real S := by
    simp only [hG2eq, G, integral_indicator_one hSm]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := μ) (f := F) (g := G) (Filter.Eventually.of_forall fun q => pow_nonneg (abs_nonneg _) _)
    (Filter.Eventually.of_forall fun q => by by_cases hq : q ∈ S <;> simp [G, hq])
    (by simpa only [ENNReal.ofReal_ofNat] using hFmem)
    (by simpa only [ENNReal.ofReal_ofNat] using hGmem)
  have hCS' : (∫ q, F q ∂μ) ≤ Real.sqrt (∫ q, F q ^ 2 ∂μ) * Real.sqrt (μ.real S) := by
    have hCS0 : (∫ q, F q ∂μ) ≤
        (∫ q, F q ^ 2 ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ q, G q ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
      simpa only [hFG, Real.rpow_two] using hCS
    rw [hGintegral] at hCS0
    simpa only [Real.sqrt_eq_rpow] using hCS0
  refine ⟨hFint, hCS'.trans ?_⟩
  exact mul_le_mul (Real.sqrt_le_sqrt hF2bound) (Real.sqrt_le_sqrt hSreal)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Rigidity.Proofs.S2
