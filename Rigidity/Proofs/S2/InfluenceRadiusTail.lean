import Rigidity.Proofs.S2.FiniteClusterVolumeMoments
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Spatial decay of single-bond influences in dimension at least three

Resampling a bond `e` changes the infinite-cluster count of a triadic cube only if an endpoint of
`e` lies, before or after resampling, in a finite open cluster that meets the cube. If `e` is at
coordinate distance `n` from the cube, that finite cluster has radius at least `n`, which happens
with probability at most `C exp(-c n)` above the critical point in dimension `d ≥ 3`. With the
factorial moment bounds and the Cauchy–Schwarz inequality this gives moments of the influence that
decay exponentially in `n`.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- A bond at coordinate distance `n` from a triadic cube changes its infinite-cluster count with
probability at most `C exp(-c n)`. -/
theorem density_influence_radius_tail [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (m : ℕ) (k : Vertex d) (e : Bond d) (i : Fin d) (n : ℕ),
      (∀ x ∈ triadicCube d m k, ∀ y ∈ e.val, (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)|) →
      ((latticeBondLaw d p).prod (latticeBondLaw d p))
        {q | infiniteClusterCount (triadicCube d m k) q.1 ≠
          infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e)} ≤
        ENNReal.ofReal (C * Real.exp (-(c * n))) := by
  classical
  obtain ⟨C, c, hC, hc, htail⟩ := Rigidity.Percolation.exists_finite_cluster_radius_le hd hp
  refine ⟨4 * C, c, by positivity, hc, fun m k e i n hsep => ?_⟩
  let μ := latticeBondLaw d p
  let ν := μ.prod μ
  let S := e.val.toFinset
  let E : Vertex d → Set (Configuration d) := fun y =>
    {ω | {z | (openGraph ω).Reachable y z}.Finite ∧
      ∃ z, (openGraph ω).Reachable y z ∧ ∃ j, (n : ℤ) ≤ |z j - y j|}
  let A : Vertex d → Set (Configuration d × Configuration d) := fun y =>
    Prod.fst ⁻¹' E y ∪ (fun q => resampleBond q.1 q.2 e) ⁻¹' E y
  have hSm : S.card ≤ 2 := by
    dsimp [S]
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  have hmem (ω : Configuration d) (x y : Vertex d) (hx : x ∈ triadicCube d m k)
      (hy : y ∈ e.val) (hxy : (openGraph ω).Reachable x y)
      (hf : ((openGraph ω).connectedComponentMk y).supp.Finite) : ω ∈ E y := by
    rw [component_supp_eq_reachable] at hf
    refine ⟨hf, x, hxy.symm, i, ?_⟩
    exact_mod_cast hsep x hx y hy
  have hsub : {q : Configuration d × Configuration d |
      infiniteClusterCount (triadicCube d m k) q.1 ≠
        infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e)} ⊆
      ⋃ y ∈ S, A y := by
    intro q hq
    obtain ⟨x, hx, y, hy, h⟩ := nonzero_influence_reaches_finite_component m k q.1 q.2 e hq
    refine Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨Sym2.mem_toFinset.mpr hy, ?_⟩⟩
    rcases h with ⟨hxy, hf⟩ | ⟨hxy, hf⟩
    · exact Or.inl (hmem q.1 x y hx hy hxy hf)
    · exact Or.inr (hmem (resampleBond q.1 q.2 e) x y hx hy hxy hf)
  have hA (y : Vertex d) : ν (A y) ≤
      ENNReal.ofReal (C * Real.exp (-(c * n))) + ENNReal.ofReal (C * Real.exp (-(c * n))) := by
    have hfst : ν (Prod.fst ⁻¹' E y) ≤ μ (E y) := by
      have h := Measure.le_map_apply (μ := ν) measurable_fst.aemeasurable (E y)
      rwa [(measurePreserving_fst : MeasurePreserving Prod.fst ν μ).map_eq] at h
    have hres : ν ((fun q => resampleBond q.1 q.2 e) ⁻¹' E y) ≤ μ (E y) := by
      have h := Measure.le_map_apply (μ := ν)
        (measurePreserving_resampleBond d p e).measurable.aemeasurable (E y)
      rwa [(measurePreserving_resampleBond d p e).map_eq] at h
    calc
      _ ≤ ν (Prod.fst ⁻¹' E y) + ν ((fun q => resampleBond q.1 q.2 e) ⁻¹' E y) :=
        measure_union_le _ _
      _ ≤ μ (E y) + μ (E y) := add_le_add hfst hres
      _ ≤ _ := add_le_add (htail y n) (htail y n)
  calc
    _ ≤ ν (⋃ y ∈ S, A y) := measure_mono hsub
    _ ≤ ∑ y ∈ S, ν (A y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ S, (ENNReal.ofReal (C * Real.exp (-(c * n))) +
        ENNReal.ofReal (C * Real.exp (-(c * n)))) := Finset.sum_le_sum fun y _ => hA y
    _ ≤ 2 * (ENNReal.ofReal (C * Real.exp (-(c * n))) +
        ENNReal.ofReal (C * Real.exp (-(c * n)))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast hSm
    _ = ENNReal.ofReal (4 * C * Real.exp (-(c * n))) := by
      rw [two_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Moments of single-bond influences decay exponentially in the coordinate distance of the bond
from the counting cube. -/
theorem density_influence_spatial_moment [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) :
    ∃ a A b B : ℝ, 0 < a ∧ 0 < A ∧ 0 < b ∧ 0 < B ∧
      ∀ (m : ℕ) (k : Vertex d) (e : Bond d) (r : ℕ), 1 ≤ r →
      ∀ (i : Fin d) (n : ℕ),
      (∀ x ∈ triadicCube d m k, ∀ y ∈ e.val, (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)|) →
      Integrable (fun q : Configuration d × Configuration d =>
        |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r)
        ((latticeBondLaw d p).prod (latticeBondLaw d p)) ∧
      (∫ q : Configuration d × Configuration d,
        |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
          (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r
        ∂((latticeBondLaw d p).prod (latticeBondLaw d p))) ≤
        Real.sqrt ((4 : ℝ) ^ (2 * r + 1) *
          (((d * (2 * r)).factorial : ℝ) / a ^ (d * (2 * r))) * A) *
        Real.sqrt (B * Real.exp (-(b * n))) := by
  classical
  obtain ⟨a, A, ha, hA, hmoment⟩ := density_influence_polynomial_moment hd hp
  obtain ⟨B, b, hB, hb, htail⟩ := density_influence_radius_tail hd hp
  refine ⟨a, A, b, B, ha, hA, hb, hB, fun m k e r hr i n hsep => ?_⟩
  let μ := (latticeBondLaw d p).prod (latticeBondLaw d p)
  let X (q : Configuration d × Configuration d) : ℝ :=
    |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
      (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)|
  let F (q : Configuration d × Configuration d) : ℝ := X q ^ r
  let S : Set (Configuration d × Configuration d) := {q | 0 < X q}
  let G : Configuration d × Configuration d → ℝ := S.indicator 1
  have hXm : Measurable X := measurable_count_influence m k e
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hXm
  have hFm : Measurable F := hXm.pow_const r
  have hFint : Integrable F μ := (hmoment m k e r hr).1
  have hF2int : Integrable (fun q => F q ^ 2) μ := by
    have h := (hmoment m k e (2 * r) (by omega)).1
    simpa only [F, ← pow_mul, mul_comm] using h
  have hF2bound : (∫ q, F q ^ 2 ∂μ) ≤
      (4 : ℝ) ^ (2 * r + 1) * (((d * (2 * r)).factorial : ℝ) / a ^ (d * (2 * r))) * A := by
    have h := (hmoment m k e (2 * r) (by omega)).2
    have hF2 : (fun q => F q ^ 2) = fun q => X q ^ (2 * r) := by
      funext q
      dsimp only [F]
      rw [← pow_mul, mul_comm]
    rw [hF2]
    exact h
  have hGm : Measurable G := measurable_const.indicator hSm
  have hG2eq (q) : G q ^ 2 = G q := by
    by_cases hq : q ∈ S <;> simp [G, hq]
  have hGint : Integrable G μ := (integrable_const (1 : ℝ)).indicator hSm
  have hG2int : Integrable (fun q => G q ^ 2) μ := by simpa only [hG2eq] using hGint
  have hFmem : MemLp F 2 μ := (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 hF2int
  have hGmem : MemLp G 2 μ := (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2 hG2int
  have hSprob : μ S ≤ ENNReal.ofReal (B * Real.exp (-(b * n))) := by
    have heq : S = {q | infiniteClusterCount (triadicCube d m k) q.1 ≠
        infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e)} := by
      ext q
      simp only [S, X, Set.mem_setOf_eq, abs_pos, sub_ne_zero]
      constructor <;> intro h hn <;> apply h <;> exact_mod_cast hn
    rw [heq]
    exact htail m k e i n hsep
  have hSreal : μ.real S ≤ B * Real.exp (-(b * n)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSprob
    have hnonneg : 0 ≤ B * Real.exp (-(b * n)) := mul_nonneg hB.le (Real.exp_pos _).le
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
