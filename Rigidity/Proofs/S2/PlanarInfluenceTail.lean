import PercolationClusterHomogenization.Proofs.Density.FiniteClusterMoment
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityResampleLaw
import PercolationClusterHomogenization.Proofs.Density.FiniteClusterGeometry
import PercolationClusterHomogenization.Proofs.Density.PlanarInfluenceTail

/-!
# Tails of planar single-bond density influences

The finite-cluster tail and the endpoint bound give a uniform tail for each unnormalized
single-bond density influence.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- Every one-bond influence on the infinite-cluster count has a uniform stretched-exponential
 tail, including for bonds arbitrarily far from the counting cube. -/
theorem planar_density_single_influence_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (m : ℕ) (k : Vertex 2) (e : Bond 2)
      (n : ℕ), 1 ≤ n →
      ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
        {q | (4 * n : ℝ) ≤
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) := by
  classical
  obtain ⟨C, c, hC, hc, htail⟩ := planar_finiteComponent_size_tail p hp
  refine ⟨4 * C, c, by positivity, hc, fun m k e n hn => ?_⟩
  let μ := latticeBondLaw 2 p
  let ν := μ.prod μ
  let S := e.val.toFinset
  let A : Vertex 2 → Set (Configuration 2 × Configuration 2) := fun y =>
    {q | n ≤ (finiteComponentVertices q.1 y).card} ∪
    {q | n ≤ (finiteComponentVertices (resampleBond q.1 q.2 e) y).card}
  have hSm : S.card ≤ 2 := by
    dsimp [S]
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  have hsub : {q : Configuration 2 × Configuration 2 | (4 * n : ℝ) ≤
      |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)|} ⊆
      ⋃ y ∈ S, A y := by
    intro q hq
    by_contra hbad
    have hsmall : ∀ y ∈ S,
        (finiteComponentVertices q.1 y).card < n ∧
          (finiteComponentVertices (resampleBond q.1 q.2 e) y).card < n := by
      intro y hy
      have hy' : q ∉ A y := by
        intro hmem
        exact hbad (Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hmem⟩⟩)
      simpa only [A, Set.mem_union, Set.mem_setOf_eq, not_or, not_le] using hy'
    have hsum : (∑ y ∈ S, (((finiteComponentVertices q.1 y).card : ℝ) +
        ((finiteComponentVertices (resampleBond q.1 q.2 e) y).card : ℝ))) ≤
        (S.card : ℝ) * (2 * ((n : ℝ) - 1)) := by
      calc
        _ ≤ ∑ _y ∈ S, (2 * ((n : ℝ) - 1)) := by
          apply Finset.sum_le_sum
          intro y hy
          obtain ⟨h1, h2⟩ := hsmall y hy
          have h1' : ((finiteComponentVertices q.1 y).card : ℝ) ≤ n - 1 := by
            have hh : ((finiteComponentVertices q.1 y).card : ℝ) + 1 ≤ n := by
              exact_mod_cast (show (finiteComponentVertices q.1 y).card + 1 ≤ n by omega)
            linarith
          have h2' : ((finiteComponentVertices (resampleBond q.1 q.2 e) y).card : ℝ) ≤ n - 1 := by
            have hh : ((finiteComponentVertices (resampleBond q.1 q.2 e) y).card : ℝ) + 1 ≤ n := by
              exact_mod_cast (show (finiteComponentVertices (resampleBond q.1 q.2 e) y).card + 1 ≤ n by omega)
            linarith
          linarith
        _ = _ := by simp [nsmul_eq_mul]
    have hinf := abs_infiniteClusterCount_resampleBond_le m k q.1 q.2 e
    have hc' : (S.card : ℝ) ≤ 2 := by exact_mod_cast hSm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    change (4 * n : ℝ) ≤ _ at hq
    dsimp [S] at hsum hc'
    nlinarith
  have hA (y : Vertex 2) : ν (A y) ≤
      ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) +
        ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) := by
    let E : Set (Configuration 2) := {ω | n ≤ (finiteComponentVertices ω y).card}
    have hEm : MeasurableSet E := measurableSet_le measurable_const (measurable_finiteComponent_size y)
    have hfst : ν (Prod.fst ⁻¹' E) = μ E := (measurePreserving_fst :
      MeasurePreserving Prod.fst ν μ).measure_preimage hEm.nullMeasurableSet
    have hres : ν ((fun q => resampleBond q.1 q.2 e) ⁻¹' E) = μ E :=
      (measurePreserving_resampleBond 2 p e).measure_preimage hEm.nullMeasurableSet
    calc
      _ ≤ ν (Prod.fst ⁻¹' E) + ν ((fun q => resampleBond q.1 q.2 e) ⁻¹' E) := measure_union_le _ _
      _ = μ E + μ E := by rw [hfst, hres]
      _ ≤ _ := add_le_add (htail y n hn) (htail y n hn)
  calc
    _ ≤ ν (⋃ y ∈ S, A y) := measure_mono hsub
    _ ≤ ∑ y ∈ S, ν (A y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ S, (ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) +
        ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n)))) := Finset.sum_le_sum fun y _ => hA y
    _ ≤ 2 * (ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) +
        ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n)))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast hSm
    _ = ENNReal.ofReal (4 * C * Real.exp (-(c * Real.sqrt n))) := by
      rw [two_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- A density influence has a joint stretched-exponential bound in its magnitude and the
coordinate separation of the bond from the counting cube. -/
theorem planar_density_influence_joint_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (m : ℕ) (k : Vertex 2) (e : Bond 2)
      (i : Fin 2) (n t : ℕ), 1 ≤ n → 1 ≤ t →
      (∀ x ∈ triadicCube 2 m k, ∀ y ∈ e.val, (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)|) →
      ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
        {q | (4 * t : ℝ) ≤
          |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
            (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (Real.sqrt n + Real.sqrt t)))) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hsize⟩ := planar_density_single_influence_tail p hp
  obtain ⟨C₂, c₂, hC₂, hc₂, hspace⟩ := planar_density_influence_spatial_tail p hp
  let C := max C₁ C₂
  let c := min c₁ c₂ / 2
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc₁' : 2 * c ≤ c₁ := by dsimp [c]; linarith [min_le_left c₁ c₂]
  have hc₂' : 2 * c ≤ c₂ := by dsimp [c]; linarith [min_le_right c₁ c₂]
  refine ⟨C, c, hC, hc, fun m k e i n t hn ht hsep => ?_⟩
  have hsubset : {q : Configuration 2 × Configuration 2 | (4 * t : ℝ) ≤
      |(infiniteClusterCount (triadicCube 2 m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e) : ℝ)|} ⊆
      {q | infiniteClusterCount (triadicCube 2 m k) q.1 ≠
        infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e)} := by
    intro q hq heq
    have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    simp only [Set.mem_setOf_eq, heq, sub_self, abs_zero] at hq
    linarith
  by_cases hnt : n ≤ t
  · have hsqrt : Real.sqrt n ≤ Real.sqrt t := Real.sqrt_le_sqrt (by exact_mod_cast hnt)
    have he : Real.exp (-(c₁ * Real.sqrt t)) ≤
        Real.exp (-(c * (Real.sqrt n + Real.sqrt t))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hc₁') (Real.sqrt_nonneg t),
        mul_nonneg hc.le (sub_nonneg.mpr hsqrt)]
    refine (hsize m k e t ht).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_left _ _) he (Real.exp_pos _).le hC.le
  · have htn : t ≤ n := by omega
    have hsqrt : Real.sqrt t ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast htn)
    have he : Real.exp (-(c₂ * Real.sqrt n)) ≤
        Real.exp (-(c * (Real.sqrt n + Real.sqrt t))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hc₂') (Real.sqrt_nonneg n),
        mul_nonneg hc.le (sub_nonneg.mpr hsqrt)]
    refine ((measure_mono hsubset).trans (hspace m k e i n hn hsep)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_right _ _) he (Real.exp_pos _).le hC.le

end Rigidity.Proofs.S2
