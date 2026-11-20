import Rigidity.Proofs.S2.FiniteClusterMoment
import Rigidity.Proofs.S2.ClusterDensityResampleLaw
import Rigidity.Proofs.S2.FiniteClusterGeometry

/-!
# Tails of planar single-bond density influences

The finite-cluster tail and the endpoint bound give a uniform tail for each unnormalized
single-bond density influence.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

/-- A finite-component size has a uniform square-root exponential tail at positive levels. -/
theorem planar_finiteComponent_size_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (n : ℕ), 1 ≤ n →
      latticeBondLaw 2 p {ω | n ≤ (finiteComponentVertices ω x).card} ≤
        ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := Rigidity.Percolation.planar_finite_cluster_size_tail_at p hp
  refine ⟨C, c, hC, hc, fun x n hn => (measure_mono ?_).trans (htail x n)⟩
  intro ω hω
  change n ≤ (finiteComponentVertices ω x).card at hω
  rw [card_finiteComponentVertices] at hω
  have hf : ((openGraph ω).connectedComponentMk x).supp.Finite := by
    by_contra hnot
    have hz := (Set.not_finite.mp hnot).ncard
    omega
  exact ⟨hf, hω⟩

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

/-- The probability of a nonzero density influence decays with coordinate separation between
the resampled bond and the counting cube. -/
theorem planar_density_influence_spatial_tail (p : unitInterval)
    (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (m : ℕ) (k : Vertex 2) (e : Bond 2)
      (i : Fin 2) (n : ℕ), 1 ≤ n →
      (∀ x ∈ triadicCube 2 m k, ∀ y ∈ e.val, (n : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)|) →
      ((latticeBondLaw 2 p).prod (latticeBondLaw 2 p))
        {q | infiniteClusterCount (triadicCube 2 m k) q.1 ≠
          infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e)} ≤
        ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt n))) := by
  classical
  obtain ⟨C, c, hC, hc, htail⟩ := planar_finiteComponent_size_tail p hp
  refine ⟨4 * C, c, by positivity, hc, fun m k e i n hn hsep => ?_⟩
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
  have hsub : {q : Configuration 2 × Configuration 2 |
      infiniteClusterCount (triadicCube 2 m k) q.1 ≠
        infiniteClusterCount (triadicCube 2 m k) (resampleBond q.1 q.2 e)} ⊆
      ⋃ y ∈ S, A y := by
    intro q hq
    obtain ⟨y, hy, hsize⟩ := nonzero_influence_large_finite_component m k q.1 q.2 e i n hsep hq
    refine Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨Sym2.mem_toFinset.mpr hy, ?_⟩⟩
    rcases hsize with h | h
    · left
      exact_mod_cast h.le
    · right
      exact_mod_cast h.le
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

end Rigidity.Proofs.S2
