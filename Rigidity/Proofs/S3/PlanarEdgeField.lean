import Rigidity.Proofs.S3.PlanarCorrectorValid
import Rigidity.Proofs.S3.HomogenizedCoefficient

/-!
# Planar corrected-plane edge fields

The edge field and its integrability follow from the planar qualitative and quantitative
corrector inputs.
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation LatticeProb.External
  Rigidity.Section3 Rigidity.Steps.S3
open scoped BigOperators Classical ENNReal

namespace Rigidity.Proofs.S3

open FluxEvent HomogenizedCoefficient

theorem exists_edgeField_two (hU : SupercriticalBondUniqueness)
    (hCorr : Rigidity.External.SupercriticalBondCorrectorInputTwo) (p : unitInterval)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ G : Set (Configuration 2), MeasurableSet G ∧ latticeBondLaw 2 p G = 1 ∧
      ∃ Φ : Vertex 2 → Vertex 2 → Configuration 2 → ℝ, (∀ x y, Measurable (Φ x y)) ∧
        (∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
          ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 2) u) ∧
        IsEdgeField G Φ := by
  classical
  obtain ⟨G, hG, hG1, hvalid⟩ := exists_measurable_corrector_valid_set_two hU hCorr p hpc hp1
  obtain ⟨g, hgm, hzero, hgrad, -⟩ :=
    exists_measurable_corrector_gradients_on_valid_set G hG hvalid
  refine ⟨G, hG, hG1, fun x y ω => if hω : ω ∈ G then -g ⟨ω, hω⟩ (x, y) 0 else 0,
    fun x y => Measurable.dite (hgm (x, y) 0).neg (g := fun _ => (0 : ℝ)) measurable_const hG,
    fun ω hω => ⟨(hvalid hω).1, fun C hC => ?_⟩, fun ω hω C hC u hu x y => ?_⟩
  · have h := (hvalid hω).1
    obtain rfl := (eq_uniqueInfiniteComponent_iff h C).2 hC
    obtain ⟨o, ho⟩ := hC.nonempty
    obtain ⟨u, ⟨hu, -⟩, -⟩ := ((hvalid hω).2 h).1 (slopeE1 2) ⟨o, ho⟩
    exact ⟨u, hu⟩
  · have h := (hvalid hω).1
    obtain rfl := (eq_uniqueInfiniteComponent_iff h C).2 hC
    simp only [dif_pos hω]
    unfold edgeDifference
    split_ifs with hxy
    · have hy : y ∈ (uniqueInfiniteComponent h).supp :=
        (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp hxy.1 hxy.2
      have hg := hgrad ⟨ω, hω⟩ (slopeE1 2) u hu ⟨x, hxy.1⟩ ⟨y, hy⟩ hxy.2
      have hsum : ∑ j, slopeE1 2 j * g ⟨ω, hω⟩ (x, y) j = g ⟨ω, hω⟩ (x, y) 0 := by
        simp [slopeE1, Pi.single_apply]
      simp only [Rigidity.Section3.extend, dif_pos hxy.1, dif_pos hy]
      linarith
    · rw [hzero ⟨ω, hω⟩ (x, y) ?_ 0, neg_zero]
      rintro ⟨hinf, hadj⟩
      exact hxy ⟨(SimpleGraph.ConnectedComponent.mem_supp_iff _ _).2
        ((eq_uniqueInfiniteComponent_iff h _).2 hinf), hadj⟩


theorem integrable_sideField_two (hQ : Rigidity.External.CorrectorQuantitativeInputTwo)
    (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {G : Set (Configuration 2)} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G)
    {Φ : Vertex 2 → Vertex 2 → Configuration 2 → ℝ} (hΦm : ∀ x y, Measurable (Φ x y))
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 2) u)
    (hΦ : IsEdgeField G Φ) {j : Fin 2} (hj : j ≠ 0) :
    Integrable (Φ 0 (unit j)) (latticeBondLaw 2 p) := by
  obtain ⟨s, C, hs, hC, hM⟩ := hQ p hpc hp1 1 one_pos
  obtain ⟨M, hMm, hM0, hMos, hbound⟩ := hM 0
  refine Integrable.mono' (((integrable_of_isOsBond hs hC hMm hM0 hMos).add
    (integrable_const 2)).const_mul C) (hΦm 0 (unit j)).aestronglyMeasurable ?_
  filter_upwards [hGae, hbound] with ω hω hb
  obtain ⟨h, hexu⟩ := hex ω hω
  obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
  rw [← hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu, Real.norm_eq_abs]
  have hr : 0 ≤ M ω + 2 := by linarith [hM0 ω]
  unfold edgeDifference
  split_ifs with h0
  · have hj' : unit j ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp h0.1 h0.2
    let a : uniqueInfiniteComponent h := ⟨0, h0.1⟩
    let b : uniqueInfiniteComponent h := ⟨unit j, hj'⟩
    have hna : ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding 0‖ < M ω + 2 := by
      simp only [a, sub_self, norm_zero]
      linarith [hM0 ω]
    have hnb : ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding 0‖ < M ω + 2 :=
      (norm_latticeEuclideanEmbedding_unit_sub_zero j).trans_lt (by linarith [hM0 ω])
    have hab : (componentGraph (uniqueInfiniteComponent h)).Adj a b :=
      ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).2 h0.2
    have hbd := hb h (slopeE1 2) u hu (M ω + 2) (by linarith) a a a b hna hna hna hnb hab
    have hqa : ∑ i, slopeE1 2 i * ((a.val i : ℤ) : ℝ) = 0 := by simp [a]
    have hqb : ∑ i, slopeE1 2 i * ((b.val i : ℤ) : ℝ) = 0 := by
      simp [b, slopeE1, unit, Pi.single_apply, hj]
    have hq : ∑ i, |slopeE1 2 i| = 1 := by
      rw [Finset.sum_eq_single (0 : Fin 2) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1]
    rw [hqa, hqb, hq, sub_self, abs_zero, zero_add, Real.rpow_one, sub_zero, sub_zero,
      mul_one] at hbd
    have e0 : Rigidity.Section3.extend (uniqueInfiniteComponent h) u 0 = u a := dif_pos h0.1
    have ej : Rigidity.Section3.extend (uniqueInfiniteComponent h) u (unit j) = u b :=
      dif_pos hj'
    rw [e0, ej]
    exact hbd
  · rw [abs_zero]
    exact mul_nonneg hC.le hr


theorem integrable_edgeField_unit_two (hQ : Rigidity.External.CorrectorQuantitativeInputTwo) (p : unitInterval) (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {G : Set (Configuration 2)} (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G)
    {Φ : Vertex 2 → Vertex 2 → Configuration 2 → ℝ} (hΦm : ∀ x y, Measurable (Φ x y))
    (hex : ∀ ω ∈ G, HasUniqueInfiniteOpenComponent ω ∧
      ∀ C : OpenComponent ω, C.supp.Infinite → ∃ u, IsCorrectedPlane C (slopeE1 2) u)
    (hΦ : IsEdgeField G Φ) (k : Fin 2) :
    Integrable (Φ (unit k) 0) (latticeBondLaw 2 p) := by
  obtain ⟨s, C, hs, hC, hM⟩ := hQ p hpc hp1 1 one_pos
  obtain ⟨M, hMm, hM0, hMos, hbound⟩ := hM 0
  refine Integrable.mono' ((((integrable_of_isOsBond hs hC hMm hM0 hMos).add
    (integrable_const 2)).const_mul C).add (integrable_const 1))
    (hΦm (unit k) 0).aestronglyMeasurable ?_
  filter_upwards [hGae, hbound] with ω hω hb
  obtain ⟨h, hexu⟩ := hex ω hω
  obtain ⟨u, hu⟩ := hexu _ (uniqueInfiniteComponent_infinite h)
  rw [← hΦ ω hω _ (uniqueInfiniteComponent_infinite h) u hu, Real.norm_eq_abs]
  have hr : 0 ≤ C * (M ω + 2) := mul_nonneg hC.le (by linarith [hM0 ω])
  unfold edgeDifference
  split_ifs with h0
  · have h0' : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp :=
      (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp h0.1 h0.2
    let a : uniqueInfiniteComponent h := ⟨unit k, h0.1⟩
    let b : uniqueInfiniteComponent h := ⟨0, h0'⟩
    have hna : ‖latticeEuclideanEmbedding a.val - latticeEuclideanEmbedding 0‖ < M ω + 2 :=
      (norm_latticeEuclideanEmbedding_unit_sub_zero k).trans_lt (by linarith [hM0 ω])
    have hnb : ‖latticeEuclideanEmbedding b.val - latticeEuclideanEmbedding 0‖ < M ω + 2 := by
      simp only [b, sub_self, norm_zero]
      linarith [hM0 ω]
    have hab : (componentGraph (uniqueInfiniteComponent h)).Adj a b :=
      ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).2 h0.2
    have hbd := hb h (slopeE1 2) u hu (M ω + 2) (by linarith) a b a b hna hnb hna hnb hab
    have hqa : ∑ i, slopeE1 2 i * ((a.val i : ℤ) : ℝ) = (((unit k : Vertex 2) 0 : ℤ) : ℝ) := by
      rw [Finset.sum_eq_single (0 : Fin 2) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1, a]
    have hqa1 : |(((unit k : Vertex 2) 0 : ℤ) : ℝ)| ≤ 1 := by
      by_cases hk : k = 0
      · subst hk
        simp [unit]
      · simp [unit, Ne.symm hk]
    have hqb : ∑ i, slopeE1 2 i * ((b.val i : ℤ) : ℝ) = 0 := by simp [b]
    have hq : ∑ i, |slopeE1 2 i| = 1 := by
      rw [Finset.sum_eq_single (0 : Fin 2) (fun i _ hi => by simp [slopeE1, hi]) (by simp)]
      simp [slopeE1]
    rw [hqa, hqb, hq, Real.rpow_one, sub_zero, mul_one] at hbd
    have ea : Rigidity.Section3.extend (uniqueInfiniteComponent h) u (unit k) = u a := dif_pos h0.1
    have eb : Rigidity.Section3.extend (uniqueInfiniteComponent h) u 0 = u b := dif_pos h0'
    rw [ea, eb]
    have h1 : |u a - (((unit k : Vertex 2) 0 : ℤ) : ℝ) - u b| ≤ C * (M ω + 2) := by
      linarith [abs_nonneg (u a - (((unit k : Vertex 2) 0 : ℤ) : ℝ) - u b)]
    calc |u a - u b| = |(u a - (((unit k : Vertex 2) 0 : ℤ) : ℝ) - u b) +
          (((unit k : Vertex 2) 0 : ℤ) : ℝ)| := by ring_nf
      _ ≤ |u a - (((unit k : Vertex 2) 0 : ℤ) : ℝ) - u b| + |(((unit k : Vertex 2) 0 : ℤ) : ℝ)| :=
          abs_add_le _ _
      _ ≤ C * (M ω + 2) + 1 := add_le_add h1 hqa1
  · rw [abs_zero]
    show (0 : ℝ) ≤ C * (M ω + 2) + 1
    linarith [hr]


end Rigidity.Proofs.S3
