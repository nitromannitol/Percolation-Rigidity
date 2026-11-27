import Rigidity.Proofs.Corrector.GeneralLocalGradientDom
import Rigidity.Proofs.Corrector.GeneralLemmaThreeTwoStepTwo
import Rigidity.Proofs.WeakPoincare.VeryGood
import PercolationClusterHomogenization.Percolation.Pisztora.FiniteClusters

/-!
# The local gradient bound dominates the corrector with high probability on `ℤᵈ`

The local gradient bound dominates the corrector at the origin on the event `LocalGradGood` that
the local cluster at scale `R` lies in the infinite cluster and the corrector of slope `e_i` rooted
at the origin is at most `R` on it (`planeGrad_le_localGrad`). Its complement is rare
(`measure_not_localGradGood_le`, for `d ≥ 3`):

* a point of the local cluster outside the infinite cluster lies in a finite cluster joined to
  the boundary of `B(0, 2R)`, hence of at least `R + 1` points (`le_card_support_of_walk`, a
  discrete intermediate value theorem along walks); for `d ≥ 3` the finite clusters have the tail
  `C exp(-c N^{1/d})` (`exists_finite_cluster_card_le`);
* the corrector oscillates by at most `Z` on the Euclidean ball of radius `2dR`, which contains
  `B(0, R)` (`exists_osc_correctorDiff`, the quantitative sublinearity (1.22) of Armstrong and
  Dario), with `Z ≤ O_s(C (2dR)^{1-δ})`, and `P(Z > R) ≤ 2 exp(-(R/θ)^s)`
  (`Rigidity.WeakPoincare.measure_lt_le_of_isOsBond`).

This is the planar file `DarioLocalGradientProb` on `ℤᵈ`. The planar tail `C exp(-c √N)` of the
finite clusters becomes `C exp(-c N^{1/d})`, the factor `(2R + 1)²` of the union bound over
`B(0, R)` becomes `(2R + 1)^d`, the Euclidean radius `3R` of `B(0, R)` becomes `2dR`, and the
bound `1 + 4(localGrad + 1)` of the plane gradient becomes `1 + 2d(localGrad + 1)`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare.GeneralDim
open scoped Classical ENNReal

variable {d : ℕ}

/-- **A discrete intermediate value theorem along walks**: every value of a coordinate between its
values at the ends of an open walk is taken on the walk. -/
theorem exists_mem_support_coord_eq {ω : Configuration d} (i : Fin d) :
    ∀ {a b : Vertex d} (W : (openGraph ω).Walk a b) (t : ℤ), min (a i) (b i) ≤ t →
      t ≤ max (a i) (b i) → ∃ v ∈ W.support, v i = t
  | _, _, .nil, t, h1, h2 => ⟨_, SimpleGraph.Walk.start_mem_support _, by
      simp only [min_self, max_self] at h1 h2; omega⟩
  | a, b, .cons (v := c) h W', t, h1, h2 => by
      by_cases hc : min (c i) (b i) ≤ t ∧ t ≤ max (c i) (b i)
      · obtain ⟨v, hv, hvt⟩ := exists_mem_support_coord_eq i W' t hc.1 hc.2
        exact ⟨v, by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv, hvt⟩
      · refine ⟨a, SimpleGraph.Walk.start_mem_support _, ?_⟩
        have hac : |a i - c i| ≤ 1 := by exact_mod_cast abs_sub_le_one_of_adj h i
        rw [abs_le] at hac
        rw [not_and_or, not_le, not_le] at hc
        rcases hc with hc | hc <;> omega

/-- A walk between points `R` apart in a coordinate has at least `R + 1` distinct points. -/
theorem le_card_support_of_walk {ω : Configuration d} {a b : Vertex d}
    (W : (openGraph ω).Walk a b) (i : Fin d) {R : ℕ} (h : (R : ℤ) ≤ |b i - a i|) :
    R + 1 ≤ W.support.toFinset.card := by
  have hsub : Finset.Icc (min (a i) (b i)) (max (a i) (b i)) ⊆
      W.support.toFinset.image (fun v => v i) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨v, hv, hvt⟩ := exists_mem_support_coord_eq i W t ht.1 ht.2
    exact Finset.mem_image.2 ⟨v, List.mem_toFinset.2 hv, hvt⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := W.support.toFinset) (f := fun v => v i)
  rw [Int.card_Icc] at h1
  have : (R : ℤ) + 1 ≤ max (a i) (b i) + 1 - min (a i) (b i) := by
    rcases le_total (a i) (b i) with hab | hab
    · rw [abs_of_nonneg (sub_nonneg.2 hab)] at h
      rw [min_eq_left hab, max_eq_right hab]
      omega
    · rw [abs_of_nonpos (sub_nonpos.2 hab)] at h
      rw [min_eq_right hab, max_eq_left hab]
      omega
  omega

section Planes

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The event of the domination of the corrector by the local gradient bound at scale `R`. -/
def LocalGradGood (i : Fin d) (R : ℕ) (ω : Configuration d) : Prop :=
  (∀ y ∈ localCluster R ω, ω ∈ infiniteComponentEvent y) ∧
    ∀ y ∈ localCluster R ω, |correctorDiff hG hGv (Pi.single i 1) ω y 0| ≤ R

/-- **On the good event the plane gradient bound at the origin is dominated.** -/
theorem planeGrad_le_localGrad {ω : Configuration d} (hω : ω ∈ G) {i : Fin d} {R : ℕ}
    (hR : 1 ≤ R) (hgood : LocalGradGood hG hGv i R ω) :
    planeGrad hG hGv i ω 0 ≤ 1 + 2 * d * (localGrad R ω + 1) := by
  have hJ0 := localGrad_nonneg ω hR
  have hcD : ∀ w, (openGraph ω).Adj 0 w →
      |correctorDiff hG hGv (Pi.single i 1) ω 0 w| ≤ localGrad R ω + 1 := by
    intro w hw
    by_cases h0 : ω ∈ infiniteComponentEvent 0
    · exact abs_correctorDiff_le_localGrad hG hGv hω hR h0 hgood.1 hgood.2 hw
    · have hw' : ω ∉ infiniteComponentEvent w := fun h =>
        h0 (mem_infiniteComponentEvent_of_adj hw.symm h)
      have : correctorDiff hG hGv (Pi.single i 1) ω 0 w = 0 := by
        unfold correctorDiff
        rw [dif_neg fun h => hw' h.2]
      rw [this, abs_zero]
      linarith
  unfold planeGrad
  have hterm : ∀ k : Fin d, (if EdgeOpen ω ((0 : Vertex d), k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω ((0 : Vertex d) - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 - LatticeProb.unit k)| else 0) ≤
      2 * (localGrad R ω + 1) := by
    intro k
    have h1 : (if EdgeOpen ω ((0 : Vertex d), k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 + LatticeProb.unit k)| else 0) ≤
        localGrad R ω + 1 := by
      split_ifs with hk
      · exact hcD _ hk
      · linarith
    have h2 : (if EdgeOpen ω ((0 : Vertex d) - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 - LatticeProb.unit k)| else 0) ≤
        localGrad R ω + 1 := by
      split_ifs with hk
      · refine hcD _ ?_
        have : (openGraph ω).Adj (0 - LatticeProb.unit k)
            (0 - LatticeProb.unit k + LatticeProb.unit k) := hk
        rw [sub_add_cancel] at this
        exact this.symm
      · linarith
    linarith
  have := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm k
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

/-- **The domination fails with small probability**, for `d ≥ 3`. -/
theorem measure_not_localGradGood_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ C₁ c₁ s δ C₂ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ 0 < s ∧ 0 < δ ∧ 0 < C₂ ∧ ∀ (i : Fin d) (R : ℕ),
      1 ≤ R → latticeBondLaw d p {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω} ≤
        ENNReal.ofReal ((2 * R + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (2 * (d : ℝ) * R) ^ (1 - δ))) ^ s)) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, htail⟩ := exists_finite_cluster_card_le hd hpc
  obtain ⟨s, δ, C₂, hs, hδ, hδ1, hC₂, hosc⟩ :=
    exists_osc_correctorDiff hG hGv (by omega) hpc hp1
  refine ⟨C₁, c₁, s, δ, C₂, hC₁, hc₁, hs, hδ, hC₂, fun i R hR => ?_⟩
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hdR : 0 < (d : ℝ) * R := mul_pos (by linarith) (by linarith)
  obtain ⟨Z, hZm, hZ0, hZO, hZ⟩ := hosc i (2 * (d : ℝ) * R) (by nlinarith)
  set S₁ := {ω : Configuration d | ∃ y ∈ supBox (0 : Vertex d) R,
    {y' | (openGraph ω).Reachable y y'}.Finite ∧
      R + 1 ≤ {y' | (openGraph ω).Reachable y y'}.ncard} with hS₁
  set N := {ω : Configuration d | ¬ (ω ∈ G → ∀ a b : Vertex d, ω ∈ infiniteComponentEvent a →
      ω ∈ infiniteComponentEvent b → ‖latticeEuclideanEmbedding a‖ < 2 * (d : ℝ) * R →
      ‖latticeEuclideanEmbedding b‖ < 2 * (d : ℝ) * R →
      |correctorDiff hG hGv (Pi.single i 1) ω a b| ≤ Z ω)} with hN
  have hN0 : latticeBondLaw d p N = 0 := ae_iff.1 hZ
  have hsub : {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω} ⊆ S₁ ∪ (N ∪ {ω | (R : ℝ) < Z ω}) := by
    rintro ω ⟨hωG, hbad⟩
    by_cases hA : ∀ y ∈ localCluster R ω, ω ∈ infiniteComponentEvent y
    · right
      have hb : ¬ ∀ y ∈ localCluster R ω, |correctorDiff hG hGv (Pi.single i 1) ω y 0| ≤ R :=
        fun h => hbad ⟨hA, h⟩
      by_cases hN' : ω ∈ N
      · exact Or.inl hN'
      · right
        push Not at hb
        obtain ⟨y, hy, hyR⟩ := hb
        simp only [hN, Set.mem_setOf_eq, not_not] at hN'
        by_cases h0 : ω ∈ infiniteComponentEvent 0
        · have hyB := (Finset.mem_filter.1 hy).1
          have hnorm : ∀ v ∈ supBox (0 : Vertex d) R,
              ‖latticeEuclideanEmbedding v‖ < 2 * (d : ℝ) * R := by
            intro v hv
            have h1 := norm_latticeEuclideanEmbedding_le_of_abs_le (Nat.cast_nonneg R)
              fun k => (by exact_mod_cast abs_le_of_mem_supBox_zero hv k :
                |((v k : ℤ) : ℝ)| ≤ R)
            linarith
          have h0B : (0 : Vertex d) ∈ supBox (0 : Vertex d) R := by
            rw [mem_supBox]; intro k; simp
          have := hN' hωG y 0 (hA y hy) h0 (hnorm y hyB) (hnorm 0 h0B)
          simp only [Set.mem_setOf_eq]
          linarith
        · exfalso
          have : correctorDiff hG hGv (Pi.single i 1) ω y 0 = 0 := by
            unfold correctorDiff
            rw [dif_neg fun h => h0 h.2]
          rw [this, abs_zero] at hyR
          linarith
    · left
      push Not at hA
      obtain ⟨y, hy, hyinf⟩ := hA
      obtain ⟨hyR, p', hp', ⟨k, hk⟩, W, hW⟩ := Finset.mem_filter.1 hy
      have hsuppE : ((openGraph ω).connectedComponentMk y).supp =
          {y' | (openGraph ω).Reachable y y'} := by
        ext y'
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      have hfin : {y' | (openGraph ω).Reachable y y'}.Finite := by
        rw [← hsuppE]
        exact Set.not_infinite.1 hyinf
      refine ⟨y, hyR, hfin, ?_⟩
      have hyk := abs_le_of_mem_supBox_zero hyR k
      have hdist : (R : ℤ) ≤ |p' k - y k| := by
        have t := abs_sub_abs_le_abs_sub (p' k) (y k)
        push_cast at hk
        omega
      have hcard := le_card_support_of_walk W k hdist
      have hsupp : (W.support.toFinset : Set (Vertex d)) ⊆
          {y' | (openGraph ω).Reachable y y'} := fun v hv =>
        (W.takeUntil v (List.mem_toFinset.1 (Finset.mem_coe.1 hv))).reachable
      have := Set.ncard_le_ncard hsupp hfin
      rw [Set.ncard_coe_finset] at this
      omega
  have hS₁ : latticeBondLaw d p S₁ ≤
      ENNReal.ofReal ((2 * R + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹)))) := by
    have e : S₁ = ⋃ y ∈ supBox (0 : Vertex d) R, {ω : Configuration d |
        {y' | (openGraph ω).Reachable y y'}.Finite ∧
          R + 1 ≤ {y' | (openGraph ω).Reachable y y'}.ncard} := by
      ext ω
      simp only [hS₁, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [e]
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hy : ∀ y ∈ supBox (0 : Vertex d) R, latticeBondLaw d p {ω : Configuration d |
        {y' | (openGraph ω).Reachable y y'}.Finite ∧
          R + 1 ≤ {y' | (openGraph ω).Reachable y y'}.ncard} ≤
        ENNReal.ofReal (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹))) := by
      intro y _
      have := htail y (R + 1)
      push_cast at this
      exact this
    refine (Finset.sum_le_sum hy).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, card_supBox, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  have hθ : 0 < C₂ * (2 * (d : ℝ) * R) ^ (1 - δ) :=
    mul_pos hC₂ (Real.rpow_pos_of_pos (by linarith) _)
  have hZtail := Rigidity.WeakPoincare.measure_lt_le_of_isOsBond hZ0 hθ hs hZO
    (show (0 : ℝ) ≤ R by positivity)
  calc latticeBondLaw d p {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω}
      ≤ latticeBondLaw d p (S₁ ∪ (N ∪ {ω | (R : ℝ) < Z ω})) := measure_mono hsub
    _ ≤ latticeBondLaw d p S₁ + (latticeBondLaw d p N + latticeBondLaw d p {ω | (R : ℝ) < Z ω}) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal ((2 * R + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ (d : ℝ)⁻¹)))) +
        (0 + ENNReal.ofReal
          (2 * Real.exp (-((R : ℝ) / (C₂ * (2 * (d : ℝ) * R) ^ (1 - δ))) ^ s))) := by
        rw [hN0]
        exact add_le_add hS₁ (add_le_add le_rfl hZtail)
    _ = _ := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]

end Planes

end Rigidity.Corrector.GeneralDim
