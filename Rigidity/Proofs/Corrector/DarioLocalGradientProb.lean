import Rigidity.Proofs.Corrector.DarioLocalGradientDom
import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoHolds
import PercolationClusterHomogenization.Proofs.Percolation.PlanarFiniteCluster

/-!
# The local gradient bound dominates the corrector with high probability

The local gradient bound dominates the corrector at the origin on the event `LocalGradGood` that
the local cluster at scale `R` lies in the infinite cluster and the corrector of slope `e_i` rooted
at the origin is at most `R` on it (`planeGrad_le_localGrad`). Its complement is rare
(`measure_not_localGradGood_le`):

* a point of the local cluster outside the infinite cluster lies in a finite cluster joined to
  the boundary of `B(0, 2R)`, hence of at least `R + 1` points (`le_card_support_of_walk`, a
  discrete intermediate value theorem along walks); the planar finite clusters have the tail
  `C exp(-c √N)` (`planar_finite_cluster_size_tail_at`);
* the corrector oscillates by at most `Z` on the ball of radius `3R`
  (`exists_osc_correctorDiff`,
  the quantitative sublinearity (1.22) of Armstrong and Dario), with `Z ≤ O_s(C R^{1-δ})`, and
  `P(Z > R) ≤ 2 exp(-(R/θ)^s)` (`measure_lt_le_of_isOsBond`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- **A discrete intermediate value theorem along walks**: every value of a coordinate between its
values at the ends of an open walk is taken on the walk. -/
theorem exists_mem_support_coord_eq {ω : Configuration 2} (i : Fin 2) :
    ∀ {a b : Vertex 2} (W : (openGraph ω).Walk a b) (t : ℤ), min (a i) (b i) ≤ t →
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
theorem le_card_support_of_walk {ω : Configuration 2} {a b : Vertex 2}
    (W : (openGraph ω).Walk a b) (i : Fin 2) {R : ℕ} (h : (R : ℤ) ≤ |b i - a i|) :
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

/-- **Markov's inequality for `𝒪_s` bounds**: `P(X > t) ≤ 2 exp(-(t/θ)^s)`. -/
theorem measure_lt_le_of_isOsBond {p : unitInterval} {X : Configuration 2 → ℝ} {s θ : ℝ}
    (hθ : 0 < θ) (hs : 0 < s) (hX : IsOsBond 2 p X s θ) {t : ℝ}
    (ht : 0 ≤ t) :
    latticeBondLaw 2 p {ω | t < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(t / θ) ^ s)) := by
  obtain ⟨hint, hle⟩ := hX
  set f : Configuration 2 → ℝ := fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s) with hf
  have hf0 : 0 ≤ᵐ[latticeBondLaw 2 p] f := ae_of_all _ fun ω => (Real.exp_pos _).le
  have hsub : {ω | t < X ω} ⊆ {ω | Real.exp ((t / θ) ^ s) ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, hf]
    refine Real.exp_le_exp.2 ?_
    have h1 : t / θ ≤ max (X ω / θ) 0 :=
      (div_le_div_of_nonneg_right hω.le hθ.le).trans (le_max_left _ _)
    exact Real.rpow_le_rpow (div_nonneg ht hθ.le) h1 hs.le
  have hmark := mul_meas_ge_le_integral_of_nonneg hf0 hint (Real.exp ((t / θ) ^ s))
  have hpos := Real.exp_pos ((t / θ) ^ s)
  have hreal : (latticeBondLaw 2 p).real {ω | Real.exp ((t / θ) ^ s) ≤ f ω} ≤
      2 * Real.exp (-(t / θ) ^ s) := by
    rw [Real.exp_neg]
    rw [le_mul_inv_iff₀ hpos]
    linarith [mul_comm (Real.exp ((t / θ) ^ s))
      ((latticeBondLaw 2 p).real {ω | Real.exp ((t / θ) ^ s) ≤ f ω})]
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

section Planes

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The event of the domination of the corrector by the local gradient bound at scale `R`. -/
def LocalGradGood (i : Fin 2) (R : ℕ) (ω : Configuration 2) : Prop :=
  (∀ y ∈ localCluster R ω, ω ∈ infiniteComponentEvent y) ∧
    ∀ y ∈ localCluster R ω, |correctorDiff hG hGv (Pi.single i 1) ω y 0| ≤ R

/-- **On the good event the plane gradient bound at the origin is dominated.** -/
theorem planeGrad_le_localGrad {ω : Configuration 2} (hω : ω ∈ G) {i : Fin 2} {R : ℕ}
    (hR : 1 ≤ R) (hgood : LocalGradGood hG hGv i R ω) :
    planeGrad hG hGv i ω 0 ≤ 1 + 4 * (localGrad R ω + 1) := by
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
  have hterm : ∀ k : Fin 2, (if EdgeOpen ω ((0 : Vertex 2), k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 + LatticeProb.unit k)| else 0) +
      (if EdgeOpen ω ((0 : Vertex 2) - LatticeProb.unit k, k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 - LatticeProb.unit k)| else 0) ≤
      2 * (localGrad R ω + 1) := by
    intro k
    have h1 : (if EdgeOpen ω ((0 : Vertex 2), k) then
        |correctorDiff hG hGv (Pi.single i 1) ω 0 (0 + LatticeProb.unit k)| else 0) ≤
        localGrad R ω + 1 := by
      split_ifs with hk
      · exact hcD _ hk
      · linarith
    have h2 : (if EdgeOpen ω ((0 : Vertex 2) - LatticeProb.unit k, k) then
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
  push_cast at this
  linarith

/-- **The domination fails with small probability.** -/
theorem measure_not_localGradGood_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) :
    ∃ C₁ c₁ s δ C₂ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ 0 < s ∧ 0 < δ ∧ 0 < C₂ ∧ ∀ (i : Fin 2) (R : ℕ),
      1 ≤ R → latticeBondLaw 2 p {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω} ≤
        ENNReal.ofReal ((2 * R + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s)) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, htail⟩ := planar_finite_cluster_size_tail_at p hpc
  obtain ⟨s, δ, C₂, hs, hδ, hδ1, hC₂, hosc⟩ :=
    exists_osc_correctorDiff hG hGv correctorOscSublinearTwo_holds hpc hp1
  refine ⟨C₁, c₁, s, δ, C₂, hC₁, hc₁, hs, hδ, hC₂, fun i R hR => ?_⟩
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  obtain ⟨Z, hZm, hZ0, hZO, hZ⟩ := hosc i (3 * R) (by linarith)
  set S₁ := {ω : Configuration 2 | ∃ y ∈ supBox (0 : Vertex 2) R,
    ((openGraph ω).connectedComponentMk y).supp.Finite ∧
      R + 1 ≤ ((openGraph ω).connectedComponentMk y).supp.ncard} with hS₁
  set N := {ω : Configuration 2 | ¬ (ω ∈ G → ∀ a b : Vertex 2, ω ∈ infiniteComponentEvent a →
      ω ∈ infiniteComponentEvent b → ‖latticeEuclideanEmbedding a‖ < 3 * R →
      ‖latticeEuclideanEmbedding b‖ < 3 * R →
      |correctorDiff hG hGv (Pi.single i 1) ω a b| ≤ Z ω)} with hN
  have hN0 : latticeBondLaw 2 p N = 0 := ae_iff.1 hZ
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
          have hnorm : ∀ v ∈ supBox (0 : Vertex 2) R, ‖latticeEuclideanEmbedding v‖ < 3 * R := by
            intro v hv
            have h1 := norm_latticeEuclideanEmbedding_le_sum v
            have h2 := abs_le_of_mem_supBox_zero hv 0
            have h3 := abs_le_of_mem_supBox_zero hv 1
            have h2' : |((v 0 : ℤ) : ℝ)| ≤ R := by exact_mod_cast h2
            have h3' : |((v 1 : ℤ) : ℝ)| ≤ R := by exact_mod_cast h3
            linarith
          have h0B : (0 : Vertex 2) ∈ supBox (0 : Vertex 2) R := by
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
      refine ⟨y, hyR, Set.not_infinite.1 hyinf, ?_⟩
      have hyk := abs_le_of_mem_supBox_zero hyR k
      have hdist : (R : ℤ) ≤ |p' k - y k| := by
        have t := abs_sub_abs_le_abs_sub (p' k) (y k)
        push_cast at hk
        omega
      have hcard := le_card_support_of_walk W k hdist
      have hsupp : (W.support.toFinset : Set (Vertex 2)) ⊆
          ((openGraph ω).connectedComponentMk y).supp := by
        intro v hv
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact (SimpleGraph.ConnectedComponent.sound
          (W.takeUntil v (List.mem_toFinset.1 (Finset.mem_coe.1 hv))).reachable).symm
      have := Set.ncard_le_ncard hsupp (Set.not_infinite.1 hyinf)
      rw [Set.ncard_coe_finset] at this
      omega
  have hS₁ : latticeBondLaw 2 p S₁ ≤
      ENNReal.ofReal ((2 * R + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1))))) := by
    have e : S₁ = ⋃ y ∈ supBox (0 : Vertex 2) R, {ω : Configuration 2 |
        ((openGraph ω).connectedComponentMk y).supp.Finite ∧
          R + 1 ≤ ((openGraph ω).connectedComponentMk y).supp.ncard} := by
      ext ω
      simp only [hS₁, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [e]
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hy : ∀ y ∈ supBox (0 : Vertex 2) R, latticeBondLaw 2 p {ω : Configuration 2 |
        ((openGraph ω).connectedComponentMk y).supp.Finite ∧
          R + 1 ≤ ((openGraph ω).connectedComponentMk y).supp.ncard} ≤
        ENNReal.ofReal (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) := by
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
  have hZtail := measure_lt_le_of_isOsBond (by positivity) hs hZO
    (show (0 : ℝ) ≤ R by positivity)
  calc latticeBondLaw 2 p {ω | ω ∈ G ∧ ¬ LocalGradGood hG hGv i R ω}
      ≤ latticeBondLaw 2 p (S₁ ∪ (N ∪ {ω | (R : ℝ) < Z ω})) := measure_mono hsub
    _ ≤ latticeBondLaw 2 p S₁ + (latticeBondLaw 2 p N + latticeBondLaw 2 p {ω | (R : ℝ) < Z ω}) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal ((2 * R + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1))))) +
        (0 + ENNReal.ofReal (2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s))) := by
        rw [hN0]
        exact add_le_add hS₁ (add_le_add le_rfl hZtail)
    _ = _ := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]

end Planes

end Rigidity.Corrector
