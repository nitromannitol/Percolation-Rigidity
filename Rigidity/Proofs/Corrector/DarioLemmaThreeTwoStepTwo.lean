import Rigidity.Proofs.Corrector.DarioLemmaThreeTwoMoments

/-!
# Dario, Lemma 3.2, Step 2: the stationary coarsened gradient has mean zero over a period

Step 2 of the proof of Lemma 3.2 uses the quantitative sublinearity of the corrector (Dario,
(2.1), from Armstrong and Dario, (1.22)): `osc_{𝒞_∞ ∩ B_R} χ_p ≤ O_s(C |p| R^{1-δ})`, here the
hypothesis `CorrectorOscSublinearTwo`. With it, the sum of `∇_j[χ]_{𝒫_stat^k}` along a segment
of length `N` in the direction `e_j`, which telescopes to `χ(z̄_stat(y + N e_j)) - χ(z̄_stat(y))`,
has expectation `O(N^{1-δ})`; by the stationarity under `3^k ℤ²`, the sum over `m` periods is `m`
times the sum over one period, which therefore vanishes.

* `CorrectorOscSublinearTwo`: (1.22) in dimension two (hypothesis);
* `sum_statGrad_eq`: the telescoping of the coarsened gradient along a segment;
* `exists_lintegral_abs_statSegment_le`: `E|χ(z̄_stat(y + N e_j)) - χ(z̄_stat(y))| ≤ C₂ N^{1-δ} + C₃`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

/-- **Armstrong and Dario, (1.22)** (Dario, (2.1); hypothesis): the oscillation of the correctors on
`𝒞_∞ ∩ B_R` is at most `O_s(C |q| R^{1-δ})`, for some `δ ∈ (0, 1]`. -/
def CorrectorOscSublinearTwo : Prop :=
  ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s δ C : ℝ, 0 < s ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond 2 p Z s (C * R ^ (1 - δ)) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ (q : Fin 2 → ℝ)
          (ℓ : uniqueInfiniteComponent h → ℝ), IsCorrectedPlane (uniqueInfiniteComponent h) q ℓ →
          ∀ a b : uniqueInfiniteComponent h,
            ‖latticeEuclideanEmbedding a.val‖ < R → ‖latticeEuclideanEmbedding b.val‖ < R →
            |(ℓ a - ∑ i, q i * (a.val i : ℝ)) - (ℓ b - ∑ i, q i * (b.val i : ℝ))| ≤
              (|q 0| + |q 1|) * Z ω

section Carrier

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- (1.22) for the corrector increments of the carrier. -/
theorem exists_osc_correctorDiff (h122 : CorrectorOscSublinearTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ s δ C : ℝ, 0 < s ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ ∀ (i : Fin 2) (R : ℝ), 1 ≤ R →
      ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
        IsOsBond 2 p Z s (C * R ^ (1 - δ)) ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G → ∀ a b : Vertex 2, ω ∈ infiniteComponentEvent a →
          ω ∈ infiniteComponentEvent b → ‖latticeEuclideanEmbedding a‖ < R →
          ‖latticeEuclideanEmbedding b‖ < R →
          |correctorDiff hG hGv (Pi.single i 1) ω a b| ≤ Z ω := by
  obtain ⟨s, δ, C, hs, hδ, hδ1, hC, h⟩ := h122 p hpc hp1
  refine ⟨s, δ, C, hs, hδ, hδ1, hC, fun i R hR => ?_⟩
  obtain ⟨Z, hZm, hZ0, hZO, hZ⟩ := h R hR
  refine ⟨Z, hZm, hZ0, hZO, ?_⟩
  filter_upwards [hZ] with ω hω hωG a b ha hb haR hbR
  obtain ⟨hu, -⟩ := hGv hωG
  have hinf := uniqueInfiniteComponent_infinite hu
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hωG) hinf (Pi.single i 1)
  set a' : uniqueInfiniteComponent hu := ⟨a, (mem_uniqueInfiniteComponent_iff hu a).2 ha⟩
  set b' : uniqueInfiniteComponent hu := ⟨b, (mem_uniqueInfiniteComponent_iff hu b).2 hb⟩
  have e := correctorDiff_eq hG hGv hωG hinf hℓ a' b'
  have hq : |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) 0| + |(Pi.single i (1 : ℝ) : Fin 2 → ℝ) 1| = 1 := by
    fin_cases i <;> simp
  have := hω hu (Pi.single i 1) ℓ hℓ a' b' haR hbR
  rw [hq, one_mul] at this
  change |correctorDiff hG hGv (Pi.single i 1) ω a'.val b'.val| ≤ Z ω
  rw [e]
  exact this

/-- **The telescoping of the coarsened gradient** along the segment `y, y + e_j, …, y + N e_j`. -/
theorem sum_statGrad_eq {ω : Configuration 2} (hω : ω ∈ G) {v₀ : Vertex 2}
    (h₀ : ω ∈ infiniteComponentEvent v₀) (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2) (N : ℕ) :
    ∑ t ∈ Finset.range N, statGrad hG hGv i k (y + (t : ℤ) • LatticeProb.unit j) j ω =
      correctorDiff hG hGv (Pi.single i 1) ω (statAnchor k ω (y + (N : ℤ) • LatticeProb.unit j))
        (statAnchor k ω y) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_smul, add_zero]
    have hb := statAnchor_mem_inf k y h₀
    have := correctorDiff_sub_eq hG hGv (q := Pi.single i 1) hω hb hb hb
    linarith
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold statGrad
    have e : y + ((N + 1 : ℕ) : ℤ) • LatticeProb.unit j =
        y + (N : ℤ) • LatticeProb.unit j + LatticeProb.unit j := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e]
    have h1 := statAnchor_mem_inf k (y + (N : ℤ) • LatticeProb.unit j + LatticeProb.unit j) h₀
    have h2 := statAnchor_mem_inf k (y + (N : ℤ) • LatticeProb.unit j) h₀
    have h3 := statAnchor_mem_inf k y h₀
    rw [correctorDiff_add' hG hGv hω h1 h2 h3]
    ring

/-- The chain of coarse gradients between two vertices: `|χ(z̄(a')) - χ(z̄(a))|` is at most twice
the sum of the sums of (5.10) over the lattice rectangle between `a'` and `a`. -/
theorem ofReal_abs_correctorDiff_coarseAnchors_le {ω : Configuration 2} (hω : ω ∈ G)
    (hP : PlanarPartitionEvent ω) {q : Fin 2 → ℝ} (a a' : Vertex 2)
    {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛ0 : ∀ x, 0 ≤ Λ x ω)
    (hΛ : ∀ x, ω ∈ infiniteComponentEvent x → ∀ y, (openGraph ω).Adj x y →
      |correctorDiff hG hGv q ω x y| ≤ Λ x ω) :
    ENNReal.ofReal |correctorDiff hG hGv q ω (planarCoarseAnchor ω a') (planarCoarseAnchor ω a)| ≤
      2 * ∑ u ∈ latticeBetween a' a, stepSixSum Λ u ω := by
  set b := planarCoarseAnchor ω a with hbdef
  have hb : ω ∈ infiniteComponentEvent b := infinite_planarCoarseAnchor hP a
  have ha' : ω ∈ infiniteComponentEvent (planarCoarseAnchor ω a') :=
    infinite_planarCoarseAnchor hP a'
  set w : Vertex 2 → ℝ := fun x => if ω ∈ infiniteComponentEvent x then
    correctorDiff hG hGv q ω x b else 0 with hw
  set W : Vertex 2 → ℝ := fun u => w (planarCoarseAnchor ω u) with hW
  set e : Vertex 2 → ℝ := fun u => edgeVariationIn ω (planarPartCube ω u).ninefold.vertices w
    with he
  have he0 : ∀ u, 0 ≤ e u := fun u => edgeVariationIn_nonneg _ _ _
  have hchain := abs_sub_le_of_chain (W := W) he0 (fun u u' hn => abs_coarse_step_le hP w hn)
    _ a' a le_rfl
  have hbb : correctorDiff hG hGv q ω b b = 0 := by
    have := correctorDiff_sub_eq hG hGv (q := q) hω hb hb hb
    linarith
  have hWa' : W a' = correctorDiff hG hGv q ω (planarCoarseAnchor ω a') b := by
    simp only [hW, hw]
    exact if_pos ha'
  have hWa : W a = 0 := by
    simp only [hW, hw]
    rw [← hbdef, if_pos hb, hbb]
  have hle : |W a' - W a| ≤ 2 * ∑ u ∈ latticeBetween a' a, e u := by
    have := he0 a'
    have := he0 a
    linarith
  rw [hWa', hWa, sub_zero] at hle
  calc ENNReal.ofReal |correctorDiff hG hGv q ω (planarCoarseAnchor ω a') b|
      ≤ ENNReal.ofReal (2 * ∑ u ∈ latticeBetween a' a, e u) := ENNReal.ofReal_le_ofReal hle
    _ = 2 * ∑ u ∈ latticeBetween a' a, ENNReal.ofReal (e u) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_sum_of_nonneg fun u _ => he0 u]
        simp
    _ ≤ 2 * ∑ u ∈ latticeBetween a' a, stepSixSum Λ u ω := by
        gcongr with u hu
        exact ofReal_edgeVariationIn_le_stepSixSum hG hGv hω hP hb hΛ0 hΛ u

end Carrier

/-- The lattice rectangle between two vertices within `N` in every coordinate has at most
`(N + 1)²` vertices. -/
theorem card_latticeBetween_le {a a' : Vertex 2} {N : ℕ} (h : ∀ i, |a' i - a i| ≤ N) :
    (latticeBetween a' a).card ≤ (N + 1) ^ 2 := by
  unfold latticeBetween
  rw [Fintype.card_piFinset]
  calc ∏ i : Fin 2, (Finset.Icc (min (a' i) (a i)) (max (a' i) (a i))).card
      ≤ ∏ _i : Fin 2, (N + 1) := by
        refine Finset.prod_le_prod' fun i _ => ?_
        rw [Int.card_Icc]
        have := h i
        rw [abs_le] at this
        omega
    _ = (N + 1) ^ 2 := by simp

end Rigidity.Corrector
