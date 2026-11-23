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

section Segment

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- `(N + 1)^4 e^{-N/c} ≤ 24 c^4 e^{1/c}`. -/
theorem pow_four_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 ≤ N) :
    (N + 1) ^ 4 * Real.exp (-(N / c)) ≤ 24 * c ^ 4 * Real.exp (1 / c) := by
  have h := Real.pow_div_factorial_le_exp ((N + 1) / c) (by positivity) 4
  rw [div_pow, Nat.factorial, Nat.factorial, Nat.factorial, Nat.factorial, Nat.factorial] at h
  norm_num at h
  have e : Real.exp ((N + 1) / c) = Real.exp (N / c) * Real.exp (1 / c) := by
    rw [← Real.exp_add, add_div]
  rw [e] at h
  have hc4 : 0 < c ^ 4 := by positivity
  rw [div_div, div_le_iff₀ (by positivity)] at h
  have hen : Real.exp (-(N / c)) * Real.exp (N / c) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos : 0 < Real.exp (-(N / c)) := Real.exp_pos _
  calc (N + 1) ^ 4 * Real.exp (-(N / c))
      ≤ Real.exp (N / c) * Real.exp (1 / c) * (c ^ 4 * 24) * Real.exp (-(N / c)) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = 24 * c ^ 4 * Real.exp (1 / c) * (Real.exp (-(N / c)) * Real.exp (N / c)) := by ring
    _ = 24 * c ^ 4 * Real.exp (1 / c) := by rw [hen, mul_one]

/-- **Dario, Lemma 3.2, Step 2, the segments**: from (1.22),
`E|χ(z̄_stat(y + N e_j)) - χ(z̄_stat(y))| ≤ C₂ N^{1-δ} + C₃` for `N ≥ 1`. -/
theorem exists_lintegral_abs_statSegment_le (hR3 : ArmstrongDarioOrderZeroTwo)
    (h122 : CorrectorOscSublinearTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (i : Fin 2) (k : ℕ) (y : Vertex 2) (j : Fin 2), ∃ C₂ C₃ : ℝ,
      0 ≤ C₂ ∧ 0 ≤ C₃ ∧ ∀ N : ℕ, 1 ≤ N →
        ∫⁻ ω, ENNReal.ofReal |correctorDiff hG hGv (Pi.single i 1) ω
          (statAnchor k ω (y + (N : ℤ) • LatticeProb.unit j)) (statAnchor k ω y)|
            ∂latticeBondLaw 2 p ≤ ENNReal.ofReal (C₂ * (N : ℝ) ^ (1 - δ) + C₃) := by
  obtain ⟨Λ, A, κ, hA0, -, hΛm, hΛ0, hlip, hmom6⟩ := stepSix_data hG hGv hR3 hpc hp1 hGae
  obtain ⟨θ, hθ, hexp⟩ := (planar_meshed_partition_estimates hpc).2.1
  obtain ⟨K₁, θ₀, hK₁, hθ₀, hsq⟩ := exists_lintegral_sq_statDiscrepancy_le hG hGv hR3 hpc hp1 hGae
  obtain ⟨s, δ, C, hs, hδ, hδ1, hC, hosc⟩ := exists_osc_correctorDiff hG hGv h122 hpc hp1
  refine ⟨δ, hδ, hδ1, fun i k y j => ?_⟩
  set b : ℝ := ‖latticeEuclideanEmbedding y‖ with hb
  have hb0 : 0 ≤ b := norm_nonneg _
  set Nk : ℝ := (((2 * 3 ^ k + 1) ^ 2 : ℕ) : ℝ) with hNk
  have hNk0 : 0 < Nk := by positivity
  set c : ℝ := 2 * Nk * θ with hc
  have hc0 : 0 < c := by positivity
  set Mε : ℝ := K₁ * (1 + θ₀ * 9 ^ k) ^ 4 with hMε
  have hMε0 : 0 ≤ Mε := by positivity
  set B2 : ℝ := (A * 2 ^ κ) ^ (2 : ℝ) with hB2
  have hB20 : 0 ≤ B2 := by positivity
  set CZ : ℝ := 2 * C * ((1 / s) ^ (1 / s) * Real.exp (-(1 / s))) with hCZ
  have hCZ0 : 0 ≤ CZ := by positivity
  refine ⟨CZ * (b + 4) ^ (1 - δ), Real.exp ((3 : ℝ) ^ k / c) *
    (8 * Mε + 4 + 16 * B2 * (24 * c ^ 4 * Real.exp (1 / c))), by positivity, by positivity,
    fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a' : Vertex 2 := y + (N : ℤ) • LatticeProb.unit j with ha'
  set R : ℝ := b + 3 * N + 1 with hR
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨Z, hZm, hZ0, hZO, hZ⟩ := hosc i R hR1
  set D : Configuration 2 → ℝ := fun ω => correctorDiff hG hGv (Pi.single i 1) ω
    (statAnchor k ω a') (statAnchor k ω y) with hD
  set DP : Configuration 2 → ℝ := fun ω => correctorDiff hG hGv (Pi.single i 1) ω
    (guardAnchor ω a') (guardAnchor ω y) with hDP
  have hDPm : Measurable DP :=
    measurable_correctorDiff_comp hG hGv _ (measurable_guardAnchor a') (measurable_guardAnchor y)
  set εa := statDiscrepancy hG hGv i k y
  set εa' := statDiscrepancy hG hGv i k a'
  have hεam := measurable_statDiscrepancy hG hGv i k y
  have hεa'm := measurable_statDiscrepancy hG hGv i k a'
  set Gd : Set (Configuration 2) := {ω | (3 : ℝ) ^ k + sizeSum k y ω ≤ N ∧
    (3 : ℝ) ^ k + sizeSum k a' ω ≤ N} with hGd
  have hGdm : MeasurableSet Gd :=
    (measurableSet_le ((measurable_sizeSum k y).const_add _) measurable_const).inter
      (measurableSet_le ((measurable_sizeSum k a').const_add _) measurable_const)
  set η : ℝ := Real.exp (-((((N : ℝ) - 3 ^ k) / (Nk * θ)) / 2)) with hη
  have hη0 : 0 < η := Real.exp_pos _
  set crude : Configuration 2 → ℝ := fun ω => |εa' ω| + |εa ω| + |DP ω| with hcrude
  have hall : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ x, ω ∈ infiniteComponentEvent x → ∀ y,
      (openGraph ω).Adj x y → |correctorDiff hG hGv (Pi.single i 1) ω x y| ≤ Λ i x ω :=
    ae_all_iff.2 fun x => hlip i x
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂latticeBondLaw 2 p, ENNReal.ofReal |D ω| ≤ ENNReal.ofReal (Z ω) +
      (ENNReal.ofReal η * ENNReal.ofReal (crude ω) ^ (2 : ℝ) +
        ENNReal.ofReal η⁻¹ * Gdᶜ.indicator 1 ω) := by
    filter_upwards [hGae, ae_planarPartitionEvent hpc, hZ] with ω hω hP hZω
    have hinf := infinite_planarCoarseAnchor hP y
    have hsa := statAnchor_mem_inf k y hinf
    have hsa' := statAnchor_mem_inf k a' hinf
    by_cases hg : ω ∈ Gd
    · obtain ⟨hg1, hg2⟩ := hg
      have hnorm : ∀ z : Vertex 2, (3 : ℝ) ^ k + sizeSum k z ω ≤ N →
          ‖latticeEuclideanEmbedding (statAnchor k ω z)‖ ≤
            ‖latticeEuclideanEmbedding z‖ + 2 * N := by
        intro z hz
        have h1 := norm_latticeEuclideanEmbedding_le_sum (statAnchor k ω z - z)
        have h2 := abs_statAnchor_sub_le hP k z 0
        have h3 := abs_statAnchor_sub_le hP k z 1
        have h4 := norm_le_insert' (latticeEuclideanEmbedding (statAnchor k ω z))
          (latticeEuclideanEmbedding z)
        rw [← latticeEuclideanEmbedding_sub] at h4
        linarith
      have hya : ‖latticeEuclideanEmbedding a'‖ ≤ b + N := by
        have h1 := norm_le_insert' (latticeEuclideanEmbedding a') (latticeEuclideanEmbedding y)
        rw [← latticeEuclideanEmbedding_sub] at h1
        have h2 := norm_latticeEuclideanEmbedding_le_sum (a' - y)
        have e : a' - y = (N : ℤ) • LatticeProb.unit j := by rw [ha']; abel
        rw [e] at h1 h2
        have h3 : |(((N : ℤ) • LatticeProb.unit j) 0 : ℝ)| + |(((N : ℤ) • LatticeProb.unit j) 1 : ℝ)|
            ≤ N := by
          fin_cases j <;> simp [LatticeProb.unit]
        linarith
      have hDZ : |D ω| ≤ Z ω := hZω hω _ _ hsa' hsa (by linarith [hnorm a' hg2])
        (by linarith [hnorm y hg1])
      calc ENNReal.ofReal |D ω| ≤ ENNReal.ofReal (Z ω) := ENNReal.ofReal_le_ofReal hDZ
        _ ≤ _ := le_self_add
    · have hsplit : D ω = εa' ω + DP ω - εa ω := by
        simp only [hD, hDP, εa, εa', statDiscrepancy]
        rw [guardAnchor_of_event hP, guardAnchor_of_event hP]
        have hpa' := infinite_planarCoarseAnchor hP a'
        rw [correctorDiff_add' hG hGv hω hsa' hpa' hsa,
          correctorDiff_add' hG hGv hω hpa' hinf hsa, correctorDiff_swap' hG hGv hω hsa hinf]
        ring
      have hcr : |D ω| ≤ crude ω := by
        rw [hsplit]
        simp only [hcrude]
        have := abs_sub (εa' ω + DP ω) (εa ω)
        have := abs_add_le (εa' ω) (DP ω)
        linarith
      have hc0 : 0 ≤ crude ω := by simp only [hcrude]; positivity
      have hAM : crude ω ≤ η * crude ω ^ 2 + η⁻¹ := by
        have := abs_le_mul_sq_add_inv (e := crude ω) hη0
        rw [abs_of_nonneg hc0] at this
        split_ifs at this <;> linarith [inv_pos.2 hη0]
      rw [Set.indicator_of_mem (show ω ∈ Gdᶜ from hg), Pi.one_apply, mul_one]
      calc ENNReal.ofReal |D ω| ≤ ENNReal.ofReal (η * crude ω ^ 2 + η⁻¹) :=
            ENNReal.ofReal_le_ofReal (hcr.trans hAM)
        _ = ENNReal.ofReal η * ENNReal.ofReal (crude ω) ^ (2 : ℝ) + ENNReal.ofReal η⁻¹ := by
            rw [ENNReal.ofReal_add (by positivity) (inv_pos.2 hη0).le, ENNReal.ofReal_mul hη0.le,
              ENNReal.ofReal_pow hc0, ← ENNReal.rpow_natCast, Nat.cast_ofNat]
        _ ≤ _ := le_add_self
  -- the expectation of `Z`
  have hθR : 0 < C * R ^ (1 - δ) := by positivity
  obtain ⟨hZi, hZle⟩ := IsOsBond.integral_rpow_le hs hθR one_pos hZm hZ0 hZO
  simp only [Real.rpow_one] at hZi hZle
  have hEZ : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (CZ * R ^ (1 - δ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hZi (Eventually.of_forall hZ0)]
    refine ENNReal.ofReal_le_ofReal (hZle.trans_eq ?_)
    rw [hCZ]
    ring
  -- the second moment of the crude bound
  set F := latticeBetween a' y with hF
  have hFcard : (F.card : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by
    have h := card_latticeBetween_le (a := y) (a' := a') (N := N) (fun i' => by
      rw [ha']
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
      fin_cases j <;> fin_cases i' <;> simp [LatticeProb.unit])
    exact_mod_cast h
  have hDP2 : ∫⁻ ω, ENNReal.ofReal |DP ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (4 * ((N : ℝ) + 1) ^ 4 * B2) := by
    have hpt2 : ∀ᵐ ω ∂latticeBondLaw 2 p, ENNReal.ofReal |DP ω| ^ (2 : ℝ) ≤
        4 * ((F.card : ℝ≥0∞) * ∑ u ∈ F, stepSixSum (Λ i) u ω ^ (2 : ℝ)) := by
      filter_upwards [hGae, ae_planarPartitionEvent hpc, hall] with ω hω hP hl
      have h1 : ENNReal.ofReal |DP ω| ≤ 2 * ∑ u ∈ F, stepSixSum (Λ i) u ω := by
        simp only [hDP]
        rw [guardAnchor_of_event hP, guardAnchor_of_event hP]
        exact ofReal_abs_correctorDiff_coarseAnchors_le hG hGv hω hP y a' (fun x => hΛ0 i x ω) hl
      have h2 := ENNReal.rpow_sum_le_const_mul_sum_rpow (s := F)
        (f := fun u => stepSixSum (Λ i) u ω) (p := 2) (by norm_num)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h2
      calc ENNReal.ofReal |DP ω| ^ (2 : ℝ) ≤ (2 * ∑ u ∈ F, stepSixSum (Λ i) u ω) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = 4 * (∑ u ∈ F, stepSixSum (Λ i) u ω) ^ (2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
            congr 1
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
            norm_num
        _ ≤ 4 * ((F.card : ℝ≥0∞) * ∑ u ∈ F, stepSixSum (Λ i) u ω ^ (2 : ℝ)) :=
            mul_le_mul_right h2 _
    calc ∫⁻ ω, ENNReal.ofReal |DP ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, 4 * ((F.card : ℝ≥0∞) * ∑ u ∈ F, stepSixSum (Λ i) u ω ^ (2 : ℝ))
            ∂latticeBondLaw 2 p := lintegral_mono_ae hpt2
      _ = 4 * ((F.card : ℝ≥0∞) * ∑ u ∈ F, ∫⁻ ω, stepSixSum (Λ i) u ω ^ (2 : ℝ)
            ∂latticeBondLaw 2 p) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by simp),
            lintegral_finsetSum _ fun u _ => (measurable_stepSixSum (hΛm i) u).pow_const _]
      _ ≤ 4 * ((F.card : ℝ≥0∞) * ∑ _u ∈ F, ENNReal.ofReal B2) := by
          gcongr with u hu
          exact (hmom6 i u 2 (by norm_num)).trans_eq (by rw [hB2])
      _ = ENNReal.ofReal (4 * ((F.card : ℝ) * ((F.card : ℝ) * B2))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal (4 * ((N : ℝ) + 1) ^ 4 * B2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hc0 : (0 : ℝ) ≤ F.card := by positivity
          have : (F.card : ℝ) * F.card ≤ ((N : ℝ) + 1) ^ 4 := by
            calc (F.card : ℝ) * F.card ≤ ((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 1) ^ 2 :=
                  mul_le_mul hFcard hFcard hc0 (by positivity)
              _ = ((N : ℝ) + 1) ^ 4 := by ring
          have h := mul_le_mul_of_nonneg_right this hB20
          linarith
  have hcr2 : ∫⁻ ω, ENNReal.ofReal (crude ω) ^ (2 : ℝ) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal (8 * Mε + 16 * ((N : ℝ) + 1) ^ 4 * B2) := by
    have hpt3 : ∀ ω, ENNReal.ofReal (crude ω) ^ (2 : ℝ) ≤
        4 * (ENNReal.ofReal |εa' ω| ^ (2 : ℝ) + ENNReal.ofReal |εa ω| ^ (2 : ℝ) +
          ENNReal.ofReal |DP ω| ^ (2 : ℝ)) := by
      intro ω
      simp only [hcrude]
      rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      have h1 := ENNReal.rpow_add_le_mul_rpow_add_rpow
        (ENNReal.ofReal |εa' ω| + ENNReal.ofReal |εa ω|) (ENNReal.ofReal |DP ω|)
        (by norm_num : (1 : ℝ) ≤ 2)
      have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow (ENNReal.ofReal |εa' ω|)
        (ENNReal.ofReal |εa ω|) (by norm_num : (1 : ℝ) ≤ 2)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h1 h2
      calc _ ≤ 2 * ((ENNReal.ofReal |εa' ω| + ENNReal.ofReal |εa ω|) ^ (2 : ℝ) +
            ENNReal.ofReal |DP ω| ^ (2 : ℝ)) := h1
        _ ≤ 2 * (2 * (ENNReal.ofReal |εa' ω| ^ (2 : ℝ) + ENNReal.ofReal |εa ω| ^ (2 : ℝ)) +
            ENNReal.ofReal |DP ω| ^ (2 : ℝ)) := by gcongr
        _ ≤ 2 * (2 * (ENNReal.ofReal |εa' ω| ^ (2 : ℝ) + ENNReal.ofReal |εa ω| ^ (2 : ℝ)) +
            2 * ENNReal.ofReal |DP ω| ^ (2 : ℝ)) := by
            gcongr
            exact le_mul_of_one_le_left (zero_le) (by norm_num)
        _ = 4 * (ENNReal.ofReal |εa' ω| ^ (2 : ℝ) + ENNReal.ofReal |εa ω| ^ (2 : ℝ) +
            ENNReal.ofReal |DP ω| ^ (2 : ℝ)) := by ring
    have hm1 : Measurable fun ω => ENNReal.ofReal |εa' ω| ^ (2 : ℝ) :=
      (ENNReal.measurable_ofReal.comp hεa'm.abs).pow_const _
    have hm2 : Measurable fun ω => ENNReal.ofReal |εa ω| ^ (2 : ℝ) :=
      (ENNReal.measurable_ofReal.comp hεam.abs).pow_const _
    calc ∫⁻ ω, ENNReal.ofReal (crude ω) ^ (2 : ℝ) ∂latticeBondLaw 2 p
        ≤ ∫⁻ ω, 4 * (ENNReal.ofReal |εa' ω| ^ (2 : ℝ) + ENNReal.ofReal |εa ω| ^ (2 : ℝ) +
            ENNReal.ofReal |DP ω| ^ (2 : ℝ)) ∂latticeBondLaw 2 p := lintegral_mono hpt3
      _ = 4 * (∫⁻ ω, ENNReal.ofReal |εa' ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p +
            ∫⁻ ω, ENNReal.ofReal |εa ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p +
            ∫⁻ ω, ENNReal.ofReal |DP ω| ^ (2 : ℝ) ∂latticeBondLaw 2 p) := by
          rw [lintegral_const_mul' _ _ (by norm_num),
            lintegral_add_left (f := fun ω => ENNReal.ofReal |εa' ω| ^ (2 : ℝ) +
              ENNReal.ofReal |εa ω| ^ (2 : ℝ)) (hm1.add hm2),
            lintegral_add_left (f := fun ω => ENNReal.ofReal |εa' ω| ^ (2 : ℝ)) hm1]
      _ ≤ 4 * (ENNReal.ofReal Mε + ENNReal.ofReal Mε +
            ENNReal.ofReal (4 * ((N : ℝ) + 1) ^ 4 * B2)) := by
          gcongr
          · exact hsq i k a'
          · exact hsq i k y
      _ = ENNReal.ofReal (8 * Mε + 16 * ((N : ℝ) + 1) ^ 4 * B2) := by
          rw [← ENNReal.ofReal_add hMε0 hMε0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  -- the probability of the bad event
  have hbad : latticeBondLaw 2 p Gdᶜ ≤
      ENNReal.ofReal (4 * Real.exp (-(((N : ℝ) - 3 ^ k) / (Nk * θ)))) := by
    have hsub : Gdᶜ ⊆ {ω | (N : ℝ) - 3 ^ k ≤ sizeSum k y ω} ∪
        {ω | (N : ℝ) - 3 ^ k ≤ sizeSum k a' ω} := by
      intro ω hω
      simp only [hGd, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hω
      rcases hω with h | h
      · left
        simp only [Set.mem_setOf_eq]
        linarith
      · right
        simp only [Set.mem_setOf_eq]
        linarith
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have h1 := measure_le_sizeSum_le (p := p) hθ hexp k y ((N : ℝ) - 3 ^ k)
    have h2 := measure_le_sizeSum_le (p := p) hθ hexp k a' ((N : ℝ) - 3 ^ k)
    refine (add_le_add h1 h2).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  -- the expectation
  calc ∫⁻ ω, ENNReal.ofReal |D ω| ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, (ENNReal.ofReal (Z ω) + (ENNReal.ofReal η * ENNReal.ofReal (crude ω) ^ (2 : ℝ) +
          ENNReal.ofReal η⁻¹ * Gdᶜ.indicator 1 ω)) ∂latticeBondLaw 2 p := lintegral_mono_ae hpt
    _ = ∫⁻ ω, ENNReal.ofReal (Z ω) ∂latticeBondLaw 2 p +
          (ENNReal.ofReal η * ∫⁻ ω, ENNReal.ofReal (crude ω) ^ (2 : ℝ) ∂latticeBondLaw 2 p +
          ENNReal.ofReal η⁻¹ * latticeBondLaw 2 p Gdᶜ) := by
        have hcm : Measurable fun ω => ENNReal.ofReal (crude ω) ^ (2 : ℝ) :=
          (ENNReal.measurable_ofReal.comp ((hεa'm.abs.add hεam.abs).add hDPm.abs)).pow_const _
        rw [lintegral_add_left (f := fun ω => ENNReal.ofReal (Z ω))
            (ENNReal.measurable_ofReal.comp hZm),
          lintegral_add_left (f := fun ω => ENNReal.ofReal η * ENNReal.ofReal (crude ω) ^ (2 : ℝ))
            (hcm.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one hGdm.compl]
    _ ≤ ENNReal.ofReal (CZ * R ^ (1 - δ)) +
          (ENNReal.ofReal η * ENNReal.ofReal (8 * Mε + 16 * ((N : ℝ) + 1) ^ 4 * B2) +
          ENNReal.ofReal η⁻¹ *
            ENNReal.ofReal (4 * Real.exp (-(((N : ℝ) - 3 ^ k) / (Nk * θ))))) := by
        gcongr
    _ ≤ ENNReal.ofReal (CZ * R ^ (1 - δ) + η * (8 * Mε + 4 + 16 * B2 * ((N : ℝ) + 1) ^ 4)) := by
        set Av : ℝ := CZ * R ^ (1 - δ) with hAv
        set Bv : ℝ := 8 * Mε + 16 * ((N : ℝ) + 1) ^ 4 * B2 with hBv
        set Dv : ℝ := 4 * Real.exp (-(((N : ℝ) - 3 ^ k) / (Nk * θ))) with hDv
        have hA0 : 0 ≤ Av := by positivity
        have hB0 : 0 ≤ Bv := by positivity
        have hD0 : 0 ≤ Dv := by positivity
        have hinv : η⁻¹ * Dv = 4 * η := by
          rw [hDv, hη, ← Real.exp_neg, mul_left_comm, ← Real.exp_add]
          congr 2
          ring
        have e1 : ENNReal.ofReal η * ENNReal.ofReal Bv + ENNReal.ofReal η⁻¹ * ENNReal.ofReal Dv =
            ENNReal.ofReal (η * Bv + η⁻¹ * Dv) := by
          rw [← ENNReal.ofReal_mul hη0.le, ← ENNReal.ofReal_mul (inv_pos.2 hη0).le,
            ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [e1, ← ENNReal.ofReal_add hA0 (by positivity)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        rw [hinv, hBv]
        ring
    _ ≤ ENNReal.ofReal (CZ * (b + 4) ^ (1 - δ) * (N : ℝ) ^ (1 - δ) + Real.exp ((3 : ℝ) ^ k / c) *
          (8 * Mε + 4 + 16 * B2 * (24 * c ^ 4 * Real.exp (1 / c)))) := by
        refine ENNReal.ofReal_le_ofReal (add_le_add ?_ ?_)
        · have hRle : R ≤ (b + 4) * N := by nlinarith
          have h1 : R ^ (1 - δ) ≤ ((b + 4) * N) ^ (1 - δ) :=
            Real.rpow_le_rpow (by linarith) hRle (by linarith)
          rw [Real.mul_rpow (by positivity) (by positivity)] at h1
          calc CZ * R ^ (1 - δ) ≤ CZ * ((b + 4) ^ (1 - δ) * (N : ℝ) ^ (1 - δ)) :=
                mul_le_mul_of_nonneg_left h1 hCZ0
            _ = _ := by ring
        · have hηe : η = Real.exp ((3 : ℝ) ^ k / c) * Real.exp (-((N : ℝ) / c)) := by
            rw [hη, ← Real.exp_add]
            congr 1
            rw [hc]
            field_simp
            ring
          have hen : Real.exp (-((N : ℝ) / c)) ≤ 1 := Real.exp_le_one_iff.2 (by
            have : 0 ≤ (N : ℝ) / c := by positivity
            linarith)
          have hp4 := pow_four_mul_exp_neg_le hc0 (N : ℝ) (by positivity)
          rw [hηe]
          have hE : 0 < Real.exp ((3 : ℝ) ^ k / c) := Real.exp_pos _
          have h8 : (0 : ℝ) ≤ 8 * Mε + 4 := by linarith only [hMε0]
          have hk : (8 * Mε + 4) * Real.exp (-((N : ℝ) / c)) ≤ 8 * Mε + 4 :=
            mul_le_of_le_one_right h8 hen
          have hk2 : 16 * B2 * (((N : ℝ) + 1) ^ 4 * Real.exp (-((N : ℝ) / c))) ≤
              16 * B2 * (24 * c ^ 4 * Real.exp (1 / c)) :=
            mul_le_mul_of_nonneg_left hp4 (mul_nonneg (by norm_num) hB20)
          calc Real.exp ((3 : ℝ) ^ k / c) * Real.exp (-((N : ℝ) / c)) *
                (8 * Mε + 4 + 16 * B2 * ((N : ℝ) + 1) ^ 4)
              = Real.exp ((3 : ℝ) ^ k / c) * ((8 * Mε + 4) * Real.exp (-((N : ℝ) / c)) +
                  16 * B2 * (((N : ℝ) + 1) ^ 4 * Real.exp (-((N : ℝ) / c)))) := by ring
            _ ≤ Real.exp ((3 : ℝ) ^ k / c) * (8 * Mε + 4 + 16 * B2 * (24 * c ^ 4 *
                  Real.exp (1 / c))) := by gcongr

end Segment

end Rigidity.Corrector
