import Rigidity.Proofs.Regularity.PlanarRestrictBadOs
import Rigidity.Proofs.Cluster.PlanarRHRestrictQuad

/-!
# The ingredients of Lemma 5.5 with stretched-exponential failure probabilities

* `exists_restrictBad_os`: the constants `A₂, A_τ, K` of the bad event of the proof of Lemma 5.5 of
  Armstrong and Dario (arXiv:1609.09431v2) for which the bad event is almost surely contained in a
  measurable event of probability at most `C exp(-c 3^{n σ})`;
* `sum_exceptionalIndicator_le_of_reach`: when the subcubes of scale `n` are resolved and the reach
  is at most `S` on `U`, at most `484 S² |U| 3^{-n}` vertices of `U` are exceptional;
* `planarNuDefect_le_of_errors`: the energy `D^ν_n(U, ξ)` of the differences between the maximizer
  on `U` and the maximizers on the subcubes is at most `2 ε |U|` plus Young's error term when
  `ν(V, ξ)` is within `ε` of a constant on `U` and on the subcubes. With `ε` the subadditivity
  error of Proposition 5.2 this replaces `τ` in Lemma 5.5 by a quantity of class `O_s`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Cluster Rigidity.Proofs.Section5
open scoped Classical ENNReal

/-- **The bad event of Lemma 5.5 with a stretched-exponential probability.** -/
theorem exists_restrictBad_os {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    {A₀ : ℝ} (hRH : PlanarRHFailureBound p A₀) (t : ℝ) (τ : ℕ) :
    ∃ A₂ Aτ K : ℝ, 0 ≤ A₂ ∧ 0 ≤ Aτ ∧ 0 ≤ K ∧
    ∃ E : TriadicCube 2 → ℕ → Set (Configuration 2), (∀ U n, MeasurableSet (E U n)) ∧
      (∃ C c σ : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 < σ ∧ ∀ (U : TriadicCube 2) (n : ℕ),
        9 * U.scale ≤ 10 * n → n < U.scale →
        latticeBondLaw 2 p (E U n) ≤ ENNReal.ofReal (C * Real.exp (-c * ((3 : ℝ) ^ n) ^ σ))) ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (U : TriadicCube 2) (n : ℕ),
        ω ∈ restrictBad (fun ω => stoppingScale (planarRHGood A₀ ω)) t K τ Aτ A₂ U n →
        ω ∈ E U n := by
  set μ := latticeBondLaw 2 p with hμ
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨hHc, ⟨θc, hθc, hmomc⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num) μ
    planarCoarseGood measurableSet_mem_planarCoarseGood hC₀ hc₀ one_pos hq
  obtain ⟨C2f, D2, hD2, c2, hc2, h2⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p planarCoarseGood measurableSet_mem_planarCoarseGood
    measurableSet_not_mem_planarCoarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq 2
  obtain ⟨Cτf, Dτ, hDτ, cτ, hcτ, hτ⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p planarCoarseGood measurableSet_mem_planarCoarseGood
    measurableSet_not_mem_planarCoarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq τ
  obtain ⟨C1, cR, s0R, hC1, hcR, hs0R, hs1R, hfail⟩ := hRH
  obtain ⟨hu, ⟨θr, hθr, hmomr⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num) μ
    (planarRHGood A₀) (measurableSet_mem_planarRHGood A₀) hC1 hcR hs0R hfail
  obtain ⟨Crf, Dr, hDr, cr, hcr, hr⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p (planarRHGood A₀) (measurableSet_mem_planarRHGood A₀)
    (measurableSet_not_mem_planarRHGood_local A₀) hC1 hcR hs0R hs1R hfail ⌈t⌉₊
  obtain ⟨C, c, σ, hC, hc, hσ, hbound⟩ := exists_measure_restrictBadProxy_le (p := p)
    (Gr := fun ω => planarRHGood A₀ ω) hθc one_pos hθr hs0R hmomc hmomr hD2 hDτ hDr hc2 hcτ hcr
    (by positivity) (by positivity) (by positivity) h2 hτ hr
  refine ⟨max C2f 0, max Cτf 0, max Crf 0, le_max_right _ _, le_max_right _ _, le_max_right _ _,
    fun U n => restrictBadProxy planarCoarseGood (fun ω => planarRHGood A₀ ω) C2f Cτf Crf τ ⌈t⌉₊
      U n,
    fun U n => measurableSet_restrictBadProxy measurableSet_mem_planarCoarseGood
      (measurableSet_mem_planarRHGood A₀) _ _ _ _ _ U n,
    ⟨C, c, σ, hC, hc, hσ, hbound⟩, ?_⟩
  filter_upwards [ae_planarPartitionEvent hpc, hHc, hu] with ω hP hH hu' U n hω
  exact restrictBad_subset_proxy hP hH hu' (Nat.le_ceil t) hω

/-- **The number of exceptional vertices** when the reach is bounded on `U`. -/
theorem sum_exceptionalIndicator_le_of_reach {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    (hres : ∀ x ∈ U.toIntegerCube.vertices, PlanarResolved ω (scaleCube n x)) {S : ℝ}
    (hS : 0 ≤ S) (hreach : ∀ z ∈ U.toIntegerCube.vertices, planarReach ω z ≤ ENNReal.ofReal S) :
    ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x ≤
      484 * S ^ 2 * U.volume / 3 ^ n := by
  have h1 : ∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x ≤
      ∑ x ∈ U.toIntegerCube.vertices, ∑ k ∈ boundaryIndex (scaleCube n x),
        (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun x hx => (exceptionalIndicator_le hP n x).trans ?_
    rw [if_pos (hres x hx), zero_add]
  have hre : ∑ x ∈ U.toIntegerCube.vertices, ∑ k ∈ boundaryIndex (scaleCube n x),
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) =
      ∑ V ∈ subcubesAt U n, ∑ k ∈ boundaryIndex V, ∑ x ∈ V.toIntegerCube.vertices,
        (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) := by
    rw [sum_scaleCube_eq hn (fun V x => ∑ k ∈ boundaryIndex V,
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0))]
    exact Finset.sum_congr rfl fun V _ => Finset.sum_comm
  have h2 : ∀ V ∈ subcubesAt U n, ∀ k ∈ boundaryIndex V, ∑ x ∈ V.toIntegerCube.vertices,
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) ≤ 121 * S ^ 2 := by
    intro V hV k hk
    have hkV : k.2.2 ∈ V.toIntegerCube.vertices :=
      (Finset.mem_product.1 (Finset.mem_product.1 (Finset.mem_filter.1 hk).1).2).2
    have hkU := toIntegerCube_vertices_subset_of_mem_subcubesAt hn hV hkV
    have h := ofReal_sum_ninefold_le hP V.toIntegerCube.vertices k.2.2 0
    simp only [zero_mul, pow_zero, zero_add] at h
    have h3 : (121 : ℝ≥0∞) * planarReach ω k.2.2 ^ 2 ≤ ENNReal.ofReal (121 * S ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hS]
      simp only [ENNReal.ofReal_ofNat]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le (hreach _ hkU) 2) zero_le
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h.trans h3)
  have h4 : ∑ V ∈ subcubesAt U n, ∑ k ∈ boundaryIndex V, ∑ x ∈ V.toIntegerCube.vertices,
      (if k.2.2 ∈ (planarPartCube ω x).ninefold.vertices then (1 : ℝ) else 0) ≤
      ∑ V ∈ subcubesAt U n, 4 * (3 : ℝ) ^ n * (121 * S ^ 2) := by
    refine Finset.sum_le_sum fun V hV => (Finset.sum_le_sum (h2 V hV)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hb := card_boundaryIndex_le V
    have hs : (V.toIntegerCube.size : ℝ) = (3 : ℝ) ^ n := by
      rw [← scale_of_mem_subcubesAt hV]
      exact_mod_cast V.cast_toIntegerCube_size
    rw [hs] at hb
    exact hb
  have hcard := card_subcubesAt_mul hn
  rw [Finset.sum_const, nsmul_eq_mul] at h4
  have e : ((subcubesAt U n).card : ℝ) * (4 * (3 : ℝ) ^ n * (121 * S ^ 2)) =
      484 * S ^ 2 * U.volume / 3 ^ n := by
    rw [← hcard, show (9 : ℝ) ^ n = 3 ^ n * 3 ^ n by
      rw [← mul_pow]; norm_num]
    field_simp
    ring
  rw [e] at h4
  exact h1.trans (hre ▸ h4)

/-- **The energy of the differences from the subadditivity errors.** -/
theorem planarNuDefect_le_of_errors {ω : Configuration 2} (hP : PlanarPartitionEvent ω)
    {U : TriadicCube 2} (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (ξ : Fin 2 → ℝ)
    (hres : ∀ x ∈ U.toIntegerCube.vertices, PlanarResolved ω (scaleCube n x)) {νb ε : ℝ}
    (hV : ∀ x ∈ U.toIntegerCube.vertices, |planarNu ω (scaleCube n x) ξ - νb| ≤ ε)
    (hUe : |planarNu ω U ξ - νb| ≤ ε) {t : ℝ} (ht : 0 < t) :
    planarNuDefect ω U n ξ ≤ 2 * ε * U.volume +
      (|ξ 0| + |ξ 1|) * (9 * (∑ x ∈ U.toIntegerCube.vertices, exceptionalIndicator ω n x) / t +
        t * (9 * (|ξ 0| + |ξ 1|) ^ 2 * U.volume)) / 4 := by
  have h := planarNuDefect_add_le_young hP hU hn ξ ht
  have hsum : ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarNu ω (scaleCube n x) ξ else 0) ≤
      U.volume * (νb + ε) := by
    rw [volume_eq_card, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [if_pos (hres x hx)]
    have := hV x hx
    rw [abs_le] at this
    linarith
  have hνU : (νb - ε) * U.volume ≤ planarNu ω U ξ * U.volume := by
    have := hUe
    rw [abs_le] at this
    exact mul_le_mul_of_nonneg_right (by linarith) U.volume_pos.le
  nlinarith

end Rigidity.Proofs.Regularity
