import Rigidity.Steps.Section5.GradientTrichotomy

/-!
# Proposition 5.7, Step 3: the density conclusion

`step:5.7-conclusion` of Proposition 5.7 (corrected draft L1833-1836), in the abstract form
`DensityConclusionStep` of `Rigidity/Steps/Section5/GradientTrichotomy.lean`: if the events `A_e`,
indexed by the oriented nearest-neighbour edges, satisfy `P[A_e] → 0`, and almost surely on `E` the
edges `e` of `B_{2^k}` with `ω ∈ A_e` have density at least `c > 0` for all large `k`, then
`P[E] = 0`.

Proof. Let `M_e ⊇ A_e` be a measurable hull and `g_k = (π 4^k)⁻¹ Σ_{e ∈ B_{2^k}} 1_{M_e}`. There are
at most `36 · 4^k` oriented edges in `B_{2^k}`, so `E[g_k] = (π 4^k)⁻¹ Σ_e P[A_e] → 0` (a Cesàro
average of a null sequence). By Fatou's lemma `lim inf_k g_k = 0` almost surely, while
`lim inf_k g_k ≥ c > 0` on `E`. The density is used in its eventual (`lim inf`) form, as in the
carving; with a `lim sup` the conclusion would not follow from `E[g_k] → 0`.
-/

open MeasureTheory LatticeProb.Percolation Filter Topology
open scoped ENNReal
open Classical

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- The square `[-N, N]²` of lattice points. -/
noncomputable def latticeSquare (N : ℤ) : Finset (Vertex 2) :=
  Fintype.piFinset fun _ => Finset.Icc (-N) N

/-- The four unit displacements `± e_i` of `ℤ²`. -/
def unitDisplacements : Finset (Vertex 2) :=
  Finset.univ.biUnion fun i : Fin 2 => {LatticeProb.unit i, -LatticeProb.unit i}

/-- The oriented nearest-neighbour edges `(x, y)` with both endpoints in the Euclidean ball
`B_{2^k}`. -/
noncomputable def ballEdges (k : ℕ) : Finset (Vertex 2 × Vertex 2) :=
  ((latticeSquare (2 ^ k) ×ˢ unitDisplacements).image fun p => (p.1, p.1 + p.2)).filter
    fun e => eucl e.1 < 2 ^ k ∧ eucl e.2 < 2 ^ k ∧ (nearestNeighborGraph 2).Adj e.1 e.2

/-- A coordinate is bounded by the Euclidean norm. -/
theorem abs_coord_le_eucl (x : Vertex 2) (i : Fin 2) : |(x i : ℝ)| ≤ eucl x := by
  have h := PiLp.norm_apply_le (latticeEuclideanEmbedding x) i
  change ‖(x i : ℝ)‖ ≤ eucl x at h
  rwa [Real.norm_eq_abs] at h

theorem mem_latticeSquare_of_eucl_lt {x : Vertex 2} {k : ℕ} (hx : eucl x < 2 ^ k) :
    x ∈ latticeSquare (2 ^ k) := by
  rw [latticeSquare, Fintype.mem_piFinset]
  intro i
  obtain ⟨h1, h2⟩ := abs_lt.mp ((abs_coord_le_eucl x i).trans_lt hx)
  rw [Finset.mem_Icc]
  constructor
  · have : ((-(2 : ℤ) ^ k : ℤ) : ℝ) < (x i : ℝ) := by push_cast; linarith
    exact_mod_cast this.le
  · have : (x i : ℝ) < ((2 ^ k : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this.le

theorem mem_ballEdges {k : ℕ} {e : Vertex 2 × Vertex 2} :
    e ∈ ballEdges k ↔
      eucl e.1 < 2 ^ k ∧ eucl e.2 < 2 ^ k ∧ (nearestNeighborGraph 2).Adj e.1 e.2 := by
  rw [ballEdges, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_image]
  refine ⟨(e.1, e.2 - e.1), Finset.mem_product.mpr ⟨mem_latticeSquare_of_eucl_lt h.1, ?_⟩, ?_⟩
  · obtain ⟨i, hi | hi⟩ := h.2.2
    · rw [unitDisplacements, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, by rw [hi, add_sub_cancel_left]; simp⟩
    · rw [unitDisplacements, Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have : e.2 - e.1 = -LatticeProb.unit i := by rw [hi]; abel
      rw [this]; simp
  · simp

theorem card_unitDisplacements_le : unitDisplacements.card ≤ 4 := by
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ i : Fin 2, ({LatticeProb.unit i, -LatticeProb.unit i} : Finset (Vertex 2)).card
      ≤ ∑ _i : Fin 2, 2 := Finset.sum_le_sum fun i _ => Finset.card_le_two
    _ = 4 := by simp

/-- The ball `B_{2^k}` carries at most `36 · 4^k` oriented edges. -/
theorem card_ballEdges_le (k : ℕ) : ((ballEdges k).card : ℝ) ≤ 36 * 4 ^ k := by
  have hsq : (latticeSquare (2 ^ k)).card = (2 * 2 ^ k + 1) ^ 2 := by
    rw [latticeSquare, Fintype.card_piFinset, Finset.prod_const, Int.card_Icc, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl]
    omega
  have hcard : (ballEdges k).card ≤ (2 * 2 ^ k + 1) ^ 2 * 4 := by
    unfold ballEdges
    refine (Finset.card_filter_le _ _).trans ((Finset.card_image_le).trans ?_)
    rw [Finset.card_product, hsq]
    exact Nat.mul_le_mul_left _ card_unitDisplacements_le
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hnat : (2 * 2 ^ k + 1) ^ 2 * 4 ≤ 36 * 4 ^ k := by
    calc (2 * 2 ^ k + 1) ^ 2 * 4 ≤ (3 * 2 ^ k) ^ 2 * 4 := by gcongr; omega
      _ = 36 * 4 ^ k := by
        rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num; ring
  exact_mod_cast hcard.trans hnat

/-- A Cesàro average over the balls `B_{2^k}` of a nonnegative family tending to zero along the
edges tends to zero. -/
theorem tendsto_sum_ballEdges_div {a : Vertex 2 × Vertex 2 → ℝ} (ha0 : ∀ e, 0 ≤ a e)
    (ha : Tendsto a cofinite (𝓝 0)) :
    Tendsto (fun k : ℕ => (∑ e ∈ ballEdges k, a e) / (Real.pi * 4 ^ k)) atTop (𝓝 0) := by
  have hpos : ∀ k : ℕ, 0 < Real.pi * 4 ^ k := fun k => by positivity
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun k =>
    hb.trans_le (div_nonneg (Finset.sum_nonneg fun e _ => ha0 e) (hpos k).le), fun ε hε => ?_⟩
  set η := ε / 72 with hη
  have hη0 : 0 < η := by positivity
  have hF : {e | ¬ a e < η}.Finite := eventually_cofinite.mp (ha.eventually (gt_mem_nhds hη0))
  set F := hF.toFinset
  set A := ∑ e ∈ F, a e
  have hbound : ∀ k : ℕ, ∑ e ∈ ballEdges k, a e ≤ A + η * (36 * 4 ^ k) := by
    intro k
    rw [← Finset.sum_filter_add_sum_filter_not (ballEdges k) (fun e => a e < η), add_comm]
    gcongr
    · refine Finset.sum_le_sum_of_subset_of_nonneg (fun e he => ?_) fun e _ _ => ha0 e
      rw [Set.Finite.mem_toFinset]
      exact (Finset.mem_filter.mp he).2
    · calc ∑ e ∈ (ballEdges k).filter (fun e => a e < η), a e
          ≤ ∑ _e ∈ (ballEdges k).filter (fun e => a e < η), η :=
            Finset.sum_le_sum fun e he => (Finset.mem_filter.mp he).2.le
        _ = ((ballEdges k).filter (fun e => a e < η)).card * η := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (ballEdges k).card * η := by
            gcongr; exact Finset.filter_subset _ _
        _ ≤ (36 * 4 ^ k) * η := by gcongr; exact card_ballEdges_le k
        _ = η * (36 * 4 ^ k) := mul_comm _ _
  have hA : Tendsto (fun k : ℕ => A / (Real.pi * 4 ^ k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).const_mul_atTop
        Real.pi_pos)
  filter_upwards [hA.eventually (gt_mem_nhds (half_pos hε))] with k hk
  have hpi : 3 < Real.pi := Real.pi_gt_three
  calc (∑ e ∈ ballEdges k, a e) / (Real.pi * 4 ^ k)
      ≤ (A + η * (36 * 4 ^ k)) / (Real.pi * 4 ^ k) := by gcongr; exact hbound k
    _ = A / (Real.pi * 4 ^ k) + 36 * η / Real.pi := by
        field_simp
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add hk ?_
        rw [div_lt_iff₀ Real.pi_pos, hη]
        nlinarith
    _ = ε := add_halves ε

/-- `step:5.7-conclusion` (`DensityConclusionStep`, corrected draft L1833-1836). -/
theorem densityConclusionStep : DensityConclusionStep := by
  intro Ω _ μ _ E A hadj hA hE
  set M : Vertex 2 × Vertex 2 → Set Ω := fun e => toMeasurable μ (A e) with hM
  set g : ℕ → Ω → ℝ≥0∞ := fun k z =>
    ENNReal.ofReal (Real.pi * 4 ^ k)⁻¹ * ∑ e ∈ ballEdges k, (M e).indicator 1 z with hg
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (Finset.measurable_sum _ fun e _ =>
      measurable_one.indicator (measurableSet_toMeasurable _ _)).const_mul _
  have hint : ∀ k, ∫⁻ z, g k z ∂μ =
      ENNReal.ofReal ((∑ e ∈ ballEdges k, (μ (A e)).toReal) / (Real.pi * 4 ^ k)) := by
    intro k
    rw [hg, lintegral_const_mul _ (Finset.measurable_sum _ fun e _ =>
        measurable_one.indicator (measurableSet_toMeasurable _ _)),
      lintegral_finsetSum _ fun e _ =>
        measurable_one.indicator (measurableSet_toMeasurable _ _)]
    simp_rw [lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
    rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)),
      ENNReal.ofReal_sum_of_nonneg fun e _ => ENNReal.toReal_nonneg]
    simp_rw [ENNReal.ofReal_toReal (measure_ne_top μ _)]
  have ha : Tendsto (fun e => (μ (A e)).toReal) cofinite (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hA
    simpa [Function.comp_def] using h
  have hlim : Tendsto (fun k => ∫⁻ z, g k z ∂μ) atTop (𝓝 0) := by
    simp_rw [hint]
    simpa using ENNReal.tendsto_ofReal
      (tendsto_sum_ballEdges_div (fun e => ENNReal.toReal_nonneg) ha)
  have h0 : ∫⁻ z, liminf (fun k => g k z) atTop ∂μ = 0 :=
    le_antisymm ((lintegral_liminf_le hgm).trans hlim.liminf_eq.le) bot_le
  have hae : ∀ᵐ z ∂μ, liminf (fun k => g k z) atTop = 0 :=
    (lintegral_eq_zero_iff (Measurable.liminf hgm)).mp h0
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hae, hE] with z hz hzE
  intro hzE'
  obtain ⟨c, hc, hev⟩ := hzE hzE'
  have hle : ENNReal.ofReal c ≤ liminf (fun k => g k z) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) (hev.mono fun k hk => ?_)
    have hset : {e : Vertex 2 × Vertex 2 | eucl e.1 < 2 ^ k ∧ eucl e.2 < 2 ^ k ∧ z ∈ A e} =
        ↑((ballEdges k).filter fun e => z ∈ A e) := by
      ext e
      simp only [Set.mem_setOf_eq, Finset.coe_filter, mem_ballEdges]
      exact ⟨fun h => ⟨⟨h.1, h.2.1, hadj e ⟨z, h.2.2⟩⟩, h.2.2⟩,
        fun h => ⟨h.1.1, h.1.2.1, h.2⟩⟩
    rw [hset, Set.ncard_coe_finset] at hk
    have hcount : (((ballEdges k).filter fun e => z ∈ A e).card : ℝ≥0∞) ≤
        ∑ e ∈ ballEdges k, (M e).indicator 1 z := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_le_sum fun e _ => ?_
      by_cases hze : z ∈ A e
      · rw [if_pos hze, Set.indicator_of_mem (subset_toMeasurable μ (A e) hze)]
        simp
      · rw [if_neg hze]; simp
    calc ENNReal.ofReal c
        ≤ ENNReal.ofReal ((((ballEdges k).filter fun e => z ∈ A e).card : ℝ) /
            (Real.pi * 4 ^ k)) := ENNReal.ofReal_le_ofReal hk
      _ = ENNReal.ofReal (Real.pi * 4 ^ k)⁻¹ *
            (((ballEdges k).filter fun e => z ∈ A e).card : ℝ≥0∞) := by
          rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)),
            ENNReal.ofReal_natCast]
      _ ≤ g k z := mul_le_mul_right hcount _
  rw [hz] at hle
  exact absurd (ENNReal.ofReal_pos.mpr hc) (not_lt.mpr hle)

end Rigidity.Proofs.Section5
