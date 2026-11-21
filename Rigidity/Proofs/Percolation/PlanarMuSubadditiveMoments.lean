import Rigidity.Proofs.Percolation.PlanarSubcubeCounts

/-!
# Expected error in the subadditivity of `μ`

With `t = 1 / (|q|₁ 3 ^ (n / 2))` in the subadditivity bound, the error is at most
`|q|₁² (729000000 · 3 ^ (n / 2) S_F + 2916000000 · 3 ^ (-n / 2) S) `, where `S_F` and `S` are the
sums of sixth powers of partition sides over the exceptional and over all lattice edges of `U`.
Since `E[S_F] ≤ C |U| / 3 ^ n` and `E[S] ≤ C |U|`,

`E[(∑_{x ∈ U} 1{V(x) resolved} μ(V(x), q) - |U| μ(U, q))⁺] ≤ C |q|₁² |U| / 3 ^ (n / 2)`

uniformly in `U` and `n` (Armstrong and Dario, Lemma 4.8, (4.32), in expectation).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **Subadditivity of `μ` with the optimized error.** -/
theorem sum_planarMu_subcubes_sub_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ) :
    ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
      planarMu ω U q * U.volume ≤
      (|q 0| + |q 1|) ^ 2 * (729000000 * Real.sqrt (3 ^ n) *
        edgeSideSum ω (subcubeExceptionalEdges ω U n) +
        2916000000 / Real.sqrt (3 ^ n) * edgeSideSum ω (latticeEdgesIn U)) := by
  set Q₁ := |q 0| + |q 1| with hQ
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hSF := edgeSideSum_nonneg (ω := ω) (subcubeExceptionalEdges ω U n)
  have hSA := edgeSideSum_nonneg (ω := ω) (latticeEdgesIn U)
  rcases (show (0 : ℝ) ≤ Q₁ by positivity).eq_or_lt with hQ0 | hQpos
  · have h := sum_planarMu_subcubes_le_young hP hU hn q (t := 1) one_pos
    rw [← hQ, ← hQ0] at h
    rw [← hQ0]
    simp only [zero_mul, zero_div, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h ⊢
    linarith
  · have ht : 0 < 1 / (Q₁ * s) := by positivity
    have h := sum_planarMu_subcubes_le_young hP hU hn q ht
    rw [← hQ] at h
    have e : Q₁ * ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n))) /
        (1 / (Q₁ * s)) + 1 / (Q₁ * s) * (36 * Q₁ ^ 2 *
          (162000000 * edgeSideSum ω (latticeEdgesIn U)))) / 2 =
        Q₁ ^ 2 * (729000000 * s * edgeSideSum ω (subcubeExceptionalEdges ω U n) +
          2916000000 / s * edgeSideSum ω (latticeEdgesIn U)) := by
      field_simp
      ring
    rw [e] at h
    linarith

/-- Lattice edges of a triadic cube number at most twice its vertices. -/
theorem card_latticeEdgesIn_le (U : TriadicCube 2) :
    ((latticeEdgesIn U).card : ℝ) ≤ 2 * U.volume := by
  have h : (latticeEdgesIn U).card ≤ U.toIntegerCube.vertices.card * 2 := by
    calc (latticeEdgesIn U).card
        ≤ (U.toIntegerCube.vertices ×ˢ (Finset.univ : Finset (Fin 2))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = U.toIntegerCube.vertices.card * 2 := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  rw [volume_eq_card]
  have : ((latticeEdgesIn U).card : ℝ) ≤ (U.toIntegerCube.vertices.card : ℝ) * 2 := by
    exact_mod_cast h
  linarith

/-- The reach sum with the two endpoints of an edge. -/
noncomputable def edgeReachSum (ω : Configuration 2) (m : ℕ) (k : Vertex 2 × Fin 2) : ℝ≥0∞ :=
  reachSum ω m (k.1 + unitVertex k.2) + reachSum ω m k.1

theorem measurable_edgeReachSum (m : ℕ) (k : Vertex 2 × Fin 2) :
    Measurable fun ω : Configuration 2 => edgeReachSum ω m k :=
  (measurable_reachSum m _).add (measurable_reachSum m _)

/-- Sums of sixth powers over a set of edges, by reach sums. -/
theorem ofReal_edgeSideSum_le (hP : PlanarPartitionEvent ω) (F : Finset (Vertex 2 × Fin 2)) :
    ENNReal.ofReal (edgeSideSum ω F) ≤ ∑ k ∈ F, edgeReachSum ω 6 k := by
  unfold edgeSideSum
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => by
    have := one_le_partSide (ω := ω) k.1
    have := one_le_partSide (ω := ω) (k.1 + unitVertex k.2)
    positivity]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [ENNReal.ofReal_add (by have := one_le_partSide (ω := ω) (k.1 + unitVertex k.2); positivity)
    (by have := one_le_partSide (ω := ω) k.1; positivity)]
  exact add_le_add (ofReal_partSide_pow_le hP _ 5) (ofReal_partSide_pow_le hP _ 5)

/-- The exceptional sum is at most the crossing sum plus the unresolved contributions. -/
theorem edgeSideSum_exceptional_le {U : TriadicCube 2} {n : ℕ} :
    edgeSideSum ω (subcubeExceptionalEdges ω U n) ≤
      edgeSideSum ω (subcubeCrossingEdges U n) +
      ∑ k ∈ latticeEdgesIn U, ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
        (1 / (3 : ℝ) ^ (6 * (n + 1))) * (partSide ω z ^ 12 +
          (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) := by
  set h : Vertex 2 × Fin 2 → ℝ := fun k =>
    partSide ω (k.1 + unitVertex k.2) ^ 6 + partSide ω k.1 ^ 6 with hh
  have hh0 : ∀ k, 0 ≤ h k := fun k => by
    have := one_le_partSide (ω := ω) k.1
    have := one_le_partSide (ω := ω) (k.1 + unitVertex k.2)
    simp only [hh]
    positivity
  have hpoint : ∀ k ∈ latticeEdgesIn U,
      (if k ∈ subcubeExceptionalEdges ω U n then h k else 0) ≤
      (if k ∈ subcubeCrossingEdges U n then h k else 0) +
        ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
          (1 / (3 : ℝ) ^ (6 * (n + 1))) * (partSide ω z ^ 12 +
            (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) := by
    intro k hk
    have hunres := indicator_unresolved_le (ω := ω) (n := n) k.1
    have hsum : (if PlanarResolved ω (scaleCube n k.1) then (0 : ℝ) else 1) * h k ≤
        ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
          (1 / (3 : ℝ) ^ (6 * (n + 1))) * (partSide ω z ^ 12 +
            (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) := by
      refine (mul_le_mul_of_nonneg_right hunres (hh0 k)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun z _ => ?_
      have hz := one_le_partSide (ω := ω) z
      have ha := one_le_partSide (ω := ω) (k.1 + unitVertex k.2)
      have hb := one_le_partSide (ω := ω) k.1
      set a := partSide ω (k.1 + unitVertex k.2)
      set b := partSide ω k.1
      set c := partSide ω z
      simp only [hh]
      rw [div_pow, ← pow_mul, mul_comm (n + 1) 6]
      have h3 : (0 : ℝ) < 3 ^ (6 * (n + 1)) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ h3]
      have hkey : c ^ 6 * (a ^ 6 + b ^ 6) ≤ c ^ 12 + (a ^ 12 + b ^ 12) := by
        nlinarith [sq_nonneg (c ^ 6 - a ^ 6), sq_nonneg (c ^ 6 - b ^ 6), sq_nonneg (a ^ 6),
          sq_nonneg (b ^ 6)]
      calc c ^ 6 * (a ^ 6 + b ^ 6) ≤ c ^ 12 + (a ^ 12 + b ^ 12) := hkey
        _ = 1 / 3 ^ (6 * (n + 1)) * (c ^ 12 + (a ^ 12 + b ^ 12)) * 3 ^ (6 * (n + 1)) := by
          field_simp
    by_cases hexc : k ∈ subcubeExceptionalEdges ω U n
    · rw [if_pos hexc]
      have hexc' := (Finset.mem_filter.1 hexc).2
      by_cases hcr : k ∈ subcubeCrossingEdges U n
      · rw [if_pos hcr]
        have : 0 ≤ ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
            (1 / (3 : ℝ) ^ (6 * (n + 1))) * (partSide ω z ^ 12 +
              (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) :=
          Finset.sum_nonneg fun z _ => by
            have := one_le_partSide (ω := ω) z
            have := one_le_partSide (ω := ω) k.1
            have := one_le_partSide (ω := ω) (k.1 + unitVertex k.2)
            positivity
        linarith
      · rw [if_neg hcr, zero_add]
        have hres : ¬ PlanarResolved ω (scaleCube n k.1) := by
          intro hr
          apply hexc'
          refine ⟨hr, ?_⟩
          by_contra hnot
          exact hcr (Finset.mem_filter.2 ⟨hk, hnot⟩)
        rw [if_neg hres, one_mul] at hsum
        exact hsum
    · rw [if_neg hexc]
      have : 0 ≤ ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
          (1 / (3 : ℝ) ^ (6 * (n + 1))) * (partSide ω z ^ 12 +
            (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) :=
        Finset.sum_nonneg fun z _ => by
          have := one_le_partSide (ω := ω) z
          have := one_le_partSide (ω := ω) k.1
          have := one_le_partSide (ω := ω) (k.1 + unitVertex k.2)
          positivity
      have : 0 ≤ (if k ∈ subcubeCrossingEdges U n then h k else 0) := by
        split_ifs
        · exact hh0 k
        · exact le_rfl
      linarith
  have e1 : edgeSideSum ω (subcubeExceptionalEdges ω U n) =
      ∑ k ∈ latticeEdgesIn U, (if k ∈ subcubeExceptionalEdges ω U n then h k else 0) := by
    rw [← Finset.sum_filter]
    unfold edgeSideSum
    congr 1
    ext k
    simp only [Finset.mem_filter, subcubeExceptionalEdges]
    tauto
  have e2 : edgeSideSum ω (subcubeCrossingEdges U n) =
      ∑ k ∈ latticeEdgesIn U, (if k ∈ subcubeCrossingEdges U n then h k else 0) := by
    rw [← Finset.sum_filter]
    unfold edgeSideSum
    congr 1
    ext k
    simp only [Finset.mem_filter, subcubeCrossingEdges]
    tauto
  rw [e1, e2, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hpoint

/-- The reach-sum majorant of the sum of sixth powers over the exceptional edges. -/
noncomputable def exceptionalReachBound (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ) :
    ℝ≥0∞ :=
  ∑ k ∈ subcubeCrossingEdges U n, edgeReachSum ω 6 k +
    ∑ k ∈ latticeEdgesIn U, ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * (reachSum ω 12 z + edgeReachSum ω 12 k)

theorem measurable_exceptionalReachBound (U : TriadicCube 2) (n : ℕ) :
    Measurable fun ω : Configuration 2 => exceptionalReachBound ω U n := by
  unfold exceptionalReachBound
  exact (Finset.measurable_sum _ fun k _ => measurable_edgeReachSum 6 k).add
    (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun z _ =>
      ((measurable_reachSum 12 z).add (measurable_edgeReachSum 12 k)).const_mul _)

/-- On the partition event the exceptional sum is bounded by its reach-sum majorant. -/
theorem ofReal_edgeSideSum_exceptional_le (hP : PlanarPartitionEvent ω) (U : TriadicCube 2)
    (n : ℕ) :
    ENNReal.ofReal (edgeSideSum ω (subcubeExceptionalEdges ω U n)) ≤
      exceptionalReachBound ω U n := by
  have hnn : ∀ k : Vertex 2 × Fin 2, ∀ z : Vertex 2, 0 ≤ (1 / (3 : ℝ) ^ (6 * (n + 1))) *
      (partSide ω z ^ 12 + (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12)) :=
    fun k z => by positivity
  have hpt : ∀ k : Vertex 2 × Fin 2, ∀ z : Vertex 2,
      ENNReal.ofReal ((1 / (3 : ℝ) ^ (6 * (n + 1))) *
        (partSide ω z ^ 12 + (partSide ω (k.1 + unitVertex k.2) ^ 12 + partSide ω k.1 ^ 12))) ≤
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) *
        (reachSum ω 12 z + edgeReachSum ω 12 k) := by
    intro k z
    have e1 : ENNReal.ofReal (partSide ω z ^ 12) ≤ reachSum ω 12 z :=
      ofReal_partSide_pow_le hP z 11
    have e2 : ENNReal.ofReal (partSide ω (k.1 + unitVertex k.2) ^ 12) ≤
        reachSum ω 12 (k.1 + unitVertex k.2) := ofReal_partSide_pow_le hP _ 11
    have e3 : ENNReal.ofReal (partSide ω k.1 ^ 12) ≤ reachSum ω 12 k.1 :=
      ofReal_partSide_pow_le hP _ 11
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    unfold edgeReachSum
    gcongr
  refine (ENNReal.ofReal_le_ofReal edgeSideSum_exceptional_le).trans ?_
  rw [ENNReal.ofReal_add (edgeSideSum_nonneg _)
    (Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun z _ => hnn k z),
    ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun z _ => hnn k z]
  unfold exceptionalReachBound
  refine add_le_add (ofReal_edgeSideSum_le hP _) (Finset.sum_le_sum fun k _ => ?_)
  rw [ENNReal.ofReal_sum_of_nonneg fun z _ => hnn k z]
  exact Finset.sum_le_sum fun z _ => hpt k z

theorem lintegral_edgeReachSum_le {p : unitInterval} {m : ℕ} {C : ℝ≥0∞}
    (hC : ∀ a, ∫⁻ ω, reachSum ω m a ∂(latticeBondLaw 2 p) ≤ C) (k : Vertex 2 × Fin 2) :
    ∫⁻ ω, edgeReachSum ω m k ∂(latticeBondLaw 2 p) ≤ 2 * C := by
  unfold edgeReachSum
  rw [lintegral_add_left (measurable_reachSum m _), two_mul]
  exact add_le_add (hC _) (hC _)

/-- The expected reach-sum majorant of the exceptional sum. -/
theorem lintegral_exceptionalReachBound_le {p : unitInterval} {C₆ C₁₂ : ℝ≥0∞}
    (h6 : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ C₆)
    (h12 : ∀ a, ∫⁻ ω, reachSum ω 12 a ∂(latticeBondLaw 2 p) ≤ C₁₂) (U : TriadicCube 2) (n : ℕ) :
    ∫⁻ ω, exceptionalReachBound ω U n ∂(latticeBondLaw 2 p) ≤
      ((subcubeCrossingEdges U n).card : ℝ≥0∞) * (2 * C₆) +
        ((latticeEdgesIn U).card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
          (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * (C₁₂ + 2 * C₁₂))) := by
  have hm : ∀ k : Vertex 2 × Fin 2, ∀ z : Vertex 2, Measurable fun ω : Configuration 2 =>
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * (reachSum ω 12 z + edgeReachSum ω 12 k) :=
    fun k z => ((measurable_reachSum 12 z).add (measurable_edgeReachSum 12 k)).const_mul _
  unfold exceptionalReachBound
  rw [lintegral_add_left (Finset.measurable_sum _ fun k _ => measurable_edgeReachSum 6 k),
    lintegral_finsetSum _ fun k _ => measurable_edgeReachSum 6 k,
    lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun z _ => hm k z]
  refine add_le_add ?_ ?_
  · calc ∑ k ∈ subcubeCrossingEdges U n, ∫⁻ ω, edgeReachSum ω 6 k ∂(latticeBondLaw 2 p)
        ≤ ∑ _k ∈ subcubeCrossingEdges U n, 2 * C₆ :=
          Finset.sum_le_sum fun k _ => lintegral_edgeReachSum_le h6 k
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  · calc ∑ k ∈ latticeEdgesIn U, ∫⁻ ω, ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices,
          ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) *
            (reachSum ω 12 z + edgeReachSum ω 12 k) ∂(latticeBondLaw 2 p)
        ≤ ∑ _k ∈ latticeEdgesIn U, ENNReal.ofReal ((9 : ℝ) ^ n) *
          (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * (C₁₂ + 2 * C₁₂)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [lintegral_finsetSum _ fun z _ => hm k z]
          calc ∑ z ∈ (scaleCube n k.1).toIntegerCube.vertices, ∫⁻ ω,
                ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) *
                  (reachSum ω 12 z + edgeReachSum ω 12 k) ∂(latticeBondLaw 2 p)
              ≤ ∑ _z ∈ (scaleCube n k.1).toIntegerCube.vertices,
                ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * (C₁₂ + 2 * C₁₂) := by
                refine Finset.sum_le_sum fun z _ => ?_
                have hmz : Measurable fun ω : Configuration 2 =>
                    reachSum ω 12 z + edgeReachSum ω 12 k :=
                  (measurable_reachSum 12 z).add (measurable_edgeReachSum 12 k)
                rw [lintegral_const_mul _ hmz, lintegral_add_left (measurable_reachSum 12 z)]
                have e1 := h12 z
                have e2 := lintegral_edgeReachSum_le h12 k
                gcongr
            _ = _ := by
                rw [Finset.sum_const, nsmul_eq_mul, card_toIntegerCube_vertices,
                  TriadicCube.volume, scale_scaleCube]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Expected error in the subadditivity of `μ`** (Armstrong and Dario, Lemma 4.8, (4.32), in
expectation). -/
theorem exists_lintegral_sum_planarMu_subcubes_sub_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
              (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
            planarMu ω U q * U.volume) else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n)) := by
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  obtain ⟨C₁₂, hC₁₂, h12⟩ := exists_lintegral_tsum_ninefold_le hpc 12
  refine ⟨1458000000 * (2 * C₆) + 1458000000 * (C₁₂ + 2 * C₁₂) + 5832000000 * (2 * C₆),
    by finiteness, fun U n hn q => ?_⟩
  have h6' : ∀ a, ∫⁻ ω, reachSum ω 6 a ∂(latticeBondLaw 2 p) ≤ C₆ := h6
  have h12' : ∀ a, ∫⁻ ω, reachSum ω 12 a ∂(latticeBondLaw 2 p) ≤ C₁₂ := h12
  set Q₁ := |q 0| + |q 1| with hQ
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 3 ^ n := Real.sq_sqrt (by positivity)
  have hvol := U.volume_pos
  have hE : ((latticeEdgesIn U).card : ℝ) ≤ 2 * U.volume := card_latticeEdgesIn_le U
  have hcr : ((subcubeCrossingEdges U n).card : ℝ) * 3 ^ n ≤ 2 * U.volume :=
    card_subcubeCrossingEdges_le hn
  set A := ENNReal.ofReal (Q₁ ^ 2 * 729000000 * s) with hA
  set B := ENNReal.ofReal (Q₁ ^ 2 * 2916000000 / s) with hB
  set a := ENNReal.ofReal (Q₁ ^ 2 * U.volume / s) with ha
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
        planarMu ω U q * U.volume) else 0) ≤
      A * exceptionalReachBound ω U n + B * ∑ k ∈ latticeEdgesIn U, edgeReachSum ω 6 k := by
    intro ω
    split_ifs with h
    · have hb : ∑ x ∈ U.toIntegerCube.vertices,
            (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
          planarMu ω U q * U.volume ≤
          Q₁ ^ 2 * 729000000 * s * edgeSideSum ω (subcubeExceptionalEdges ω U n) +
            Q₁ ^ 2 * 2916000000 / s * edgeSideSum ω (latticeEdgesIn U) := by
        refine (sum_planarMu_subcubes_sub_le h.1 h.2 hn q).trans (le_of_eq ?_)
        rw [← hQ, ← hs]
        ring
      have hF := edgeSideSum_nonneg (ω := ω) (subcubeExceptionalEdges ω U n)
      have hS := edgeSideSum_nonneg (ω := ω) (latticeEdgesIn U)
      refine (ENNReal.ofReal_le_ofReal hb).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      refine add_le_add ?_ ?_
      · rw [ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_of_nonneg_left (ofReal_edgeSideSum_exceptional_le h.1 U n) zero_le
      · rw [ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_of_nonneg_left (ofReal_edgeSideSum_le h.1 _) zero_le
    · exact zero_le
  have h1 : A * ((subcubeCrossingEdges U n).card : ℝ≥0∞) ≤ 1458000000 * a := by
    rw [← ENNReal.ofReal_natCast, hA, ha, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (1458000000 : ℝ) * (Q₁ ^ 2 * U.volume / s) = 1458000000 * Q₁ ^ 2 * U.volume / s by
      ring, le_div_iff₀ hspos]
    have e : Q₁ ^ 2 * 729000000 * s * ((subcubeCrossingEdges U n).card : ℝ) * s =
        729000000 * Q₁ ^ 2 * (((subcubeCrossingEdges U n).card : ℝ) * 3 ^ n) := by
      rw [← hs2]
      ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hcr (show (0 : ℝ) ≤ 729000000 * Q₁ ^ 2 by positivity)
    linarith
  have h2 : A * (((latticeEdgesIn U).card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
      ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))))) ≤ 1458000000 * a := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), hA, ← ENNReal.ofReal_mul (by positivity), ha,
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show (1458000000 : ℝ) * (Q₁ ^ 2 * U.volume / s) = 1458000000 * Q₁ ^ 2 * U.volume / s by
      ring, le_div_iff₀ hspos]
    have h27 : (3 : ℝ) ^ n * 9 ^ n ≤ 3 ^ (6 * (n + 1)) := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hr : s ^ 2 * 9 ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1))) ≤ 1 := by
      rw [hs2, mul_one_div, div_le_one (by positivity)]
      exact h27
    have e : Q₁ ^ 2 * 729000000 * s * (((latticeEdgesIn U).card : ℝ) *
        ((9 : ℝ) ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1))))) * s =
        729000000 * Q₁ ^ 2 * ((latticeEdgesIn U).card : ℝ) *
          (s ^ 2 * 9 ^ n * (1 / (3 : ℝ) ^ (6 * (n + 1)))) := by ring
    rw [e]
    have hc0 : (0 : ℝ) ≤ 729000000 * Q₁ ^ 2 * ((latticeEdgesIn U).card : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hr hc0
    have := mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ 729000000 * Q₁ ^ 2 by positivity)
    nlinarith
  have h3 : B * ((latticeEdgesIn U).card : ℝ≥0∞) ≤ 5832000000 * a := by
    rw [← ENNReal.ofReal_natCast, hB, ha, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show Q₁ ^ 2 * 2916000000 / s * ((latticeEdgesIn U).card : ℝ) =
        2916000000 * Q₁ ^ 2 * ((latticeEdgesIn U).card : ℝ) / s by ring,
      show (5832000000 : ℝ) * (Q₁ ^ 2 * U.volume / s) = 5832000000 * Q₁ ^ 2 * U.volume / s by
        ring]
    refine div_le_div_of_nonneg_right ?_ hspos.le
    have := mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ 2916000000 * Q₁ ^ 2 by positivity)
    linarith
  refine (lintegral_mono hpoint).trans ?_
  have hX := lintegral_exceptionalReachBound_le h6' h12' U n
  have hY : ∑ k ∈ latticeEdgesIn U, ∫⁻ ω, edgeReachSum ω 6 k ∂(latticeBondLaw 2 p) ≤
      ((latticeEdgesIn U).card : ℝ≥0∞) * (2 * C₆) := by
    calc ∑ k ∈ latticeEdgesIn U, ∫⁻ ω, edgeReachSum ω 6 k ∂(latticeBondLaw 2 p)
        ≤ ∑ _k ∈ latticeEdgesIn U, 2 * C₆ :=
          Finset.sum_le_sum fun k _ => lintegral_edgeReachSum_le h6' k
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∫⁻ ω, (A * exceptionalReachBound ω U n +
        B * ∑ k ∈ latticeEdgesIn U, edgeReachSum ω 6 k) ∂(latticeBondLaw 2 p)
      = A * ∫⁻ ω, exceptionalReachBound ω U n ∂(latticeBondLaw 2 p) +
          B * ∑ k ∈ latticeEdgesIn U, ∫⁻ ω, edgeReachSum ω 6 k ∂(latticeBondLaw 2 p) := by
        rw [lintegral_add_left ((measurable_exceptionalReachBound U n).const_mul A),
          lintegral_const_mul A (measurable_exceptionalReachBound U n),
          lintegral_const_mul B (Finset.measurable_sum _ fun k _ => measurable_edgeReachSum 6 k),
          lintegral_finsetSum _ fun k _ => measurable_edgeReachSum 6 k]
    _ ≤ A * (((subcubeCrossingEdges U n).card : ℝ≥0∞) * (2 * C₆) +
          ((latticeEdgesIn U).card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
            (ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1))) * (C₁₂ + 2 * C₁₂)))) +
        B * (((latticeEdgesIn U).card : ℝ≥0∞) * (2 * C₆)) := by gcongr
    _ = (A * ((subcubeCrossingEdges U n).card : ℝ≥0∞)) * (2 * C₆) +
          (A * (((latticeEdgesIn U).card : ℝ≥0∞) * (ENNReal.ofReal ((9 : ℝ) ^ n) *
            ENNReal.ofReal (1 / (3 : ℝ) ^ (6 * (n + 1)))))) * (C₁₂ + 2 * C₁₂) +
          (B * ((latticeEdgesIn U).card : ℝ≥0∞)) * (2 * C₆) := by ring
    _ ≤ (1458000000 * a) * (2 * C₆) + (1458000000 * a) * (C₁₂ + 2 * C₁₂) +
          (5832000000 * a) * (2 * C₆) := by gcongr
    _ = _ := by ring

end Rigidity.Percolation
