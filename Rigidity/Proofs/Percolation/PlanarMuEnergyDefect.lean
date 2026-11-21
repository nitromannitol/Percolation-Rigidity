import Rigidity.Proofs.Percolation.PlanarSecondVariation
import Rigidity.Proofs.Percolation.PlanarMuSubadditiveMoments
import Rigidity.Proofs.Percolation.PlanarMuConvergence

/-!
# The energy of the differences between the minimizers of `μ` at two scales

For a resolved triadic cube `U` and `n ≤ U.scale`, let `u` be a minimizer of `μ(U, q)` and `u_V` a
minimizer of `μ(V, q)` for each resolved subcube `V` of scale `n`. The quantity

`D_n(U, q) = ∑_V B_V(u|_V - u_V, u|_V - u_V) / 2`

is the energy of the differences `u - u_V` on the clusters of the subcubes. By the second variation
and the subadditivity error bound,

`D_n(U, q) + ∑_{x ∈ U} 1{V(x) resolved} μ(V(x), q) - |U| μ(U, q) ≤
  |q|₁² (729000000 · 3 ^ (n / 2) S_F + 2916000000 · 3 ^ (-n / 2) S)`,

and, taking expectations and using the stationarity of `μ` across cubes of the same scale,

`E[D_n(U, q)] + |U| E[-μ(U, q)] ≤ |U| E[-μ(W, q)] + C |q|₁² |U| (3 ^ (-n / 2) + exp (-c 3 ^ n))`

for every cube `W` of scale `n`. This is Lemma 5.4 of Armstrong and Dario for `μ` (display
(5.10), first term), in dimension two: the right side is `|U|` times the decrease of `E[-μ]` from
scale `n` to the scale of `U`, up to the error.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- A minimizer of `μ(U, q)`, on the partition event and for a resolved cube (zero otherwise). -/
noncomputable def planarMuMinimizer (ω : Configuration 2) (U : TriadicCube 2) (q : Fin 2 → ℝ) :
    ClusterFun ω U :=
  if h : PlanarPartitionEvent ω ∧ PlanarResolved ω U then
    Classical.choose (exists_planarMu_minimizer h.1 h.2 q)
  else 0

theorem planarMuMinimizer_spec (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (q : Fin 2 → ℝ) :
    planarMuMinimizer ω U q ∈ clusterHarmonic ω U ∧ ∀ w ∈ clusterHarmonic ω U,
      clusterForm ω U w (planarMuMinimizer ω U q) = coarsePairing ω U q w := by
  have h : PlanarPartitionEvent ω ∧ PlanarResolved ω U := ⟨hP, hU⟩
  rw [planarMuMinimizer, dif_pos h]
  obtain ⟨h1, h2, -⟩ := Classical.choose_spec (exists_planarMu_minimizer h.1 h.2 q)
  exact ⟨h1, h2⟩

/-- The energy `D_n(U, q)` of the differences between the restrictions of the minimizer of
`μ(U, q)` and the minimizers of `μ(V, q)` on the resolved subcubes `V` of scale `n`. -/
noncomputable def planarMuDefect (ω : Configuration 2) (U : TriadicCube 2) (n : ℕ)
    (q : Fin 2 → ℝ) : ℝ :=
  ∑ V ∈ (subcubesAt U n).filter (fun V => PlanarResolved ω V),
    clusterForm ω V (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q)
      (clusterRestrictExt V (planarMuMinimizer ω U q) - planarMuMinimizer ω V q) / 2

theorem planarMuDefect_nonneg (U : TriadicCube 2) (n : ℕ) (q : Fin 2 → ℝ) :
    0 ≤ planarMuDefect ω U n q :=
  Finset.sum_nonneg fun _ _ => div_nonneg (clusterForm_self_nonneg _) (by norm_num)

/-- The energy of the differences and the subadditivity defect of `μ`, with Young's parameter. -/
theorem planarMuDefect_add_sum_le_young (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ) {t : ℝ} (ht : 0 < t) :
    planarMuDefect ω U n q + ∑ x ∈ U.toIntegerCube.vertices,
        (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) ≤
      planarMu ω U q * U.volume + (|q 0| + |q 1|) *
        ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n))) / t +
          t * (36 * (|q 0| + |q 1|) ^ 2 *
            (162000000 * edgeSideSum ω (latticeEdgesIn U)))) / 2 := by
  rw [planarMuDefect]
  obtain ⟨hu, hvar⟩ := planarMuMinimizer_spec hP hU q
  have hsub := sum_clusterForm_sub_add_sum_planarMu_subcubes_le hP hU hn q hu hvar
    (fun V => planarMuMinimizer ω V q) (fun V _ hV => planarMuMinimizer_spec hP hV q)
  beta_reduce at hsub
  set u := planarMuMinimizer ω U q with hudef
  have herr : ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
      (if x + unitVertex i ∈ U.toIntegerCube.vertices ∧
          ¬ (PlanarResolved ω (scaleCube n x) ∧
            x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices) then
        q i * (coarsen ω U u (x + unitVertex i) - coarsen ω U u x) else 0) =
      ∑ k ∈ subcubeExceptionalEdges ω U n,
        q k.2 * (coarsen ω U u (k.1 + unitVertex k.2) - coarsen ω U u k.1) := by
    rw [subcubeExceptionalEdges, latticeEdgesIn, Finset.filter_filter, Finset.sum_filter,
      Finset.sum_product]
  rw [herr] at hsub
  have hμ : planarMu ω U q = (clusterForm ω U u u / 2 - coarsePairing ω U q u) / U.volume := by
    rw [eq_div_iff U.volume_pos.ne', planarMu_mul_volume_eq hP hU q hu hvar, ← hvar u hu]
    ring
  have hBu := clusterForm_minimizer_le hP hU q hu hvar hμ
  have hy := sum_edges_coarsen_le_young hP hU (subcubeExceptionalEdges_subset (ω := ω) U n) q u ht
  have hQ0 : 0 ≤ |q 0| + |q 1| := by positivity
  have hmono : (|q 0| + |q 1|) * ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n)))
      / t + t * (2 * clusterForm ω U u u)) / 2 ≤
      (|q 0| + |q 1|) * ((9 * (162000000 * edgeSideSum ω (subcubeExceptionalEdges ω U n))) / t +
        t * (36 * (|q 0| + |q 1|) ^ 2 *
          (162000000 * edgeSideSum ω (latticeEdgesIn U)))) / 2 := by
    have h2B : 2 * clusterForm ω U u u ≤ 36 * (|q 0| + |q 1|) ^ 2 *
        (162000000 * edgeSideSum ω (latticeEdgesIn U)) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2B ht.le
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) hQ0)
      (by norm_num)
  linarith

/-- **The energy of the differences and the subadditivity defect of `μ`** (Armstrong and Dario,
proof of Lemma 5.4, display (5.11), with the planar error bound). -/
theorem planarMuDefect_add_sum_sub_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) {n : ℕ} (hn : n ≤ U.scale) (q : Fin 2 → ℝ) :
    planarMuDefect ω U n q + ∑ x ∈ U.toIntegerCube.vertices,
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
  · have h := planarMuDefect_add_sum_le_young hP hU hn q (t := 1) one_pos
    rw [← hQ, ← hQ0] at h
    rw [← hQ0]
    simp only [zero_mul, zero_div, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h ⊢
    linarith
  · have ht : 0 < 1 / (Q₁ * s) := by positivity
    have h := planarMuDefect_add_sum_le_young hP hU hn q ht
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

/-- **Expected size of functions dominated by the subadditivity error bound.** If `g` is at most
`|q|₁² (729000000 · 3 ^ (n / 2) S_F + 2916000000 · 3 ^ (-n / 2) S)` on the partition event for
the resolved cube `U`, then `E[g⁺; P, U resolved] ≤ C |q|₁² |U| / 3 ^ (n / 2)`. -/
theorem exists_lintegral_le_of_le_subadditivityBound {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∀ g : Configuration 2 → ℝ, (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω U →
        g ω ≤ (|q 0| + |q 1|) ^ 2 * (729000000 * Real.sqrt (3 ^ n) *
          edgeSideSum ω (subcubeExceptionalEdges ω U n) +
          2916000000 / Real.sqrt (3 ^ n) * edgeSideSum ω (latticeEdgesIn U))) →
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (g ω) else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * U.volume / Real.sqrt (3 ^ n)) := by
  obtain ⟨C₆, hC₆, h6⟩ := exists_lintegral_tsum_ninefold_le hpc 6
  obtain ⟨C₁₂, hC₁₂, h12⟩ := exists_lintegral_tsum_ninefold_le hpc 12
  refine ⟨1458000000 * (2 * C₆) + 1458000000 * (C₁₂ + 2 * C₁₂) + 5832000000 * (2 * C₆),
    by finiteness, fun U n hn q g hg => ?_⟩
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
      ENNReal.ofReal (g ω) else 0) ≤
      A * exceptionalReachBound ω U n + B * ∑ k ∈ latticeEdgesIn U, edgeReachSum ω 6 k := by
    intro ω
    split_ifs with h
    · have hb : g ω ≤
          Q₁ ^ 2 * 729000000 * s * edgeSideSum ω (subcubeExceptionalEdges ω U n) +
            Q₁ ^ 2 * 2916000000 / s * edgeSideSum ω (latticeEdgesIn U) := by
        refine (hg ω h.1 h.2).trans (le_of_eq ?_)
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
/-- **The energy of the differences in expectation** (Armstrong and Dario, Lemma 5.4, display
(5.10), first term, in dimension two). For every resolved cube `U`, `n ≤ U.scale` and every cube `W`
of scale `n`,
`E[D_n(U, q)] + |U| E[-μ(U, q)] ≤ |U| E[-μ(W, q)] + C |q|₁² |U| (3 ^ (-n / 2) + exp (-c 3 ^ n))`,
the expectations being taken on the partition event and the resolution of the cube. -/
theorem exists_lintegral_planarMuDefect_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ c : ℝ, 0 < c ∧ ∀ (U W : TriadicCube 2) (n : ℕ), n ≤ U.scale →
      W.scale = n → ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMuDefect ω U n q) else 0) ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal U.volume * ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal U.volume * ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
          ENNReal.ofReal (-planarMu ω W q) else 0) ∂(latticeBondLaw 2 p) +
        C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2 * U.volume *
          (1 / Real.sqrt (3 ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C₁, hC₁, hint⟩ := exists_lintegral_le_of_le_subadditivityBound hpc
  obtain ⟨C₂, hC₂, c, hc, hstat⟩ := exists_lintegral_neg_planarMu_le_of_scale_eq hpc
  refine ⟨C₁ + C₂, by finiteness, c, hc, fun U W n hn hW q => ?_⟩
  set Q := (|q 0| + |q 1|) ^ 2 with hQ
  set s := Real.sqrt ((3 : ℝ) ^ n) with hs
  set e := Real.exp (-c * (3 : ℝ) ^ n) with he
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hvol := U.volume_pos
  have hQ0 : 0 ≤ Q := by positivity
  set G : Configuration 2 → ℝ := fun ω => planarMuDefect ω U n q +
    ∑ x ∈ U.toIntegerCube.vertices,
      (if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) -
    planarMu ω U q * U.volume with hG
  set H : Vertex 2 → Configuration 2 → ℝ≥0∞ := fun x ω =>
    if PlanarPartitionEvent ω ∧ PlanarResolved ω (scaleCube n x) then
      ENNReal.ofReal (-planarMu ω (scaleCube n x) q) else 0 with hH
  have hpoint : ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (planarMuDefect ω U n q) else 0) +
      ENNReal.ofReal U.volume * (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
        ENNReal.ofReal (-planarMu ω U q) else 0) ≤
      ∑ x ∈ U.toIntegerCube.vertices, H x ω +
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (G ω) else 0) := by
    intro ω
    split_ifs with hω
    · have hD := planarMuDefect_nonneg (ω := ω) U n q
      have hμU := planarMu_nonpos hω.1 hω.2 q
      have hnn : ∀ x ∈ U.toIntegerCube.vertices,
          0 ≤ -(if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) := by
        intro x _
        split_ifs with hx
        · exact neg_nonneg.2 (planarMu_nonpos hω.1 hx q)
        · simp
      have hsplit : planarMuDefect ω U n q + U.volume * -planarMu ω U q = G ω +
          ∑ x ∈ U.toIntegerCube.vertices,
            -(if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0) := by
        rw [Finset.sum_neg_distrib, hG]
        ring
      calc ENNReal.ofReal (planarMuDefect ω U n q) +
            ENNReal.ofReal U.volume * ENNReal.ofReal (-planarMu ω U q)
          = ENNReal.ofReal (planarMuDefect ω U n q + U.volume * -planarMu ω U q) := by
            rw [ENNReal.ofReal_add hD (mul_nonneg hvol.le (neg_nonneg.2 hμU)),
              ENNReal.ofReal_mul hvol.le]
        _ = ENNReal.ofReal (G ω + ∑ x ∈ U.toIntegerCube.vertices,
            -(if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0)) := by
            rw [hsplit]
        _ ≤ ENNReal.ofReal (G ω) + ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
            -(if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0)) :=
            ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (G ω) + ∑ x ∈ U.toIntegerCube.vertices, ENNReal.ofReal
            (-(if PlanarResolved ω (scaleCube n x) then planarMu ω (scaleCube n x) q else 0)) := by
            rw [ENNReal.ofReal_sum_of_nonneg hnn]
        _ ≤ ENNReal.ofReal (G ω) + ∑ x ∈ U.toIntegerCube.vertices, H x ω := by
            gcongr with x hx
            simp only [hH]
            split_ifs with h1 h2 h2
            · exact le_rfl
            · exact absurd ⟨hω.1, h1⟩ h2
            · simp
            · simp
        _ = _ := add_comm _ _
    · simp
  have hHmeas : ∀ x ∈ U.toIntegerCube.vertices, Measurable (H x) := fun x _ =>
    measurable_planarMu_indicator (scaleCube n x) q
  have hHx : ∀ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, H x ω ∂(latticeBondLaw 2 p) ≤
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
          ENNReal.ofReal (-planarMu ω W q) else 0) ∂(latticeBondLaw 2 p) +
        C₂ * ENNReal.ofReal (Q * e) := by
    intro x _
    have h := hstat W (scaleCube n x) (by rw [hW, scale_scaleCube]) q
    rw [hW] at h
    exact h
  have hGint := hint U n hn q G fun ω hP hU => planarMuDefect_add_sum_sub_le hP hU hn q
  have hcard : (U.toIntegerCube.vertices.card : ℝ≥0∞) = ENNReal.ofReal U.volume := by
    rw [volume_eq_card, ENNReal.ofReal_natCast]
  set I := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
      ENNReal.ofReal (-planarMu ω W q) else 0) ∂(latticeBondLaw 2 p) with hI
  have hfin : ENNReal.ofReal (Q * U.volume * (1 / s + e)) =
      ENNReal.ofReal (Q * U.volume / s) + ENNReal.ofReal U.volume * ENNReal.ofReal (Q * e) := by
    rw [← ENNReal.ofReal_mul hvol.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMuDefect ω U n q) else 0) ∂(latticeBondLaw 2 p) +
        ENNReal.ofReal U.volume * ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0) ∂(latticeBondLaw 2 p)
      ≤ ∫⁻ ω, ((if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMuDefect ω U n q) else 0) +
        ENNReal.ofReal U.volume * (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (-planarMu ω U q) else 0)) ∂(latticeBondLaw 2 p) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact le_lintegral_add _ _
    _ ≤ ∫⁻ ω, (∑ x ∈ U.toIntegerCube.vertices, H x ω +
        (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (G ω) else 0))
          ∂(latticeBondLaw 2 p) := lintegral_mono hpoint
    _ = ∑ x ∈ U.toIntegerCube.vertices, ∫⁻ ω, H x ω ∂(latticeBondLaw 2 p) +
        ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then ENNReal.ofReal (G ω) else 0)
          ∂(latticeBondLaw 2 p) := by
        rw [lintegral_add_left (Finset.measurable_sum _ hHmeas), lintegral_finsetSum _ hHmeas]
    _ ≤ ∑ _x ∈ U.toIntegerCube.vertices, (I + C₂ * ENNReal.ofReal (Q * e)) +
        C₁ * ENNReal.ofReal (Q * U.volume / s) := add_le_add (Finset.sum_le_sum hHx) hGint
    _ = ENNReal.ofReal U.volume * I + (C₁ * ENNReal.ofReal (Q * U.volume / s) +
        C₂ * (ENNReal.ofReal U.volume * ENNReal.ofReal (Q * e))) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ ENNReal.ofReal U.volume * I + (C₁ + C₂) * ENNReal.ofReal (Q * U.volume * (1 / s + e)) := by
        rw [hfin, add_mul, mul_add, mul_add]
        gcongr
        · exact le_add_right le_rfl
        · exact le_add_left le_rfl

end Rigidity.Percolation
