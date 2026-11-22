import Rigidity.Proofs.Percolation.PlanarOmegaChain
import Rigidity.Proofs.Cluster.PlanarRestrictQuad
import Rigidity.Proofs.Cluster.ReverseHolderSobolev

/-!
# Measurable majorants for the proof of Lemma 5.9 of Armstrong and Dario

The quantities of the pointwise bound `planarOmega_chain` (energies of minimizers on subcubes,
coarsening errors) are not known to be measurable functions of the configuration. Since the
Lebesgue integral of a sum splits when all but one summand are measurable, each of them except
one is bounded by a measurable majorant with controlled expectation:

* `exists_subadditivityMajorant`: the subadditivity error bound of `μ` of Lemma 5.4 (the bound of
  `exists_lintegral_le_of_le_subadditivityBound` with its majorant);
* `ofReal_coarseError_le`: the coarsening error `∑_{C_*(U)} |w - [w]_P|²` of a function `w` on the
  cluster, by the reach of the partition and the energy of `w` (Lemma 3.2 with `s = 2`), and the
  splitting `R⁴ ≤ λ + R⁸/λ` of the reach.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical ENNReal

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **The subadditivity error bound of `μ` with a measurable majorant** (the bound of Lemma 5.4,
display (5.11), in dimension two). -/
theorem exists_subadditivityMajorant {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∃ M : Configuration 2 → ℝ≥0∞, Measurable M ∧
        (∀ g : Configuration 2 → ℝ, (∀ ω, PlanarPartitionEvent ω → PlanarResolved ω U →
          g ω ≤ (|q 0| + |q 1|) ^ 2 * (729000000 * Real.sqrt (3 ^ n) *
            edgeSideSum ω (subcubeExceptionalEdges ω U n) +
            2916000000 / Real.sqrt (3 ^ n) * edgeSideSum ω (latticeEdgesIn U))) →
          ∀ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
            ENNReal.ofReal (g ω) else 0) ≤ M ω) ∧
        ∫⁻ ω, M ω ∂(latticeBondLaw 2 p) ≤
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
  refine ⟨fun ω => A * exceptionalReachBound ω U n +
      B * ∑ k ∈ latticeEdgesIn U, edgeReachSum ω 6 k,
    ((measurable_exceptionalReachBound U n).const_mul A).add
      ((Finset.measurable_sum _ fun k _ => measurable_edgeReachSum 6 k).const_mul B),
    fun g hg ω => ?_, ?_⟩
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

/-- **The coarsening error by the reach and the energy** (Armstrong and Dario, Lemma 3.2 with
`s = 2`, in dimension two), with the splitting `R⁴ ≤ λ + λ⁻¹ R⁸` of the reach. -/
theorem ofReal_coarseError_le (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (w : ClusterFun ω U) {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ∞) :
    ENNReal.ofReal (∑ x ∈ clusterVertices ω U,
        (clusterExtend ω U w x - clusterExtend ω U w (planarCoarseAnchor ω x)) ^ 2) ≤
      ENNReal.ofReal ((3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ 2) *
        ((l + l⁻¹ * ∑ z ∈ U.toIntegerCube.vertices, planarReach ω z ^ 8) *
          ENNReal.ofReal (clusterForm ω U w w)) := by
  set K := (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2 * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
    (2 * √((2 : ℕ) : ℝ))) with hK
  have hK0 : 0 ≤ K := by positivity
  set P := planarCoarseData hP U hU with hPdef
  set g : Vertex 2 → ℝ := fun z =>
    gradNormIn (openGraph ω) (clusterVertices ω U) (clusterExtend ω U w) z ^ 2 with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => sq_nonneg _
  have h32 := planar_sum_abs_sub_coarseAnchor_rpow_le hP hU (clusterExtend ω U w)
    (s := 2) (by norm_num)
  have e1 : ∀ x, |clusterExtend ω U w x - clusterExtend ω U w (planarCoarseAnchor ω x)| ^ (2 : ℝ) =
      (clusterExtend ω U w x - clusterExtend ω U w (planarCoarseAnchor ω x)) ^ 2 := fun x => by
    rw [Real.rpow_two, sq_abs]
  have e2 : ∀ z, ((3 : ℝ) ^ (planarCoarseData hP U hU).reachScale z) ^ ((2 : ℝ) * ((2 : ℕ) : ℝ)) =
      ((3 : ℝ) ^ (planarCoarseData hP U hU).reachScale z) ^ 4 := fun z => by
    rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [e1, Real.rpow_two, e2] at h32
  -- `∑ g = B(w, w)`
  have hsumg : ∑ z ∈ clusterVertices ω U, g z = clusterForm ω U w w := by
    rw [← Rigidity.Proofs.Cluster.sum_clusterGradSq_eq_clusterForm U w]
    refine Finset.sum_congr rfl fun z _ => ?_
    change gradNormIn (openGraph ω) (clusterVertices ω U) (clusterExtend ω U w) z ^ 2 = _
    rw [Rigidity.Proofs.Cluster.gradNormIn_openGraph_eq,
      Real.sq_sqrt (Rigidity.Proofs.Cluster.clusterGradSq_nonneg _ _ _ _)]
  set M := l + l⁻¹ * ∑ z ∈ U.toIntegerCube.vertices, planarReach ω z ^ 8 with hM
  have hR : ∀ z ∈ clusterVertices ω U,
      ENNReal.ofReal (((3 : ℝ) ^ P.reachScale z) ^ 4 * g z) ≤ M * ENNReal.ofReal (g z) := by
    intro z hz
    rw [ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have h3 : ENNReal.ofReal (((3 : ℝ) ^ P.reachScale z) ^ 4) ≤ planarReach ω z ^ 4 := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat]
      exact pow_le_pow_left₀ zero_le (three_pow_reachScale_le_planarReach hP hU hz) 4
    refine h3.trans ((ENNReal.le_add_inv_mul_sq hl0 hlt).trans ?_)
    rw [hM, ← pow_mul]
    gcongr
    exact Finset.single_le_sum (f := fun z => planarReach ω z ^ 8) (fun _ _ => zero_le)
      ((U.mem_toIntegerCube_vertices z).2 (mem_clusterVertices.1 hz).1)
  calc ENNReal.ofReal (∑ x ∈ clusterVertices ω U,
        (clusterExtend ω U w x - clusterExtend ω U w (planarCoarseAnchor ω x)) ^ 2)
      ≤ ENNReal.ofReal (K ^ 2 * ∑ z ∈ clusterVertices ω U,
          ((3 : ℝ) ^ P.reachScale z) ^ 4 * g z) := ENNReal.ofReal_le_ofReal h32
    _ = ENNReal.ofReal (K ^ 2) * ∑ z ∈ clusterVertices ω U,
          ENNReal.ofReal (((3 : ℝ) ^ P.reachScale z) ^ 4 * g z) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun z _ => mul_nonneg (by positivity) (hg0 z)]
    _ ≤ ENNReal.ofReal (K ^ 2) * ∑ z ∈ clusterVertices ω U, M * ENNReal.ofReal (g z) := by
        gcongr with z hz
        exact hR z hz
    _ = ENNReal.ofReal (K ^ 2) * (M * ENNReal.ofReal (clusterForm ω U w w)) := by
        rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun z _ => hg0 z, hsumg]

end Rigidity.Percolation
