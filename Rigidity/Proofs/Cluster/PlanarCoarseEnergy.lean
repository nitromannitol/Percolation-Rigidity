import Rigidity.Proofs.Cluster.PlanarMeyersHarmonic

/-!
# The energy of a coarsened function on a resolved cube

On a triadic cube `V` resolved by the planar partition, Lemma 3.3 with `s = 2` and the identity
between the energy densities and the Dirichlet form give, for a function `w` on the cluster and a
weight `W ≥ 3 planarReach` on `V`,
`∑_{x ∈ V} |∇[w]_𝒫|²(x) ≤ C² (max_V W)³ B(w, w)` (`sum_gradNormIn_coarse_sq_le_clusterForm`),
the deterministic part of display (4.24) of Armstrong and Dario (the bound on the coarsened
gradient of the minimizers of `μ`, used with `B(u, u) = -2 |V| μ(V, q)` for the minimizer). With
the per-subcube estimate through the Meyers estimate, the pairing of the coarsened gradient of
`w` with a bounded field on `V` is then bounded by a multiple of `B(w, w)` alone
(`edgePairing_clusterExtend_sq_le_clusterForm`): for `w = u(·, □_m, q)|_V - u(·, V, q)` this is
twice the summand of the energy of the differences of Lemma 5.4, so that Lemma 5.5 follows from
Lemma 5.4 on the event where the weights are controlled and the Meyers cells exist.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation Rigidity.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- A real weight dominating `3 planarReach` dominates `3^{ρ'}` for the pair reach scale of the
coarse-graining data of a resolved cube. -/
theorem three_pow_pairReachScale_le_of_le (hP : PlanarPartitionEvent ω) {V : TriadicCube 2}
    (hV : PlanarResolved ω V) {W : ℝ} {z : Vertex 2}
    (hW : 3 * planarReach ω z ≤ ENNReal.ofReal W) :
    (3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z ≤ W := by
  have h1 := (three_pow_pairReachScale_le_planarReach hP hV z).trans hW
  have h2 : ENNReal.ofReal ((3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z) =
      (3 : ℝ≥0∞) ^ (planarCoarseData hP V hV).pairReachScale z := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rw [← h2] at h1
  have hpos : (0 : ℝ) < W := by
    by_contra hcon
    push Not at hcon
    rw [ENNReal.ofReal_of_nonpos hcon] at h1
    have : (0 : ℝ) < (3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z := by positivity
    exact absurd h1 (not_le.2 (ENNReal.ofReal_pos.2 this))
  exact (ENNReal.ofReal_le_ofReal_iff hpos.le).1 h1

/-- **The energy of a coarsened function on a resolved cube.** For a weight `W` with
`3 planarReach ≤ W` on the cluster of `V`,
`∑_{x ∈ V} |∇[w]_𝒫|²(x) ≤ C² W³ B(w, w)`, `C = 4 · (3/2) · 10² · 9² · 2√2`. -/
theorem sum_gradNormIn_coarse_sq_le_clusterForm (hP : PlanarPartitionEvent ω)
    {V : TriadicCube 2} (hV : PlanarResolved ω V) (w : ClusterFun ω V) {W : ℝ}
    (hW : ∀ z ∈ clusterVertices ω V, 3 * planarReach ω z ≤ ENNReal.ofReal W) :
    ∑ x ∈ V.toIntegerCube.vertices, gradNormIn (nearestNeighborGraph 2) V.toIntegerCube.vertices
        (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) x ^ 2 ≤
      (2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) * (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 *
        (2 * √((2 : ℕ) : ℝ))) ^ 2 * (W ^ 3 * clusterForm ω V w w) := by
  have h := planar_sum_gradNormIn_coarseAnchor_rpow_le hP hV (clusterExtend ω V w) (s := 2)
    (by norm_num)
  simp only [Real.rpow_two] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← sum_clusterGradSq_eq_clusterForm V w, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have he : ((3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z) ^
      ((2 : ℝ) * ((2 : ℕ) : ℝ) - 1) =
      ((3 : ℝ) ^ (planarCoarseData hP V hV).pairReachScale z) ^ 3 := by
    rw [show (2 : ℝ) * ((2 : ℕ) : ℝ) - 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [he, gradNormIn_openGraph_eq, Real.sq_sqrt (clusterGradSq_nonneg _ _ _ _)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (three_pow_pairReachScale_le_of_le hP hV (hW z hz)) 3)
    (clusterGradSq_nonneg _ _ _ _)

/-- **The pairing of the coarsened gradient with a bounded field, by the Dirichlet form**
(Armstrong and Dario, proof of Lemma 5.5, Steps 2 and 3, deterministic part, in dimension two).
Under the hypotheses of `edgePairing_clusterExtend_sq_le_of_meyers`, with `V` resolved and
`3 planarReach ≤ W` on `𝒞(V)`,
`⟨∇[w]_𝒫, g⟩_V² ≤ (8 G² 9^n C² A C_M^{1/p} N + 64 G² 3^{n+j} C² W³) B(w, w)`.
-/
theorem edgePairing_clusterExtend_sq_le_clusterForm (hP : PlanarPartitionEvent ω)
    {V : TriadicCube 2} (hVr : PlanarResolved ω V) {j : ℕ} (hj : j < V.scale)
    (hres : ∀ x ∈ V.vertices, (planarPartCube ω x).scale ≤ j) (w : ClusterFun ω V)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (Wt : Vertex 2 → ℝ)
    (hWt : ∀ z, 3 * planarReach ω z ≤ ENNReal.ofReal (Wt z)) {W : ℝ}
    (hW : ∀ z ∈ clusterVertices ω V, 3 * planarReach ω z ≤ ENNReal.ofReal W)
    {p q CM A : ℝ} (hpq : p.HolderConjugate q) (hCM : 0 ≤ CM) (hA0 : 0 ≤ A)
    (I : Finset (ℕ × Vertex 2)) {N : ℕ}
    (hcov : ∀ z ∈ boxClusterVertices ω (innerSquare V j), ∃ c ∈ I, z ∈ cube c.1 c.2)
    (hV : ∀ c ∈ I, enl 1 c.1 c.2 ⊆ V.toIntegerCube.vertices)
    (hN : ∀ x, (I.filter fun c => x ∈ enl 1 c.1 c.2).card ≤ N)
    (hA : ∀ c ∈ I, avg (cube c.1 c.2) (fun x => (Wt x ^ 3) ^ q) ^ (1 / q) ≤ A)
    (hM : ∀ c ∈ I, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w) x ^ p) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (clusterVertices ω V) (clusterExtend ω V w)) ^ p) :
    edgePairing V.toIntegerCube.vertices g
        (fun x => clusterExtend ω V w (planarCoarseAnchor ω x)) ^ 2 ≤
      (8 * G ^ 2 * 9 ^ V.scale *
          ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
            (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 *
            (A * (CM ^ (1 / p) * (N : ℝ)))) +
        64 * G ^ 2 * 3 ^ (V.scale + j) *
          ((2 * ((2 : ℕ) : ℝ) * (3 / 2 * (2 * ((4 : ℕ) : ℝ) + 2) ^ 2) *
            (2 * ((4 : ℕ) : ℝ) + 1) ^ 2 * (2 * √((2 : ℕ) : ℝ))) ^ 2 * W ^ 3)) *
        clusterForm ω V w w := by
  have h := edgePairing_clusterExtend_sq_le_of_meyers hP hj hres w hg Wt hWt hpq hCM hA0 I hcov hV
    hN hA hM
  have h2 := sum_gradNormIn_coarse_sq_le_clusterForm hP hVr w hW
  refine h.trans (le_of_le_of_eq (add_le_add_right
    (mul_le_mul_of_nonneg_left h2 (by positivity)) _) ?_)
  ring

end Rigidity.Proofs.Cluster
