import Rigidity.Proofs.Cluster.PlanarCoarseEnergyMoments

/-!
# Pairings on a cube and on its subcubes, in expectation

Armstrong and Dario, proof of Lemma 5.7, Step 2, display (5.29), in expectation, in dimension two.
For a triadic cube `U`, `n ≤ scale U`, a deterministic field `g` with `|g| ≤ G` on the lattice edges
and the minimizer `u = u(·, U, q)` of `μ(U, q)`, the pairing of `g` with the coarsened gradient of
`u` over `U` differs from the sum of the pairings over the subcubes of scale `n` by at most the
crossing edges times the energy (`edgePairing_sub_sum_subcubes_sq_le`), so that
`E[(⟨∇[u]_𝒫, g⟩_U - ∑_V ⟨∇[u]_𝒫, g⟩_V)²] ≤ C G² |q|₁² 3^{-n} |U|² |U|^{1/a}`
for every `a ≥ 2` (`exists_lintegral_edgePairing_sub_sum_subcubes_le`): after division by `|U|²`
this is `C G² |q|₁² 3^{-n} |U|^{1/a}`, small when `|U|` is a bounded power of `3^n`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **Pairings on a cube and on its subcubes, in expectation** (Armstrong and Dario, proof of
Lemma 5.7, Step 2, in dimension two). -/
theorem exists_lintegral_edgePairing_sub_sum_subcubes_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {a : ℕ} (ha : 2 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ (q : Fin 2 → ℝ)
      (g : Vertex 2 → Fin 2 → ℝ) (G : ℝ), (∀ x i, |g x i| ≤ G) →
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal ((edgePairing U.toIntegerCube.vertices g
              (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x)) -
            ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g
              (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))) ^ 2)
          else 0) ∂(latticeBondLaw 2 p) ≤
        C * ENNReal.ofReal (G ^ 2) * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) *
          ENNReal.ofReal (U.volume / 3 ^ n) * (U.toIntegerCube.vertices.card : ℝ≥0∞) *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (1 / (a : ℝ)) := by
  obtain ⟨C, hC, hE⟩ := exists_lintegral_coarse_minimizer_le hpc ha
  refine ⟨4 * C, ENNReal.mul_ne_top (by norm_num) hC, fun U n hn q g G hg => ?_⟩
  set μ := latticeBondLaw 2 p with hμ
  set F : Configuration 2 → ℝ≥0∞ := fun ω => if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
    ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
      gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
        (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x)) x ^ 2)
    else 0 with hF
  have hD : ((subcubeCrossingEdges U n).card : ℝ) ≤ 2 * (U.volume / 3 ^ n) := by
    have h := card_subcubeCrossingEdges_le hn
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    exact h
  have hpoint : ∀ ω : Configuration 2, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
      ENNReal.ofReal ((edgePairing U.toIntegerCube.vertices g
          (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x)) -
        ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g
          (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))) ^ 2)
      else 0) ≤ 4 * ENNReal.ofReal (G ^ 2) * ENNReal.ofReal (U.volume / 3 ^ n) * F ω := by
    intro ω
    split_ifs with h
    · have hFω : F ω = ENNReal.ofReal (∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
            (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))
              x ^ 2) := by
        simp only [hF, if_pos h]
      rw [hFω]
      have h1 := edgePairing_sub_sum_subcubes_sq_le hn hg
        (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))
      have hS0 : 0 ≤ ∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
            (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))
              x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : (edgePairing U.toIntegerCube.vertices g
          (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x)) -
        ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g
          (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))) ^ 2 ≤
          4 * G ^ 2 * (U.volume / 3 ^ n) * ∑ x ∈ U.toIntegerCube.vertices,
            gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
              (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))
                x ^ 2 := by
        refine h1.trans ?_
        have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
        calc G ^ 2 * ((subcubeCrossingEdges U n).card : ℝ) * (2 * ∑ x ∈ U.toIntegerCube.vertices,
              gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
                (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))
                  x ^ 2)
            ≤ G ^ 2 * (2 * (U.volume / 3 ^ n)) * (2 * ∑ x ∈ U.toIntegerCube.vertices,
              gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices
                (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))
                  x ^ 2) := by gcongr
          _ = _ := by ring
      refine (ENNReal.ofReal_le_ofReal h2).trans (le_of_eq ?_)
      have hv : 0 ≤ U.volume / 3 ^ n := div_nonneg U.volume_pos.le (by positivity)
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · exact zero_le
  calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal ((edgePairing U.toIntegerCube.vertices g
              (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x)) -
            ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g
              (fun x => clusterExtend ω U (planarMuMinimizer ω U q) (planarCoarseAnchor ω x))) ^ 2)
          else 0) ∂μ
      ≤ ∫⁻ ω, (4 * ENNReal.ofReal (G ^ 2) * ENNReal.ofReal (U.volume / 3 ^ n)) * F ω ∂μ :=
        lintegral_mono hpoint
    _ = (4 * ENNReal.ofReal (G ^ 2) * ENNReal.ofReal (U.volume / 3 ^ n)) * ∫⁻ ω, F ω ∂μ :=
        lintegral_const_mul' _ _ (by finiteness)
    _ ≤ (4 * ENNReal.ofReal (G ^ 2) * ENNReal.ofReal (U.volume / 3 ^ n)) *
          (C * ENNReal.ofReal ((|q 0| + |q 1|) ^ 2) * (U.toIntegerCube.vertices.card : ℝ≥0∞) *
            (U.toIntegerCube.vertices.card : ℝ≥0∞) ^ (1 / (a : ℝ))) := by
        gcongr
        exact hE U q
    _ = _ := by ring

end Rigidity.Proofs.Cluster
