import Rigidity.Proofs.Cluster.PlanarCoarseEnergy
import Rigidity.Proofs.Percolation.PlanarSubcubeCounts

/-!
# Pairings on a cube and on its subcubes

For a triadic cube `U` and `n ≤ scale U`, the pairing of an edge field `g` with the gradient of a
function `f` over the edges inside `U` differs from the sum of the pairings over its subcubes of
scale `n` by the pairing over the edges crossing between subcubes. By the Cauchy–Schwarz
inequality, when `|g| ≤ G`,
`(⟨∇f, g⟩_U - ∑_V ⟨∇f, g⟩_V)² ≤ G² |D| · 2 ∑_{x ∈ U} |∇f|²(x)`, where `D` is the set of crossing
edges, `|D| 3^n ≤ 2 |U|` (`card_subcubeCrossingEdges_le`). This is the deterministic part of Step 2
of the proof of Lemma 5.7 of Armstrong and Dario (display (5.29)), in dimension two.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation
open scoped BigOperators Classical

/-- **Pairings on a cube and on its subcubes** (Armstrong and Dario, proof of Lemma 5.7, Step 2,
deterministic part, in dimension two). -/
theorem edgePairing_sub_sum_subcubes_sq_le {U : TriadicCube 2} {n : ℕ} (hn : n ≤ U.scale)
    {g : Vertex 2 → Fin 2 → ℝ} {G : ℝ} (hg : ∀ x i, |g x i| ≤ G) (f : Vertex 2 → ℝ) :
    (edgePairing U.toIntegerCube.vertices g f -
        ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g f) ^ 2 ≤
      G ^ 2 * (subcubeCrossingEdges U n).card *
        (2 * ∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices f x ^ 2) := by
  set D := subcubeCrossingEdges U n with hD
  set F : Vertex 2 × Fin 2 → ℝ := fun k => g k.1 k.2 * (f (k.1 + unitVertex k.2) - f k.1) with hF
  -- the pairings over the subcubes
  have hsub : ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g f =
      ∑ x ∈ U.toIntegerCube.vertices, ∑ i : Fin 2,
        if x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices then F (x, i) else 0 := by
    rw [sum_scaleCube_eq hn (fun V x => ∑ i : Fin 2,
      if x + unitVertex i ∈ V.toIntegerCube.vertices then F (x, i) else 0)]
    rfl
  have hdiff : edgePairing U.toIntegerCube.vertices g f -
      ∑ V ∈ subcubesAt U n, edgePairing V.toIntegerCube.vertices g f = ∑ k ∈ D, F k := by
    rw [hsub, edgePairing, ← Finset.sum_sub_distrib, hD, subcubeCrossingEdges, latticeEdgesIn,
      Finset.sum_filter, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : x + unitVertex i ∈ U.toIntegerCube.vertices
    · by_cases h2 : x + unitVertex i ∈ (scaleCube n x).toIntegerCube.vertices
      · simp only [h1, h2, if_true, not_true_eq_false, if_false, hF, sub_self]
      · simp only [h1, h2, if_true, not_false_eq_true, if_false, sub_zero, hF]
    · have h2 : x + unitVertex i ∉ (scaleCube n x).toIntegerCube.vertices := by
        intro h2
        apply h1
        rw [TriadicCube.mem_toIntegerCube_vertices] at h2 ⊢
        have hxU : x ∈ U.vertices := (U.mem_toIntegerCube_vertices x).1 hx
        exact scaleCube_subset hn hxU h2
      simp only [h1, h2, if_false, sub_zero]
  -- Cauchy–Schwarz over the crossing edges
  set a : Vertex 2 × Fin 2 → ℝ := fun k => g k.1 k.2 with ha
  set b : Vertex 2 × Fin 2 → ℝ := fun k => f (k.1 + unitVertex k.2) - f k.1 with hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D a b
  have ha2 : ∑ k ∈ D, a k ^ 2 ≤ G ^ 2 * D.card := by
    calc ∑ k ∈ D, a k ^ 2 ≤ ∑ _k ∈ D, G ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [ha, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hg _ _) 2
      _ = G ^ 2 * D.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hb2 : ∑ k ∈ D, b k ^ 2 ≤ edgeEnergy U.toIntegerCube.vertices f := by
    rw [edgeEnergy, hD, subcubeCrossingEdges, latticeEdgesIn, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_product]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
    split_ifs
    all_goals first | exact le_rfl | exact sq_nonneg _
  have hE := edgeEnergy_le_two_mul_sum_gradNormIn_sq U.toIntegerCube.vertices f
  rw [hdiff]
  calc (∑ k ∈ D, F k) ^ 2 = (∑ k ∈ D, a k * b k) ^ 2 := rfl
    _ ≤ (∑ k ∈ D, a k ^ 2) * ∑ k ∈ D, b k ^ 2 := hcs
    _ ≤ (G ^ 2 * D.card) * edgeEnergy U.toIntegerCube.vertices f :=
        mul_le_mul ha2 hb2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ ≤ G ^ 2 * D.card * (2 * ∑ x ∈ U.toIntegerCube.vertices,
          gradNormIn (nearestNeighborGraph 2) U.toIntegerCube.vertices f x ^ 2) :=
        mul_le_mul_of_nonneg_left hE (by positivity)

end Rigidity.Percolation
