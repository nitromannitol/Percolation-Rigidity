import Rigidity.Proofs.Dirichlet.CutoffRegions

/-!
# Lemma 6.3 of Armstrong–Dario on the lattice with the cube cutoff

With the cutoff `η = cubeCutoff T ρ` of the tiled cube `T = z + {0,…,MN−1}^d`, which reaches depth
`D` in every direction of `Q`, the regions of `edgeEnergy_patch_le_of_nu` are the regions of the
cutoff (`CutoffRegions`), and the patched function `ũ = η ṽ + (1 − η) u` satisfies:

* (i) `ũ = u` off `T` (`patch_cubeCutoff_of_not_mem`), in particular near the boundary of `Q`;
* (ii) `E_c(ũ) ≤ E_ā(u) + 6 N^d Σ δ + 3 F + 2 Σ_{layer(D + ρ + N + 1)} ā|∇u|²
  + 3 Λ Σ_{layer(D + ρ + 2)} |∇u|² + 6 Λ d ρ^{-2} (Σ Σ (ṽ − ℓ)² + Σ Σ (u − ℓ)²)`
  (`edgeEnergy_patch_cubeCutoff_le`);
* (iii) `Σ_Q (ũ − u)² ≤ 2 Σ Σ (ṽ − ℓ)² + 2 Σ Σ (u − ℓ)²` (`sum_sq_patch_cubeCutoff_sub_le`).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Lemma 6.3 (ii) on the lattice with the cube cutoff.** -/
theorem edgeEnergy_patch_cubeCutoff_le (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hcΛ : ∀ e, c e ≤ Λ) (Q : IntegerCube d)
    {u : Vertex d → ℝ} (hu : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u x = 0)
    {r : ℕ} (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices)
    {D : ℕ} (hT1 : ∀ k, z k ≤ Q.corner k + D)
    (hT2 : ∀ k, Q.corner k + Q.size ≤ z k + (M * N : ℕ) + D) {ρ : ℕ} (hρ : 0 < ρ)
    (v : Vertex d → ℝ) (δ : Vertex d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hinner : ∀ i ∈ (cornerCube 0 M).vertices,
      innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v / (N : ℝ) ^ d ≤
        ∑ k, a k * cubeSlope N u (z + (N : ℤ) • i) k ^ 2 + 2 * δ i)
    (hface : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j, c (x, j) ≠ 0 →
        v x = cubeAffine N u (z + (N : ℤ) • i) x ∧
          v (x + unit j) = cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j)) :
    edgeEnergy c Q.vertices (patch (cubeCutoff (cornerCube z (M * N)) ρ) v u) ≤
      edgeEnergy (constCond a) Q.vertices u +
        6 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i +
        3 * (Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) +
            1 / N) * ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2))) +
        2 * ∑ x ∈ cubeLayer Q (D + ρ + N + 1), ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 +
        3 * Λ * ∑ x ∈ cubeLayer Q (D + ρ + 2), ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 +
        6 * Λ * (d * (1 / (ρ : ℝ)) ^ 2) *
          (∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
              (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 +
            ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
              (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2) := by
  classical
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have ha0 : ∀ k, 0 ≤ a k := fun k => hlam.le.trans (ha k).1
  set T := cornerCube z (M * N)
  set η := cubeCutoff T ρ
  set A := cutoffInner η Q.vertices
  set B := cutoffOuter η Q.vertices
  set S := cutoffStrip η Q.vertices
  have hTQ : T.vertices ⊆ Q.vertices := cornerCube_mul_subset hsub
  have hlayer : B ∪ S ⊆ cubeLayer Q (D + ρ + 2) :=
    cutoffOuter_union_cutoffStrip_subset_cubeLayer hd Q T hρ D hT1 hT2
  have hSlayer : S ⊆ cubeLayer Q (D + ρ + 2) :=
    (Finset.subset_union_right).trans hlayer
  have hST : S ⊆ T.vertices := cutoffStrip_cubeCutoff_subset T ρ Q.vertices
  set I := tilesMeeting z M N S
  have hI : I ⊆ (cornerCube 0 M).vertices := tilesMeeting_subset z M N S
  have hw : D + ρ + 2 + N - 1 = D + ρ + N + 1 := by omega
  have hR : ∀ i ∈ I, (cornerCube (z + (N : ℤ) • i) N).vertices ⊆ cubeLayer Q (D + ρ + N + 1) :=
    fun i hi => hw ▸ tilesMeeting_subset_cubeLayer hTQ hSlayer hi
  have hmain := edgeEnergy_patch_le_of_nu hd a hlam ha c hc0 hcΛ Q hu hr z M hN hsub v δ hinner
    hface (η := η) (fun x => cubeCutoff_nonneg T ρ x) (fun x => cubeCutoff_le_one T ρ x) A B S
    (disjoint_cutoffInner_cutoffOuter hd η Q.vertices) (disjoint_union_cutoffStrip η Q.vertices)
    (cutoffInner_union_cutoffOuter_union_cutoffStrip η Q.vertices)
    (cutoffInner_cubeCutoff_subset hd T ρ Q.vertices) hST
    (fun x hx j => (Finset.mem_filter.mp hx).2 j) (fun x hx j => (Finset.mem_filter.mp hx).2 j)
    (K := 1 / (ρ : ℝ)) (fun x _ j => abs_cubeCutoff_add_unit_sub_le T ρ x j) hI
    (subset_biUnion_tilesMeeting hN z M hST) (cubeLayer Q (D + ρ + N + 1)) hR
  refine hmain.trans ?_
  -- enlarge the index set and the strip
  have hδI : ∑ i ∈ I, δ i ≤ ∑ i ∈ (cornerCube 0 M).vertices, δ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hI fun i _ _ => hδ i
  have hNd : (0 : ℝ) ≤ (N : ℝ) ^ d := by positivity
  have hδall : 0 ≤ ∑ i ∈ (cornerCube 0 M).vertices, δ i := Finset.sum_nonneg fun i _ => hδ i
  have hBS : ∑ x ∈ B ∪ S, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 ≤
      ∑ x ∈ cubeLayer Q (D + ρ + 2), ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hlayer fun x _ _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _
  have hX : ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 ≤
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hI fun i _ _ =>
      Finset.sum_nonneg fun x _ => sq_nonneg _
  have hY : ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 ≤
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
        (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hI fun i _ _ =>
      Finset.sum_nonneg fun x _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hδI (show (0 : ℝ) ≤ 4 * (N : ℝ) ^ d by positivity)
  have h2 := mul_le_mul_of_nonneg_left hBS (show (0 : ℝ) ≤ 3 * Λ by positivity)
  have h3 := mul_le_mul_of_nonneg_left (add_le_add hX hY)
    (show (0 : ℝ) ≤ 6 * Λ * (d * (1 / (ρ : ℝ)) ^ 2) by positivity)
  linarith

/-- **Lemma 6.3 (iii) on the lattice with the cube cutoff.** -/
theorem sum_sq_patch_cubeCutoff_sub_le {N : ℕ} (hN : 0 < N) (z : Vertex d) (M ρ : ℕ)
    (U : Finset (Vertex d)) (v u : Vertex d → ℝ) :
    ∑ x ∈ U, (patch (cubeCutoff (cornerCube z (M * N)) ρ) v u x - u x) ^ 2 ≤
      2 * ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 +
        2 * ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 :=
  sum_sq_patch_sub_le (fun x => cubeCutoff_nonneg _ ρ x) (fun x => cubeCutoff_le_one _ ρ x) z N
    _ (subset_biUnion_tiles hN z M) U
    (fun _ _ hx => (mem_vertices_of_cubeCutoff_ne_zero _ ρ hx).1) v u (cubeAffine N u)

end Rigidity.Dirichlet
