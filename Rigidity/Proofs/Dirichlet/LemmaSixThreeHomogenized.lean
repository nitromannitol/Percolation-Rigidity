import Rigidity.Proofs.Dirichlet.StripEnergy
import Rigidity.Proofs.Dirichlet.Patching

/-!
# Lemma 6.3 of Armstrong–Dario on the lattice, from the mesoscopic inputs

Let `u` be `ā`-harmonic on the lattice cube `Q`, let the tiles `y_i + □` (side `N`, indices
`i ∈ {0,…,M−1}^d`) of the cube `T = z + {0,…,MN−1}^d` sit, with one extra layer of tiles, at
depth `r + 3` inside `Q`, and let `ṽ` agree on the faces of the tiles with the affine
approximations `ℓ_{y_i}` of `u` and have inner energy on each tile at most
`N^d (p(y_i) · ā p(y_i) + 2 δ_i)`. For a cutoff `0 ≤ η ≤ 1` equal to one along the edges from
`A ⊆ T`, zero along the edges from `B`, with `|∇η| ≤ K` on the strip `S ⊆ T` (`A`, `B`, `S`
partition `Q`), and `S` covered by the tiles with indices in `I`, all inside a region `R`, the
patched function `ũ = η ṽ + (1 − η) u` satisfies:

* (i) `ũ = u` on `B` (`patch_of_eq_zero`);
* (ii) `E_c(ũ) ≤ E_ā(u) + 2 N^d Σ δ + 4 N^d Σ_I δ + 3 F + 2 Σ_R ā|∇u|² + 3 Λ Σ_{B ∪ S} |∇u|²
  + 6 Λ d K² (Σ_I Σ (ṽ − ℓ)² + Σ_I Σ (u − ℓ)²)`, with `F` the bound for the face jumps
  (`edgeEnergy_patch_le_of_nu`);
* (iii) `Σ_Q (ũ − u)² ≤ 2 Σ_I Σ (ṽ − ℓ)² + 2 Σ_I Σ (u − ℓ)²` when `η` vanishes off the tiles
  with indices in `I` (`sum_sq_patch_sub_le`).

The remaining terms are small by the layer estimate `sum_energy_cubeLayer_div_le` (for
`Σ_R ā|∇u|²` and `Σ_{B ∪ S} |∇u|²` with `R`, `B ∪ S` in a boundary layer of `Q`), by
`exists_sum_tiles_sq_sub_cubeAffine_le_energy` (for `Σ (u − ℓ)²`) and by the Poincaré inequality
on the clusters of the tiles (for `Σ (ṽ − ℓ)²`). This is the proof of Armstrong–Dario,
Lemma 6.3 (Steps 1–3), on the lattice, with the cluster inputs as hypotheses.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **`L²` distance on covered points**: for `S` covered by the tiles with indices in `I`,
`Σ_S (v − u)² ≤ 2 Σ_{i∈I} Σ_{y_i+□} (v − ℓ_{y_i})² + 2 Σ_{i∈I} Σ_{y_i+□} (u − ℓ_{y_i})²`. -/
theorem sum_sq_sub_le_tiles (z : Vertex d) (N : ℕ) (I : Finset (Vertex d)) {S : Finset (Vertex d)}
    (hS : S ⊆ I.biUnion fun i => (cornerCube (z + (N : ℤ) • i) N).vertices)
    (v u : Vertex d → ℝ) (ℓ : Vertex d → Vertex d → ℝ) :
    ∑ x ∈ S, (v x - u x) ^ 2 ≤
      2 * ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (v x - ℓ (z + (N : ℤ) • i) x) ^ 2 +
        2 * ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (u x - ℓ (z + (N : ℤ) • i) x) ^ 2 := by
  refine (sum_le_sum_sum_of_subset_biUnion I _ hS _ fun x => sq_nonneg _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  nlinarith [sq_nonneg (v x + u x - 2 * ℓ (z + (N : ℤ) • i) x)]

/-- **Lemma 6.3 (iii) on the lattice**: if `η` vanishes off a set `S'` covered by the tiles with
indices in `I`, then `Σ_U (ũ − u)² ≤ 2 Σ_I Σ (ṽ − ℓ)² + 2 Σ_I Σ (u − ℓ)²`. -/
theorem sum_sq_patch_sub_le {η : Vertex d → ℝ} (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (z : Vertex d) (N : ℕ) (I : Finset (Vertex d)) {S' : Finset (Vertex d)}
    (hS' : S' ⊆ I.biUnion fun i => (cornerCube (z + (N : ℤ) • i) N).vertices)
    (U : Finset (Vertex d)) (hsupp : ∀ x ∈ U, η x ≠ 0 → x ∈ S')
    (v u : Vertex d → ℝ) (ℓ : Vertex d → Vertex d → ℝ) :
    ∑ x ∈ U, (patch η v u x - u x) ^ 2 ≤
      2 * ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (v x - ℓ (z + (N : ℤ) • i) x) ^ 2 +
        2 * ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (u x - ℓ (z + (N : ℤ) • i) x) ^ 2 := by
  classical
  have hpt : ∀ x, (patch η v u x - u x) ^ 2 ≤ (v x - u x) ^ 2 := fun x => by
    rw [patch_sub, mul_pow]
    have h1 : η x ^ 2 ≤ 1 := by nlinarith [hη0 x, hη1 x]
    nlinarith [sq_nonneg (v x - u x)]
  calc ∑ x ∈ U, (patch η v u x - u x) ^ 2
      = ∑ x ∈ U.filter (· ∈ S'), (patch η v u x - u x) ^ 2 := by
        refine (Finset.sum_filter_of_ne fun x hx hne => ?_).symm
        refine hsupp x hx fun h0 => hne ?_
        rw [patch_sub, h0, zero_mul, zero_pow two_ne_zero]
    _ ≤ ∑ x ∈ S', (patch η v u x - u x) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
          fun x _ _ => sq_nonneg _
    _ ≤ ∑ x ∈ S', (v x - u x) ^ 2 := Finset.sum_le_sum fun x _ => hpt x
    _ ≤ _ := sum_sq_sub_le_tiles z N I hS' v u ℓ

/-- The tiled cube lies in `Q`. -/
theorem cornerCube_mul_subset {Q : IntegerCube d} {z : Vertex d} {M N r : ℕ}
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices) :
    (cornerCube z (M * N)).vertices ⊆ Q.vertices := by
  refine subset_trans ?_ (hsub.trans (shrinkCube_vertices_subset_self Q _))
  intro x hx
  rw [IntegerCube.mem_vertices] at hx ⊢
  intro t
  have h := hx t
  simp only [cornerCube] at h ⊢
  refine ⟨h.1, h.2.trans_le ?_⟩
  have : ((M * N : ℕ) : ℤ) ≤ ((M + 1) * N : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_right N (Nat.le_succ M)
  linarith

/-- **Lemma 6.3 (ii) on the lattice**, from the mesoscopic inputs. -/
theorem edgeEnergy_patch_le_of_nu (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ} (hlam : 0 < lam)
    (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e)
    (hcΛ : ∀ e, c e ≤ Λ) (Q : IntegerCube d)
    {u : Vertex d → ℝ} (hu : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u x = 0)
    {r : ℕ} (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices)
    (v : Vertex d → ℝ) (δ : Vertex d → ℝ)
    (hinner : ∀ i ∈ (cornerCube 0 M).vertices,
      innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v / (N : ℝ) ^ d ≤
        ∑ k, a k * cubeSlope N u (z + (N : ℤ) • i) k ^ 2 + 2 * δ i)
    (hface : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j, c (x, j) ≠ 0 →
        v x = cubeAffine N u (z + (N : ℤ) • i) x ∧
          v (x + unit j) = cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j))
    {η : Vertex d → ℝ} (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (A B S : Finset (Vertex d)) (hAB : Disjoint A B) (hABS : Disjoint (A ∪ B) S)
    (hQ : A ∪ B ∪ S = Q.vertices) (hAT : A ⊆ (cornerCube z (M * N)).vertices)
    (hST : S ⊆ (cornerCube z (M * N)).vertices)
    (hA : ∀ x ∈ A, ∀ j : Fin d, η x = 1 ∧ η (x + unit j) = 1)
    (hB : ∀ x ∈ B, ∀ j : Fin d, η x = 0 ∧ η (x + unit j) = 0) {K : ℝ}
    (hK : ∀ x ∈ S, ∀ j : Fin d, |η (x + unit j) - η x| ≤ K)
    {I : Finset (Vertex d)} (hI : I ⊆ (cornerCube 0 M).vertices)
    (hSI : S ⊆ I.biUnion fun i => (cornerCube (z + (N : ℤ) • i) N).vertices)
    (R : Finset (Vertex d)) (hR : ∀ i ∈ I, (cornerCube (z + (N : ℤ) • i) N).vertices ⊆ R) :
    edgeEnergy c Q.vertices (patch η v u) ≤
      edgeEnergy (constCond a) Q.vertices u +
        2 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i +
        4 * (N : ℝ) ^ d * ∑ i ∈ I, δ i +
        3 * (Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) +
            1 / N) * ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2))) +
        2 * ∑ x ∈ R, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 +
        3 * Λ * ∑ x ∈ B ∪ S, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 +
        6 * Λ * (d * K ^ 2) *
          (∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
              (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 +
            ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
              (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2) := by
  classical
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have ha0 : ∀ k, 0 ≤ a k := fun k => hlam.le.trans (ha k).1
  set T := (cornerCube z (M * N)).vertices
  set Fc := Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) +
    1 / N) * ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2))
  set X := ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
    (v x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2
  set Y := ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
    (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2
  have hdisjAS : Disjoint A S :=
    Finset.disjoint_left.mpr fun x hxA hxS =>
      Finset.disjoint_left.mp hABS (Finset.mem_union_left _ hxA) hxS
  have hdisjBS : Disjoint B S :=
    Finset.disjoint_left.mpr fun x hxB hxS =>
      Finset.disjoint_left.mp hABS (Finset.mem_union_right _ hxB) hxS
  have hcnn : ∀ (f : Vertex d → ℝ) (x : Vertex d),
      0 ≤ ∑ j : Fin d, c (x, j) * (f (x + unit j) - f x) ^ 2 := fun _ x =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hc0 _) (sq_nonneg _)
  -- the patch
  have hP := edgeEnergy_patch_le c hc0 hcΛ v u hη0 hη1 A B S hAB hABS hA hB hK
  rw [hQ] at hP
  -- the inner function on `A ∪ S ⊆ T`
  have hAS : edgeEnergy c A v + edgeEnergy c S v ≤ edgeEnergy c T v := by
    rw [edgeEnergy, edgeEnergy, ← Finset.sum_union hdisjAS]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hAT hST)
      fun x _ _ => hcnn v x
  have hT := edgeEnergy_tiles_le_of_nu hd a hlam ha c hcΛ Q hu hr z M hN hsub v δ hinner hface
  have hTQ : edgeEnergy (constCond a) T u ≤ edgeEnergy (constCond a) Q.vertices u :=
    Finset.sum_le_sum_of_subset_of_nonneg (cornerCube_mul_subset hsub) fun x _ _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (ha0 j) (sq_nonneg _)
  have hSv := edgeEnergy_strip_le_of_nu hd a hlam ha c hc0 hcΛ Q hu hr z M hN hsub v δ hinner
    hface hI hSI R hR
  -- the outer function
  have hcu : ∀ V : Finset (Vertex d),
      edgeEnergy c V u ≤ Λ * ∑ x ∈ V, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 := by
    intro V
    rw [edgeEnergy, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcΛ _) (sq_nonneg _)
  have hBu := hcu B
  have hSu := hcu S
  have hBS : ∑ x ∈ B ∪ S, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 =
      ∑ x ∈ B, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 +
        ∑ x ∈ S, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 :=
    Finset.sum_union hdisjBS
  have hB0 : 0 ≤ ∑ x ∈ B, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hBΛ := mul_nonneg hΛ hB0
  -- the `L²` term
  have hL2 := sum_sq_sub_le_tiles z N I hSI v u (cubeAffine N u)
  have hL2' : 3 * (Λ * (d * K ^ 2 * ∑ x ∈ S, (v x - u x) ^ 2)) ≤
      6 * Λ * (d * K ^ 2) * (X + Y) := by
    have h := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ 3 * Λ * (d * K ^ 2) by positivity)
    calc 3 * (Λ * (d * K ^ 2 * ∑ x ∈ S, (v x - u x) ^ 2))
        = 3 * Λ * (d * K ^ 2) * ∑ x ∈ S, (v x - u x) ^ 2 := by ring
      _ ≤ 3 * Λ * (d * K ^ 2) * (2 * X + 2 * Y) := h
      _ = 6 * Λ * (d * K ^ 2) * (X + Y) := by ring
  have hRS : 3 * Λ * ∑ x ∈ B ∪ S, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 =
      3 * (Λ * ∑ x ∈ B, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2) +
        3 * (Λ * ∑ x ∈ S, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2) := by
    rw [hBS]
    ring
  linarith

end Rigidity.Dirichlet
