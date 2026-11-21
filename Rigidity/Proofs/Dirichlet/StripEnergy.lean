import Rigidity.Proofs.Dirichlet.TiledEnergy

/-!
# Energy of the patched mesoscopic function in a strip of tiles

Let `ṽ` agree with the affine approximations of `u` on the faces of the tiles and have, on every
tile, inner energy at most `N^d (p · ā p + 2 δ)`, as in `edgeEnergy_tiles_le_of_nu`. For a set
`S` of points covered by the tiles with indices in `I`, all contained in a region `R`, the energy
of `ṽ` from `S` is at most the homogenized energy of `u` on `R`, plus `2 N^d Σ_{i∈I} δ_i`, plus
the bound for the face jumps:
`E_S(ṽ) ≤ Σ_R Σ_k a_k (∇_k u)² + 2 N^d Σ_I δ + Λ d C (N³ r⁻² + N⁻¹) E_Q(u)`.

This is estimate (1) of Step 3 of the proof of Armstrong–Dario, Lemma 6.3, on the lattice, with
the strip `□° ∖ □°_int`; taking `R` in a boundary layer of `Q`, the homogenized energy of `u` on
`R` is bounded by the Hardy-weighted layer estimate `sum_energy_cubeLayer_div_le`.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Convexity on one cube**: `N^d Σ_k a_k p_k(y)² ≤ Σ_{y+□} Σ_k a_k (∇_k g)²`. -/
theorem cubeSlope_quadratic_le (a : Fin d → ℝ) (ha : ∀ k, 0 ≤ a k) (N : ℕ) (g : Vertex d → ℝ)
    (y : Vertex d) :
    (N : ℝ) ^ d * ∑ k : Fin d, a k * cubeSlope N g y k ^ 2 ≤
      ∑ x ∈ (cornerCube y N).vertices, ∑ k : Fin d, a k * (g (x + unit k) - g x) ^ 2 := by
  set T := (cornerCube y N).vertices
  have hT : (#T : ℝ) = (N : ℝ) ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  have h := card_mul_sum_quadratic_avg_le T a ha (fun x k => g (x + unit k) - g x)
  rw [hT] at h
  refine le_trans (le_of_eq ?_) h
  congr 1

/-- **Sums over a covered set**: for `F ≥ 0` and `S ⊆ ⋃_{i∈I} T_i`,
`Σ_S F ≤ Σ_{i∈I} Σ_{T_i} F`. -/
theorem sum_le_sum_sum_of_subset_biUnion {ι : Type*} (I : Finset ι) (T : ι → Finset (Vertex d))
    {S : Finset (Vertex d)} (hS : S ⊆ I.biUnion T) (F : Vertex d → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ x ∈ S, F x ≤ ∑ i ∈ I, ∑ x ∈ T i, F x := by
  classical
  have key : ∀ J : Finset ι, ∑ x ∈ J.biUnion T, F x ≤ ∑ i ∈ J, ∑ x ∈ T i, F x := by
    intro J
    refine Finset.induction_on J (by simp) ?_
    intro a J ha ih
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := T a) (s₂ := J.biUnion T) (f := F)
    have h0 : 0 ≤ ∑ x ∈ T a ∩ J.biUnion T, F x := Finset.sum_nonneg fun x _ => hF x
    linarith
  exact (Finset.sum_le_sum_of_subset_of_nonneg hS fun x _ _ => hF x).trans (key I)

/-- **Sums over some tiles inside a region**: for `G ≥ 0`, indices `I ⊆ {0,…,M−1}^d` and tiles
`y_i + □ ⊆ R` (`i ∈ I`), `Σ_{i∈I} Σ_{y_i+□} G ≤ Σ_R G`. -/
theorem sum_tiles_le_of_subset {N : ℕ} (hN : 0 < N) (z : Vertex d) (M : ℕ)
    {I : Finset (Vertex d)} (hI : I ⊆ (cornerCube 0 M).vertices) (R : Finset (Vertex d))
    (hR : ∀ i ∈ I, (cornerCube (z + (N : ℤ) • i) N).vertices ⊆ R) (G : Vertex d → ℝ)
    (hG : ∀ x, 0 ≤ G x) :
    ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, G x ≤ ∑ x ∈ R, G x := by
  classical
  have hH0 : ∀ x, 0 ≤ (if x ∈ R then G x else 0) := fun x => by
    split_ifs
    · exact hG x
    · exact le_rfl
  calc ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, G x
      = ∑ i ∈ I, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (if x ∈ R then G x else 0) :=
        Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun x hx => by
          rw [if_pos (hR i hi hx)]
    _ ≤ ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (if x ∈ R then G x else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hI fun i _ _ =>
          Finset.sum_nonneg fun x _ => hH0 x
    _ = ∑ x ∈ (cornerCube z (M * N)).vertices, (if x ∈ R then G x else 0) :=
        (sum_cornerCube_mul hN z M _).symm
    _ = ∑ x ∈ (cornerCube z (M * N)).vertices.filter (· ∈ R), G x := by
        rw [Finset.sum_filter]
    _ ≤ ∑ x ∈ R, G x :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
          fun x _ _ => hG x

/-- **Energy of `ṽ` in a strip of tiles** (Lemma 6.3, Step 3, estimate (1), on the lattice). -/
theorem edgeEnergy_strip_le_of_nu (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ} (hlam : 0 < lam)
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
    {I : Finset (Vertex d)} (hI : I ⊆ (cornerCube 0 M).vertices) {S : Finset (Vertex d)}
    (hS : S ⊆ I.biUnion fun i => (cornerCube (z + (N : ℤ) • i) N).vertices)
    (R : Finset (Vertex d)) (hR : ∀ i ∈ I, (cornerCube (z + (N : ℤ) • i) N).vertices ⊆ R) :
    edgeEnergy c S v ≤
      ∑ x ∈ R, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 +
        2 * (N : ℝ) ^ d * ∑ i ∈ I, δ i +
          Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) +
            1 / N) * ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2)) := by
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have ha0 : ∀ k, 0 ≤ a k := fun k => hlam.le.trans (ha k).1
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  set tile : Vertex d → IntegerCube d := fun i => cornerCube (z + (N : ℤ) • i) N
  set E := ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2
  set K := 3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) + 1 / N)
  set J : Vertex d → ℝ := fun i => ∑ j : Fin d, ∑ x ∈ (tile i).upperFace j,
    (cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) -
      cubeAffine N u (z + (N : ℤ) • i) x) ^ 2
  have hJ0 : ∀ i, 0 ≤ J i := fun i =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- cover `S` by the tiles
  have h1 : edgeEnergy c S v ≤
      ∑ i ∈ I, ∑ x ∈ (tile i).vertices, ∑ j : Fin d, c (x, j) * (v (x + unit j) - v x) ^ 2 :=
    sum_le_sum_sum_of_subset_biUnion I (fun i => (tile i).vertices) hS _ fun x =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hc0 _) (sq_nonneg _)
  -- each tile
  have h2 : ∀ i ∈ I, ∑ x ∈ (tile i).vertices, ∑ j : Fin d, c (x, j) * (v (x + unit j) - v x) ^ 2 ≤
      ∑ x ∈ (tile i).vertices, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 +
        2 * (N : ℝ) ^ d * δ i + Λ * J i := by
    intro i hi
    have hiM := hI hi
    have ht := sum_tile_energy_le c hcΛ (tile i) v (cubeAffine N u (z + (N : ℤ) • i))
      (fun j => cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j)) (hface i hiM)
    have hin := hinner i hiM
    rw [div_le_iff₀ hNd] at hin
    have hconv := cubeSlope_quadratic_le a ha0 N u (z + (N : ℤ) • i)
    simp only [tile, J] at ht hconv ⊢
    nlinarith
  have h3 : ∑ i ∈ I, ∑ x ∈ (tile i).vertices, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 ≤
      ∑ x ∈ R, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 :=
    sum_tiles_le_of_subset hN z M hI R hR _ fun x =>
      Finset.sum_nonneg fun k _ => mul_nonneg (ha0 k) (sq_nonneg _)
  -- the faces
  have h4 : ∑ i ∈ I, J i ≤ d * (K * E) := by
    calc ∑ i ∈ I, J i ≤ ∑ i ∈ (cornerCube 0 M).vertices, J i :=
          Finset.sum_le_sum_of_subset_of_nonneg hI fun i _ _ => hJ0 i
      _ = ∑ j : Fin d, ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (tile i).upperFace j,
            (cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) -
              cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 := Finset.sum_comm
      _ ≤ ∑ _j : Fin d, K * E := Finset.sum_le_sum fun j _ =>
          sum_face_jumps_le_energy hd a hlam ha Q hu hr z M hN hsub j
      _ = d * (K * E) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h5 := mul_le_mul_of_nonneg_left h4 hΛ
  have h6 : ∑ i ∈ I, ∑ x ∈ (tile i).vertices, ∑ j : Fin d, c (x, j) * (v (x + unit j) - v x) ^ 2 ≤
      ∑ i ∈ I, ∑ x ∈ (tile i).vertices, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 +
        2 * (N : ℝ) ^ d * ∑ i ∈ I, δ i + Λ * ∑ i ∈ I, J i := by
    refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linarith

end Rigidity.Dirichlet
