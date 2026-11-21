import Rigidity.Proofs.Dirichlet.AffinePatch
import Rigidity.Proofs.Dirichlet.MesoscopicAffine
import Rigidity.Proofs.Dirichlet.InteriorLinfty

/-!
# Jumps of the patched affine approximations across the faces of a tiling

Sums over the doubled cubes `y_i + {0, …, 2N − 1}^d` of a tiling by cubes of side `N` count every
point at most `2^d` times, so with the face bound `sq_cubeAffine_neighbour_sub_le_secondDiff`
and the convexity of the tile slopes, the squared jumps of the patched affine approximations
across the faces orthogonal to `e_j` satisfy
`Σ_{faces} (ℓ_{y'}(x + e_j) − ℓ_y(x))² ≤ 3 (1 + d) 2^d N³ Σ_k Σ (∇_j∇_k g)² + 3 N⁻¹ Σ (∇_j g)²`.

This is the bound of the energy of `ṽ` on the edges between mesoscopic cubes in the proof of
Armstrong–Dario, Lemma 6.3, Step 2: `C 3^{−n} (|p|² + 3^{4n} ⨍ |∇∇u_hom|²)` after normalization.
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Overlap of the doubled tiles**: for `F ≥ 0`,
`Σ_i Σ_{y_i + {0,…,2N−1}^d} F ≤ 2^d Σ_{z + {0,…,(M+1)N−1}^d} F`. -/
theorem sum_tiles_doubled_le {N : ℕ} (hN : 0 < N) (z : Vertex d) (M : ℕ) (F : Vertex d → ℝ)
    (hF : ∀ w, 0 ≤ F w) :
    ∑ i ∈ (cornerCube 0 M).vertices, ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices, F w ≤
      2 ^ d * ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices, F w := by
  classical
  set G : Vertex d → ℝ := fun m => ∑ w ∈ (cornerCube (z + (N : ℤ) • m) N).vertices, F w
  have hG : ∀ m, 0 ≤ G m := fun m => Finset.sum_nonneg fun w _ => hF w
  have h2 : ∀ i, ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices, F w =
      ∑ i' ∈ (cornerCube 0 2).vertices, G (i + i') := by
    intro i
    rw [sum_cornerCube_mul hN (z + (N : ℤ) • i) 2 F]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [G, smul_add, add_assoc]
  simp only [h2]
  rw [Finset.sum_comm, sum_cornerCube_mul hN z (M + 1) F]
  have hcard : ((cornerCube (0 : Vertex d) 2).vertices.card : ℝ) = 2 ^ d := by
    rw [card_vertices]
    simp [cornerCube]
  calc ∑ i' ∈ (cornerCube 0 2).vertices, ∑ i ∈ (cornerCube 0 M).vertices, G (i + i')
      ≤ ∑ _i' ∈ (cornerCube (0 : Vertex d) 2).vertices,
          ∑ m ∈ (cornerCube 0 (M + 1)).vertices, G m := by
        refine Finset.sum_le_sum fun i' hi' => ?_
        calc ∑ i ∈ (cornerCube 0 M).vertices, G (i + i')
            = ∑ m ∈ (cornerCube 0 M).vertices.map (addRightEmbedding i'), G m := by
              rw [Finset.sum_map]
              rfl
          _ ≤ ∑ m ∈ (cornerCube 0 (M + 1)).vertices, G m := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun m _ _ => hG m
              obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hm
              rw [IntegerCube.mem_vertices] at hi hi' ⊢
              intro k
              have h1 := hi k
              have h2 := hi' k
              simp only [cornerCube, Pi.zero_apply, zero_add, addRightEmbedding_apply,
                Pi.add_apply] at h1 h2 ⊢
              push_cast at h1 h2 ⊢
              constructor <;> omega
    _ = 2 ^ d * ∑ m ∈ (cornerCube 0 (M + 1)).vertices, G m := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- **Jumps across the faces of a tiling**: for tiles `y_i = z + N i`, `i ∈ {0,…,M−1}^d`, and the
faces orthogonal to `e_j`,
`Σ_i Σ_{x ∈ upper face of y_i + □} (ℓ_{y_i + N e_j}(x + e_j) − ℓ_{y_i}(x))² ≤
  3 ((1 + d) 2^d N³ Σ_k Σ_{z + {0,…,(M+1)N−1}^d} (∇_j∇_k g)² +
    N⁻¹ Σ_{z + {0,…,MN−1}^d} (∇_j g)²)`. -/
theorem sum_face_jumps_le {N : ℕ} (hN : 0 < N) (g : Vertex d → ℝ) (z : Vertex d) (M : ℕ)
    (j : Fin d) :
    ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j,
        (cubeAffine N g (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) -
          cubeAffine N g (z + (N : ℤ) • i) x) ^ 2 ≤
      3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices,
          ∑ k, ((g (w + unit j + unit k) - g (w + unit j)) - (g (w + unit k) - g w)) ^ 2 +
        1 / N * ∑ x ∈ (cornerCube z (M * N)).vertices, (g (x + unit j) - g x) ^ 2) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ j).elim0
  set F : Vertex d → ℝ := fun w => ∑ k,
    ((g (w + unit j + unit k) - g (w + unit j)) - (g (w + unit k) - g w)) ^ 2 with hF
  have hF0 : ∀ w, 0 ≤ F w := fun w => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set p : Vertex d → ℝ := fun y => cubeSlope N g y j
  -- the bound on one tile
  have htile : ∀ i ∈ (cornerCube (0 : Vertex d) M).vertices,
      ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j,
        (cubeAffine N g (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) -
          cubeAffine N g (z + (N : ℤ) • i) x) ^ 2 ≤
        (N : ℝ) ^ (d - 1) * (3 * ((1 + d) * (N : ℝ) ^ 4 / (N : ℝ) ^ d *
          ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices, F w +
            p (z + (N : ℤ) • i) ^ 2)) := by
    intro i _
    set y := z + (N : ℤ) • i
    have hpt : ∀ x ∈ (cornerCube y N).upperFace j,
        (cubeAffine N g (y + (N : ℤ) • unit j) (x + unit j) - cubeAffine N g y x) ^ 2 ≤
          3 * ((1 + d) * (N : ℝ) ^ 4 / (N : ℝ) ^ d *
            ∑ w ∈ (cornerCube y (2 * N)).vertices, F w + p y ^ 2) := by
      intro x hx
      have hx' : x + unit j ∈ (cornerCube (y + (N : ℤ) • unit j) N).vertices := by
        obtain ⟨hxQ, hxj⟩ := (IntegerCube.mem_upperFace _ j x).mp hx
        rw [IntegerCube.mem_vertices] at hxQ ⊢
        intro k
        have h1 := hxQ k
        simp only [cornerCube] at h1 hxj ⊢
        rw [add_unit_apply]
        by_cases hk : k = j
        · subst hk
          rw [if_pos rfl, add_smul_unit_apply_self]
          constructor <;> linarith
        · rw [if_neg hk, add_zero, add_smul_unit_apply_of_ne _ _ hk]
          exact h1
      have h := sq_cubeAffine_neighbour_sub_le_secondDiff hN g y x j hx'
      have hswap : ∑ k, ∑ w ∈ (cornerCube y (2 * N)).vertices,
          ((g (w + unit j + unit k) - g (w + unit j)) - (g (w + unit k) - g w)) ^ 2 =
            ∑ w ∈ (cornerCube y (2 * N)).vertices, F w := Finset.sum_comm
      rw [hswap] at h
      exact h
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by
      have := Finset.sum_nonneg fun w (_ : w ∈ (cornerCube y (2 * N)).vertices) => hF0 w
      positivity)
    exact_mod_cast card_upperFace_le _ j
  refine (Finset.sum_le_sum htile).trans ?_
  -- sum over the tiles
  have hdoubled := sum_tiles_doubled_le hN z M F hF0
  have hjensen := sum_tiles_cubeSlope_sq_le (fun k => if k = j then (1 : ℝ) else 0)
    (fun k => by split_ifs <;> norm_num) z M hN g
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hjensen
  have hpow : (N : ℝ) ^ d = (N : ℝ) ^ (d - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  set S : Vertex d → ℝ := fun i => ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices, F w
  set c : ℝ := (1 + d) * (N : ℝ) ^ 4 / (N : ℝ) ^ d
  have e1 : ∑ i ∈ (cornerCube (0 : Vertex d) M).vertices, (N : ℝ) ^ (d - 1) *
      (3 * (c * S i + p (z + (N : ℤ) • i) ^ 2)) =
      3 * (c * (N : ℝ) ^ (d - 1)) * ∑ i ∈ (cornerCube (0 : Vertex d) M).vertices, S i +
        3 * (N : ℝ) ^ (d - 1) * ∑ i ∈ (cornerCube (0 : Vertex d) M).vertices,
          p (z + (N : ℤ) • i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1]
  have ec : 3 * (c * (N : ℝ) ^ (d - 1)) = 3 * ((1 + d) * (N : ℝ) ^ 3) := by
    simp only [c]
    rw [hpow]
    field_simp
  have ep : 3 * (N : ℝ) ^ (d - 1) * ∑ i ∈ (cornerCube (0 : Vertex d) M).vertices,
      p (z + (N : ℤ) • i) ^ 2 = 3 * (1 / N * ∑ i ∈ (cornerCube (0 : Vertex d) M).vertices,
        (N : ℝ) ^ d * p (z + (N : ℤ) • i) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpow]
    field_simp
  rw [ec, ep]
  have hFsum : ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices, ∑ k,
      ((g (w + unit j + unit k) - g (w + unit j)) - (g (w + unit k) - g w)) ^ 2 =
        ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices, F w := rfl
  rw [hFsum]
  have hA := mul_le_mul_of_nonneg_left hdoubled
    (by positivity : (0 : ℝ) ≤ (1 + d) * (N : ℝ) ^ 3)
  have hB := mul_le_mul_of_nonneg_left hjensen (by positivity : (0 : ℝ) ≤ 1 / N)
  have hS : ∑ i ∈ (cornerCube (0 : Vertex d) M).vertices, S i =
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ w ∈ (cornerCube (z + (N : ℤ) • i) (2 * N)).vertices,
        F w := rfl
  rw [hS]
  nlinarith [hA, hB]

theorem shrinkCube_vertices_subset_self (Q : IntegerCube d) (t : ℕ) :
    (shrinkCube Q t).vertices ⊆ Q.vertices := by
  have h := shrinkCube_vertices_subset Q (Nat.zero_le t)
  rwa [shrinkCube_zero_vertices] at h

/-- **Lemma 6.3 (iii), homogenized part**: for `u` harmonic (constant conductances
`λ ≤ a_k ≤ Λ`) on `shrink(Q, 1)` and a tiled cube inside `shrink(Q, r + 3)`, the distance from `u`
to its mesoscopic affine approximations on the tiles satisfies
`Σ_i Σ_{tile i} (u − ℓ_{y_i})² ≤ C N⁴ r^{−2} Σ_{x∈Q} Σ_j (∇_j u(x))²`, `C = C(d, λ, Λ)`. -/
theorem exists_sum_tiles_sq_sub_cubeAffine_le_energy (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ}
    (hlam : 0 < lam) (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : IntegerCube d) (u : Vertex d → ℝ),
      (∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u x = 0) →
      ∀ (r : ℕ), 0 < r → ∀ (z : Vertex d) (M N : ℕ), 0 < N →
      (cornerCube z (M * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices →
      ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices,
          (u x - cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 ≤
        C * (N : ℝ) ^ 4 / (r : ℝ) ^ 2 *
          ∑ x ∈ Q.vertices, ∑ j : Fin d, (u (x + unit j) - u x) ^ 2 := by
  obtain ⟨CA, hCA, hA⟩ := exists_sum_tiles_sq_sub_cubeAffine_le (d := d)
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  refine ⟨CA * (10 * d * Λ / lam), by positivity, fun Q u hu r hr z M N hN hsub => ?_⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  refine (hA z M N u hN).trans ?_
  set Q' := shrinkCube Q 1
  -- each difference `∇_j u` is harmonic on `shrink(Q', 1)`
  have hharm : ∀ j : Fin d, ∀ x ∈ (shrinkCube Q' 1).vertices,
      condLaplacian (constCond a) (fun y => u (y + unit j) - u y) x = 0 := by
    intro j x hx
    rw [condLaplacian_constCond_grad, hu, hu, sub_zero]
    · rw [shrinkCube_shrinkCube_vertices] at hx
      exact shrinkCube_vertices_subset Q (by norm_num) hx
    · rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff] at hx
      rw [mem_shrinkCube_iff]
      intro k
      have := hx k
      rw [add_unit_apply]
      push_cast at this ⊢
      split_ifs <;> constructor <;> omega
  have hcacc : ∀ j : Fin d, ∑ x ∈ (shrinkCube Q (r + 3)).vertices, ∑ k : Fin d,
      ((u (x + unit k + unit j) - u (x + unit k)) - (u (x + unit j) - u x)) ^ 2 ≤
        10 * d * Λ / (lam * (r : ℝ) ^ 2) * ∑ x ∈ Q.vertices, (u (x + unit j) - u x) ^ 2 := by
    intro j
    have h := sum_sq_grad_shrinkCube_le hd a hlam ha Q' (hharm j) hr
    rw [shrinkCube_shrinkCube_vertices, show 1 + (r + 2) = r + 3 by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (shrinkCube_vertices_subset_self Q 1) fun _ _ _ => sq_nonneg _) (by positivity))
  calc CA * (N : ℝ) ^ 4 * ∑ y ∈ (cornerCube z (M * N)).vertices, ∑ j : Fin d, ∑ k : Fin d,
        ((u (y + unit k + unit j) - u (y + unit k)) - (u (y + unit j) - u y)) ^ 2
      = CA * (N : ℝ) ^ 4 * ∑ j : Fin d, ∑ y ∈ (cornerCube z (M * N)).vertices, ∑ k : Fin d,
        ((u (y + unit k + unit j) - u (y + unit k)) - (u (y + unit j) - u y)) ^ 2 := by
        rw [Finset.sum_comm (s := (cornerCube z (M * N)).vertices)]
    _ ≤ CA * (N : ℝ) ^ 4 * ∑ j : Fin d, 10 * d * Λ / (lam * (r : ℝ) ^ 2) *
          ∑ x ∈ Q.vertices, (u (x + unit j) - u x) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
          Finset.sum_nonneg fun k _ => sq_nonneg _) (hcacc j)
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))]
        field_simp

/-- **Lemma 6.3, Step 2, homogenized part**: for `u` harmonic (constant conductances
`λ ≤ a_k ≤ Λ`) on `shrink(Q, 1)` and a tiling whose doubled region
`z + {0, …, (M+1)N − 1}^d` lies in `shrink(Q, r + 3)`, the squared jumps of the patched affine
approximations of `u` across the faces orthogonal to `e_j` satisfy
`Σ_faces jump² ≤ 3 ((1 + d) 2^d N³ · 10dΛ/(λ r²) + N⁻¹) Σ_{x∈Q} Σ_k (∇_k u(x))²`. -/
theorem sum_face_jumps_le_energy (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ} (hlam : 0 < lam)
    (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (Q : IntegerCube d) {u : Vertex d → ℝ}
    (hu : ∀ x ∈ (shrinkCube Q 1).vertices, condLaplacian (constCond a) u x = 0) {r : ℕ}
    (hr : 0 < r) (z : Vertex d) (M : ℕ) {N : ℕ} (hN : 0 < N)
    (hsub : (cornerCube z ((M + 1) * N)).vertices ⊆ (shrinkCube Q (r + 3)).vertices) (j : Fin d) :
    ∑ i ∈ (cornerCube 0 M).vertices, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j,
        (cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) -
          cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 ≤
      3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) + 1 / N) *
        ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2 := by
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set E := ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2
  have hjump := sum_face_jumps_le hN u z M j
  -- the second differences: `∇_j∇_k u = ∇_k∇_j u`, harmonic `∇_j u`, Caccioppoli
  set Q' := shrinkCube Q 1
  have hharm : ∀ x ∈ (shrinkCube Q' 1).vertices,
      condLaplacian (constCond a) (fun y => u (y + unit j) - u y) x = 0 := by
    intro x hx
    rw [condLaplacian_constCond_grad, hu, hu, sub_zero]
    · rw [shrinkCube_shrinkCube_vertices] at hx
      exact shrinkCube_vertices_subset Q (by norm_num) hx
    · rw [shrinkCube_shrinkCube_vertices, mem_shrinkCube_iff] at hx
      rw [mem_shrinkCube_iff]
      intro k
      have := hx k
      rw [add_unit_apply]
      push_cast at this ⊢
      split_ifs <;> constructor <;> omega
  have hcacc := sum_sq_grad_shrinkCube_le hd a hlam ha Q' hharm hr
  rw [shrinkCube_shrinkCube_vertices, show 1 + (r + 2) = r + 3 by ring] at hcacc
  have hsecond : ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices, ∑ k,
      ((u (w + unit j + unit k) - u (w + unit j)) - (u (w + unit k) - u w)) ^ 2 ≤
        10 * d * Λ / (lam * (r : ℝ) ^ 2) * E := by
    have hcomm : ∀ w : Vertex d, ∀ k : Fin d,
        ((u (w + unit j + unit k) - u (w + unit j)) - (u (w + unit k) - u w)) ^ 2 =
          ((u (w + unit k + unit j) - u (w + unit k)) - (u (w + unit j) - u w)) ^ 2 := by
      intro w k
      rw [add_right_comm w (unit j) (unit k)]
      ring
    simp only [hcomm]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _).trans (hcacc.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.sum_le_sum_of_subset_of_nonneg (shrinkCube_vertices_subset_self Q 1)
      fun _ _ _ => sq_nonneg _).trans ?_
    exact Finset.sum_le_sum fun x _ => Finset.single_le_sum
      (f := fun k => (u (x + unit k) - u x) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hgrad : ∑ x ∈ (cornerCube z (M * N)).vertices, (u (x + unit j) - u x) ^ 2 ≤ E := by
    have hsub' : (cornerCube z (M * N)).vertices ⊆ Q.vertices := by
      intro x hx
      refine shrinkCube_vertices_subset_self Q (r + 3) (hsub ?_)
      rw [IntegerCube.mem_vertices] at hx ⊢
      intro k
      have := hx k
      simp only [cornerCube] at this ⊢
      constructor
      · exact this.1
      · have : ((M * N : ℕ) : ℤ) ≤ (((M + 1) * N : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right N (Nat.le_succ M)
        linarith [(hx k).2]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub' fun _ _ _ => sq_nonneg _).trans ?_
    exact Finset.sum_le_sum fun x _ => Finset.single_le_sum
      (f := fun k => (u (x + unit k) - u x) ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  refine hjump.trans ?_
  have hc0 : 0 ≤ (1 + d) * 2 ^ d * (N : ℝ) ^ 3 := by positivity
  calc 3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * ∑ w ∈ (cornerCube z ((M + 1) * N)).vertices,
          ∑ k, ((u (w + unit j + unit k) - u (w + unit j)) - (u (w + unit k) - u w)) ^ 2 +
        1 / N * ∑ x ∈ (cornerCube z (M * N)).vertices, (u (x + unit j) - u x) ^ 2)
      ≤ 3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2) * E) +
          1 / N * E) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hsecond hc0)
          (mul_le_mul_of_nonneg_left hgrad (by positivity))) (by norm_num)
    _ = _ := by ring

end Rigidity.Dirichlet
