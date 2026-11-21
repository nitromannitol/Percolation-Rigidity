import Rigidity.Proofs.Dirichlet.FaceJumps

/-!
# Energy of a function patched from mesoscopic pieces

Let a cube `z + {0, …, MN − 1}^d` be tiled by the cubes `y_i + □` of side `N`, `y_i = z + N i`, and
let `ṽ` be a function whose values on the faces between the tiles are given by affine functions
`ℓ_{y_i}` of the tiles: for every edge `(x, x + e_j)` leaving the tile `y_i + □` through its upper
face and carrying a nonzero conductance, `ṽ(x) = ℓ_{y_i}(x)` and
`ṽ(x + e_j) = ℓ_{y_i + N e_j}(x + e_j)`. Then the energy of `ṽ` splits into the energies of `ṽ` on
the edges inside the tiles and at most `Λ` times the squared jumps of the affine functions across
the faces.

With the energy of the maximizer of `ν` on each tile (`energy_le_of_nu_maximizer`), the
convexity of the tile slopes and the face bound `sum_face_jumps_le_energy`, this gives Steps 1
and 2 of the proof of Armstrong–Dario, Lemma 6.3, on the lattice: the energy of `ṽ` exceeds the
homogenized energy of `u_hom` by at most the convergence errors and `C (N³ r⁻² + N⁻¹)` times the
energy of `u_hom` (`edgeEnergy_tiles_le_of_nu`).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Inner points and the upper face**: `Σ_Q h = Σ_{x ∈ Q, x + e_j ∈ Q} h + Σ_{upper face j} h`. -/
theorem sum_vertices_eq_sum_inner_add_sum_upperFace (Q : IntegerCube d) (j : Fin d)
    (h : Vertex d → ℝ) :
    ∑ x ∈ Q.vertices, h x =
      ∑ x ∈ Q.vertices.filter (fun x => x + unit j ∈ Q.vertices), h x +
        ∑ x ∈ Q.upperFace j, h x := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q.vertices (fun x => x + unit j ∈ Q.vertices)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hnot⟩
    by_contra h
    exact hnot ((add_unit_mem_vertices_iff Q hx j).mpr h)
  · intro hx
    have hxQ := (IntegerCube.mem_upperFace Q j x).mp hx
    exact ⟨hxQ.1, fun h => (add_unit_mem_vertices_iff Q hxQ.1 j).mp h hx⟩

/-- The energy `Σ_j Σ_{x ∈ Q, x + e_j ∈ Q} c(x,j) (∇_j v(x))²` of `v` on the edges inside `Q`. -/
noncomputable def innerEdgeEnergy (c : Edge d → ℝ) (Q : IntegerCube d) (v : Vertex d → ℝ) : ℝ :=
  ∑ j : Fin d, ∑ x ∈ Q.vertices.filter (fun x => x + unit j ∈ Q.vertices),
    c (x, j) * (v (x + unit j) - v x) ^ 2

/-- **Energy of a patched function**: the energy of `ṽ` on the tiled cube is at most the sum of
its energies inside the tiles plus `Λ` times the squared jumps of the affine functions across the
faces. -/
theorem edgeEnergy_le_sum_tiles (c : Edge d → ℝ) {Λ : ℝ} (hcΛ : ∀ e, c e ≤ Λ) {N : ℕ}
    (hN : 0 < N) (z : Vertex d) (M : ℕ) (v : Vertex d → ℝ) (ℓ : Vertex d → Vertex d → ℝ)
    (hface : ∀ i ∈ (cornerCube 0 M).vertices, ∀ j : Fin d,
      ∀ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j, c (x, j) ≠ 0 →
        v x = ℓ (z + (N : ℤ) • i) x ∧
          v (x + unit j) = ℓ (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j)) :
    edgeEnergy c (cornerCube z (M * N)).vertices v ≤
      ∑ i ∈ (cornerCube 0 M).vertices, innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v +
        Λ * ∑ j : Fin d, ∑ i ∈ (cornerCube 0 M).vertices,
          ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j,
            (ℓ (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) - ℓ (z + (N : ℤ) • i) x) ^ 2 := by
  classical
  rw [edgeEnergy, sum_cornerCube_mul hN z M]
  have key : ∀ i ∈ (cornerCube (0 : Vertex d) M).vertices,
      ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).vertices, ∑ j : Fin d,
          c (x, j) * (v (x + unit j) - v x) ^ 2 ≤
        innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v +
          Λ * ∑ j : Fin d, ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j,
            (ℓ (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) - ℓ (z + (N : ℤ) • i) x) ^ 2 := by
    intro i hi
    rw [Finset.sum_comm, innerEdgeEnergy, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [sum_vertices_eq_sum_inner_add_sum_upperFace _ j, Finset.mul_sum]
    refine add_le_add le_rfl (Finset.sum_le_sum fun x hx => ?_)
    by_cases hc : c (x, j) = 0
    · rw [hc, zero_mul]
      have hΛ : 0 ≤ Λ := hc ▸ hcΛ (x, j)
      positivity
    · obtain ⟨h1, h2⟩ := hface i hi j x hx hc
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right (hcΛ _) (sq_nonneg _)
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm (s := (cornerCube 0 M).vertices)]

/-- **Steps 1 and 2 of Lemma 6.3 of Armstrong–Dario on the lattice**: let `u` be `ā`-harmonic on
`Q` (constant diagonal `ā` with `λ ≤ a_k ≤ Λ`), let the tiling of `z + {0,…,MN−1}^d` sit, with one
extra layer of tiles, at depth `r + 3` inside `Q`, and let `ṽ` agree on the faces of the tiles
with the affine approximations `ℓ_{y_i}` of `u` (`cubeAffine`), with conductances `c ≤ Λ`. If on
every tile the inner energy of `ṽ` is at most `N^d (p(y_i) · ā p(y_i) + 2 δ_i)` (the energy of the
maximizer of `ν`), then the energy of `ṽ` is at most the homogenized energy of `u` plus
`2 N^d Σ_i δ_i` and `C (N³ r⁻² + N⁻¹)` times the energy of `u` on `Q`. -/
theorem edgeEnergy_tiles_le_of_nu (hd : 0 < d) (a : Fin d → ℝ) {lam Λ : ℝ} (hlam : 0 < lam)
    (ha : ∀ j, lam ≤ a j ∧ a j ≤ Λ) (c : Edge d → ℝ) (hcΛ : ∀ e, c e ≤ Λ) (Q : IntegerCube d)
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
          v (x + unit j) = cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j)) :
    edgeEnergy c (cornerCube z (M * N)).vertices v ≤
      edgeEnergy (constCond a) (cornerCube z (M * N)).vertices u +
        2 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i +
          Λ * (d * (3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) +
            1 / N) * ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2)) := by
  have hΛ : 0 ≤ Λ := (hlam.le.trans (ha ⟨0, hd⟩).1).trans (ha ⟨0, hd⟩).2
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  refine (edgeEnergy_le_sum_tiles c hcΛ hN z M v (cubeAffine N u) hface).trans ?_
  set E := ∑ x ∈ Q.vertices, ∑ k : Fin d, (u (x + unit k) - u x) ^ 2
  set K := 3 * ((1 + d) * 2 ^ d * (N : ℝ) ^ 3 * (10 * d * Λ / (lam * (r : ℝ) ^ 2)) + 1 / N)
  -- the tiles
  have h1 : ∑ i ∈ (cornerCube 0 M).vertices, innerEdgeEnergy c (cornerCube (z + (N : ℤ) • i) N) v ≤
      ∑ i ∈ (cornerCube 0 M).vertices, (N : ℝ) ^ d *
          ∑ k, a k * cubeSlope N u (z + (N : ℤ) • i) k ^ 2 +
        2 * (N : ℝ) ^ d * ∑ i ∈ (cornerCube 0 M).vertices, δ i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have := hinner i hi
    rw [div_le_iff₀ hNd] at this
    linarith
  have h2 := sum_tiles_cubeSlope_sq_le a (fun k => (hlam.le.trans (ha k).1)) z M hN u
  have h2' : ∑ x ∈ (cornerCube z (M * N)).vertices, ∑ k : Fin d, a k * (u (x + unit k) - u x) ^ 2 =
      edgeEnergy (constCond a) (cornerCube z (M * N)).vertices u := by
    simp only [edgeEnergy, constCond]
  -- the faces
  have h3 : ∑ j : Fin d, ∑ i ∈ (cornerCube 0 M).vertices,
      ∑ x ∈ (cornerCube (z + (N : ℤ) • i) N).upperFace j,
        (cubeAffine N u (z + (N : ℤ) • i + (N : ℤ) • unit j) (x + unit j) -
          cubeAffine N u (z + (N : ℤ) • i) x) ^ 2 ≤ d * (K * E) := by
    calc _ ≤ ∑ _j : Fin d, K * E := Finset.sum_le_sum fun j _ =>
          sum_face_jumps_le_energy hd a hlam ha Q hu hr z M hN hsub j
      _ = d * (K * E) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3' := mul_le_mul_of_nonneg_left h3 hΛ
  linarith

end Rigidity.Dirichlet
