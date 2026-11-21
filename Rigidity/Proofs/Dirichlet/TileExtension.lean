import Rigidity.Proofs.Dirichlet.TileAffine

/-!
# Extending a mesoscopic function by its affine datum

Let `K` be a set of points of a tile `T` (the cluster `C_*(y + □_n)` of the tile) such that no
edge with nonzero conductance joins `T ∖ K` to `K` inside `T`, and let `v = ℓ` on `T ∖ K`, with
`ℓ` affine of slope `p`. Then the inner energy of `v` on `T` is at most its energy on the edges
from `K` plus `Λ |p|² #(T ∖ K)` (`innerEdgeEnergy_le_of_eq_affine`).

This is (intermediate.estimate2) in Step 1 of the proof of Armstrong–Dario, Lemma 6.3, on the
lattice: the maximizer `v_y` of `ν(y + □_n, p(y))`, extended by `ℓ_y` to
`C_*(□_m) ∩ (y + □_n)`, has energy on the tile at most its energy on `C_*(y + □_n)` plus
`C |p(y)|² |∂_𝒫(y + □_n)|`. With the energy of the maximizer (`energy_le_of_nu_maximizer`), it
gives the per-tile hypothesis of `edgeEnergy_patch_cubeCutoff_le`
(`innerEdgeEnergy_div_le_of_cluster`).
-/

open Finset LatticeProb LatticeHC

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- **Energy of the extension by the affine datum.** -/
theorem innerEdgeEnergy_le_of_eq_affine (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e) {Λ : ℝ}
    (hcΛ : ∀ e, c e ≤ Λ) (T : IntegerCube d) (K : Finset (Vertex d)) (v ℓ : Vertex d → ℝ)
    (p : Fin d → ℝ) (hℓ : ∀ x j, ℓ (x + unit j) - ℓ x = p j)
    (hv : ∀ x ∈ T.vertices, x ∉ K → v x = ℓ x)
    (hsep : ∀ x ∈ T.vertices, ∀ j : Fin d, x + unit j ∈ T.vertices → x ∉ K → c (x, j) ≠ 0 →
      x + unit j ∉ K) :
    innerEdgeEnergy c T v ≤
      ∑ j : Fin d, ∑ x ∈ (T.vertices.filter fun x => x + unit j ∈ T.vertices).filter (· ∈ K),
          c (x, j) * (v (x + unit j) - v x) ^ 2 +
        Λ * (∑ j : Fin d, p j ^ 2) * #(T.vertices \ K) := by
  classical
  rw [innerEdgeEnergy, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  set F := T.vertices.filter fun x => x + unit j ∈ T.vertices
  rw [← Finset.sum_filter_add_sum_filter_not F (· ∈ K)]
  refine add_le_add le_rfl ?_
  have hterm : ∀ x ∈ F.filter (· ∉ K), c (x, j) * (v (x + unit j) - v x) ^ 2 ≤ Λ * p j ^ 2 := by
    intro x hx
    obtain ⟨hxF, hxK⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxT, hxjT⟩ := Finset.mem_filter.mp hxF
    by_cases hc : c (x, j) = 0
    · rw [hc, zero_mul]
      have : 0 ≤ Λ := hc ▸ hcΛ (x, j)
      positivity
    · rw [hv x hxT hxK, hv _ hxjT (hsep x hxT j hxjT hxK hc), hℓ]
      exact mul_le_mul_of_nonneg_right (hcΛ _) (sq_nonneg _)
  have hΛ : 0 ≤ Λ := (hc0 (0, j)).trans (hcΛ _)
  have hsub : F.filter (· ∉ K) ⊆ T.vertices \ K := fun x hx => by
    obtain ⟨hxF, hxK⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hxF).1, hxK⟩
  calc ∑ x ∈ F.filter (· ∉ K), c (x, j) * (v (x + unit j) - v x) ^ 2
      ≤ ∑ _x ∈ F.filter (· ∉ K), Λ * p j ^ 2 := Finset.sum_le_sum hterm
    _ = #(F.filter (· ∉ K)) * (Λ * p j ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ #(T.vertices \ K) * (Λ * p j ^ 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
    _ = Λ * p j ^ 2 * #(T.vertices \ K) := by ring

/-- **The per-tile hypothesis of Lemma 6.3 from the cluster of the tile**: if the energy of `v` on
the edges from `K` is at most `N^d (p · ā p + 2 δ₀)` (the energy of the maximizer of `ν`), and `v`
is the affine approximation off `K`, then the inner energy of `v` on the tile is at most
`N^d (p · ā p + 2 δ)` with `δ = δ₀ + Λ |p|² #(T ∖ K) / (2 N^d)`. -/
theorem innerEdgeEnergy_div_le_of_cluster (c : Edge d → ℝ) (hc0 : ∀ e, 0 ≤ c e) {Λ : ℝ}
    (hcΛ : ∀ e, c e ≤ Λ) {N : ℕ} (hN : 0 < N) (a : Fin d → ℝ) (u : Vertex d → ℝ) (y : Vertex d)
    (K : Finset (Vertex d)) (v : Vertex d → ℝ)
    (hv : ∀ x ∈ (cornerCube y N).vertices, x ∉ K → v x = cubeAffine N u y x)
    (hsep : ∀ x ∈ (cornerCube y N).vertices, ∀ j : Fin d, x + unit j ∈ (cornerCube y N).vertices →
      x ∉ K → c (x, j) ≠ 0 → x + unit j ∉ K) {δ₀ : ℝ}
    (hK : (∑ j : Fin d, ∑ x ∈ ((cornerCube y N).vertices.filter
        fun x => x + unit j ∈ (cornerCube y N).vertices).filter (· ∈ K),
          c (x, j) * (v (x + unit j) - v x) ^ 2) / (N : ℝ) ^ d ≤
        ∑ k, a k * cubeSlope N u y k ^ 2 + 2 * δ₀) :
    innerEdgeEnergy c (cornerCube y N) v / (N : ℝ) ^ d ≤
      ∑ k, a k * cubeSlope N u y k ^ 2 +
        2 * (δ₀ + Λ * (∑ j : Fin d, cubeSlope N u y j ^ 2) *
          #((cornerCube y N).vertices \ K) / (2 * (N : ℝ) ^ d)) := by
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have h := innerEdgeEnergy_le_of_eq_affine c hc0 hcΛ (cornerCube y N) K v (cubeAffine N u y)
    (cubeSlope N u y) (fun x j => cubeAffine_add_unit_sub N u y x j) hv hsep
  have h2 := div_le_div_of_nonneg_right h hNd.le
  rw [add_div] at h2
  have e : 2 * (δ₀ + Λ * (∑ j : Fin d, cubeSlope N u y j ^ 2) *
      #((cornerCube y N).vertices \ K) / (2 * (N : ℝ) ^ d)) =
      2 * δ₀ + Λ * (∑ j : Fin d, cubeSlope N u y j ^ 2) *
        #((cornerCube y N).vertices \ K) / (N : ℝ) ^ d := by
    field_simp
  rw [e]
  linarith

end Rigidity.Dirichlet
