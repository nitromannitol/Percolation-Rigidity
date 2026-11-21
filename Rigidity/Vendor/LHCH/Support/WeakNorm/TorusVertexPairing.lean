/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/TorusVertexPairing.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusPairing

/-!
# The vertex form of the torus pairing identity

A vertex `y` of `{0, …, N}^d` has `2^{d − #\{i : y_i ∈ \{0,N\}\}}` preimages under the fold of the
period box, so `Σ_{torus} f̃ g̃ = 2^d Σ_{y} w_v(y) f(y) g(y)` for the even reflections, with the
vertex face weight `w_v(y) = 2^{−#\{i : y_i ∈ \{0,N\}\}}`.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The vertex face weight `w_v(y) = 2^{−#{i : y_i ∈ {0, N}}}` of a vertex of `{0, …, N}^d`: one
over the number of reflected copies of `y` that coincide with it. -/
def vertexWeight (N : ℕ) (y : Site d) : ℝ :=
  (1 / 2 : ℝ) ^ (Finset.univ.filter fun i : Fin d => y i = 0 ∨ y i = N).card

/-- The fold maps every site of the periodicity box into the cube `{0, …, N}^d`. -/
theorem foldSite_mem_latticeCube (N : ℕ) (hN : 0 < N) (x : Site d) :
    foldSite N x ∈ latticeCube 0 N := by
  rw [mem_latticeCube_iff_coord]
  intro i
  have := foldCoord_mem N hN (x i)
  simpa [foldSite] using this

/-- The sites of the periodicity box that fold onto the vertex `y` are exactly those whose
coordinates `x_i` lie in the preimage of `y_i` under the one-dimensional fold. -/
theorem filter_foldSite_eq_piFinset (N : ℕ) (y : Site d) :
    (torusBox d N).filter (fun x => foldSite N x = y) =
      Fintype.piFinset fun i =>
        (Finset.Ico (0 : ℤ) (2 * N)).filter fun s => foldCoord N s = y i := by
  ext x
  simp only [torusBox, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hbox, h⟩ i
    exact ⟨hbox i, congrFun h i⟩
  · intro h
    exact ⟨fun i => (h i).1, funext fun i => (h i).2⟩

/-- A value `b ∈ [0, N]` has one preimage under the fold on `[0, 2N)` if `b ∈ {0, N}` and two
otherwise. -/
theorem card_filter_foldCoord (N : ℕ) (hN : 0 < N) (b : ℤ) (hb0 : 0 ≤ b) (hb1 : b ≤ N) :
    ((Finset.Ico (0 : ℤ) (2 * N)).filter fun s => foldCoord N s = b).card =
      if b = 0 ∨ b = N then 1 else 2 := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  split_ifs with hface
  · rw [Finset.card_eq_one]
    refine ⟨b, ?_⟩
    ext s
    rw [mem_filter_foldCoord_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, h1, h⟩
      split_ifs at h <;> omega
    · rintro rfl
      exact ⟨hb0, by omega, by rw [if_pos hb1]⟩
  · rw [Finset.card_eq_two]
    refine ⟨b, 2 * N - b, by omega, ?_⟩
    ext s
    rw [mem_filter_foldCoord_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, h1, h⟩
      split_ifs at h <;> omega
    · rintro (rfl | rfl)
      · exact ⟨hb0, by omega, by rw [if_pos hb1]⟩
      · exact ⟨by omega, by omega, by rw [if_neg (by omega)]; ring⟩

/-- **The fibres of the fold on vertices**: a vertex `y` of the cube `{0, …, N}^d` has
`2^d w_v(y)` preimages in the periodicity box. -/
theorem card_filter_foldSite (N : ℕ) (hN : 0 < N) (y : Site d) (hy : y ∈ latticeCube 0 N) :
    (((torusBox d N).filter (fun x => foldSite N x = y)).card : ℝ) =
      2 ^ d * vertexWeight N y := by
  have hcoord := (mem_latticeCube_iff_coord 0 y N).1 hy
  rw [filter_foldSite_eq_piFinset N y, Fintype.card_piFinset]
  have hfac : ∀ i, (((Finset.Ico (0 : ℤ) (2 * N)).filter fun s => foldCoord N s = y i).card : ℝ) =
      2 * (1 / 2 : ℝ) ^ (if y i = 0 ∨ y i = N then 1 else 0) := by
    intro i
    obtain ⟨h0, h1⟩ := hcoord i
    simp only [Pi.zero_apply, zero_add] at h0 h1
    rw [card_filter_foldCoord N hN (y i) h0 h1]
    by_cases hface : y i = 0 ∨ y i = N
    · rw [if_pos hface, if_pos hface]
      norm_num
    · rw [if_neg hface, if_neg hface]
      norm_num
  push_cast
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold vertexWeight
  congr 1
  rw [Finset.card_filter]

/-- **The vertex form of the pairing identity**: for `N ≥ 1`,
`Σ_{x ∈ {0,…,2N−1}^d} f̃(x) g̃(x) = 2^d Σ_{y ∈ {0,…,N}^d} w_v(y) f(y) g(y)` for the even
reflections `f̃`, `g̃` (a vertex `y` has `2^{d − #{i : y_i ∈ {0,N}}}` preimages under the fold). -/
theorem sum_torusBox_reflectFun_mul (N : ℕ) (hN : 0 < N) (f g : Site d → ℝ) :
    ∑ x ∈ torusBox d N, reflectFun N f x * reflectFun N g x =
      2 ^ d * ∑ y ∈ latticeCube 0 N, vertexWeight N y * f y * g y := by
  classical
  have hmul : ∀ x, reflectFun N f x * reflectFun N g x = f (foldSite N x) * g (foldSite N x) :=
    fun x => rfl
  simp only [hmul]
  rw [← Finset.sum_fiberwise_of_maps_to (g := foldSite N) (t := latticeCube 0 N)
    (fun x _ => foldSite_mem_latticeCube N hN x), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const,
    nsmul_eq_mul, card_filter_foldSite N hN y hy]
  ring

end LatticeHC

end
