/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Analysis/CubePoincare.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Lattice
import Rigidity.Vendor.LHCH.Support.Lattice.Membership

/-!
# The discrete Poincaré inequality on a lattice cube

For every lattice cube `B = z + {0, …, L}^d` and every `g`, `Σ_{x∈B}(g(x) − ḡ)² ≤ d L² Σ_{edges of
B}(∇g)²`: write the variance as a double
sum, telescope `g(x) − g(y)` through the hybrids that take the first `k` coordinates from `y`, and
bound each one-dimensional difference by the energy on its line, counting by involutions of `B × B`.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The variance of `f` over a nonempty finite set is half the mean square of its differences. -/
theorem two_mul_card_mul_sum_sq_sub_avg {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℝ) :
    2 * (s.card : ℝ) * ∑ x ∈ s, (f x - (s.card : ℝ)⁻¹ * ∑ y ∈ s, f y) ^ 2 =
      ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 := by
  have hN : (s.card : ℝ) ≠ 0 := by
    have := hs.card_pos
    positivity
  have h1 : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
      2 * s.card * ∑ x ∈ s, f x ^ 2 - 2 * (∑ x ∈ s, f x) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.mul_sum, ← Finset.sum_mul, nsmul_eq_mul]
    ring
  have h2 : ∑ x ∈ s, (f x - (s.card : ℝ)⁻¹ * ∑ y ∈ s, f y) ^ 2 =
      ∑ x ∈ s, f x ^ 2 - (s.card : ℝ)⁻¹ * (∑ x ∈ s, f x) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.mul_sum, ← Finset.sum_mul, nsmul_eq_mul]
    field_simp
    ring
  rw [h1, h2]
  field_simp

/-- A one-dimensional Poincaré-type bound: the squared difference of `φ` at two points of the
range `[a, a + L]` is at most `L` times the sum of the squared increments of `φ` over the range. -/
theorem sq_sub_le_mul_sum_sq_succ_sub (φ : ℤ → ℝ) (a : ℤ) (L : ℕ) {s t : ℤ}
    (hs : s ∈ Finset.Icc a (a + L)) (ht : t ∈ Finset.Icc a (a + L)) :
    (φ s - φ t) ^ 2 ≤
      (L : ℝ) * ∑ r ∈ Finset.Ico a (a + L), (φ (r + 1) - φ r) ^ 2 := by
  wlog hst : s ≤ t generalizing s t
  · rw [show (φ s - φ t) ^ 2 = (φ t - φ s) ^ 2 by ring]
    exact this ht hs (by omega)
  rw [Finset.mem_Icc] at hs ht
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, t = s + m := ⟨(t - s).toNat, by omega⟩
  have htel : φ (s + m) - φ s = ∑ j ∈ Finset.range m, (φ (s + j + 1) - φ (s + j)) := by
    have := Finset.sum_range_sub (fun j : ℕ => φ (s + j)) m
    simp only [Nat.cast_zero, add_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  have hsub : ∑ j ∈ Finset.range m, (φ (s + j + 1) - φ (s + j)) ^ 2 ≤
      ∑ r ∈ Finset.Ico a (a + L), (φ (r + 1) - φ r) ^ 2 := by
    calc ∑ j ∈ Finset.range m, (φ (s + j + 1) - φ (s + j)) ^ 2
        = ∑ r ∈ (Finset.range m).image (fun j : ℕ => s + (j : ℤ)), (φ (r + 1) - φ r) ^ 2 := by
          rw [Finset.sum_image]
          intro i _ j _ hij
          simpa using hij
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
          intro r hr
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
          rw [Finset.mem_range] at hj
          rw [Finset.mem_Ico]
          omega
  have hm : (m : ℝ) ≤ L := by
    have : m ≤ L := by omega
    exact_mod_cast this
  rw [show (φ s - φ (s + m)) ^ 2 = (φ (s + m) - φ s) ^ 2 by ring, htel]
  calc (∑ j ∈ Finset.range m, (φ (s + j + 1) - φ (s + j))) ^ 2
      ≤ (Finset.range m).card * ∑ j ∈ Finset.range m, (φ (s + j + 1) - φ (s + j)) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (L : ℝ) * ∑ r ∈ Finset.Ico a (a + L), (φ (r + 1) - φ r) ^ 2 := by
        rw [Finset.card_range]
        exact mul_le_mul hm hsub (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)

/-- Replacing the `i`th coordinate of a point of the cube by a value of its range stays in the
cube. -/
theorem update_mem_latticeCube {z p : Site d} {L : ℕ} (i : Fin d) {t : ℤ}
    (hp : p ∈ latticeCube z L) (ht : t ∈ Finset.Icc (z i) (z i + L)) :
    Function.update p i t ∈ latticeCube z L := by
  rw [mem_latticeCube_iff_coord] at hp ⊢
  rw [Finset.mem_Icc] at ht
  intro j
  by_cases h : j = i
  · subst h
    simpa using ht
  · simpa [Function.update_of_ne h] using hp j

/-- The `i`th coordinate of a point of the cube lies in the range of that coordinate. -/
theorem coord_mem_Icc_of_mem_latticeCube {z p : Site d} {L : ℕ} (i : Fin d)
    (hp : p ∈ latticeCube z L) : p i ∈ Finset.Icc (z i) (z i + L) := by
  rw [mem_latticeCube_iff_coord] at hp
  exact Finset.mem_Icc.mpr (hp i)

/-- The integer interval `[a, a + L]` has `L + 1` points. -/
theorem card_Icc_add_natCast (a : ℤ) (L : ℕ) :
    ((Finset.Icc a (a + L)).card : ℝ) = (L : ℝ) + 1 := by
  rw [Int.card_Icc]
  have : (a + L + 1 - a).toNat = L + 1 := by omega
  rw [this]
  push_cast
  ring

/-- Summing over a cube and over the `i`th coordinate range the value at the point with that
coordinate replaced counts every point of the cube once for each value of the coordinate. -/
theorem sum_sum_update_eq (z : Site d) (L : ℕ) (i : Fin d) (G : Site d → ℝ) :
    ∑ p ∈ latticeCube z L, ∑ t ∈ Finset.Icc (z i) (z i + L), G (Function.update p i t) =
      ((L : ℝ) + 1) * ∑ x ∈ latticeCube z L, G x := by
  rw [← Finset.sum_product']
  have h : ∑ q ∈ latticeCube z L ×ˢ Finset.Icc (z i) (z i + L), G q.1 =
      ((L : ℝ) + 1) * ∑ x ∈ latticeCube z L, G x := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_const, nsmul_eq_mul, card_Icc_add_natCast]
  rw [← h]
  refine Finset.sum_nbij' (fun q => (Function.update q.1 i q.2, q.1 i))
    (fun q => (Function.update q.1 i q.2, q.1 i)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_product] at hq ⊢
    exact ⟨update_mem_latticeCube i hq.1 hq.2, coord_mem_Icc_of_mem_latticeCube i hq.1⟩
  · intro q hq
    rw [Finset.mem_product] at hq ⊢
    exact ⟨update_mem_latticeCube i hq.1 hq.2, coord_mem_Icc_of_mem_latticeCube i hq.1⟩
  · intro q _
    simp
  · intro q _
    simp
  · intro q _
    rfl

/-- The squared difference of `g` at a point of the cube and at the point with its `i`th coordinate
replaced by any other value in the range is bounded by `L` times the energy along the line. -/
theorem sq_sub_update_le_mul_sum_line (z : Site d) (L : ℕ) (g : Site d → ℝ) (i : Fin d)
    {p : Site d} {t : ℤ} (hp : p ∈ latticeCube z L) (ht : t ∈ Finset.Icc (z i) (z i + L)) :
    (g p - g (Function.update p i t)) ^ 2 ≤ (L : ℝ) *
      ∑ r ∈ Finset.Icc (z i) (z i + L),
        if Function.update p i r + unit i ∈ latticeCube z L then
          (g (Function.update p i r + unit i) - g (Function.update p i r)) ^ 2 else 0 := by
  have h1 := sq_sub_le_mul_sum_sq_succ_sub (fun r => g (Function.update p i r)) (z i) L
    (coord_mem_Icc_of_mem_latticeCube i hp) ht
  simp only [Function.update_eq_self] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg L))
  calc ∑ r ∈ Finset.Ico (z i) (z i + L),
        (g (Function.update p i (r + 1)) - g (Function.update p i r)) ^ 2
      = ∑ r ∈ Finset.Ico (z i) (z i + L),
        if Function.update p i r + unit i ∈ latticeCube z L then
          (g (Function.update p i r + unit i) - g (Function.update p i r)) ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Ico] at hr
        have hmem : Function.update p i r + unit i ∈ latticeCube z L := by
          rw [update_add_unit]
          exact update_mem_latticeCube i hp (Finset.mem_Icc.mpr (by omega))
        rw [if_pos hmem, ← update_add_unit]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => ?_
        · intro r hr
          rw [Finset.mem_Ico] at hr
          exact Finset.mem_Icc.mpr (by omega)
        · split_ifs
          · exact sq_nonneg _
          · exact le_rfl

/-- The energy of the differences `g p - g (p with its i-th coordinate replaced by that of p')`
over pairs of points of the cube is bounded by the energy of `g` along the edges in direction `i`,
with the factor `|B| L (L + 1)`. -/
theorem sum_sum_sq_sub_update_le (z : Site d) (L : ℕ) (g : Site d → ℝ) (i : Fin d) :
    ∑ p ∈ latticeCube z L, ∑ q ∈ latticeCube z L, (g p - g (Function.update p i (q i))) ^ 2 ≤
      ((latticeCube z L).card : ℝ) * L * (((L : ℝ) + 1) * ∑ x ∈ latticeCube z L,
        if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0) := by
  have h1 : ∀ p ∈ latticeCube z L, ∑ q ∈ latticeCube z L,
      (g p - g (Function.update p i (q i))) ^ 2 ≤ ((latticeCube z L).card : ℝ) * ((L : ℝ) *
        ∑ r ∈ Finset.Icc (z i) (z i + L),
          if Function.update p i r + unit i ∈ latticeCube z L then
            (g (Function.update p i r + unit i) - g (Function.update p i r)) ^ 2 else 0) := by
    intro p hp
    calc ∑ q ∈ latticeCube z L, (g p - g (Function.update p i (q i))) ^ 2
        ≤ ∑ _q ∈ latticeCube z L, (L : ℝ) * ∑ r ∈ Finset.Icc (z i) (z i + L),
          if Function.update p i r + unit i ∈ latticeCube z L then
            (g (Function.update p i r + unit i) - g (Function.update p i r)) ^ 2 else 0 :=
          Finset.sum_le_sum fun q hq => sq_sub_update_le_mul_sum_line z L g i hp
            (coord_mem_Icc_of_mem_latticeCube i hq)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ p ∈ latticeCube z L, ∑ q ∈ latticeCube z L, (g p - g (Function.update p i (q i))) ^ 2
      ≤ ∑ p ∈ latticeCube z L, ((latticeCube z L).card : ℝ) * ((L : ℝ) *
        ∑ r ∈ Finset.Icc (z i) (z i + L),
          if Function.update p i r + unit i ∈ latticeCube z L then
            (g (Function.update p i r + unit i) - g (Function.update p i r)) ^ 2 else 0) :=
        Finset.sum_le_sum h1
    _ = ((latticeCube z L).card : ℝ) * L * ∑ p ∈ latticeCube z L,
        ∑ r ∈ Finset.Icc (z i) (z i + L),
          (fun x => if x + unit i ∈ latticeCube z L then
            (g (x + unit i) - g x) ^ 2 else 0) (Function.update p i r) := by
        rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
        rw [sum_sum_update_eq z L i (fun x => if x + unit i ∈ latticeCube z L then
          (g (x + unit i) - g x) ^ 2 else 0)]

/-- The hybrid of two sites: it takes the first `k` coordinates from `y` and the others from
`x`. -/
def cubeHybrid (k : ℕ) (x y : Site d) : Site d := fun j => if (j : ℕ) < k then y j else x j

/-- With no coordinate taken from `y`, the hybrid is `x`. -/
theorem cubeHybrid_zero (x y : Site d) : cubeHybrid 0 x y = x := by
  funext j
  simp [cubeHybrid]

/-- With all the coordinates taken from `y`, the hybrid is `y`. -/
theorem cubeHybrid_of_le {k : ℕ} (hk : d ≤ k) (x y : Site d) : cubeHybrid k x y = y := by
  funext j
  have := j.isLt
  simp [cubeHybrid, show (j : ℕ) < k by omega]

/-- The hybrid of two points of a cube lies in the cube. -/
theorem cubeHybrid_mem {z : Site d} {L : ℕ} {x y : Site d} (k : ℕ) (hx : x ∈ latticeCube z L)
    (hy : y ∈ latticeCube z L) : cubeHybrid k x y ∈ latticeCube z L := by
  rw [mem_latticeCube_iff_coord] at hx hy ⊢
  intro j
  simp only [cubeHybrid]
  split_ifs
  · exact hy j
  · exact hx j

/-- Taking hybrids twice with the roles exchanged recovers the first point. -/
theorem cubeHybrid_cubeHybrid (k : ℕ) (x y : Site d) :
    cubeHybrid k (cubeHybrid k x y) (cubeHybrid k y x) = x := by
  funext j
  by_cases h : (j : ℕ) < k <;> simp [cubeHybrid, h]

/-- Taking one more coordinate from `y` replaces the `k`th coordinate (as the `Fin d` index `i`) of
the hybrid by that of `y`. -/
theorem cubeHybrid_succ {k : ℕ} (i : Fin d) (hi : (i : ℕ) = k) (x y : Site d) :
    cubeHybrid (k + 1) x y = Function.update (cubeHybrid k x y) i (y i) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [cubeHybrid, hi]
  · have : (j : ℕ) ≠ k := fun hj => h (Fin.ext (by omega))
    have h2 : ((j : ℕ) < k + 1) ↔ ((j : ℕ) < k) := by omega
    simp [cubeHybrid, Function.update_of_ne h, h2]

/-- The `k`th coordinate of the `k`th hybrid is that of `x`. -/
theorem cubeHybrid_apply_self {k : ℕ} (i : Fin d) (hi : (i : ℕ) = k) (x y : Site d) :
    cubeHybrid k x y i = x i := by
  simp [cubeHybrid, hi]

/-- Exchanging the low coordinates of the two variables is an involution of the cube squared. -/
theorem sum_sum_cubeHybrid_swap (z : Site d) (L k : ℕ) (F : Site d → Site d → ℝ) :
    ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, F (cubeHybrid k x y) (cubeHybrid k y x) =
      ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, F x y := by
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun q => (cubeHybrid k q.1 q.2, cubeHybrid k q.2 q.1))
    (fun q => (cubeHybrid k q.1 q.2, cubeHybrid k q.2 q.1)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_product] at hq ⊢
    exact ⟨cubeHybrid_mem k hq.1 hq.2, cubeHybrid_mem k hq.2 hq.1⟩
  · intro q hq
    rw [Finset.mem_product] at hq ⊢
    exact ⟨cubeHybrid_mem k hq.1 hq.2, cubeHybrid_mem k hq.2 hq.1⟩
  · intro q _
    simp only [cubeHybrid_cubeHybrid]
  · intro q _
    simp only [cubeHybrid_cubeHybrid]
  · intro q _
    rfl

/-- The difference of `g` at two points is the sum of the differences along the chain of hybrids
that exchanges the coordinates one at a time. -/
theorem sub_eq_sum_cubeHybrid (g : Site d → ℝ) (x y : Site d) :
    g x - g y = ∑ i : Fin d, (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) := by
  have h := Finset.sum_range_sub' (fun k => g (cubeHybrid k x y)) d
  simp only [cubeHybrid_zero, cubeHybrid_of_le (le_refl d)] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => g (cubeHybrid k x y) -
    g (cubeHybrid (k + 1) x y)) d, h]

/-- The squared difference of `g` at two points is at most `d` times the sum of the squared
differences along the chain of hybrids. -/
theorem sq_sub_le_card_mul_sum_sq_cubeHybrid (g : Site d → ℝ) (x y : Site d) :
    (g x - g y) ^ 2 ≤
      (d : ℝ) * ∑ i : Fin d, (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
    (f := fun i : Fin d => g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y))
  rw [sub_eq_sum_cubeHybrid g x y]
  simpa using h

/-- The `i`-th term of the chain of hybrids, summed over the cube squared, is bounded by the
energy of `g` along the edges in direction `i`. -/
theorem sum_sum_sq_sub_cubeHybrid_le (z : Site d) (L : ℕ) (g : Site d → ℝ) (i : Fin d) :
    ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
        (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2 ≤
      ((latticeCube z L).card : ℝ) * L * (((L : ℝ) + 1) * ∑ x ∈ latticeCube z L,
        if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0) := by
  have h := sum_sum_cubeHybrid_swap z L i
    (fun p q => (g p - g (Function.update p i (q i))) ^ 2)
  have h2 : ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
        (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2 =
      ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
        (g (cubeHybrid i x y) - g (Function.update (cubeHybrid i x y) i
          (cubeHybrid i y x i))) ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [cubeHybrid_succ i rfl, cubeHybrid_apply_self i rfl]
  rw [h2, h]
  exact sum_sum_sq_sub_update_le z L g i

/-- **The discrete Poincaré inequality on a lattice cube**: there is `C(d)` such that for every
cube `B = z + {0, …, L}^d` and every `g`, `Σ_{x∈B} (g(x) − ḡ)² ≤ C L² Σ_{x∈B} Σ_i [x + e_i ∈ B]
(g(x + e_i) − g(x))²`, with `ḡ` the average of `g` over `B`. -/
theorem exists_sum_sq_sub_avg_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Site d) (L : ℕ) (g : Site d → ℝ),
      ∑ x ∈ latticeCube z L, (g x - ((latticeCube z L).card : ℝ)⁻¹ *
          ∑ y ∈ latticeCube z L, g y) ^ 2 ≤
        C * (L : ℝ) ^ 2 * ∑ x ∈ latticeCube z L, ∑ i : Fin d,
          if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0 := by
  refine ⟨d, Nat.cast_nonneg d, fun z L g => ?_⟩
  have hne : (latticeCube z L).Nonempty :=
    ⟨z, (mem_latticeCube_iff_coord z z L).2 fun i => ⟨le_rfl, by omega⟩⟩
  have hN : (0 : ℝ) < (latticeCube z L).card := by exact_mod_cast hne.card_pos
  have hpair := two_mul_card_mul_sum_sq_sub_avg (latticeCube z L) hne g
  have hE : 0 ≤ ∑ x ∈ latticeCube z L, ∑ i : Fin d,
      if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  have hsum : ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, (g x - g y) ^ 2 ≤
      (d : ℝ) * (((latticeCube z L).card : ℝ) * L * (((L : ℝ) + 1) * ∑ x ∈ latticeCube z L,
        ∑ i : Fin d, if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0)) := by
    calc ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, (g x - g y) ^ 2
        ≤ ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, (d : ℝ) * ∑ i : Fin d,
          (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
            sq_sub_le_card_mul_sum_sq_cubeHybrid g x y
      _ = (d : ℝ) * ∑ i : Fin d, ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
          (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2 := by
          simp_rw [← Finset.mul_sum]
          congr 1
          calc ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, ∑ i : Fin d,
                (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2
              = ∑ x ∈ latticeCube z L, ∑ i : Fin d, ∑ y ∈ latticeCube z L,
                (g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) ^ 2 :=
                Finset.sum_congr rfl fun x _ => Finset.sum_comm
            _ = _ := Finset.sum_comm
      _ ≤ (d : ℝ) * ∑ i : Fin d, ((latticeCube z L).card : ℝ) * L *
          (((L : ℝ) + 1) * ∑ x ∈ latticeCube z L,
            if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0) := by
          gcongr with i _
          exact sum_sum_sq_sub_cubeHybrid_le z L g i
      _ = _ := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_comm]
  have hL : (L : ℝ) * ((L : ℝ) + 1) ≤ 2 * (L : ℝ) ^ 2 := by
    have : (L : ℝ) ≤ (L : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero L
    nlinarith
  have hcoef : 0 ≤ (d : ℝ) * ((latticeCube z L).card : ℝ) * ∑ x ∈ latticeCube z L, ∑ i : Fin d,
      if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hN.le) hE
  refine le_of_mul_le_mul_left (a := 2 * ((latticeCube z L).card : ℝ)) ?_ (by positivity)
  calc 2 * ((latticeCube z L).card : ℝ) * ∑ x ∈ latticeCube z L,
        (g x - ((latticeCube z L).card : ℝ)⁻¹ * ∑ y ∈ latticeCube z L, g y) ^ 2
      = ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, (g x - g y) ^ 2 := hpair
    _ ≤ _ := hsum
    _ = ((d : ℝ) * ((latticeCube z L).card : ℝ) * ∑ x ∈ latticeCube z L, ∑ i : Fin d,
        if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0) *
          ((L : ℝ) * ((L : ℝ) + 1)) := by ring
    _ ≤ ((d : ℝ) * ((latticeCube z L).card : ℝ) * ∑ x ∈ latticeCube z L, ∑ i : Fin d,
        if x + unit i ∈ latticeCube z L then (g (x + unit i) - g x) ^ 2 else 0) *
          (2 * (L : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hL hcoef
    _ = _ := by ring

end LatticeHC

end
