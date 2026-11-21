/-
Adapted from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/Analysis/CubePoincare.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: squares replaced by `p`-th powers of absolute values for a real exponent `p ≥ 1`, the
Cauchy–Schwarz steps by the power-mean inequality; the hybrid and counting lemmas are imported.
-/
import Rigidity.Vendor.LHCH.Support.Analysis.CubePoincare

/-!
# The `L^p` Poincaré inequality on a lattice cube

For every lattice cube `B = z + {0, …, L}^d`, every real `p ≥ 1` and every `g`,
`∑_{x ∈ B} |g(x) - ḡ|^p ≤ d^{p-1} L^{p-1} (L + 1) ∑_{x ∈ B}
∑_i [x + e_i ∈ B] |g(x + e_i) - g(x)|^p`,
with `ḡ` the average of `g` over `B`: bound `|g(x) - ḡ|^p` by the mean of `|g(x) - g(y)|^p`,
telescope `g(x) - g(y)` through the hybrids that take the first `k` coordinates from `y`, and bound
each one-dimensional difference by the `p`-energy on its line.
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- A one-dimensional Poincaré-type bound: `|φ(s) - φ(t)|^p` at two points of `[a, a + L]` is at
most `L^{p-1}` times the sum of the `p`-th powers of the increments of `φ` over the range. -/
theorem abs_sub_rpow_le_mul_sum_abs_succ_sub (φ : ℤ → ℝ) (a : ℤ) (L : ℕ) {p : ℝ} (hp : 1 ≤ p)
    {s t : ℤ} (hs : s ∈ Finset.Icc a (a + L)) (ht : t ∈ Finset.Icc a (a + L)) :
    |φ s - φ t| ^ p ≤ (L : ℝ) ^ (p - 1) * ∑ r ∈ Finset.Ico a (a + L), |φ (r + 1) - φ r| ^ p := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm]
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
  have hsub : ∑ j ∈ Finset.range m, |φ (s + j + 1) - φ (s + j)| ^ p ≤
      ∑ r ∈ Finset.Ico a (a + L), |φ (r + 1) - φ r| ^ p := by
    calc ∑ j ∈ Finset.range m, |φ (s + j + 1) - φ (s + j)| ^ p
        = ∑ r ∈ (Finset.range m).image (fun j : ℕ => s + (j : ℤ)), |φ (r + 1) - φ r| ^ p := by
          rw [Finset.sum_image]
          intro i _ j _ hij
          simpa using hij
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
            Real.rpow_nonneg (abs_nonneg _) _
          intro r hr
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
          rw [Finset.mem_range] at hj
          rw [Finset.mem_Ico]
          omega
  have hm : (m : ℝ) ≤ L := by
    have : m ≤ L := by omega
    exact_mod_cast this
  rw [abs_sub_comm, htel]
  calc |∑ j ∈ Finset.range m, (φ (s + j + 1) - φ (s + j))| ^ p
      ≤ (∑ j ∈ Finset.range m, |φ (s + j + 1) - φ (s + j)|) ^ p :=
        Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (by linarith)
    _ ≤ ((Finset.range m).card : ℝ) ^ (p - 1) *
          ∑ j ∈ Finset.range m, |φ (s + j + 1) - φ (s + j)| ^ p :=
        Real.rpow_sum_le_const_mul_sum_rpow (s := Finset.range m)
          (f := fun j : ℕ => φ (s + j + 1) - φ (s + j)) hp
    _ ≤ (L : ℝ) ^ (p - 1) * ∑ r ∈ Finset.Ico a (a + L), |φ (r + 1) - φ r| ^ p := by
        rw [Finset.card_range]
        exact mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hm (by linarith)) hsub
          (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `|g(x) - g(x')|^p`, for `x'` obtained from a point `x` of the cube by replacing its `i`th
coordinate by a value in the range, is at most `L^{p-1}` times the `p`-energy along the line. -/
theorem abs_sub_update_rpow_le_mul_sum_line (z : Site d) (L : ℕ) (g : Site d → ℝ) (i : Fin d)
    {p : ℝ} (hp : 1 ≤ p) {x : Site d} {t : ℤ} (hx : x ∈ latticeCube z L)
    (ht : t ∈ Finset.Icc (z i) (z i + L)) :
    |g x - g (Function.update x i t)| ^ p ≤ (L : ℝ) ^ (p - 1) *
      ∑ r ∈ Finset.Icc (z i) (z i + L),
        if Function.update x i r + unit i ∈ latticeCube z L then
          |g (Function.update x i r + unit i) - g (Function.update x i r)| ^ p else 0 := by
  have h1 := abs_sub_rpow_le_mul_sum_abs_succ_sub (fun r => g (Function.update x i r)) (z i) L hp
    (coord_mem_Icc_of_mem_latticeCube i hx) ht
  simp only [Function.update_eq_self] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg L) _))
  calc ∑ r ∈ Finset.Ico (z i) (z i + L),
        |g (Function.update x i (r + 1)) - g (Function.update x i r)| ^ p
      = ∑ r ∈ Finset.Ico (z i) (z i + L),
        if Function.update x i r + unit i ∈ latticeCube z L then
          |g (Function.update x i r + unit i) - g (Function.update x i r)| ^ p else 0 := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_Ico] at hr
        have hmem : Function.update x i r + unit i ∈ latticeCube z L := by
          rw [update_add_unit]
          exact update_mem_latticeCube i hx (Finset.mem_Icc.mpr (by omega))
        rw [if_pos hmem, ← update_add_unit]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => ?_
        · intro r hr
          rw [Finset.mem_Ico] at hr
          exact Finset.mem_Icc.mpr (by omega)
        · split_ifs
          · exact Real.rpow_nonneg (abs_nonneg _) _
          · exact le_rfl

/-- The `p`-energy of the differences `g x - g (x with its i-th coordinate replaced by that of y)`
over pairs of points of the cube is at most `|B| L^{p-1} (L + 1)` times the `p`-energy of `g` along
the edges in direction `i`. -/
theorem sum_sum_abs_sub_update_rpow_le (z : Site d) (L : ℕ) (g : Site d → ℝ) (i : Fin d)
    {p : ℝ} (hp : 1 ≤ p) :
    ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, |g x - g (Function.update x i (y i))| ^ p ≤
      ((latticeCube z L).card : ℝ) * (L : ℝ) ^ (p - 1) * (((L : ℝ) + 1) *
        ∑ x ∈ latticeCube z L,
          if x + unit i ∈ latticeCube z L then |g (x + unit i) - g x| ^ p else 0) := by
  have h1 : ∀ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
      |g x - g (Function.update x i (y i))| ^ p ≤ ((latticeCube z L).card : ℝ) *
        ((L : ℝ) ^ (p - 1) * ∑ r ∈ Finset.Icc (z i) (z i + L),
          if Function.update x i r + unit i ∈ latticeCube z L then
            |g (Function.update x i r + unit i) - g (Function.update x i r)| ^ p else 0) := by
    intro x hx
    calc ∑ y ∈ latticeCube z L, |g x - g (Function.update x i (y i))| ^ p
        ≤ ∑ _y ∈ latticeCube z L, (L : ℝ) ^ (p - 1) * ∑ r ∈ Finset.Icc (z i) (z i + L),
          if Function.update x i r + unit i ∈ latticeCube z L then
            |g (Function.update x i r + unit i) - g (Function.update x i r)| ^ p else 0 :=
          Finset.sum_le_sum fun y hy => abs_sub_update_rpow_le_mul_sum_line z L g i hp hx
            (coord_mem_Icc_of_mem_latticeCube i hy)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L, |g x - g (Function.update x i (y i))| ^ p
      ≤ ∑ x ∈ latticeCube z L, ((latticeCube z L).card : ℝ) * ((L : ℝ) ^ (p - 1) *
        ∑ r ∈ Finset.Icc (z i) (z i + L),
          if Function.update x i r + unit i ∈ latticeCube z L then
            |g (Function.update x i r + unit i) - g (Function.update x i r)| ^ p else 0) :=
        Finset.sum_le_sum h1
    _ = ((latticeCube z L).card : ℝ) * (L : ℝ) ^ (p - 1) * ∑ x ∈ latticeCube z L,
        ∑ r ∈ Finset.Icc (z i) (z i + L),
          (fun x => if x + unit i ∈ latticeCube z L then
            |g (x + unit i) - g x| ^ p else 0) (Function.update x i r) := by
        rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
        rw [sum_sum_update_eq z L i (fun x => if x + unit i ∈ latticeCube z L then
          |g (x + unit i) - g x| ^ p else 0)]

/-- `|g(x) - g(y)|^p` is at most `d^{p-1}` times the sum of the `p`-th powers of the differences
along the chain of hybrids. -/
theorem abs_sub_rpow_le_card_mul_sum_cubeHybrid (g : Site d → ℝ) (x y : Site d) {p : ℝ}
    (hp : 1 ≤ p) :
    |g x - g y| ^ p ≤ (d : ℝ) ^ (p - 1) *
      ∑ i : Fin d, |g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)| ^ p := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow (s := (Finset.univ : Finset (Fin d)))
    (f := fun i : Fin d => g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)) hp
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [sub_eq_sum_cubeHybrid g x y]
  exact (Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (by linarith)).trans h

/-- The `i`-th term of the chain of hybrids, summed over the cube squared, is bounded by the
`p`-energy of `g` along the edges in direction `i`. -/
theorem sum_sum_abs_sub_cubeHybrid_rpow_le (z : Site d) (L : ℕ) (g : Site d → ℝ) (i : Fin d)
    {p : ℝ} (hp : 1 ≤ p) :
    ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
        |g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)| ^ p ≤
      ((latticeCube z L).card : ℝ) * (L : ℝ) ^ (p - 1) * (((L : ℝ) + 1) *
        ∑ x ∈ latticeCube z L,
          if x + unit i ∈ latticeCube z L then |g (x + unit i) - g x| ^ p else 0) := by
  have h := sum_sum_cubeHybrid_swap z L i
    (fun u v => |g u - g (Function.update u i (v i))| ^ p)
  have h2 : ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
        |g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)| ^ p =
      ∑ x ∈ latticeCube z L, ∑ y ∈ latticeCube z L,
        |g (cubeHybrid i x y) - g (Function.update (cubeHybrid i x y) i
          (cubeHybrid i y x i))| ^ p := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [cubeHybrid_succ i rfl, cubeHybrid_apply_self i rfl]
  rw [h2, h]
  exact sum_sum_abs_sub_update_rpow_le z L g i hp

/-- `|g(x) - ḡ|^p` is at most the mean over `y ∈ s` of `|g(x) - g(y)|^p`. -/
theorem abs_sub_avg_rpow_le {α : Type*} (s : Finset α) (hs : s.Nonempty) (g : α → ℝ) (x : α)
    {p : ℝ} (hp : 1 ≤ p) :
    |g x - (s.card : ℝ)⁻¹ * ∑ y ∈ s, g y| ^ p ≤ (s.card : ℝ)⁻¹ * ∑ y ∈ s, |g x - g y| ^ p := by
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have e : g x - (s.card : ℝ)⁻¹ * ∑ y ∈ s, g y = (s.card : ℝ)⁻¹ * ∑ y ∈ s, (g x - g y) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h := Real.rpow_sum_le_const_mul_sum_rpow (s := s) (f := fun y => g x - g y) hp
  have hsplit : (s.card : ℝ) ^ (p - 1) = (s.card : ℝ) ^ p * (s.card : ℝ)⁻¹ := by
    rw [Real.rpow_sub hN, Real.rpow_one, div_eq_mul_inv]
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hN), Real.mul_rpow (inv_nonneg.2 hN.le) (abs_nonneg _),
    Real.inv_rpow hN.le]
  calc ((s.card : ℝ) ^ p)⁻¹ * |∑ y ∈ s, (g x - g y)| ^ p
      ≤ ((s.card : ℝ) ^ p)⁻¹ * (∑ y ∈ s, |g x - g y|) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _)
          (Finset.abs_sum_le_sum_abs _ _) (by linarith))
          (inv_nonneg.2 (Real.rpow_nonneg hN.le _))
    _ ≤ ((s.card : ℝ) ^ p)⁻¹ * ((s.card : ℝ) ^ (p - 1) * ∑ y ∈ s, |g x - g y| ^ p) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 (Real.rpow_nonneg hN.le _))
    _ = (s.card : ℝ)⁻¹ * ∑ y ∈ s, |g x - g y| ^ p := by
        rw [hsplit]
        have : (s.card : ℝ) ^ p ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
        field_simp

/-- **The `L^p` Poincaré inequality on a lattice cube**: for every cube `B = z + {0, …, L}^d`,
every `p ≥ 1` and every `g`, `∑_{x∈B} |g(x) − ḡ|^p ≤ d^{p-1} L^{p-1} (L + 1) ∑_{x∈B} ∑_i
[x + e_i ∈ B] |g(x + e_i) − g(x)|^p`, with `ḡ` the average of `g` over `B`. -/
theorem sum_abs_sub_avg_rpow_le (z : Site d) (L : ℕ) (g : Site d → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ∑ x ∈ latticeCube z L, |g x - ((latticeCube z L).card : ℝ)⁻¹ *
        ∑ y ∈ latticeCube z L, g y| ^ p ≤
      (d : ℝ) ^ (p - 1) * (L : ℝ) ^ (p - 1) * ((L : ℝ) + 1) * ∑ x ∈ latticeCube z L,
        ∑ i : Fin d, if x + unit i ∈ latticeCube z L then |g (x + unit i) - g x| ^ p else 0 := by
  have hne : (latticeCube z L).Nonempty :=
    ⟨z, (mem_latticeCube_iff_coord z z L).2 fun i => ⟨le_rfl, by omega⟩⟩
  set B := latticeCube z L with hB
  have hN : (0 : ℝ) < B.card := by exact_mod_cast hne.card_pos
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ (p - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ∑ x ∈ B, |g x - (B.card : ℝ)⁻¹ * ∑ y ∈ B, g y| ^ p
      ≤ ∑ x ∈ B, (B.card : ℝ)⁻¹ * ∑ y ∈ B, |g x - g y| ^ p :=
        Finset.sum_le_sum fun x _ => abs_sub_avg_rpow_le B hne g x hp
    _ ≤ ∑ x ∈ B, (B.card : ℝ)⁻¹ * ∑ y ∈ B, (d : ℝ) ^ (p - 1) *
          ∑ i : Fin d, |g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)| ^ p :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
          abs_sub_rpow_le_card_mul_sum_cubeHybrid g x y hp) (inv_nonneg.2 hN.le)
    _ = (B.card : ℝ)⁻¹ * (d : ℝ) ^ (p - 1) * ∑ i : Fin d, ∑ x ∈ B, ∑ y ∈ B,
          |g (cubeHybrid i x y) - g (cubeHybrid ((i : ℕ) + 1) x y)| ^ p := by
        rw [← Finset.mul_sum, mul_assoc]
        congr 1
        simp only [← Finset.mul_sum]
        congr 1
        exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
    _ ≤ (B.card : ℝ)⁻¹ * (d : ℝ) ^ (p - 1) * ∑ i : Fin d,
          ((B.card : ℝ) * (L : ℝ) ^ (p - 1) * (((L : ℝ) + 1) * ∑ x ∈ B,
            if x + unit i ∈ B then |g (x + unit i) - g x| ^ p else 0)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          sum_sum_abs_sub_cubeHybrid_rpow_le z L g i hp)
          (mul_nonneg (inv_nonneg.2 hN.le) hd0)
    _ = (d : ℝ) ^ (p - 1) * (L : ℝ) ^ (p - 1) * ((L : ℝ) + 1) * ∑ x ∈ B,
          ∑ i : Fin d, if x + unit i ∈ B then |g (x + unit i) - g x| ^ p else 0 := by
        conv_rhs => rw [Finset.sum_comm]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        have hNne : (B.card : ℝ) ≠ 0 := hN.ne'
        calc (B.card : ℝ)⁻¹ * (d : ℝ) ^ (p - 1) * ((B.card : ℝ) * (L : ℝ) ^ (p - 1) *
              (((L : ℝ) + 1) * ∑ i : Fin d, ∑ x ∈ B,
                if x + unit i ∈ B then |g (x + unit i) - g x| ^ p else 0))
            = ((B.card : ℝ)⁻¹ * B.card) * ((d : ℝ) ^ (p - 1) * (L : ℝ) ^ (p - 1) *
              ((L : ℝ) + 1) * ∑ i : Fin d, ∑ x ∈ B,
                if x + unit i ∈ B then |g (x + unit i) - g x| ^ p else 0) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hNne, one_mul]

end LatticeHC

end
