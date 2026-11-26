import Rigidity.Proofs.Corrector.GeneralMeyersSource

/-!
# The geometry of a partition into triadic cubes with comparable neighbours

A function `n : ℤᵈ → ℕ` describes a partition of the lattice into triadic cubes, the cell of `x`
being `cube (n x) x`, when the cell of `x` determines `n` on it and the cells of points at
`ℓ∞` distance at most one differ by at most one scale (`IsCellScale`; Armstrong and Dario,
Proposition 2.1 (ii), for the partitions of their Proposition 2.1). Then:

* `IsCellScale.le_of_mem_enl` (the collar): if `n u = k + 1` and `z` lies in the threefold
  enlargement `enl 1 k u` of the child `cube k u` of the cell of `u`, then `k ≤ n z ≤ k + 2`: the
  cube of scale `k` of `z` touches that child, and two scale comparisons along the touching points
  give both bounds;
* `IsCellScale.tsum_enl_le` (bounded overlap): `Σ_u 1{z ∈ enl 1 (n u - 1) u} / |cube (n u - 1) u|`
  is at most `3 · 4^d`, the sum running over the points of cells of positive scale;
* `IsCellScale.tsum_eq_tsum_avg`: `Σ_u f(u) = Σ_u avg_{cube (n u - 1) u} f`, the cubes
  `cube (n u - 1) u` being the children of the cells (the cells themselves when `n u = 0`).

These are the steps of the summation over the cells of estimate (2) (the route through estimate (2)
for the Step 2 sum of the proof of Lemma 3.3 of Dario) that use the partition only.
-/

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Proofs.Cluster
open scoped Classical ENNReal

variable {d : ℕ}

/-- `n` describes a partition into the cubes `cube (n x) x` with comparable neighbours. -/
structure IsCellScale (n : Vertex d → ℕ) : Prop where
  eq_of_mem : ∀ x y, y ∈ cube (n x) x → n y = n x
  le_of_near : ∀ x y : Vertex d, (∀ i, |x i - y i| ≤ 1) → n x ≤ n y + 1

namespace IsCellScale

variable {n : Vertex d → ℕ}

theorem three_pow_pos (k : ℕ) : (0 : ℤ) < 3 ^ k := by positivity

/-- **The collar of a cell**: the cubes of scale `k` in the threefold enlargement of a child of a
cell of scale `k + 1` lie in cells of scale between `k` and `k + 2`. -/
theorem le_of_mem_enl (hn : IsCellScale n) {u z : Vertex d} {k : ℕ} (hk : n u = k + 1)
    (hz : z ∈ enl 1 k u) : k ≤ n z ∧ n z ≤ k + 2 := by
  have hz' := mem_box.1 hz
  have hzz := mem_box.1 (mem_cube_self k z)
  have h2 := two_mul_halfSide_add_one k
  have hh1 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have h3 := three_pow_pos k
  have hh0 := halfSide_nonneg k
  -- the offsets of the two centres, in units of `3^k`
  have hm : ∀ i, |idx k z i - idx k u i| ≤ 1 := by
    intro i
    have a1 := hz' i
    have a2 := hzz i
    have e : center k z i - center k u i = 3 ^ k * (idx k z i - idx k u i) := by
      simp only [center]; ring
    have t := abs_sub_le (center k z i) (z i) (center k u i)
    rw [abs_sub_comm (center k z i) (z i)] at t
    have hb : |3 ^ k * (idx k z i - idx k u i)| ≤ 2 * 3 ^ k - 1 := by
      rw [← e]; linarith
    rw [abs_mul, abs_of_pos h3] at hb
    by_contra hlt
    rw [not_le] at hlt
    have : (2 : ℤ) ≤ |idx k z i - idx k u i| := by omega
    nlinarith
  set w : Vertex d := fun i => center k z i - (idx k z i - idx k u i) * halfSide k with hw
  set t : Vertex d := fun i => center k u i + (idx k z i - idx k u i) * halfSide k with ht
  have hwz : w ∈ cube k z := by
    rw [cube, mem_box]
    intro i
    simp only [hw, sub_sub_cancel_left, abs_neg, abs_mul]
    have := hm i
    nlinarith [abs_nonneg (idx k z i - idx k u i), abs_of_nonneg hh0]
  have htu : t ∈ cube k u := by
    rw [cube, mem_box]
    intro i
    simp only [ht, add_sub_cancel_left, abs_mul]
    have := hm i
    nlinarith [abs_nonneg (idx k z i - idx k u i), abs_of_nonneg hh0]
  have hwt : ∀ i, |w i - t i| ≤ 1 := by
    intro i
    have e : w i - t i = idx k z i - idx k u i := by
      simp only [hw, ht, center]
      linear_combination -(idx k z i - idx k u i) * h2
    rw [e]
    exact hm i
  have htw : ∀ i, |t i - w i| ≤ 1 := fun i => by rw [abs_sub_comm]; exact hwt i
  have hnt : n t = k + 1 := by
    rw [← hk]
    refine hn.eq_of_mem u t ?_
    rw [hk]
    exact cube_subset_succ k u htu
  have h1 := hn.le_of_near t w htw
  have h1' := hn.le_of_near w t hwt
  have hkw : k ≤ n w := by omega
  have hzw : z ∈ cube (n w) w := by
    have : z ∈ cube k w := by
      rw [cube_eq_of_mem hwz]
      exact mem_cube_self k z
    exact cube_mono hkw w this
  have := hn.eq_of_mem w z hzw
  omega

/-- The child `cube (n u - 1) u` of the cell of `u` is contained in the cell. -/
theorem cube_pred_subset (u : Vertex d) : cube (n u - 1) u ⊆ cube (n u) u :=
  cube_mono (Nat.sub_le _ _) u

theorem cube_pred_eq_of_mem (hn : IsCellScale n) {u u' : Vertex d} (h : u' ∈ cube (n u - 1) u) :
    n u' = n u ∧ cube (n u' - 1) u' = cube (n u - 1) u := by
  have h1 := hn.eq_of_mem u u' (cube_pred_subset u h)
  refine ⟨h1, ?_⟩
  rw [h1]
  exact cube_eq_of_mem h

/-- `Σ_u f(u) = Σ_u avg_{cube (n u - 1) u} f`. -/
theorem tsum_eq_tsum_avg (hn : IsCellScale n) (f : Vertex d → ℝ≥0∞) :
    ∑' u, f u = ∑' u, ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ * ∑ u' ∈ cube (n u - 1) u, f u' := by
  have hmem : ∀ u u', u' ∈ cube (n u - 1) u ↔ u ∈ cube (n u' - 1) u' := by
    intro u u'
    constructor
    · intro h
      rw [(hn.cube_pred_eq_of_mem h).2]
      exact mem_cube_self _ u
    · intro h
      rw [(hn.cube_pred_eq_of_mem h).2]
      exact mem_cube_self _ u'
  have hrhs : ∀ u, ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ * ∑ u' ∈ cube (n u - 1) u, f u' =
      ∑' u', if u' ∈ cube (n u - 1) u then
        ((cube (n u' - 1) u').card : ℝ≥0∞)⁻¹ * f u' else 0 := by
    intro u
    rw [Finset.mul_sum, tsum_eq_sum (s := cube (n u - 1) u) fun u' hu' => if_neg hu']
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [if_pos hu', (hn.cube_pred_eq_of_mem hu').2]
  simp_rw [hrhs]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u' => ?_
  have hc : (∑' u, if u' ∈ cube (n u - 1) u then
      ((cube (n u' - 1) u').card : ℝ≥0∞)⁻¹ * f u' else 0) =
      ∑ u ∈ cube (n u' - 1) u', ((cube (n u' - 1) u').card : ℝ≥0∞)⁻¹ * f u' := by
    rw [tsum_eq_sum (s := cube (n u' - 1) u') fun u hu => if_neg fun h => hu ((hmem u u').1 h)]
    exact Finset.sum_congr rfl fun u hu => if_pos ((hmem u u').2 hu)
  rw [hc, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
  · have := card_cube_pos (n u' - 1) u'
    exact_mod_cast (Nat.cast_pos.1 this).ne'
  · exact ENNReal.natCast_ne_top _

/-- The points `u` with `z ∈ enl 1 k u` lie in the box of radius `h_{k+1} + h_k` around `z`. -/
theorem mem_box_of_mem_enl {k : ℕ} {u z : Vertex d} (hz : z ∈ enl 1 k u) :
    u ∈ box z (halfSide (k + 1) + halfSide k) := by
  rw [mem_box]
  intro i
  have a1 := (mem_box.1 hz) i
  have a2 := (mem_box.1 (mem_cube_self k u)) i
  have t := abs_sub_le (u i) (center k u i) (z i)
  rw [abs_sub_comm (center k u i) (z i)] at t
  linarith

theorem card_box_enl_le (z : Vertex d) (k : ℕ) :
    ((box z (halfSide (k + 1) + halfSide k)).card : ℝ) ≤ 4 ^ d * (cube k z).card := by
  have hh0 := halfSide_nonneg k
  have hh1 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
  have h2 := two_mul_halfSide_add_one k
  rw [card_box (d := d) z (R := halfSide (k + 1) + halfSide k) (by omega), card_cube]
  have e : (2 * (halfSide (k + 1) + halfSide k) + 1 : ℤ) = 4 * 3 ^ k - 1 := by
    rw [hh1]; linarith
  rw [e, ← mul_pow]
  push_cast
  have h3 : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  exact pow_le_pow_left₀ (by linarith) (by linarith) d

/-- **Bounded overlap of the enlarged children of the cells**:
`Σ_u 1{n u ≥ 1, z ∈ enl 1 (n u - 1) u} / |cube (n u - 1) u| ≤ 3 · 4^d`. -/
theorem tsum_enl_le (hn : IsCellScale n) (z : Vertex d) :
    ∑' u, (if 1 ≤ n u ∧ z ∈ enl 1 (n u - 1) u then
      ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ else 0) ≤ 3 * 4 ^ d := by
  have hpt : ∀ u, (if 1 ≤ n u ∧ z ∈ enl 1 (n u - 1) u then
      ((cube (n u - 1) u).card : ℝ≥0∞)⁻¹ else 0) ≤
      ∑ k ∈ Finset.Icc (n z - 2) (n z), if u ∈ box z (halfSide (k + 1) + halfSide k) then
        ((cube k z).card : ℝ≥0∞)⁻¹ else 0 := by
    intro u
    split_ifs with h
    · obtain ⟨h1, hz⟩ := h
      have hk : n u = (n u - 1) + 1 := by omega
      have hb := hn.le_of_mem_enl hk hz
      have hmem : n u - 1 ∈ Finset.Icc (n z - 2) (n z) := Finset.mem_Icc.2 ⟨by omega, hb.1⟩
      have hcard : (cube (n u - 1) u).card = (cube (n u - 1) z).card := by
        have a := card_cube (d := d) (n u - 1) u
        have b := card_cube (d := d) (n u - 1) z
        exact_mod_cast a.trans b.symm
      refine le_trans ?_ (Finset.single_le_sum (f := fun k => if u ∈ box z
        (halfSide (k + 1) + halfSide k) then ((cube k z).card : ℝ≥0∞)⁻¹ else 0)
        (fun _ _ => by positivity) hmem)
      rw [if_pos (mem_box_of_mem_enl hz), hcard]
    · positivity
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  have hk : ∀ k ∈ Finset.Icc (n z - 2) (n z),
      (∑' u, if u ∈ box z (halfSide (k + 1) + halfSide k) then
        ((cube k z).card : ℝ≥0∞)⁻¹ else 0) ≤ 4 ^ d := by
    intro k _
    rw [tsum_eq_sum (s := box z (halfSide (k + 1) + halfSide k)) fun u hu => if_neg hu,
      Finset.sum_congr rfl fun u hu => if_pos hu, Finset.sum_const, nsmul_eq_mul]
    have hr := card_box_enl_le z k
    have hpos : ((cube k z).card : ℝ≥0∞) ≠ 0 := by
      have := card_cube_pos (d := d) k z
      exact_mod_cast (Nat.cast_pos.1 this).ne'
    have hN : (box z (halfSide (k + 1) + halfSide k)).card ≤ 4 ^ d * (cube k z).card := by
      exact_mod_cast hr
    have he : ((box z (halfSide (k + 1) + halfSide k)).card : ℝ≥0∞) ≤
        4 ^ d * ((cube k z).card : ℝ≥0∞) := by exact_mod_cast hN
    calc ((box z (halfSide (k + 1) + halfSide k)).card : ℝ≥0∞) * ((cube k z).card : ℝ≥0∞)⁻¹
        ≤ 4 ^ d * ((cube k z).card : ℝ≥0∞) * ((cube k z).card : ℝ≥0∞)⁻¹ := by gcongr
      _ = 4 ^ d := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hpos (ENNReal.natCast_ne_top _), mul_one]
  refine (Finset.sum_le_sum hk).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  have : n z + 1 - (n z - 2) ≤ 3 := by omega
  have h3 : ((n z + 1 - (n z - 2) : ℕ) : ℝ≥0∞) ≤ 3 := by exact_mod_cast this
  calc ((n z + 1 - (n z - 2) : ℕ) : ℝ≥0∞) * 4 ^ d ≤ 3 * 4 ^ d := by gcongr

end IsCellScale

end Rigidity.Corrector.GeneralDim
