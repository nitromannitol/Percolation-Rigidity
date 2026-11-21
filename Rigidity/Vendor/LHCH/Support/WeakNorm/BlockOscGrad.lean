/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/BlockOscGrad.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Analysis.CauchySchwarz
import Rigidity.Vendor.LHCH.Support.Analysis.CubePoincare
import Rigidity.Vendor.LHCH.Support.AppendixA.FaceWeight
import Rigidity.Vendor.LHCH.Support.Lattice.Membership
import Rigidity.Vendor.LHCH.Support.WeakNorm.Multiscale
import Rigidity.Vendor.LHCH.Support.WeakNorm.TorusCalculus
import Rigidity.Vendor.LHCH.Support.WeakNorm.TriadicRegroup

/-!
# Block oscillation of a gradient by its second differences

The oscillation of the
block means of `∇w` between scales `k` and `k + 1` in `□_n` is at most `C(d) 3^{2k}` times the
average of the squared second differences of `w` over `□_n`. Jensen for the face-weighted block
means, the discrete Poincaré inequality on each parent cube for `x ↦ w(x + e_j) − w(x)`, and an
overlap count of the parent cubes.
-/

open LatticeProb Matrix

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The face weight is at most one. -/
theorem faceWeight_le_one (z : Site d) (L : ℕ) (e : Edge d) : faceWeight z L e ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

/-- **The mean gradient minus a constant is a face-weighted average**: in direction `j`, the block
mean of `∇w` on a cube of side `L ≥ 1`, minus `g`, is the sum over the edges `e ∥ e_j` of `□` of
the weights `L^{-d} w_□(e)` times `w(e + e_j) − w(e) − g`. -/
theorem blockMean_grad_sub_eq_sum (z : Site d) {L : ℕ} (hL : 1 ≤ L) (w : Site d → ℝ) (j : Fin d)
    (g : ℝ) :
    blockMean z L (fun e => w e.tgt - w e.src) j - g =
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
        (((L : ℝ) ^ d)⁻¹ * faceWeight z L e) * (w (e.1 + unit j) - w e.1 - g) := by
  have hsum := sum_faceWeight_eq z hL j
  have hLd : ((L : ℝ) ^ d) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have e1 : ∀ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
      (((L : ℝ) ^ d)⁻¹ * faceWeight z L e) * (w (e.1 + unit j) - w e.1 - g) =
        ((L : ℝ) ^ d)⁻¹ * (faceWeight z L e * (w e.tgt - w e.src)) -
          g * (((L : ℝ) ^ d)⁻¹ * faceWeight z L e) := by
    intro e he
    have h2 : e.2 = j := (Finset.mem_filter.1 he).2
    simp only [Edge.tgt, Edge.src, h2]
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hsum]
  simp only [blockMean]
  field_simp

/-- **Jensen for the face-weighted mean gradient**: if the vertices of a cube of side `L ≥ 1` lie in
a cube `B`, then in direction `j` the squared distance of the block mean of `∇w` to any constant
`g` is at most `L^{-d}` times the sum over `B` of the squared deviations of `w(x + e_j) − w(x)`
from `g`. -/
theorem sq_blockMean_grad_sub_le (z P : Site d) {L LP : ℕ} (hL : 1 ≤ L)
    (hsub : latticeCube z L ⊆ latticeCube P LP) (w : Site d → ℝ) (j : Fin d) (g : ℝ) :
    (blockMean z L (fun e => w e.tgt - w e.src) j - g) ^ 2 ≤
      ((L : ℝ) ^ d)⁻¹ * ∑ x ∈ latticeCube P LP, (w (x + unit j) - w x - g) ^ 2 := by
  have hLd : (0 : ℝ) ≤ ((L : ℝ) ^ d)⁻¹ := by positivity
  rw [blockMean_grad_sub_eq_sum z hL w j g]
  have hw : ∀ e : Edge d, 0 ≤ faceWeight z L e := fun e => by unfold faceWeight; positivity
  refine (sq_sum_mul_le_sum_mul_sq _ _ _ (fun e _ => mul_nonneg hLd (hw e)) ?_).trans ?_
  · have hLd' : ((L : ℝ) ^ d) ≠ 0 := by
      have : (0 : ℝ) < L := by exact_mod_cast hL
      positivity
    rw [← Finset.mul_sum, sum_faceWeight_eq z hL j, inv_mul_cancel₀ hLd']
  · calc ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          ((L : ℝ) ^ d)⁻¹ * faceWeight z L e * (w (e.1 + unit j) - w e.1 - g) ^ 2
        ≤ ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          ((L : ℝ) ^ d)⁻¹ * (w (e.1 + unit j) - w e.1 - g) ^ 2 := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hLd
          exact mul_le_of_le_one_left (sq_nonneg _) (faceWeight_le_one z L e)
      _ = ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j),
          (w (e.1 + unit j) - w e.1 - g) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hLd
          have hinj : Set.InjOn Prod.fst (((edgesOf z L).filter (fun e => e.2 = j) : Finset _) :
              Set (Edge d)) := by
            intro e he e' he' h
            have h1 : e.2 = j := (Finset.mem_filter.1 he).2
            have h2 : e'.2 = j := (Finset.mem_filter.1 he').2
            exact Prod.ext h (h1.trans h2.symm)
          rw [← Finset.sum_image (f := fun x => (w (x + unit j) - w x - g) ^ 2) hinj]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
          intro x hx
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
          have := (Finset.mem_filter.1 he).1
          simp only [edgesOf, Finset.mem_filter, Finset.mem_product] at this
          exact hsub this.1.1

/-- **A child block mean is close to its parent's**: for a cube of side `L ≥ 1` inside a cube of
side `3 L`, the squared difference in direction `j` of the two block means of `∇w` is at most
`4 · 3^d (3L)^{-d}` times the sum over the large cube of the squared deviations of
`w(x + e_j) − w(x)` from any constant `g`. -/
theorem sq_blockMean_grad_sub_blockMean_grad_le (z P : Site d) {L : ℕ} (hL : 1 ≤ L)
    (hsub : latticeCube z L ⊆ latticeCube P (3 * L)) (w : Site d → ℝ) (j : Fin d) (g : ℝ) :
    (blockMean z L (fun e => w e.tgt - w e.src) j -
        blockMean P (3 * L) (fun e => w e.tgt - w e.src) j) ^ 2 ≤
      4 * 3 ^ d * ((((3 * L : ℕ) : ℝ) ^ d)⁻¹ *
        ∑ x ∈ latticeCube P (3 * L), (w (x + unit j) - w x - g) ^ 2) := by
  have ha := sq_blockMean_grad_sub_le z P hL hsub w j g
  have hb := sq_blockMean_grad_sub_le P P (by omega : 1 ≤ 3 * L) (Finset.Subset.refl _) w j g
  set V := ∑ x ∈ latticeCube P (3 * L), (w (x + unit j) - w x - g) ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hrel : ((L : ℝ) ^ d)⁻¹ = 3 ^ d * ((((3 * L : ℕ) : ℝ) ^ d)⁻¹) := by
    push_cast
    rw [mul_pow, mul_inv]
    field_simp
  have hX : 0 ≤ (((3 * L : ℕ) : ℝ) ^ d)⁻¹ * V := by positivity
  have h3 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  rw [hrel] at ha
  set A := blockMean z L (fun e => w e.tgt - w e.src) j with hA
  set B := blockMean P (3 * L) (fun e => w e.tgt - w e.src) j with hB
  set X := (((3 * L : ℕ) : ℝ) ^ d)⁻¹ * V with hXdef
  have ha' : (A - g) ^ 2 ≤ 3 ^ d * X := by rw [hXdef, ← mul_assoc]; simpa [mul_assoc] using ha
  have hb' : (B - g) ^ 2 ≤ X := hb
  have h2 : (A - B) ^ 2 ≤ 2 * (A - g) ^ 2 + 2 * (B - g) ^ 2 := by
    nlinarith [sq_nonneg (A + B - 2 * g)]
  nlinarith

/-- **The discrete Poincaré inequality for the component of a gradient**: there is `C(d)` such that
for every cube, every `w` and every direction `j`, the sum of the squared deviations of
`w(x + e_j) − w(x)` from its average over the cube is at most `C L²` times the sum of the squared
second differences `∇_i∇_j w`. -/
theorem exists_sum_sq_grad_sub_avg_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Site d) (L : ℕ) (w : Site d → ℝ) (j : Fin d),
      ∑ x ∈ latticeCube P L, (w (x + unit j) - w x - ((latticeCube P L).card : ℝ)⁻¹ *
          ∑ y ∈ latticeCube P L, (w (y + unit j) - w y)) ^ 2 ≤
        C * (L : ℝ) ^ 2 * ∑ x ∈ latticeCube P L, ∑ i : Fin d, secondDiff w i j x ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_sum_sq_sub_avg_le (d := d)
  refine ⟨C, hC, fun P L w j => ?_⟩
  refine (h P L (fun x => w (x + unit j) - w x)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ => ?_
  split_ifs
  · refine le_of_eq ?_
    simp only [secondDiff]
    ring
  · exact sq_nonneg _

/-- **One child against its parent**: there is `K(d)` such that if the cube of side `3^k` at `z`
lies in the cube of side `3^{k+1}` at `P`, then in each direction `j` the squared difference of
the block means of `∇w` is at most `K 3^{2k} (3^{k+1})^{-d}` times the sum over the parent of the
squared second differences `∇_i∇_j w`. -/
theorem exists_sq_blockMean_grad_sub_blockMean_grad_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z P : Site d) (k : ℕ),
      latticeCube z (3 ^ k) ⊆ latticeCube P (3 ^ (k + 1)) → ∀ (w : Site d → ℝ) (j : Fin d),
      (blockMean z (3 ^ k) (fun e => w e.tgt - w e.src) j -
          blockMean P (3 ^ (k + 1)) (fun e => w e.tgt - w e.src) j) ^ 2 ≤
        K * (3 : ℝ) ^ (2 * k) * ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
          ∑ x ∈ latticeCube P (3 ^ (k + 1)), ∑ i : Fin d, secondDiff w i j x ^ 2) := by
  obtain ⟨C, hC, hP⟩ := exists_sum_sq_grad_sub_avg_le (d := d)
  refine ⟨36 * 3 ^ d * C, by positivity, fun z P k hsub w j => ?_⟩
  have hk : 3 ^ (k + 1) = 3 * 3 ^ k := pow_succ' 3 k
  have hL : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [hk] at hsub ⊢
  have h1 := sq_blockMean_grad_sub_blockMean_grad_le z P hL hsub w j
    (((latticeCube P (3 * 3 ^ k)).card : ℝ)⁻¹ *
      ∑ y ∈ latticeCube P (3 * 3 ^ k), (w (y + unit j) - w y))
  have h2 := hP P (3 * 3 ^ k) w j
  have hX : 0 ≤ (((3 * 3 ^ k : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  refine h1.trans ?_
  have h3 : (4 : ℝ) * 3 ^ d * ((((3 * 3 ^ k : ℕ) : ℝ) ^ d)⁻¹ * (C * ((3 * 3 ^ k : ℕ) : ℝ) ^ 2 *
      ∑ x ∈ latticeCube P (3 * 3 ^ k), ∑ i : Fin d, secondDiff w i j x ^ 2)) =
      36 * 3 ^ d * C * (3 : ℝ) ^ (2 * k) * ((((3 * 3 ^ k : ℕ) : ℝ) ^ d)⁻¹ *
        ∑ x ∈ latticeCube P (3 * 3 ^ k), ∑ i : Fin d, secondDiff w i j x ^ 2) := by
    push_cast
    ring
  rw [← h3]
  gcongr

/-- A site lies in the subcube of side `3^k` with corner `Z + 3^k y` exactly when each coordinate
lies between the corresponding coordinates of the corner and the corner plus `3^k`. -/
theorem mem_latticeCube_triadicCorner_iff (Z x : Site d) (k : ℕ) (y : Fin d → ℕ) :
    x ∈ latticeCube (triadicCorner Z k y) (3 ^ k) ↔ ∀ i,
      Z i + ((3 ^ k : ℕ) : ℤ) * (y i : ℤ) ≤ x i ∧
        x i ≤ Z i + ((3 ^ k : ℕ) : ℤ) * (y i : ℤ) + ((3 ^ k : ℕ) : ℤ) := by
  rw [mem_latticeCube_iff_coord]
  rfl

/-- The `3^d` children of a cube of side `3^{k+1}` at scale `k` lie in it. -/
theorem latticeCube_triadicCorner_subset (P : Site d) (k : ℕ) {y : Fin d → ℕ}
    (hy : y ∈ triadicIndex d 1) :
    latticeCube (triadicCorner P k y) (3 ^ k) ⊆ latticeCube P (3 ^ (k + 1)) := by
  intro x hx
  rw [mem_latticeCube_triadicCorner_iff] at hx
  rw [mem_latticeCube_iff_coord]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hyi : (y i : ℤ) ≤ 2 := by
    have := mem_triadicIndex.1 hy i
    rw [pow_one] at this
    omega
  have hy0 : (0 : ℤ) ≤ y i := Nat.cast_nonneg _
  have hp : (0 : ℤ) ≤ ((3 ^ k : ℕ) : ℤ) := Nat.cast_nonneg _
  have hpow : ((3 ^ (k + 1) : ℕ) : ℤ) = 3 * ((3 ^ k : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hpow]
  constructor <;> nlinarith

/-- The `3^{d(n-k-1)}` cubes of side `3^{k+1}` at scale `k + 1` lie in `{0, …, 3^n}^d`. -/
theorem latticeCube_triadicCorner_subset_triadicCube {n k : ℕ} (hkn : k < n)
    {y : Fin d → ℕ} (hy : y ∈ triadicIndex d (n - (k + 1))) :
    latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) ⊆ latticeCube 0 (3 ^ n) := by
  intro x hx
  rw [mem_latticeCube_triadicCorner_iff] at hx
  rw [mem_latticeCube_iff_coord]
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have hyi : (y i : ℤ) + 1 ≤ ((3 ^ (n - (k + 1)) : ℕ) : ℤ) := by
    have := mem_triadicIndex.1 hy i
    omega
  have hp : (0 : ℤ) ≤ ((3 ^ (k + 1) : ℕ) : ℤ) := Nat.cast_nonneg _
  have hy0 : (0 : ℤ) ≤ y i := Nat.cast_nonneg _
  have hpow : ((3 ^ n : ℕ) : ℤ) = ((3 ^ (k + 1) : ℕ) : ℤ) * ((3 ^ (n - (k + 1)) : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← pow_add]
    congr 2
    omega
  simp only [Pi.zero_apply, zero_add] at h1 h2 ⊢
  rw [hpow]
  constructor <;> nlinarith

/-- At most two integers `t` satisfy `L t ≤ x ≤ L t + L`. -/
theorem card_filter_mul_le_le_two (L : ℕ) (hL : 0 < L) (x : ℤ) (s : Finset ℕ) :
    (s.filter (fun t : ℕ => (L : ℤ) * t ≤ x ∧ x ≤ (L : ℤ) * t + L)).card ≤ 2 := by
  have hL' : (0 : ℤ) < L := by exact_mod_cast hL
  have hcard : (Finset.Icc (x / (L : ℤ) - 1) (x / (L : ℤ))).card = 2 := by
    rw [Int.card_Icc]
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun t : ℕ => (t : ℤ)) ?_
    (fun a _ b _ h => Nat.cast_injective h)
  intro t ht
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 ht).2
  have hq1 := Int.ediv_mul_le x hL'.ne'
  have hq2 : (t : ℤ) ≤ x / (L : ℤ) := Int.le_ediv_of_mul_le hL' (by linarith)
  simp only [Finset.coe_Icc, Set.mem_Icc]
  refine ⟨?_, hq2⟩
  by_contra hcon
  have hlt := lt_of_not_ge hcon
  nlinarith

/-- Every site lies in at most `2^d` of the cubes of side `3^{k+1}` of the form
`3^{k+1} y + {0, …, 3^{k+1}}^d`: in each coordinate at most two values of `y_i` are possible. -/
theorem card_filter_mem_latticeCube_triadicCorner_le (M k : ℕ) (x : Site d) :
    ((triadicIndex d M).filter
      (fun y => x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)))).card ≤ 2 ^ d := by
  classical
  have hsub : (triadicIndex d M).filter
      (fun y => x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1))) ⊆
      Fintype.piFinset (fun i : Fin d => (Finset.range (3 ^ M)).filter
        (fun t : ℕ => ((3 ^ (k + 1) : ℕ) : ℤ) * t ≤ x i ∧
          x i ≤ ((3 ^ (k + 1) : ℕ) : ℤ) * t + ((3 ^ (k + 1) : ℕ) : ℤ))) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
    rw [mem_latticeCube_triadicCorner_iff] at hy2
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨h1, h2⟩ := hy2 i
    simp only [Pi.zero_apply, zero_add] at h1 h2
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (mem_triadicIndex.1 hy1 i), h1, h2⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_pow_card _ _ 2 fun i _ => ?_).trans ?_
  · exact card_filter_mul_le_le_two _ ((by positivity)) _ _
  · simp

/-- **Overlap of the cubes at scale `k + 1`**: summing a nonnegative function over each cube of side
`3^{k+1}` of `{0, …, 3^n}^d` and then over the cubes costs at most a factor `2^d` over the sum over
`{0, …, 3^n}^d`, since the cubes overlap only on faces. -/
theorem sum_sum_latticeCube_triadicCorner_le {n k : ℕ} (hkn : k < n) (T : Site d → ℝ)
    (hT : ∀ x, 0 ≤ T x) :
    ∑ y ∈ triadicIndex d (n - (k + 1)),
        ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x ≤
      2 ^ d * ∑ x ∈ latticeCube 0 (3 ^ n), T x := by
  classical
  have h1 : ∀ y ∈ triadicIndex d (n - (k + 1)),
      ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x =
        ∑ x ∈ latticeCube 0 (3 ^ n),
          if x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) then T x else 0 := by
    intro y hy
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2
      (latticeCube_triadicCorner_subset_triadicCube hkn hy)]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h2 : ∑ y ∈ triadicIndex d (n - (k + 1)),
      (if x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) then T x else 0) =
      (((triadicIndex d (n - (k + 1))).filter
        (fun y => x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)))).card : ℝ) *
          T x := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h2]
  have hc : ((((triadicIndex d (n - (k + 1))).filter
      (fun y => x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)))).card : ℕ) : ℝ) ≤
        2 ^ d := by
    exact_mod_cast card_filter_mem_latticeCube_triadicCorner_le (n - (k + 1)) k x
  exact mul_le_mul_of_nonneg_right hc (hT x)

/-- The index set `{0, …, 3^j − 1}^d` has `(3^j)^d` elements. -/
theorem card_triadicIndex_eq_pow (j : ℕ) : (triadicIndex d j).card = (3 ^ j) ^ d := by
  simp [triadicIndex, Fintype.card_piFinset]

/-- **Block oscillation of a gradient by its second differences**: there is `C(d)` such that for
every `w`, every
`k < n`, the oscillation of the block means of `∇w` between scales `k` and `k + 1` in `□_n` is at
most `C 3^{2k}` times the average of the squared second differences of `w` over `□_n`
(Jensen for the face-weighted means and the discrete Poincaré inequality on each parent cube, for
the vertex function `x ↦ w(x + e_j) − w(x)` whose differences are the second differences). -/
theorem exists_blockOsc_grad_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n k : ℕ), k < n → ∀ w : Site d → ℝ,
      blockOsc 0 n k (fun e => w e.tgt - w e.src) ≤
        C * (3 : ℝ) ^ (2 * k) * ((((3 : ℝ) ^ n) ^ d)⁻¹ *
          ∑ x ∈ latticeCube 0 (3 ^ n), ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2) := by
  obtain ⟨K, hK, hKb⟩ := exists_sq_blockMean_grad_sub_blockMean_grad_le (d := d)
  refine ⟨K * 2 ^ d, by positivity, fun n k hkn w => ?_⟩
  set T : Site d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, secondDiff w i j x ^ 2 with hT
  have hT0 : ∀ x, 0 ≤ T x := fun x =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : ∀ P : Site d, ∑ j : Fin d, ∑ x ∈ latticeCube P (3 ^ (k + 1)),
      ∑ i : Fin d, secondDiff w i j x ^ 2 = ∑ x ∈ latticeCube P (3 ^ (k + 1)), T x := by
    intro P
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have hLpos : (0 : ℝ) < ((3 ^ (k + 1) : ℕ) : ℝ) ^ d := by positivity
  have hM : ((triadicIndex d 1).card : ℝ) ≠ 0 := by
    rw [card_triadicIndex_eq_pow]
    positivity
  -- one child against its parent
  have hterm : ∀ y ∈ triadicIndex d (n - (k + 1)), ∀ y' ∈ triadicIndex d 1,
      (blockMean (triadicCorner (triadicCorner 0 (k + 1) y) k y') (3 ^ k)
          (fun e => w e.tgt - w e.src) -
        blockMean (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) (fun e => w e.tgt - w e.src)) ⬝ᵥ
      (blockMean (triadicCorner (triadicCorner 0 (k + 1) y) k y') (3 ^ k)
          (fun e => w e.tgt - w e.src) -
        blockMean (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) (fun e => w e.tgt - w e.src)) ≤
      K * (3 : ℝ) ^ (2 * k) * ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
        ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x) := by
    intro y _ y' hy'
    have hsub := latticeCube_triadicCorner_subset (triadicCorner 0 (k + 1) y) k hy'
    calc _ = ∑ j : Fin d, (blockMean (triadicCorner (triadicCorner 0 (k + 1) y) k y') (3 ^ k)
          (fun e => w e.tgt - w e.src) j -
        blockMean (triadicCorner 0 (k + 1) y) (3 ^ (k + 1))
          (fun e => w e.tgt - w e.src) j) ^ 2 := by
          simp only [dotProduct, Pi.sub_apply]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j : Fin d, K * (3 : ℝ) ^ (2 * k) * ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
          ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)),
            ∑ i : Fin d, secondDiff w i j x ^ 2) :=
          Finset.sum_le_sum fun j _ => hKb _ _ k hsub w j
      _ = _ := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hS]
  -- the average over the children of a parent
  have hpar : ∀ y ∈ triadicIndex d (n - (k + 1)),
      ((triadicIndex d 1).card : ℝ)⁻¹ * ∑ y' ∈ triadicIndex d 1,
        (blockMean (triadicCorner (triadicCorner 0 (k + 1) y) k y') (3 ^ k)
            (fun e => w e.tgt - w e.src) -
          blockMean (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) (fun e => w e.tgt - w e.src)) ⬝ᵥ
        (blockMean (triadicCorner (triadicCorner 0 (k + 1) y) k y') (3 ^ k)
            (fun e => w e.tgt - w e.src) -
          blockMean (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)) (fun e => w e.tgt - w e.src)) ≤
      K * (3 : ℝ) ^ (2 * k) * ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
        ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x) := by
    intro y hy
    calc _ ≤ ((triadicIndex d 1).card : ℝ)⁻¹ * ∑ _y' ∈ triadicIndex d 1,
          K * (3 : ℝ) ^ (2 * k) * ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
            ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y' hy' => hterm y hy y' hy')
            (by positivity)
      _ = _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  have hN : ((triadicIndex d (n - (k + 1))).card : ℝ) *
      ((((3 ^ (k + 1) : ℕ) : ℝ)) ^ d) = ((3 : ℝ) ^ n) ^ d := by
    rw [card_triadicIndex_eq_pow]
    push_cast
    rw [← mul_pow, ← pow_add]
    congr 2
    omega
  have hNpos : (0 : ℝ) < ((triadicIndex d (n - (k + 1))).card : ℝ) := by
    rw [card_triadicIndex_eq_pow]
    positivity
  unfold blockOsc
  calc _ ≤ ((triadicIndex d (n - (k + 1))).card : ℝ)⁻¹ *
        ∑ y ∈ triadicIndex d (n - (k + 1)), K * (3 : ℝ) ^ (2 * k) *
          ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
            ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpar) (by positivity)
    _ = ((triadicIndex d (n - (k + 1))).card : ℝ)⁻¹ *
        (K * (3 : ℝ) ^ (2 * k) * (((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹) *
        ∑ y ∈ triadicIndex d (n - (k + 1)),
          ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x := by
        have hsum : ∑ y ∈ triadicIndex d (n - (k + 1)), K * (3 : ℝ) ^ (2 * k) *
            ((((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹ *
              ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x) =
            (K * (3 : ℝ) ^ (2 * k) * (((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹) *
              ∑ y ∈ triadicIndex d (n - (k + 1)),
                ∑ x ∈ latticeCube (triadicCorner 0 (k + 1) y) (3 ^ (k + 1)), T x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
        rw [hsum]
        ring
    _ ≤ ((triadicIndex d (n - (k + 1))).card : ℝ)⁻¹ *
        (K * (3 : ℝ) ^ (2 * k) * (((3 ^ (k + 1) : ℕ) : ℝ) ^ d)⁻¹) *
        (2 ^ d * ∑ x ∈ latticeCube 0 (3 ^ n), T x) :=
        mul_le_mul_of_nonneg_left (sum_sum_latticeCube_triadicCorner_le hkn T hT0) (by positivity)
    _ = _ := by
        rw [← hN, mul_inv]
        ring

end LatticeHC

end
