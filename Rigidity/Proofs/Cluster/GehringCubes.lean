import Rigidity.Proofs.Cluster.Caccioppoli
import Mathlib.Data.Int.Interval

/-!
# Triadic cubes as sup-norm balls

The triadic cube of scale `k` containing a lattice point `x` is the sup-norm ball of radius
`h_k = (3^k - 1)/2` around the point `3^k idx_k(x)`, where `idx_k(x)_i = ⌊(x_i + h_k)/3^k⌋`; these
are the cubes `Rigidity.Percolation.TriadicCube` of scale `k`, whose parent has the index
`⌊(idx_k(x) + 1)/3⌋`. The enlargement `enl j k x` is the ball of radius `h_{k+j}` around the same
center, the cube of side `3^j` times larger with the same center (`j = 1`: the cube `3□`).

We record membership, nesting, cardinalities, the position of the enlargements of nested cubes,
the covering property used in Vitali's selection, the fact that an enlargement is a union of cubes
of the same scale, and the averaging identity over a partition into finite sets.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators

variable {d : ℕ}

/-- `h_k = (3^k - 1)/2`, defined by `h_0 = 0` and `h_{k+1} = 3 h_k + 1`. -/
def halfSide : ℕ → ℤ
  | 0 => 0
  | k + 1 => 3 * halfSide k + 1

theorem two_mul_halfSide_add_one (k : ℕ) : 2 * halfSide k + 1 = 3 ^ k := by
  induction k with
  | zero => simp [halfSide]
  | succ k ih =>
      rw [halfSide, pow_succ, ← ih]
      ring

theorem halfSide_nonneg (k : ℕ) : 0 ≤ halfSide k := by
  induction k with
  | zero => simp [halfSide]
  | succ k ih =>
      rw [halfSide]
      linarith

theorem halfSide_add (k j : ℕ) : halfSide (k + j) = 3 ^ k * halfSide j + halfSide k := by
  have h1 := two_mul_halfSide_add_one (k + j)
  have h2 := two_mul_halfSide_add_one k
  have h3 := two_mul_halfSide_add_one j
  rw [pow_add, ← h2, ← h3] at h1
  have key : 2 * halfSide (k + j) = 2 * ((2 * halfSide k + 1) * halfSide j + halfSide k) := by
    linear_combination h1
  rw [← h2]
  exact mul_left_cancel₀ two_ne_zero key

theorem halfSide_mono {k k' : ℕ} (h : k ≤ k') : halfSide k ≤ halfSide k' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [halfSide_add]
  have := halfSide_nonneg j
  have : (0 : ℤ) ≤ 3 ^ k := by positivity
  nlinarith

/-- The enlargement `h_{k+j} - h_k` grows with the scale. -/
theorem halfSide_add_sub_le {k k' : ℕ} (h : k ≤ k') (j : ℕ) :
    halfSide (k + j) - halfSide k ≤ halfSide (k' + j) - halfSide k' := by
  rw [halfSide_add, halfSide_add]
  have h1 : (3 : ℤ) ^ k ≤ 3 ^ k' := pow_le_pow_right₀ (by norm_num) h
  have := halfSide_nonneg j
  nlinarith

/-- The sup-norm ball of radius `R` around `c`. -/
noncomputable def box (c : Vertex d) (R : ℤ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (c i - R) (c i + R)

theorem mem_box {c x : Vertex d} {R : ℤ} : x ∈ box c R ↔ ∀ i, |x i - c i| ≤ R := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem box_mono (c : Vertex d) {R R' : ℤ} (h : R ≤ R') : box c R ⊆ box c R' := by
  intro x hx
  rw [mem_box] at hx ⊢
  exact fun i => (hx i).trans h

theorem card_box (c : Vertex d) {R : ℤ} (hR : 0 ≤ R) :
    ((box c R).card : ℝ) = ((2 * R + 1 : ℤ) : ℝ) ^ d := by
  have h1 : ∀ i, (Finset.Icc (c i - R) (c i + R)).card = (2 * R + 1).toNat := fun i => by
    rw [Int.card_Icc]
    congr 1
    ring
  rw [box, Fintype.card_piFinset]
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith)]

theorem ediv_eq_of_le_of_lt {a b q : ℤ} (hb : 0 < b) (h1 : b * q ≤ a) (h2 : a < b * q + b) :
    a / b = q :=
  ((Int.ediv_emod_unique hb).2 ⟨(by ring : a - b * q + b * q = a), by linarith, by linarith⟩).1

/-- Division by `3^k` rounds to the nearest multiple: `|a - 3^k b| ≤ h_k` iff
`⌊(a + h_k)/3^k⌋ = b`. -/
theorem abs_sub_le_halfSide_iff (k : ℕ) (a b : ℤ) :
    |a - 3 ^ k * b| ≤ halfSide k ↔ (a + halfSide k) / 3 ^ k = b := by
  have hs : (0 : ℤ) < 3 ^ k := by positivity
  have h2 := two_mul_halfSide_add_one k
  constructor
  · intro h
    rw [abs_le] at h
    exact ediv_eq_of_le_of_lt hs (by linarith) (by linarith)
  · rintro rfl
    set s : ℤ := 3 ^ k with hsdef
    set q := (a + halfSide k) / s with hqdef
    have h3 : q * s ≤ a + halfSide k := Int.ediv_mul_le _ hs.ne'
    have h4 : a + halfSide k < (q + 1) * s := Int.lt_ediv_add_one_mul_self _ hs
    have h5 : (q + 1) * s = q * s + s := by ring
    rw [h5] at h4
    rw [abs_le, mul_comm s q]
    generalize q * s = m at h3 h4 ⊢
    constructor <;> omega

/-- The index of the triadic cube of scale `k` containing `x`. -/
def idx (k : ℕ) (x : Vertex d) : Vertex d := fun i => (x i + halfSide k) / 3 ^ k

/-- The center `3^k idx_k(x)` of the triadic cube of scale `k` containing `x`. -/
def center (k : ℕ) (x : Vertex d) : Vertex d := fun i => 3 ^ k * idx k x i

/-- The triadic cube of scale `k` containing `x`. -/
noncomputable def cube (k : ℕ) (x : Vertex d) : Finset (Vertex d) := box (center k x) (halfSide k)

/-- The enlargement of side `3^{k+j}` of the triadic cube of scale `k` containing `x`, with the same
center. -/
noncomputable def enl (j k : ℕ) (x : Vertex d) : Finset (Vertex d) :=
  box (center k x) (halfSide (k + j))

theorem mem_cube_iff {k : ℕ} {x y : Vertex d} : y ∈ cube k x ↔ idx k y = idx k x := by
  rw [cube, mem_box, funext_iff]
  exact forall_congr' fun i => abs_sub_le_halfSide_iff k (y i) (idx k x i)

theorem mem_cube_self (k : ℕ) (x : Vertex d) : x ∈ cube k x := mem_cube_iff.mpr rfl

theorem center_eq_of_mem {k : ℕ} {x y : Vertex d} (h : y ∈ cube k x) : center k y = center k x := by
  unfold center
  rw [mem_cube_iff.mp h]

theorem cube_eq_of_mem {k : ℕ} {x y : Vertex d} (h : y ∈ cube k x) : cube k y = cube k x := by
  unfold cube
  rw [center_eq_of_mem h]

theorem enl_eq_of_mem {j k : ℕ} {x y : Vertex d} (h : y ∈ cube k x) : enl j k y = enl j k x := by
  unfold enl
  rw [center_eq_of_mem h]

theorem mem_cube_comm {k : ℕ} {x y : Vertex d} : y ∈ cube k x ↔ x ∈ cube k y := by
  rw [mem_cube_iff, mem_cube_iff, eq_comm]

/-- The index of the parent: `idx_{k+1}(x) = ⌊(idx_k(x) + 1)/3⌋`. -/
theorem idx_succ (k : ℕ) (x : Vertex d) (i : Fin d) : idx (k + 1) x i = (idx k x i + 1) / 3 := by
  have hs : (0 : ℤ) < 3 ^ k := by positivity
  have h2 := two_mul_halfSide_add_one k
  set q := idx k x i with hq
  set p := (q + 1) / 3 with hp
  have hq1 : q * 3 ^ k ≤ x i + halfSide k := Int.ediv_mul_le _ hs.ne'
  have hq2 : x i + halfSide k < (q + 1) * 3 ^ k := Int.lt_ediv_add_one_mul_self _ hs
  have hp1 : p * 3 ≤ q + 1 := Int.ediv_mul_le _ (by norm_num)
  have hp2 : q + 1 < (p + 1) * 3 := Int.lt_ediv_add_one_mul_self _ (by norm_num)
  have hp1' : (3 * p - 1) * 3 ^ k ≤ q * 3 ^ k := mul_le_mul_of_nonneg_right (by linarith) hs.le
  have hp2' : (q + 1) * 3 ^ k ≤ (3 * p + 2) * 3 ^ k :=
    mul_le_mul_of_nonneg_right (by linarith) hs.le
  unfold idx
  rw [halfSide, pow_succ]
  refine ediv_eq_of_le_of_lt (by positivity) ?_ ?_ <;> nlinarith

theorem cube_subset_succ (k : ℕ) (x : Vertex d) : cube k x ⊆ cube (k + 1) x := by
  intro y hy
  rw [mem_cube_iff] at hy ⊢
  funext i
  rw [idx_succ, idx_succ, hy]

theorem cube_mono {k k' : ℕ} (h : k ≤ k') (x : Vertex d) : cube k x ⊆ cube k' x := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (cube_subset_succ _ x)

theorem cube_eq_of_mem_of_le {k k' : ℕ} (h : k ≤ k') {x y : Vertex d} (hy : y ∈ cube k x) :
    cube k' y = cube k' x :=
  cube_eq_of_mem (cube_mono h x hy)

theorem card_cube (k : ℕ) (x : Vertex d) : ((cube k x).card : ℝ) = ((3 : ℝ) ^ k) ^ d := by
  rw [cube, card_box _ (halfSide_nonneg k), two_mul_halfSide_add_one]
  norm_cast

theorem card_enl (j k : ℕ) (x : Vertex d) : ((enl j k x).card : ℝ) = ((3 : ℝ) ^ (k + j)) ^ d := by
  rw [enl, card_box _ (halfSide_nonneg _), two_mul_halfSide_add_one]
  norm_cast

theorem card_enl_eq (j k : ℕ) (x : Vertex d) :
    ((enl j k x).card : ℝ) = ((3 : ℝ) ^ j) ^ d * (cube k x).card := by
  rw [card_enl, card_cube, pow_add, mul_pow, mul_comm]

theorem card_cube_pos (k : ℕ) (x : Vertex d) : (0 : ℝ) < (cube k x).card := by
  rw [card_cube]
  positivity

theorem card_cube_succ (k : ℕ) (x : Vertex d) :
    ((cube (k + 1) x).card : ℝ) = (3 : ℝ) ^ d * (cube k x).card := by
  rw [card_cube, card_cube, pow_succ, mul_pow, mul_comm]

theorem cube_subset_enl (j k : ℕ) (x : Vertex d) : cube k x ⊆ enl j k x :=
  box_mono _ (halfSide_mono (Nat.le_add_right k j))

/-- The centers of nested cubes are at distance at most `h_{k'} - h_k`. -/
theorem abs_center_sub_center_le {k k' : ℕ} (h : k ≤ k') (x : Vertex d) (i : Fin d) :
    |center k x i - center k' x i| ≤ halfSide k' - halfSide k := by
  have hplus : (fun l => center k x l + halfSide k) ∈ cube k' x := by
    refine cube_mono h x ?_
    rw [cube, mem_box]
    intro l
    simp [abs_of_nonneg (halfSide_nonneg k)]
  have hminus : (fun l => center k x l - halfSide k) ∈ cube k' x := by
    refine cube_mono h x ?_
    rw [cube, mem_box]
    intro l
    simp [abs_of_nonneg (halfSide_nonneg k)]
  rw [cube, mem_box] at hplus hminus
  have h1 := abs_le.mp (hplus i)
  have h2 := abs_le.mp (hminus i)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The enlargement of a subcube lies in the enlargement of the cube. -/
theorem enl_subset_enl {k k' : ℕ} (h : k ≤ k') (j : ℕ) (x : Vertex d) :
    enl j k x ⊆ enl j k' x := by
  intro y hy
  rw [enl, mem_box] at hy ⊢
  intro i
  have h1 := hy i
  have h2 := abs_center_sub_center_le h x i
  have h3 := halfSide_add_sub_le h j
  calc |y i - center k' x i| ≤ |y i - center k x i| + |center k x i - center k' x i| := by
        rw [show y i - center k' x i = (y i - center k x i) + (center k x i - center k' x i) by
          ring]
        exact abs_add_le _ _
    _ ≤ halfSide (k' + j) := by linarith

/-- **Vitali's covering property.** If the enlargements of two cubes meet and the first has the
smaller scale, the first cube lies in the next enlargement of the second. -/
theorem cube_subset_enl_succ_of_inter {j k k' : ℕ} {x x' : Vertex d} (hk : k ≤ k')
    (hne : (enl j k x ∩ enl j k' x').Nonempty) : cube k x ⊆ enl (j + 1) k' x' := by
  obtain ⟨y, hy⟩ := hne
  rw [Finset.mem_inter, enl, enl, mem_box, mem_box] at hy
  intro z hz
  rw [cube, mem_box] at hz
  rw [enl, mem_box]
  intro i
  have h1 := hz i
  have h2 := hy.1 i
  have h3 := hy.2 i
  have h4 : halfSide k ≤ halfSide (k' + j) := halfSide_mono (by omega)
  have h5 : halfSide (k + j) ≤ halfSide (k' + j) := halfSide_mono (by omega)
  have h6 : halfSide (k' + (j + 1)) = 3 * halfSide (k' + j) + 1 := by
    rw [← add_assoc, halfSide]
  rw [h6]
  calc |z i - center k' x' i|
      ≤ |z i - center k x i| + |center k x i - y i| + |y i - center k' x' i| := by
        rw [show z i - center k' x' i =
          (z i - center k x i) + (center k x i - y i) + (y i - center k' x' i) by ring]
        have e1 := abs_add_le (z i - center k x i) (center k x i - y i)
        have e2 := abs_add_le (z i - center k x i + (center k x i - y i)) (y i - center k' x' i)
        linarith
    _ ≤ 3 * halfSide (k' + j) + 1 := by
        rw [abs_sub_comm (center k x i)]
        linarith

/-- An enlargement is a union of cubes of its scale. -/
theorem cube_subset_enl_of_mem {j k : ℕ} {x y : Vertex d} (hy : y ∈ enl j k x) :
    cube k y ⊆ enl j k x := by
  have hs : (0 : ℤ) < 3 ^ k := by positivity
  have h2 := two_mul_halfSide_add_one k
  have hyc : y ∈ cube k y := mem_cube_self k y
  intro z hz
  rw [enl, mem_box] at hy ⊢
  rw [cube, mem_box] at hyc hz
  intro i
  have h4 : center k y i - center k x i = 3 ^ k * (idx k y i - idx k x i) := by
    unfold center
    ring
  have hidx : |idx k y i - idx k x i| ≤ halfSide j := by
    have h3 : |center k y i - center k x i| ≤ halfSide (k + j) + halfSide k := by
      calc |center k y i - center k x i| ≤ |center k y i - y i| + |y i - center k x i| := by
            rw [show center k y i - center k x i = (center k y i - y i) + (y i - center k x i) by
              ring]
            exact abs_add_le _ _
        _ ≤ halfSide (k + j) + halfSide k := by
            rw [abs_sub_comm]
            linarith [hyc i, hy i]
    rw [h4, abs_mul, abs_of_pos hs, halfSide_add] at h3
    have h5 : 3 ^ k * |idx k y i - idx k x i| < 3 ^ k * (halfSide j + 1) := by linarith
    exact Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_left h5 hs.le)
  have h7 : |center k y i - center k x i| ≤ 3 ^ k * halfSide j := by
    rw [h4, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hidx hs.le
  rw [halfSide_add]
  calc |z i - center k x i| ≤ |z i - center k y i| + |center k y i - center k x i| := by
        rw [show z i - center k x i = (z i - center k y i) + (center k y i - center k x i) by ring]
        exact abs_add_le _ _
    _ ≤ 3 ^ k * halfSide j + halfSide k := by linarith [hz i]

/-- An enlargement lies in the ball of radius `h_k + h_{k+j}` around any point of the cube. -/
theorem enl_subset_box (j k : ℕ) (x : Vertex d) :
    enl j k x ⊆ box x (halfSide k + halfSide (k + j)) := by
  have hx : x ∈ cube k x := mem_cube_self k x
  rw [cube, mem_box] at hx
  intro y hy
  rw [enl, mem_box] at hy
  rw [mem_box]
  intro i
  calc |y i - x i| ≤ |y i - center k x i| + |center k x i - x i| := by
        rw [show y i - x i = (y i - center k x i) + (center k x i - x i) by ring]
        exact abs_add_le _ _
    _ ≤ halfSide k + halfSide (k + j) := by
        rw [abs_sub_comm (center k x i)]
        linarith [hx i, hy i]

/-- **Averaging over a partition.** If the finite sets `Q y`, `y ∈ Y`, contain `y`, lie in `Y` and
coincide for the points of each of them, the sum over `Y` equals the sum of the averages over
them. -/
theorem sum_eq_sum_avg {V : Type*} [DecidableEq V] {Y : Finset V} (Q : V → Finset V)
    (hmem : ∀ y ∈ Y, y ∈ Q y) (hsub : ∀ y ∈ Y, Q y ⊆ Y) (heq : ∀ y ∈ Y, ∀ y' ∈ Q y, Q y' = Q y)
    (F : V → ℝ) : ∑ y ∈ Y, F y = ∑ y ∈ Y, (∑ z ∈ Q y, F z) / (Q y).card := by
  have hswap : ∑ y ∈ Y, ∑ z ∈ Q y, F z / (Q y).card =
      ∑ z ∈ Y, ∑ y ∈ Q z, F z / (Q y).card := by
    refine Finset.sum_comm' fun y z => ?_
    constructor
    · rintro ⟨hy, hz⟩
      have h1 := heq y hy z hz
      refine ⟨?_, hsub y hy hz⟩
      rw [h1]
      exact hmem y hy
    · rintro ⟨hy, hz⟩
      have h1 := heq z hz y hy
      refine ⟨hsub z hz hy, ?_⟩
      rw [h1]
      exact hmem z hz
  have hinner : ∀ z ∈ Y, ∑ y ∈ Q z, F z / (Q y).card = F z := by
    intro z hz
    have h1 : ∀ y ∈ Q z, F z / (Q y).card = F z / (Q z).card := fun y hy => by
      rw [heq z hz y hy]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have hpos : ((Q z).card : ℝ) ≠ 0 := by
      have := Finset.card_pos.mpr ⟨z, hmem z hz⟩
      positivity
    field_simp
  calc ∑ y ∈ Y, F y = ∑ z ∈ Y, ∑ y ∈ Q z, F z / (Q y).card :=
        (Finset.sum_congr rfl hinner).symm
    _ = ∑ y ∈ Y, ∑ z ∈ Q y, F z / (Q y).card := hswap.symm
    _ = ∑ y ∈ Y, (∑ z ∈ Q y, F z) / (Q y).card :=
        Finset.sum_congr rfl fun y _ => (Finset.sum_div _ _ _).symm

/-- The sum over a union of cubes of scale `k` equals the sum of the averages over these cubes. -/
theorem sum_eq_sum_cube_avg {T : Finset (Vertex d)} {k : ℕ}
    (hT : ∀ y ∈ T, cube k y ⊆ T) (F : Vertex d → ℝ) :
    ∑ y ∈ T, F y = ∑ y ∈ T, (∑ z ∈ cube k y, F z) / (cube k y).card :=
  sum_eq_sum_avg (cube k) (fun y _ => mem_cube_self k y) hT
    (fun _ _ _ hy' => cube_eq_of_mem hy') F

end Rigidity.Proofs.Cluster
