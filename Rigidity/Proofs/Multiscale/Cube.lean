import Rigidity.Proofs.Multiscale.Defs

/-!
# Triadic cubes, their subcubes and the gradient energy

The lattice points of the triadic cube `3^m z + □_m` are `P + {0, …, 3^m - 1}^d`, with corner
`P_i = 3^m z_i - (3^m - 1)/2`. For `k ≤ m`, the centers `3^k ℤ^d ∩ (3^m z + □_m)` of its subcubes
of scale `k` are the points `3^k j`, `j ∈ 3^{m-k} z + □_{m-k}`, and the subcube centered at `3^k j`
is `3^k j + □_k`, with corner `P + 3^k (j - P')`, `P'` the corner of `3^{m-k} z + □_{m-k}`.

The sum of `|∇u|²` over a finite set is the sum of the squared increments over its edges, and the
mean minimizes the sum of squares of deviations.
-/

namespace Rigidity.Proofs.Multiscale

open LatticeProb.Percolation Rigidity.Percolation

variable {d : ℕ}

/-- The corner `P` of the cube `3^m z + □_m`, `P_i = 3^m z_i - (3^m - 1)/2`. -/
def cubeCorner (m : ℕ) (z : Vertex d) : Vertex d := fun i => 3 ^ m * z i - 3 ^ m / 2

/-- Membership in a triadic cube: `|2 (x_i - 3^m z_i)| < 3^m` for every `i`. -/
theorem mem_cube_iff (m : ℕ) (z x : Vertex d) :
    x ∈ cube m z ↔ ∀ i, |2 * (x i - 3 ^ m * z i)| < 3 ^ m := by
  rw [cube, TriadicCube.mem_toIntegerCube_vertices]
  rfl

/-- Membership in a triadic cube through its corner: `P_i ≤ x_i < P_i + 3^m`. -/
theorem mem_cube_iff_corner (m : ℕ) (z x : Vertex d) :
    x ∈ cube m z ↔ ∀ i, cubeCorner m z i ≤ x i ∧ x i < cubeCorner m z i + 3 ^ m := by
  rw [cube, IntegerCube.mem_vertices]
  simp only [TriadicCube.toIntegerCube, TriadicCube.side, cubeCorner, Nat.cast_pow,
    Nat.cast_ofNat]

/-- The cube `3^m z + □_m` as a product of integer intervals. -/
theorem cube_eq_piFinset (m : ℕ) (z : Vertex d) :
    cube m z = Fintype.piFinset fun i =>
      Finset.Ico (cubeCorner m z i) (cubeCorner m z i + 3 ^ m) := by
  ext x
  rw [mem_cube_iff_corner]
  simp only [Fintype.mem_piFinset, Finset.mem_Ico]

/-- A triadic cube of scale `m` has `(3^m)^d` lattice points. -/
theorem card_cube (m : ℕ) (z : Vertex d) : (cube m z).card = (3 ^ m) ^ d := by
  rw [cube_eq_piFinset, Fintype.card_piFinset]
  have h : ∀ i : Fin d,
      (Finset.Ico (cubeCorner m z i) (cubeCorner m z i + 3 ^ m)).card = 3 ^ m := by
    intro i
    rw [Int.card_Ico, add_sub_cancel_left]
    exact_mod_cast Int.toNat_natCast (3 ^ m)
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A triadic cube is nonempty. -/
theorem card_cube_pos (m : ℕ) (z : Vertex d) : 0 < (cube m z).card := by
  rw [card_cube]
  positivity

/-- The halves of odd powers of three: `3^k ⌊3^l/2⌋ + ⌊3^k/2⌋ = ⌊3^{k+l}/2⌋`. -/
theorem pow_mul_pow_div_two_add (k l : ℕ) :
    (3 : ℤ) ^ k * (3 ^ l / 2) + 3 ^ k / 2 = 3 ^ (k + l) / 2 := by
  have hodd : ∀ n : ℕ, (3 : ℤ) ^ n % 2 = 1 := fun n =>
    Int.odd_iff.mp ((show Odd (3 : ℤ) from ⟨1, by norm_num⟩).pow)
  have ha := Int.emod_add_mul_ediv ((3 : ℤ) ^ k) 2
  have hb := Int.emod_add_mul_ediv ((3 : ℤ) ^ l) 2
  have hab := Int.emod_add_mul_ediv ((3 : ℤ) ^ (k + l)) 2
  rw [hodd] at ha hb hab
  rw [pow_add] at hab ⊢
  have h2 : 2 * ((3 : ℤ) ^ k * (3 ^ l / 2) + 3 ^ k / 2) = 2 * (3 ^ k * 3 ^ l / 2) := by
    linear_combination (3 : ℤ) ^ k * hb + ha - hab
  omega

/-- For `k ≤ m`, `3^k j` lies in `3^m z + □_m` exactly when `j` lies in `3^{m-k} z + □_{m-k}`. -/
theorem pow_mul_mem_cube_iff {k m : ℕ} (hk : k ≤ m) (z j : Vertex d) :
    (fun i => 3 ^ k * j i) ∈ cube m z ↔ j ∈ cube (m - k) z := by
  rw [mem_cube_iff, mem_cube_iff]
  have hm : (3 : ℤ) ^ m = 3 ^ k * 3 ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have hpos : (0 : ℤ) < 3 ^ k := by positivity
  refine forall_congr' fun i => ?_
  rw [hm, show 2 * (3 ^ k * j i - 3 ^ k * 3 ^ (m - k) * z i) =
      3 ^ k * (2 * (j i - 3 ^ (m - k) * z i)) by ring, abs_mul, abs_of_pos hpos]
  exact ⟨fun h => lt_of_mul_lt_mul_left h hpos.le, fun h => mul_lt_mul_of_pos_left h hpos⟩

/-- Multiplication by `3^k`, as an embedding of `ℤ^d`. -/
def powMulEmb (k : ℕ) : Vertex d ↪ Vertex d where
  toFun j i := 3 ^ k * j i
  inj' a b h := by
    funext i
    have hi := congrFun h i
    simp only at hi
    exact mul_left_cancel₀ (pow_ne_zero k (by norm_num)) hi

/-- The centers of the subcubes of scale `k ≤ m` are `3^k (3^{m-k} z + □_{m-k})`. -/
theorem centers_eq_map {k m : ℕ} (hk : k ≤ m) (z : Vertex d) :
    centers m z k = (cube (m - k) z).map (powMulEmb k) := by
  ext y
  simp only [centers, Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨hy, hdvd⟩
    refine ⟨fun i => y i / 3 ^ k, ?_, ?_⟩
    · rw [← pow_mul_mem_cube_iff hk]
      convert hy using 1
      funext i
      exact Int.mul_ediv_cancel' (hdvd i)
    · funext i
      exact Int.mul_ediv_cancel' (hdvd i)
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(pow_mul_mem_cube_iff hk z j).2 hj, fun i => ⟨j i, rfl⟩⟩

/-- The subcube centered at `3^k j` is the triadic cube of scale `k` and index `j`. -/
theorem subcube_powMulEmb (k : ℕ) (j : Vertex d) : subcube k (powMulEmb k j) = cube k j := by
  have h : (fun i => powMulEmb k j i / 3 ^ k) = j := by
    funext i
    exact Int.mul_ediv_cancel_left (j i) (pow_ne_zero k (by norm_num))
  rw [subcube, h]

/-- A sum over the subcubes of scale `k ≤ m`, indexed by their centers, is a sum over the indices
`j ∈ 3^{m-k} z + □_{m-k}`. -/
theorem sum_centers {β : Type*} [AddCommMonoid β] {k m : ℕ} (hk : k ≤ m) (z : Vertex d)
    (f : Finset (Vertex d) → β) :
    ∑ y ∈ centers m z k, f (subcube k y) = ∑ j ∈ cube (m - k) z, f (cube k j) := by
  rw [centers_eq_map hk, Finset.sum_map]
  exact Finset.sum_congr rfl fun j _ => by rw [subcube_powMulEmb]

/-- There are `(3^{m-k})^d` subcubes of scale `k ≤ m`. -/
theorem card_centers {k m : ℕ} (hk : k ≤ m) (z : Vertex d) :
    (centers m z k).card = (3 ^ (m - k)) ^ d := by
  rw [centers_eq_map hk, Finset.card_map, card_cube]

/-- The corner of the subcube of index `j` is `P + 3^k (j - P')`. -/
theorem cubeCorner_subcube {k m : ℕ} (hk : k ≤ m) (z j : Vertex d) (i : Fin d) :
    cubeCorner k j i = cubeCorner m z i + 3 ^ k * (j i - cubeCorner (m - k) z i) := by
  have h := pow_mul_pow_div_two_add k (m - k)
  rw [Nat.add_sub_cancel' hk] at h
  have hm : (3 : ℤ) ^ m = 3 ^ k * 3 ^ (m - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  simp only [cubeCorner]
  rw [← h, hm]
  ring

/-- The mean square of the normalized spatial averages, as a sum over subcube indices. -/
theorem subcubeGradMeanSq_eq {k m : ℕ} (hk : k ≤ m) (z : Vertex d) (u : Vertex d → ℝ) :
    subcubeGradMeanSq m z k u = (((3 : ℝ) ^ (m - k)) ^ d)⁻¹ * ∑ j ∈ cube (m - k) z,
      ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum (cube k j) u i) ^ 2 := by
  rw [subcubeGradMeanSq, card_centers hk,
    sum_centers hk z fun B => ∑ i : Fin d, ((((3 : ℝ) ^ k) ^ d)⁻¹ * gradSum B u i) ^ 2]
  push_cast
  rfl

/-- The sum of the squared increments over the edges `(x, x + e_i)` of `A`. -/
noncomputable def edgeEnergy (A : Finset (Vertex d)) (u : Vertex d → ℝ) : ℝ :=
  ∑ x ∈ A, ∑ i : Fin d, if x + unitVec i ∈ A then (u (x + unitVec i) - u x) ^ 2 else 0

/-- The backward increments of `A` are its forward increments. -/
theorem sum_ite_sub_mem_eq (A : Finset (Vertex d)) (e : Vertex d) (f : Vertex d → Vertex d → ℝ) :
    ∑ x ∈ A, (if x - e ∈ A then f (x - e) x else 0) =
      ∑ x ∈ A, (if x + e ∈ A then f x (x + e) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun x => x - e) (fun x => x + e) (fun x hx => ?_) (fun x hx => ?_)
    (fun x _ => by simp) (fun x _ => by simp) (fun x _ => by simp)
  · simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.2, by simpa using hx.1⟩
  · simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.2, by simpa using hx.1⟩

/-- `Σ_{x ∈ A} |∇u|²(x)` is the sum of the squared increments over the edges of `A`. -/
theorem sum_gradNormSq (A : Finset (Vertex d)) (u : Vertex d → ℝ) :
    ∑ x ∈ A, gradNormSq A u x = edgeEnergy A u := by
  have h : ∀ i : Fin d, ∑ x ∈ A,
      ((if x + unitVec i ∈ A then (u x - u (x + unitVec i)) ^ 2 else 0) +
        (if x - unitVec i ∈ A then (u x - u (x - unitVec i)) ^ 2 else 0)) =
      2 * ∑ x ∈ A, (if x + unitVec i ∈ A then (u (x + unitVec i) - u x) ^ 2 else 0) := by
    intro i
    rw [Finset.sum_add_distrib, sum_ite_sub_mem_eq A (unitVec i) fun a b => (u b - u a) ^ 2,
      two_mul]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
  simp only [gradNormSq, edgeEnergy]
  conv_lhs => rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  ring

/-- The mean minimizes the sum of squared deviations: `Σ (u - (u)_A)² ≤ Σ (u - c)²`. -/
theorem sum_sq_sub_finsetMean_le (A : Finset (Vertex d)) (u : Vertex d → ℝ) (c : ℝ) :
    ∑ x ∈ A, (u x - finsetMean A u) ^ 2 ≤ ∑ x ∈ A, (u x - c) ^ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  set μ := finsetMean A u with hμ
  have hcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hzero : ∑ x ∈ A, (u x - μ) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hμ, finsetMean,
      mul_inv_cancel_left₀ hcard, sub_self]
  have hexp : ∑ x ∈ A, (u x - c) ^ 2 =
      ∑ x ∈ A, (u x - μ) ^ 2 + 2 * (μ - c) * ∑ x ∈ A, (u x - μ) + A.card * (μ - c) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show (A.card : ℝ) * (μ - c) ^ 2 = ∑ _x ∈ A, (μ - c) ^ 2 by
      rw [Finset.sum_const, nsmul_eq_mul]]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hexp, hzero]
  nlinarith [sq_nonneg (μ - c), show (0 : ℝ) ≤ A.card from Nat.cast_nonneg _]

end Rigidity.Proofs.Multiscale
