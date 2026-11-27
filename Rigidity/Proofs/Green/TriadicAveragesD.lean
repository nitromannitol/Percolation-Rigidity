import Rigidity.Proofs.Green.DarioGuTriadicAverages

/-!
# Averages on the triadic cubes of `ℤ^d`

The `d`-dimensional form of `DarioGuTriadicAverages.lean`: the triadic cubes `□_k(3^k j)`
(`triadicCubeFinset d k j`) partition `ℤ^d` at each scale, `cubeIndexD k x` is the index of the cube
of scale `k` containing `x`, `cubeMeanD f k j` is the average of `f` on it, and on a finite union
`S` of cubes of scale `K` (`IsCubeUnionD K S`)

`|Σ_{x ∈ S} f(x) u(x)| ≤ Σ_{x ∈ S} |A_K f(x)| |A_K u(x)|
  + Σ_{k < K} Σ_{x ∈ S} |A_k f(x) - A_{k+1} f(x)| |A_k u(x)|`

(`abs_sum_mul_le_multiscaleD`), the multiscale decomposition of the proof of Proposition A.7 of
Dario–Gu.
-/

open Finset LatticeProb.Percolation Rigidity.Proofs.S2

namespace Rigidity.Green

variable {d : ℕ}

/-! ### The cube containing a vertex -/

/-- The index `j` of the triadic cube `□_k(3^k j)` of scale `k` containing `x`: `jᵢ` is the integer
nearest to `xᵢ / 3^k`. -/
def cubeIndexD (k : ℕ) (x : Vertex d) : Vertex d :=
  fun i => (x i + ((3 : ℤ) ^ k - 1) / 2) / 3 ^ k

theorem mem_triadicCubeFinset_iffD (k : ℕ) (x j : Vertex d) :
    x ∈ triadicCubeFinset d k j ↔ cubeIndexD k x = j := by
  have hQ := three_pow_eq_two_mul_half_add_one k
  have hP : (0 : ℤ) < 3 ^ k := by positivity
  simp only [triadicCubeFinset, Fintype.mem_piFinset, Finset.mem_Icc, funext_iff, cubeIndexD]
  exact forall_congr' fun i => (ediv_eq_iff_of_two_mul_add_one hQ hP).symm

theorem cubeIndex_memD (k : ℕ) (x : Vertex d) : x ∈ triadicCubeFinset d k (cubeIndexD k x) :=
  (mem_triadicCubeFinset_iffD k x _).2 rfl

theorem cubeIndex_zeroD (x : Vertex d) : cubeIndexD 0 x = x := by
  funext i
  simp [cubeIndexD]

/-- The cubes of scale `k` refine those of scale `k + m`. -/
theorem cubeIndex_addD (k m : ℕ) (x : Vertex d) :
    cubeIndexD (k + m) x = cubeIndexD m (cubeIndexD k x) := by
  funext i
  simp only [cubeIndexD]
  obtain ⟨a, ha⟩ : ∃ a, (3 : ℤ) ^ k = 2 * a + 1 := ⟨_, three_pow_eq_two_mul_half_add_one k⟩
  obtain ⟨b, hb⟩ : ∃ b, (3 : ℤ) ^ m = 2 * b + 1 := ⟨_, three_pow_eq_two_mul_half_add_one m⟩
  have hk : ((3 : ℤ) ^ k - 1) / 2 = a := by rw [ha]; omega
  have hm : ((3 : ℤ) ^ m - 1) / 2 = b := by rw [hb]; omega
  have hkm : ((3 : ℤ) ^ (k + m) - 1) / 2 = a + b * 3 ^ k := by
    rw [pow_add, ha, hb, show (2 * a + 1) * (2 * b + 1) - 1 = 2 * (a + b * (2 * a + 1)) by ring,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  have hP : (3 : ℤ) ^ k ≠ 0 := by positivity
  rw [hk, hm, hkm, ← Int.add_mul_ediv_right _ _ hP, Int.ediv_ediv_of_nonneg (by positivity),
    pow_add, add_assoc]

theorem cubeIndex_succD (k : ℕ) (x : Vertex d) :
    cubeIndexD (k + 1) x = cubeIndexD 1 (cubeIndexD k x) :=
  cubeIndex_addD k 1 x

theorem card_triadicCubeFinsetD (k : ℕ) (j : Vertex d) :
    ((triadicCubeFinset d k j).card : ℝ) = (3 ^ d) ^ k := by
  rw [card_triadicCubeFinset, pow_mul]
  norm_num

/-- `|xᵢ - 3^k cubeIndexD k xᵢ| ≤ (3^k - 1)/2`. -/
theorem abs_sub_mul_cubeIndex_leD (k : ℕ) (x : Vertex d) (i : Fin d) :
    |x i - 3 ^ k * cubeIndexD k x i| ≤ ((3 : ℤ) ^ k - 1) / 2 := by
  have h := cubeIndex_memD k x
  simp only [triadicCubeFinset, Fintype.mem_piFinset, Finset.mem_Icc] at h
  rw [abs_le]
  constructor <;> linarith [(h i).1, (h i).2]

/-! ### Unions of cubes and regrouping -/

/-- `S` is a union of cubes of scale `k`. -/
def IsCubeUnionD (k : ℕ) (S : Finset (Vertex d)) : Prop :=
  ∀ x x', cubeIndexD k x = cubeIndexD k x' → x ∈ S → x' ∈ S

theorem IsCubeUnionD.mono {k K : ℕ} (hkK : k ≤ K) {S : Finset (Vertex d)} (hS : IsCubeUnionD K S) :
    IsCubeUnionD k S := by
  intro x x' h hx
  refine hS x x' ?_ hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkK
  rw [cubeIndex_addD, cubeIndex_addD, h]

/-- The union of the cubes of scale `K` with index in `J`. -/
theorem isCubeUnion_biUnionD (K : ℕ) (J : Finset (Vertex d)) :
    IsCubeUnionD K (J.biUnion (triadicCubeFinset d K)) := by
  intro x x' h hx
  simp only [Finset.mem_biUnion, mem_triadicCubeFinset_iffD] at hx ⊢
  obtain ⟨j, hj, hxj⟩ := hx
  exact ⟨j, hj, h ▸ hxj⟩

theorem filter_cubeIndex_eqD {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnionD k S) {j : Vertex d}
    (hj : j ∈ S.image (cubeIndexD k)) :
    S.filter (fun x => cubeIndexD k x = j) = triadicCubeFinset d k j := by
  ext x
  simp only [Finset.mem_filter, mem_triadicCubeFinset_iffD]
  constructor
  · exact fun h => h.2
  · intro hx
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hj
    exact ⟨hS x₀ x hx.symm hx₀, hx⟩

/-- Regrouping a sum over a union of cubes of scale `k` cube by cube. -/
theorem sum_comp_cubeIndex_mulD {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnionD k S)
    (F u : Vertex d → ℝ) :
    ∑ x ∈ S, F (cubeIndexD k x) * u x =
      ∑ j ∈ S.image (cubeIndexD k), F j * ∑ x ∈ triadicCubeFinset d k j, u x := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeIndexD k) hx)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [filter_cubeIndex_eqD hS hj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(mem_triadicCubeFinset_iffD k x j).1 hx]

/-! ### Averages on cubes -/

/-- The average of `f` on the triadic cube `□_k(3^k j)`. -/
noncomputable def cubeMeanD (f : Vertex d → ℝ) (k : ℕ) (j : Vertex d) : ℝ :=
  (∑ x ∈ triadicCubeFinset d k j, f x) / (3 ^ d) ^ k

theorem sum_triadicCubeFinset_eq_mul_cubeMeanD (f : Vertex d → ℝ) (k : ℕ) (j : Vertex d) :
    ∑ x ∈ triadicCubeFinset d k j, f x = (3 ^ d) ^ k * cubeMeanD f k j := by
  rw [cubeMeanD]
  field_simp

theorem cubeMean_zeroD (f : Vertex d → ℝ) (x : Vertex d) :
    cubeMeanD f 0 (cubeIndexD 0 x) = f x := by
  have hQ : triadicCubeFinset d 0 (cubeIndexD 0 x) = {x} := by
    ext y
    rw [mem_triadicCubeFinset_iffD, cubeIndex_zeroD, cubeIndex_zeroD, Finset.mem_singleton]
  rw [cubeMeanD, hQ, Finset.sum_singleton, pow_zero, div_one]

/-- On a union of cubes of scale `k`,
`|Σ_{x ∈ S} F(j_k(x)) u(x)| ≤ Σ_{x ∈ S} |F(j_k(x))| |A_k u(x)|`. -/
theorem abs_sum_comp_cubeIndex_mul_leD {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnionD k S)
    (F u : Vertex d → ℝ) :
    |∑ x ∈ S, F (cubeIndexD k x) * u x| ≤
      ∑ x ∈ S, |F (cubeIndexD k x)| * |cubeMeanD u k (cubeIndexD k x)| := by
  have hR : ∑ x ∈ S, |F (cubeIndexD k x)| * |cubeMeanD u k (cubeIndexD k x)| =
      ∑ j ∈ S.image (cubeIndexD k), |F j| * |∑ x ∈ triadicCubeFinset d k j, u x| := by
    have h := sum_comp_cubeIndex_mulD hS
      (fun j => |F j| * |cubeMeanD u k j|) (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_triadicCubeFinsetD,
      sum_triadicCubeFinset_eq_mul_cubeMeanD, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ d) ^ k)]
    ring
  rw [hR, sum_comp_cubeIndex_mulD hS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => abs_mul _ _

/-- **The multiscale decomposition.** On a finite union `S` of cubes of scale `K`,
`|Σ_{x ∈ S} f u| ≤ Σ_S |A_K f| |A_K u| + Σ_{k < K} Σ_S |A_k f - A_{k+1} f| |A_k u|`. -/
theorem abs_sum_mul_le_multiscaleD {K : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnionD K S)
    (f u : Vertex d → ℝ) :
    |∑ x ∈ S, f x * u x| ≤
      ∑ x ∈ S, |cubeMeanD f K (cubeIndexD K x)| * |cubeMeanD u K (cubeIndexD K x)| +
      ∑ k ∈ range K, ∑ x ∈ S,
        |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| *
          |cubeMeanD u k (cubeIndexD k x)| := by
  set g : ℕ → Vertex d → ℝ := fun k x => cubeMeanD f k (cubeIndexD k x) with hg
  have htel : ∀ x, f x = g K x + ∑ k ∈ range K, (g k x - g (k + 1) x) := by
    intro x
    rw [Finset.sum_range_sub' (fun k => g k x), hg]
    simp only [cubeMean_zeroD]
    ring
  have hsplit : ∑ x ∈ S, f x * u x =
      ∑ x ∈ S, g K x * u x + ∑ k ∈ range K, ∑ x ∈ S, (g k x - g (k + 1) x) * u x := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [htel x, add_mul, Finset.sum_mul]
  have hstep : ∀ k ∈ range K, |∑ x ∈ S, (g k x - g (k + 1) x) * u x| ≤
      ∑ x ∈ S, |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| *
        |cubeMeanD u k (cubeIndexD k x)| := by
    intro k hk
    have hkK : k ≤ K := (Finset.mem_range.1 hk).le
    have key := abs_sum_comp_cubeIndex_mul_leD (hS.mono hkK)
      (fun j => cubeMeanD f k j - cubeMeanD f (k + 1) (cubeIndexD 1 j)) u
    have e1 : ∑ x ∈ S, (g k x - g (k + 1) x) * u x = ∑ x ∈ S,
        (fun j => cubeMeanD f k j - cubeMeanD f (k + 1) (cubeIndexD 1 j)) (cubeIndexD k x) *
          u x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hg]
      rw [cubeIndex_succD k x]
    have e2 : ∑ x ∈ S, |(fun j => cubeMeanD f k j - cubeMeanD f (k + 1) (cubeIndexD 1 j))
        (cubeIndexD k x)| * |cubeMeanD u k (cubeIndexD k x)| = ∑ x ∈ S,
        |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| *
          |cubeMeanD u k (cubeIndexD k x)| := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [cubeIndex_succD k x]
    rw [e1]
    exact key.trans (le_of_eq e2)
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_sum_comp_cubeIndex_mul_leD hS (cubeMeanD f K) u
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)

/-- `|avg_P f - avg_R f| ≤ B` when `|f(x) - f(x')| ≤ B` for `x ∈ P`, `x' ∈ R`. -/
theorem abs_sum_div_sub_sum_div_leD {P R : Finset (Vertex d)} (hP : P.Nonempty) (hR : R.Nonempty)
    (f : Vertex d → ℝ) {B : ℝ} (h : ∀ x ∈ P, ∀ x' ∈ R, |f x - f x'| ≤ B) :
    |(∑ x ∈ P, f x) / P.card - (∑ x ∈ R, f x) / R.card| ≤ B := by
  have ha : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hb : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have e : (∑ x ∈ P, f x) / P.card - (∑ x ∈ R, f x) / R.card =
      (∑ x ∈ P, ∑ x' ∈ R, (f x - f x')) / (P.card * R.card) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
  rw [e, abs_div, abs_of_pos (mul_pos ha hb), div_le_iff₀ (mul_pos ha hb)]
  calc |∑ x ∈ P, ∑ x' ∈ R, (f x - f x')| ≤ ∑ x ∈ P, ∑ x' ∈ R, |f x - f x'| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x ∈ P, ∑ x' ∈ R, B :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun x' hx' => h x hx x' hx'
    _ = B * (P.card * R.card) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

/-- `|A_k f(x) - A_{k+1} f(x)| ≤ B` when `|f(x') - f(x'')| ≤ B` for `x', x''` in the cube of scale
`k + 1` containing `x`. -/
theorem abs_cubeMean_sub_cubeMean_succ_leD (f : Vertex d → ℝ) (k : ℕ) (x : Vertex d) {B : ℝ}
    (h : ∀ x' ∈ triadicCubeFinset d (k + 1) (cubeIndexD (k + 1) x),
      ∀ x'' ∈ triadicCubeFinset d (k + 1) (cubeIndexD (k + 1) x), |f x' - f x''| ≤ B) :
    |cubeMeanD f k (cubeIndexD k x) - cubeMeanD f (k + 1) (cubeIndexD (k + 1) x)| ≤ B := by
  have hsub : triadicCubeFinset d k (cubeIndexD k x) ⊆
      triadicCubeFinset d (k + 1) (cubeIndexD (k + 1) x) := by
    intro x' hx'
    rw [mem_triadicCubeFinset_iffD] at hx' ⊢
    rw [cubeIndex_succD k x', cubeIndex_succD k x, hx']
  have e : ∀ m j, cubeMeanD f m j =
      (∑ x ∈ triadicCubeFinset d m j, f x) / (triadicCubeFinset d m j).card := by
    intro m j
    rw [cubeMeanD, card_triadicCubeFinsetD]
  rw [e, e]
  exact abs_sum_div_sub_sum_div_leD ⟨x, cubeIndex_memD k x⟩ ⟨x, cubeIndex_memD (k + 1) x⟩ f
    fun x' hx' x'' hx'' => h x' (hsub hx') x'' hx''

end Rigidity.Green
