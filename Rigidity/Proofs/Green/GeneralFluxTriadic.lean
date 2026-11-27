import Rigidity.Proofs.Green.DarioGuTriadicAverages

/-!
# Averages on the triadic cubes of `ℤ^d`

The extension of `DarioGuTriadicAverages.lean` from `ℤ²` to `ℤ^d`: the index `cubeIndex k x` of
the triadic cube of scale `k` containing `x`, the finite unions of cubes of scale `k`
(`IsCubeUnion`), the averages `cubeMean f k j = 3^{-dk} Σ_{x ∈ □_k(j)} f(x)` and the multiscale
decomposition of a pairing `abs_sum_mul_le_multiscale`:
`|Σ_S f u| ≤ Σ_S |A_K f| |A_K u| + Σ_{k < K} Σ_S |A_k f - A_{k+1} f| |A_k u|`.
-/

open Finset LatticeProb.Percolation Rigidity.Proofs.S2 Rigidity.External

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ}

/-! ### The cube containing a vertex -/

/-- The index `j` of the triadic cube `□_k(3^k j)` of scale `k` containing `x`: `jᵢ` is the integer
nearest to `xᵢ / 3^k`. -/
def cubeIndex (k : ℕ) (x : Vertex d) : Vertex d :=
  fun i => (x i + ((3 : ℤ) ^ k - 1) / 2) / 3 ^ k

theorem ediv_eq_iff_of_two_mul_add_one {P h a b : ℤ} (hPh : P = 2 * h + 1) (hP : 0 < P) :
    (a + h) / P = b ↔ P * b - h ≤ a ∧ a ≤ P * b + h := by
  have e1 : b * P = P * b := mul_comm b P
  have e2 : (b + 1) * P = P * b + P := by ring
  constructor
  · intro hab
    have h1 := (Int.le_ediv_iff_mul_le hP).1 (le_of_eq hab.symm)
    have h2 := (Int.ediv_lt_iff_lt_mul hP).1 (show (a + h) / P < b + 1 by omega)
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have : (a + h) / P < b + 1 := (Int.ediv_lt_iff_lt_mul hP).2 (by linarith)
      omega
    · exact (Int.le_ediv_iff_mul_le hP).2 (by linarith)

theorem mem_triadicCubeFinset_iff (k : ℕ) (x j : Vertex d) :
    x ∈ triadicCubeFinset d k j ↔ cubeIndex k x = j := by
  have hQ := three_pow_eq_two_mul_half_add_one k
  have hP : (0 : ℤ) < 3 ^ k := by positivity
  simp only [triadicCubeFinset, Fintype.mem_piFinset, Finset.mem_Icc, funext_iff, cubeIndex]
  exact forall_congr' fun i => (ediv_eq_iff_of_two_mul_add_one hQ hP).symm

theorem cubeIndex_mem (k : ℕ) (x : Vertex d) : x ∈ triadicCubeFinset d k (cubeIndex k x) :=
  (mem_triadicCubeFinset_iff k x _).2 rfl

theorem cubeIndex_zero (x : Vertex d) : cubeIndex 0 x = x := by
  funext i
  simp [cubeIndex]

/-- The cubes of scale `k` refine those of scale `k + m`. -/
theorem cubeIndex_add (k m : ℕ) (x : Vertex d) :
    cubeIndex (k + m) x = cubeIndex m (cubeIndex k x) := by
  funext i
  simp only [cubeIndex]
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

theorem cubeIndex_succ (k : ℕ) (x : Vertex d) :
    cubeIndex (k + 1) x = cubeIndex 1 (cubeIndex k x) :=
  cubeIndex_add k 1 x

theorem card_triadicCubeFinsetD (k : ℕ) (j : Vertex d) :
    ((triadicCubeFinset d k j).card : ℝ) = (3 ^ d) ^ k := by
  rw [card_triadicCubeFinset, pow_mul]
  push_cast
  ring

/-- `|xᵢ - 3^k cubeIndex k xᵢ| ≤ (3^k - 1)/2`. -/
theorem abs_sub_mul_cubeIndex_le (k : ℕ) (x : Vertex d) (i : Fin d) :
    |x i - 3 ^ k * cubeIndex k x i| ≤ ((3 : ℤ) ^ k - 1) / 2 := by
  have h := cubeIndex_mem k x
  simp only [triadicCubeFinset, Fintype.mem_piFinset, Finset.mem_Icc] at h
  rw [abs_le]
  constructor <;> linarith [(h i).1, (h i).2]

/-! ### Unions of cubes and regrouping -/

/-- `S` is a union of cubes of scale `k`. -/
def IsCubeUnion (k : ℕ) (S : Finset (Vertex d)) : Prop :=
  ∀ x x', cubeIndex k x = cubeIndex k x' → x ∈ S → x' ∈ S

theorem IsCubeUnion.mono {k K : ℕ} (hkK : k ≤ K) {S : Finset (Vertex d)} (hS : IsCubeUnion K S) :
    IsCubeUnion k S := by
  intro x x' h hx
  refine hS x x' ?_ hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkK
  rw [cubeIndex_add, cubeIndex_add, h]

/-- The union of the cubes of scale `K` with index in `J`. -/
theorem isCubeUnion_biUnion (K : ℕ) (J : Finset (Vertex d)) :
    IsCubeUnion K (J.biUnion (triadicCubeFinset d K)) := by
  intro x x' h hx
  simp only [Finset.mem_biUnion, mem_triadicCubeFinset_iff] at hx ⊢
  obtain ⟨j, hj, hxj⟩ := hx
  exact ⟨j, hj, h ▸ hxj⟩

theorem filter_cubeIndex_eq {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion k S) {j : Vertex d}
    (hj : j ∈ S.image (cubeIndex k)) :
    S.filter (fun x => cubeIndex k x = j) = triadicCubeFinset d k j := by
  ext x
  simp only [Finset.mem_filter, mem_triadicCubeFinset_iff]
  constructor
  · exact fun h => h.2
  · intro hx
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hj
    exact ⟨hS x₀ x hx.symm hx₀, hx⟩

/-- Regrouping a sum over a union of cubes of scale `k` cube by cube. -/
theorem sum_comp_cubeIndex_mul {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion k S)
    (F u : Vertex d → ℝ) :
    ∑ x ∈ S, F (cubeIndex k x) * u x =
      ∑ j ∈ S.image (cubeIndex k), F j * ∑ x ∈ triadicCubeFinset d k j, u x := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeIndex k) hx)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [filter_cubeIndex_eq hS hj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(mem_triadicCubeFinset_iff k x j).1 hx]

/-! ### Averages on cubes -/

/-- The average of `f` on the triadic cube `□_k(3^k j)`. -/
noncomputable def cubeMean (f : Vertex d → ℝ) (k : ℕ) (j : Vertex d) : ℝ :=
  (∑ x ∈ triadicCubeFinset d k j, f x) / (3 ^ d) ^ k

theorem sum_triadicCubeFinset_eq_mul_cubeMean (f : Vertex d → ℝ) (k : ℕ) (j : Vertex d) :
    ∑ x ∈ triadicCubeFinset d k j, f x = (3 ^ d) ^ k * cubeMean f k j := by
  rw [cubeMean]
  field_simp

theorem cubeMean_zero (f : Vertex d → ℝ) (x : Vertex d) : cubeMean f 0 (cubeIndex 0 x) = f x := by
  have hQ : triadicCubeFinset d 0 (cubeIndex 0 x) = {x} := by
    ext y
    rw [mem_triadicCubeFinset_iff, cubeIndex_zero, cubeIndex_zero, Finset.mem_singleton]
  rw [cubeMean, hQ, Finset.sum_singleton, pow_zero, div_one]

/-- On a union of cubes of scale `k`, `|Σ_{x ∈ S} F(j_k(x)) u(x)| ≤ Σ_{x ∈ S} |F(j_k(x))| |A_k u(x)|`. -/
theorem abs_sum_comp_cubeIndex_mul_le {k : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion k S)
    (F u : Vertex d → ℝ) :
    |∑ x ∈ S, F (cubeIndex k x) * u x| ≤
      ∑ x ∈ S, |F (cubeIndex k x)| * |cubeMean u k (cubeIndex k x)| := by
  have hR : ∑ x ∈ S, |F (cubeIndex k x)| * |cubeMean u k (cubeIndex k x)| =
      ∑ j ∈ S.image (cubeIndex k), |F j| * |∑ x ∈ triadicCubeFinset d k j, u x| := by
    have h := sum_comp_cubeIndex_mul hS
      (fun j => |F j| * |cubeMean u k j|) (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_triadicCubeFinsetD,
      sum_triadicCubeFinset_eq_mul_cubeMean, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (3 ^ d) ^ k)]
    ring
  rw [hR, sum_comp_cubeIndex_mul hS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => abs_mul _ _

/-- **The multiscale decomposition.** On a finite union `S` of cubes of scale `K`,
`|Σ_{x ∈ S} f u| ≤ Σ_S |A_K f| |A_K u| + Σ_{k < K} Σ_S |A_k f - A_{k+1} f| |A_k u|`. -/
theorem abs_sum_mul_le_multiscale {K : ℕ} {S : Finset (Vertex d)} (hS : IsCubeUnion K S)
    (f u : Vertex d → ℝ) :
    |∑ x ∈ S, f x * u x| ≤
      ∑ x ∈ S, |cubeMean f K (cubeIndex K x)| * |cubeMean u K (cubeIndex K x)| +
      ∑ k ∈ range K, ∑ x ∈ S,
        |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| *
          |cubeMean u k (cubeIndex k x)| := by
  set g : ℕ → Vertex d → ℝ := fun k x => cubeMean f k (cubeIndex k x) with hg
  have htel : ∀ x, f x = g K x + ∑ k ∈ range K, (g k x - g (k + 1) x) := by
    intro x
    rw [Finset.sum_range_sub' (fun k => g k x), hg]
    simp only [cubeMean_zero]
    ring
  have hsplit : ∑ x ∈ S, f x * u x =
      ∑ x ∈ S, g K x * u x + ∑ k ∈ range K, ∑ x ∈ S, (g k x - g (k + 1) x) * u x := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [htel x, add_mul, Finset.sum_mul]
  have hstep : ∀ k ∈ range K, |∑ x ∈ S, (g k x - g (k + 1) x) * u x| ≤
      ∑ x ∈ S, |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| *
        |cubeMean u k (cubeIndex k x)| := by
    intro k hk
    have hkK : k ≤ K := (Finset.mem_range.1 hk).le
    have key := abs_sum_comp_cubeIndex_mul_le (hS.mono hkK)
      (fun j => cubeMean f k j - cubeMean f (k + 1) (cubeIndex 1 j)) u
    have e1 : ∑ x ∈ S, (g k x - g (k + 1) x) * u x = ∑ x ∈ S,
        (fun j => cubeMean f k j - cubeMean f (k + 1) (cubeIndex 1 j)) (cubeIndex k x) * u x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hg]
      rw [cubeIndex_succ k x]
    have e2 : ∑ x ∈ S, |(fun j => cubeMean f k j - cubeMean f (k + 1) (cubeIndex 1 j))
        (cubeIndex k x)| * |cubeMean u k (cubeIndex k x)| = ∑ x ∈ S,
        |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| *
          |cubeMean u k (cubeIndex k x)| := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [cubeIndex_succ k x]
    rw [e1]
    exact key.trans (le_of_eq e2)
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_sum_comp_cubeIndex_mul_le hS (cubeMean f K) u
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)

/-- `|avg_P f - avg_R f| ≤ B` when `|f(x) - f(x')| ≤ B` for `x ∈ P`, `x' ∈ R`. -/
theorem abs_sum_div_sub_sum_div_le {P R : Finset (Vertex d)} (hP : P.Nonempty) (hR : R.Nonempty)
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
theorem abs_cubeMean_sub_cubeMean_succ_le (f : Vertex d → ℝ) (k : ℕ) (x : Vertex d) {B : ℝ}
    (h : ∀ x' ∈ triadicCubeFinset d (k + 1) (cubeIndex (k + 1) x),
      ∀ x'' ∈ triadicCubeFinset d (k + 1) (cubeIndex (k + 1) x), |f x' - f x''| ≤ B) :
    |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| ≤ B := by
  have hsub : triadicCubeFinset d k (cubeIndex k x) ⊆
      triadicCubeFinset d (k + 1) (cubeIndex (k + 1) x) := by
    intro x' hx'
    rw [mem_triadicCubeFinset_iff] at hx' ⊢
    rw [cubeIndex_succ k x', cubeIndex_succ k x, hx']
  have e : ∀ m j, cubeMean f m j =
      (∑ x ∈ triadicCubeFinset d m j, f x) / (triadicCubeFinset d m j).card := by
    intro m j
    rw [cubeMean, card_triadicCubeFinsetD]
  rw [e, e]
  exact abs_sum_div_sub_sum_div_le ⟨x, cubeIndex_mem k x⟩ ⟨x, cubeIndex_mem (k + 1) x⟩ f
    fun x' hx' x'' hx'' => h x' (hsub hx') x'' hx''

/-! ### The deviation of the cluster from its density -/

/-- `1_{x ∈ 𝒞_∞} - θ`, where `x ∈ 𝒞_∞` is the event that the open cluster of `x` is infinite. -/
noncomputable def clusterDeviationD (ω : Configuration d) (θ : ℝ) (x : Vertex d) : ℝ :=
  (infiniteComponentEvent x).indicator (fun _ => (1 : ℝ)) ω - θ

theorem abs_clusterDeviationD_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (ω : Configuration d)
    (x : Vertex d) : |clusterDeviationD ω θ x| ≤ 1 := by
  unfold clusterDeviationD
  by_cases hx : ω ∈ infiniteComponentEvent x
  · rw [Set.indicator_of_mem hx, abs_le]
    constructor <;> linarith
  · rw [Set.indicator_of_notMem hx, abs_le]
    constructor <;> linarith

/-- The average of `1_{𝒞_∞} - θ` on a triadic cube is `|𝒞_∞ ∩ □|/|□| - θ`. -/
theorem cubeMean_clusterDeviationD (ω : Configuration d) (θ : ℝ) (k : ℕ) (j : Vertex d) :
    cubeMean (clusterDeviationD ω θ) k j =
      (infiniteClusterCount (triadicCube d k j) ω : ℝ) / ((triadicCube d k j).ncard : ℝ) - θ := by
  classical
  have hsum : ∑ x ∈ triadicCubeFinset d k j, (infiniteComponentEvent x).indicator
      (fun _ => (1 : ℝ)) ω =
      (((triadicCubeFinset d k j).filter fun y => ω ∈ infiniteComponentEvent y).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ω ∈ infiniteComponentEvent y <;> simp [hy]
  have h9 : ((triadicCube d k j).ncard : ℝ) = (3 ^ d) ^ k := by
    rw [ncard_triadicCube, pow_mul]
    push_cast
    ring
  rw [cubeMean, h9, infiniteClusterCount_triadicCube]
  simp only [clusterDeviationD, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hsum, card_triadicCubeFinsetD]
  field_simp

theorem measurable_cubeMean_clusterDeviationD (θ : ℝ) (k : ℕ) (j : Vertex d) :
    Measurable fun ω => cubeMean (clusterDeviationD ω θ) k j := by
  simp only [cubeMean_clusterDeviationD]
  exact ((measurable_infiniteClusterCount_triadicCube k j).div_const _).sub_const _

end Rigidity.Green.GeneralFlux
