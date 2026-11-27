import Rigidity.Proofs.Green.TriadicAveragesD
import Rigidity.Proofs.Green.GaussianOscD
import Rigidity.Proofs.Green.GaussianMassD
import Rigidity.Proofs.Green.DisplacementTailD

/-!
# Regions of triadic cubes around a point of `ℤ^d`

The `d`-dimensional forms of the regions of `DarioGuDensityGaussianBound.lean`:
`gaussianRegionD K J y` is the union of the cubes of scale `K` whose index is within `J` of that of
`y`; for `J = 3^{K+2}` it contains every vertex at distance less than `9^{K+1}` from `y`
(`le_latticeDist_of_notMem_gaussianRegionD`), and the indices of its cubes of scale `k ≤ K` are
within `2 · 9^{K+1}` of that of `y` (`abs_cubeIndex_sub_le_of_mem_gaussianRegionD`).
-/

open Finset LatticeProb.Percolation Rigidity.Proofs.S2

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ}

/-- The box of the indices within `R` of `c`. -/
noncomputable def indexBoxD (c : Vertex d) (R : ℤ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (c i - R) (c i + R)

theorem mem_indexBoxD {c j : Vertex d} {R : ℤ} : j ∈ indexBoxD c R ↔ ∀ i, |j i - c i| ≤ R := by
  simp only [indexBoxD, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem card_indexBoxD (c : Vertex d) {R : ℕ} : (indexBoxD c R).card = (2 * R + 1) ^ d := by
  rw [indexBoxD, Fintype.card_piFinset]
  have hc : ∀ i, (Finset.Icc (c i - (R : ℤ)) (c i + R)).card = 2 * R + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The union of the cubes of scale `K` whose index is within `J` of the index of the cube of
`y`. -/
noncomputable def gaussianRegionD (K : ℕ) (J : ℤ) (y : Vertex d) : Finset (Vertex d) :=
  (indexBoxD (cubeIndexD K y) J).biUnion (triadicCubeFinset d K)

theorem mem_gaussianRegionD {K : ℕ} {J : ℤ} {y x : Vertex d} :
    x ∈ gaussianRegionD K J y ↔ ∀ i, |cubeIndexD K x i - cubeIndexD K y i| ≤ J := by
  simp only [gaussianRegionD, Finset.mem_biUnion, mem_triadicCubeFinset_iffD]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact mem_indexBoxD.1 hj
  · intro h
    exact ⟨_, mem_indexBoxD.2 h, rfl⟩

theorem isCubeUnion_gaussianRegionD (K : ℕ) (J : ℤ) (y : Vertex d) :
    IsCubeUnionD K (gaussianRegionD K J y) :=
  isCubeUnion_biUnionD K _

theorem latticeDist_ge_absD (x y : Vertex d) (i : Fin d) : |(x i : ℝ) - y i| ≤ ldist x y := by
  have h := PiLp.norm_apply_le (edzD x y) i
  rw [edzD_apply, Real.norm_eq_abs] at h
  exact h

/-- A vertex outside `gaussianRegionD K (3^{K+2}) y` is at distance at least `9^{K+1}` from `y`. -/
theorem le_latticeDist_of_notMem_gaussianRegionD {K : ℕ} {y x : Vertex d}
    (hx : x ∉ gaussianRegionD K (3 ^ (K + 2)) y) : (9 : ℝ) ^ (K + 1) ≤ ldist x y := by
  rw [mem_gaussianRegionD] at hx
  simp only [not_forall, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  have hQ := three_pow_eq_two_mul_half_add_one K
  have hP : (0 : ℤ) < 3 ^ K := by positivity
  have h1 := abs_sub_mul_cubeIndex_leD K x i
  have h2 := abs_sub_mul_cubeIndex_leD K y i
  set a := cubeIndexD K x i
  set b := cubeIndexD K y i
  have hab : 3 ^ K * (3 ^ (K + 2) + 1) ≤ |3 ^ K * a - 3 ^ K * b| := by
    rw [← mul_sub, abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_left (Int.lt_iff_add_one_le.1 hi) hP.le
  have key := abs_sub_abs_le_abs_sub (3 ^ K * a - 3 ^ K * b) ((3 ^ K * a - 3 ^ K * b) - (x i - y i))
  rw [show (3 ^ K * a - 3 ^ K * b) - ((3 ^ K * a - 3 ^ K * b) - (x i - y i)) = x i - y i by ring]
    at key
  have hb : |(3 ^ K * a - 3 ^ K * b) - (x i - y i)| ≤ 2 * (((3 : ℤ) ^ K - 1) / 2) := by
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hint : (3 : ℤ) ^ K * 3 ^ (K + 2) ≤ |x i - y i| := by
    have : (3 : ℤ) ^ K * (3 ^ (K + 2) + 1) = 3 ^ K * 3 ^ (K + 2) + 3 ^ K := by ring
    linarith
  have hreal : (3 : ℝ) ^ K * 3 ^ (K + 2) ≤ |(x i : ℝ) - y i| := by
    have := (Int.cast_le (R := ℝ)).2 hint
    push_cast at this
    exact this
  have e9 : (3 : ℝ) ^ K * 3 ^ (K + 2) = 9 ^ (K + 1) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    ring_nf
  rw [e9] at hreal
  exact hreal.trans (latticeDist_ge_absD x y i)

/-- The cubes of scale `k ≤ K` of `gaussianRegionD K (3^{K+2}) y` have index within `2 · 9^{K+1}`
of the index of `y`. -/
theorem abs_cubeIndex_sub_le_of_mem_gaussianRegionD {K k : ℕ} (hk : k ≤ K) {y x : Vertex d}
    (hx : x ∈ gaussianRegionD K (3 ^ (K + 2)) y) (i : Fin d) :
    |cubeIndexD k x i - cubeIndexD k y i| ≤ 2 * 9 ^ (K + 1) := by
  rw [mem_gaussianRegionD] at hx
  have hP : (0 : ℤ) < 3 ^ K := by positivity
  have hp : (0 : ℤ) < 3 ^ k := by positivity
  have hpP : (3 : ℤ) ^ k ≤ 3 ^ K := pow_le_pow_right₀ (by norm_num) hk
  have hQ := three_pow_eq_two_mul_half_add_one K
  have hq := three_pow_eq_two_mul_half_add_one k
  have h1 := abs_sub_mul_cubeIndex_leD K x i
  have h2 := abs_sub_mul_cubeIndex_leD K y i
  have h3 := abs_sub_mul_cubeIndex_leD k x i
  have h4 := abs_sub_mul_cubeIndex_leD k y i
  set a := cubeIndexD K x i
  set b := cubeIndexD K y i
  set a' := cubeIndexD k x i
  set b' := cubeIndexD k y i
  have hab : |3 ^ K * a - 3 ^ K * b| ≤ 3 ^ K * 3 ^ (K + 2) := by
    rw [← mul_sub, abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_left (hx i) hP.le
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 h3
  have a4 := abs_le.1 h4
  have hxy : |x i - y i| ≤ 3 ^ K * 3 ^ (K + 2) + 3 ^ K := by
    have e : x i - y i = (3 ^ K * a - 3 ^ K * b) + ((x i - 3 ^ K * a) - (y i - 3 ^ K * b)) := by
      ring
    rw [e]
    have hb : |(x i - 3 ^ K * a) - (y i - 3 ^ K * b)| ≤ 3 ^ K := by
      rw [abs_le]
      constructor <;> linarith
    exact (abs_add_le _ _).trans (by linarith)
  have ha'b' : 3 ^ k * |a' - b'| ≤ 3 ^ K * 3 ^ (K + 2) + 3 ^ K + 3 ^ k := by
    rw [← abs_of_pos hp, ← abs_mul, abs_of_pos hp, mul_sub]
    have e : 3 ^ k * a' - 3 ^ k * b' = (x i - y i) + ((y i - 3 ^ k * b') - (x i - 3 ^ k * a')) := by
      ring
    rw [e]
    have hb : |(y i - 3 ^ k * b') - (x i - 3 ^ k * a')| ≤ 3 ^ k := by
      rw [abs_le]
      constructor <;> linarith
    exact (abs_add_le _ _).trans (by linarith)
  have hle : |a' - b'| ≤ 3 ^ k * |a' - b'| :=
    le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (by norm_num))
  have e : (9 : ℤ) ^ (K + 1) = 3 ^ K * 3 ^ (K + 2) := by
    rw [show (9 : ℤ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    ring_nf
  have h9 : (9 : ℤ) ≤ 3 ^ (K + 2) :=
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (K + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hPJ : (3 : ℤ) ^ K * 2 ≤ 3 ^ K * 3 ^ (K + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hP.le
  linarith

end Rigidity.Green
