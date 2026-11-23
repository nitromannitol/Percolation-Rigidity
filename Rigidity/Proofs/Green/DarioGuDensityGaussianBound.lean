import Rigidity.Proofs.Green.DarioGuTriadicAverages
import Rigidity.Proofs.Green.DarioGuGaussianMass

/-!
# The Gaussian mass of the cluster from the densities on triadic cubes

The deterministic part of the proof of Proposition A.7 of Dario–Gu (concentration of the Gaussian
mass of the infinite cluster). For `t ≥ 81`, `3^K ≤ √t < 3^{K+1}`, a finite union `S` of cubes of
scale `K` and `u : ℤ² → ℝ` with `|u| ≤ 1` whose averages on the cubes of scale `k ≤ K` meeting `S`
are at most `(3^k)^{α - 1}` whenever `3^k ≥ t^α`,

`|Σ_{x ∈ S} p̄(t, x - y) u(x)| ≤ C t^{-(1/2 - α)}` (`abs_sum_latticeGaussian_mul_le`).

The proof uses the multiscale decomposition `abs_sum_mul_le_multiscale`: the top term is at most
`(3^K)^{α - 1} Σ p̄`, and the term of scale `k < K` is at most `C 3^k t^{-1/2}` times the bound on
the averages of `u`, by the oscillation bound of `p̄` on the cube of scale `k + 1`.

The region `gaussianRegion K J y` is the union of the cubes of scale `K` whose index is within `J`
of that of `y`; for `J = 3^{K+2}` it contains every vertex at distance less than `t` from `y`
(`le_latticeDist_of_notMem_gaussianRegion`), and the indices of its cubes of scale `k ≤ K` are
within `2 · 9^{K+1}` of that of `y` (`abs_cubeIndex_sub_le_of_mem_gaussianRegion`).
-/

open Finset LatticeProb.Percolation Rigidity.Proofs.S2

namespace Rigidity.Green

/-! ### Sums on cubes -/

/-- On a union of cubes of scale `k`, `Σ_{x ∈ S} A_k f(x) = Σ_{x ∈ S} f(x)`. -/
theorem sum_cubeMean_eq {k : ℕ} {S : Finset (Vertex 2)} (hS : IsCubeUnion k S)
    (f : Vertex 2 → ℝ) : ∑ x ∈ S, cubeMean f k (cubeIndex k x) = ∑ x ∈ S, f x := by
  have h1 := sum_comp_cubeIndex_mul hS (cubeMean f k) (fun _ => (1 : ℝ))
  have h2 := sum_comp_cubeIndex_mul hS (fun _ => (1 : ℝ)) f
  simp only [mul_one, one_mul] at h1 h2
  rw [h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_triadicCubeFinset_two,
    sum_triadicCubeFinset_eq_mul_cubeMean]
  ring

theorem abs_cubeMean_le_one {u : Vertex 2 → ℝ} (hu : ∀ x, |u x| ≤ 1) (k : ℕ) (j : Vertex 2) :
    |cubeMean u k j| ≤ 1 := by
  rw [cubeMean, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 9 ^ k), div_le_one (by positivity)]
  calc |∑ x ∈ triadicCubeFinset 2 k j, u x| ≤ ∑ x ∈ triadicCubeFinset 2 k j, |u x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ triadicCubeFinset 2 k j, (1 : ℝ) := Finset.sum_le_sum fun x _ => hu x
    _ = 9 ^ k := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_triadicCubeFinset_two]

theorem cubeMean_nonneg {f : Vertex 2 → ℝ} (hf : ∀ x, 0 ≤ f x) (k : ℕ) (j : Vertex 2) :
    0 ≤ cubeMean f k j :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (by positivity)

/-- Two vertices of the same cube of scale `k` are at distance less than `2 · 3^k`. -/
theorem norm_sub_lt_of_cubeIndex_eq {k : ℕ} {x x' : Vertex 2}
    (h : cubeIndex k x = cubeIndex k x') :
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding x'‖ < 2 * 3 ^ k := by
  rw [← dist_eq_norm]
  have hQ := three_pow_eq_two_mul_half_add_one k
  have hc : ∀ i, |(latticeEuclideanEmbedding x).ofLp i - (latticeEuclideanEmbedding x').ofLp i| <
      3 ^ k := by
    intro i
    have h1 := abs_sub_mul_cubeIndex_le k x i
    have h2 := abs_sub_mul_cubeIndex_le k x' i
    rw [h] at h1
    have hi : |x i - x' i| < 3 ^ k := by
      have a1 := abs_le.1 h1
      have a2 := abs_le.1 h2
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have hi' : ((|x i - x' i| : ℤ) : ℝ) < ((3 ^ k : ℤ) : ℝ) := by exact_mod_cast hi
    push_cast at hi'
    exact hi'
  have := dist_lt_of_forall_abs_sub_lt (d := 2) hc
  push_cast at this
  exact this

/-! ### Geometric sums -/

theorem sum_ite_pow_lt_le {X : ℝ} (hX : 0 ≤ X) (K : ℕ) :
    ∑ k ∈ range K, (if X ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) ≤ ((3 : ℝ) ^ K - 1) / 2 ∧
      ∑ k ∈ range K, (if X ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) ≤ 3 * X / 2 := by
  induction K with
  | zero => simp only [range_zero, sum_empty, pow_zero, sub_self, zero_div, le_refl, true_and]; positivity
  | succ K ih =>
    rw [sum_range_succ]
    have hp : (3 : ℝ) ^ K ≤ 3 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ K)
    split_ifs with h
    · rw [add_zero]
      exact ⟨ih.1.trans (by linarith), ih.2⟩
    · replace h := not_le.1 h
      have e : ((3 : ℝ) ^ K - 1) / 2 + 3 ^ K = ((3 : ℝ) ^ (K + 1) - 1) / 2 := by
        rw [pow_succ]; ring
      constructor
      · linarith [ih.1]
      · have : ((3 : ℝ) ^ (K + 1) - 1) / 2 ≤ 3 * X / 2 := by rw [pow_succ]; linarith
        linarith [ih.1]

theorem sum_rpow_pow_le {α : ℝ} (hα : 0 < α) (K : ℕ) :
    ∑ k ∈ range K, ((3 : ℝ) ^ α) ^ k ≤ ((3 : ℝ) ^ α) ^ K / ((3 : ℝ) ^ α - 1) := by
  have hq : 1 < (3 : ℝ) ^ α := Real.one_lt_rpow (by norm_num) hα
  rw [geom_sum_eq hq.ne', div_le_div_iff_of_pos_right (by linarith)]
  linarith

theorem pow_mul_rpow_sub_one (α : ℝ) (k : ℕ) :
    (3 : ℝ) ^ k * ((3 : ℝ) ^ k) ^ (α - 1) = ((3 : ℝ) ^ α) ^ k := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  calc (3 : ℝ) ^ k * ((3 : ℝ) ^ k) ^ (α - 1) = ((3 : ℝ) ^ k) ^ (1 : ℝ) * ((3 : ℝ) ^ k) ^ (α - 1) := by
        rw [Real.rpow_one]
    _ = ((3 : ℝ) ^ k) ^ (1 + (α - 1)) := (Real.rpow_add h3 _ _).symm
    _ = ((3 : ℝ) ^ k) ^ α := by ring_nf
    _ = ((3 : ℝ) ^ α) ^ k := (Real.rpow_pow_comm (by norm_num) α k).symm

/-! ### The region -/

/-- The box `{j : |jᵢ - cᵢ| ≤ R}` of indices. -/
noncomputable def indexBox (c : Vertex 2) (R : ℤ) : Finset (Vertex 2) :=
  Fintype.piFinset fun i => Finset.Icc (c i - R) (c i + R)

theorem mem_indexBox {c j : Vertex 2} {R : ℤ} : j ∈ indexBox c R ↔ ∀ i, |j i - c i| ≤ R := by
  simp only [indexBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  exact forall_congr' fun i => by constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem card_indexBox (c : Vertex 2) {R : ℕ} : (indexBox c R).card = (2 * R + 1) ^ 2 := by
  rw [indexBox, Fintype.card_piFinset]
  have hc : ∀ i, (Finset.Icc (c i - (R : ℤ)) (c i + R)).card = 2 * R + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The union of the cubes of scale `K` whose index is within `J` of the index of the cube of `y`. -/
noncomputable def gaussianRegion (K : ℕ) (J : ℤ) (y : Vertex 2) : Finset (Vertex 2) :=
  (indexBox (cubeIndex K y) J).biUnion (triadicCubeFinset 2 K)

theorem mem_gaussianRegion {K : ℕ} {J : ℤ} {y x : Vertex 2} :
    x ∈ gaussianRegion K J y ↔ ∀ i, |cubeIndex K x i - cubeIndex K y i| ≤ J := by
  simp only [gaussianRegion, Finset.mem_biUnion, mem_triadicCubeFinset_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact mem_indexBox.1 hj
  · intro h
    exact ⟨_, mem_indexBox.2 h, rfl⟩

theorem isCubeUnion_gaussianRegion (K : ℕ) (J : ℤ) (y : Vertex 2) :
    IsCubeUnion K (gaussianRegion K J y) :=
  isCubeUnion_biUnion K _

theorem latticeDist_ge_abs (x y : Vertex 2) (i : Fin 2) : |(x i : ℝ) - y i| ≤ latticeDist x y := by
  have h := latticeDist_sq x y
  have h0 := latticeDist_nonneg x y
  have hsq : ((x i : ℝ) - y i) ^ 2 ≤ latticeDist x y ^ 2 := by
    rw [h]
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · nlinarith [sq_nonneg ((x 1 : ℝ) - y 1)]
    · nlinarith [sq_nonneg ((x 0 : ℝ) - y 0)]
  have := sq_le_sq.1 hsq
  rwa [abs_of_nonneg h0] at this

/-- A vertex outside `gaussianRegion K (3^{K+2}) y` is at distance at least `9^{K+1}` from `y`. -/
theorem le_latticeDist_of_notMem_gaussianRegion {K : ℕ} {y x : Vertex 2}
    (hx : x ∉ gaussianRegion K (3 ^ (K + 2)) y) : (9 : ℝ) ^ (K + 1) ≤ latticeDist x y := by
  rw [mem_gaussianRegion] at hx
  simp only [not_forall, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  have hQ := three_pow_eq_two_mul_half_add_one K
  have hP : (0 : ℤ) < 3 ^ K := by positivity
  have h1 := abs_sub_mul_cubeIndex_le K x i
  have h2 := abs_sub_mul_cubeIndex_le K y i
  set a := cubeIndex K x i
  set b := cubeIndex K y i
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
  exact hreal.trans (latticeDist_ge_abs x y i)

/-- The cubes of scale `k ≤ K` of `gaussianRegion K (3^{K+2}) y` have index within `2 · 9^{K+1}`
of the index of `y`. -/
theorem abs_cubeIndex_sub_le_of_mem_gaussianRegion {K k : ℕ} (hk : k ≤ K) {y x : Vertex 2}
    (hx : x ∈ gaussianRegion K (3 ^ (K + 2)) y) (i : Fin 2) :
    |cubeIndex k x i - cubeIndex k y i| ≤ 2 * 9 ^ (K + 1) := by
  rw [mem_gaussianRegion] at hx
  have hP : (0 : ℤ) < 3 ^ K := by positivity
  have hp : (0 : ℤ) < 3 ^ k := by positivity
  have hpP : (3 : ℤ) ^ k ≤ 3 ^ K := pow_le_pow_right₀ (by norm_num) hk
  have hQ := three_pow_eq_two_mul_half_add_one K
  have hq := three_pow_eq_two_mul_half_add_one k
  have h1 := abs_sub_mul_cubeIndex_le K x i
  have h2 := abs_sub_mul_cubeIndex_le K y i
  have h3 := abs_sub_mul_cubeIndex_le k x i
  have h4 := abs_sub_mul_cubeIndex_le k y i
  set a := cubeIndex K x i
  set b := cubeIndex K y i
  set a' := cubeIndex k x i
  set b' := cubeIndex k y i
  have hab : |3 ^ K * a - 3 ^ K * b| ≤ 3 ^ K * 3 ^ (K + 2) := by
    rw [← mul_sub, abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_left (hx i) hP.le
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 h3
  have a4 := abs_le.1 h4
  have hxy : |x i - y i| ≤ 3 ^ K * 3 ^ (K + 2) + 3 ^ K := by
    have e : x i - y i = (3 ^ K * a - 3 ^ K * b) + ((x i - 3 ^ K * a) - (y i - 3 ^ K * b)) := by ring
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

/-! ### The deterministic estimate -/

/-- **The Gaussian mass of `u` from its averages on triadic cubes.** For `t ≥ 81`,
`3^K ≤ √t < 3^{K+1}`, a finite union `S` of cubes of scale `K` and `|u| ≤ 1` with
`|A_k u| ≤ (3^k)^{α - 1}` on `S` whenever `k ≤ K` and `t^α ≤ 3^k`:
`|Σ_{x ∈ S} p̄(t, x - y) u(x)| ≤ C t^{-(1/2 - α)}`. -/
theorem abs_sum_latticeGaussian_mul_le {σ α : ℝ} (hσ : 0 < σ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (K : ℕ), 81 ≤ t → (3 : ℝ) ^ K ≤ Real.sqrt t →
      Real.sqrt t < 3 ^ (K + 1) → ∀ (y : Vertex 2) (S : Finset (Vertex 2)), IsCubeUnion K S →
      ∀ u : Vertex 2 → ℝ, (∀ x, |u x| ≤ 1) →
      (∀ k ≤ K, t ^ α ≤ (3 : ℝ) ^ k → ∀ x ∈ S,
        |cubeMean u k (cubeIndex k x)| ≤ ((3 : ℝ) ^ k) ^ (α - 1)) →
      |∑ x ∈ S, latticeGaussian σ t x y * u x| ≤ C * t ^ (-(1 / 2 - α)) := by
  set L₀ := 4 * Real.exp (1 / (8 * σ) / 2) * (1 + 1 / (1 / (8 * σ))) ^ 2 with hL₀
  set Kσ := gaussOscConst σ with hKσ
  have hKσ0 : 0 < Kσ := gaussOscConst_pos hσ
  set q := (3 : ℝ) ^ α with hq
  have hq1 : 1 < q := Real.one_lt_rpow (by norm_num) hα
  set M := gaussMassBound σ with hM
  have hM0 : 0 ≤ M := by rw [hM, gaussMassBound]; positivity
  refine ⟨3 * M + 6 * Kσ * L₀ * (3 / 2 + 1 / (q - 1)), by
    have : 0 < q - 1 := by linarith
    positivity, ?_⟩
  intro t K ht hK1 hK2 y S hS u hu hgood
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hss := Real.mul_self_sqrt ht0.le
  set f : Vertex 2 → ℝ := fun x => latticeGaussian σ t x y with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => (latticeGaussian_pos hσ ht0 x y).le
  -- `t^α ≤ 3^K`
  have h14 : (3 : ℝ) ≤ t ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) ht (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have e : (81 : ℝ) ^ (1 / 4 : ℝ) = 3 := by
      rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    linarith
  have hsq4 : Real.sqrt t = t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add ht0, Real.sqrt_eq_rpow]
    norm_num
  have hXK : t ^ α ≤ (3 : ℝ) ^ K := by
    have h1 : t ^ α ≤ t ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hα1
    have h2 : 3 * t ^ α ≤ Real.sqrt t := by
      rw [hsq4]
      have := Real.rpow_nonneg ht0.le α
      nlinarith
    rw [pow_succ] at hK2
    linarith
  have hX0 : 0 ≤ t ^ α := Real.rpow_nonneg ht0.le α
  -- the bound on the averages of `u`
  set δ : ℕ → ℝ := fun k => if t ^ α ≤ (3 : ℝ) ^ k then ((3 : ℝ) ^ k) ^ (α - 1) else 1 with hδ
  have hδu : ∀ k ≤ K, ∀ x ∈ S, |cubeMean u k (cubeIndex k x)| ≤ δ k := by
    intro k hk x hx
    simp only [hδ]
    split_ifs with h
    · exact hgood k hk h x hx
    · exact abs_cubeMean_le_one hu k _
  have hmain := abs_sum_mul_le_multiscale hS f u
  -- the top term
  have hT1 : ∑ x ∈ S, |cubeMean f K (cubeIndex K x)| * |cubeMean u K (cubeIndex K x)| ≤
      ((3 : ℝ) ^ K) ^ (α - 1) * M := by
    calc ∑ x ∈ S, |cubeMean f K (cubeIndex K x)| * |cubeMean u K (cubeIndex K x)|
        ≤ ∑ x ∈ S, cubeMean f K (cubeIndex K x) * ((3 : ℝ) ^ K) ^ (α - 1) := by
          refine Finset.sum_le_sum fun x hx => ?_
          rw [abs_of_nonneg (cubeMean_nonneg hf0 K _)]
          exact mul_le_mul_of_nonneg_left (hgood K le_rfl hXK x hx) (cubeMean_nonneg hf0 K _)
      _ = ((3 : ℝ) ^ K) ^ (α - 1) * ∑ x ∈ S, f x := by
          rw [← Finset.sum_mul, sum_cubeMean_eq hS, mul_comm]
      _ ≤ ((3 : ℝ) ^ K) ^ (α - 1) * M :=
          mul_le_mul_of_nonneg_left (sum_latticeGaussian_le hσ ht1 y S) (by positivity)
  -- the terms of scale `k < K`
  have hT2 : ∀ k ∈ range K, ∑ x ∈ S,
      |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| *
        |cubeMean u k (cubeIndex k x)| ≤
      6 * Kσ * L₀ / Real.sqrt t * ((3 : ℝ) ^ k * δ k) := by
    intro k hk
    have hkK : k + 1 ≤ K := Finset.mem_range.1 hk
    have hδ0 : 0 ≤ δ k := by
      simp only [hδ]
      split_ifs <;> positivity
    have hL : (2 : ℝ) * 3 ^ (k + 1) ≤ 2 * Real.sqrt t := by
      have : (3 : ℝ) ^ (k + 1) ≤ 3 ^ K := pow_le_pow_right₀ (by norm_num) hkK
      linarith
    have hosc : ∀ x, |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| ≤
        Kσ * (2 * 3 ^ (k + 1)) / (t * Real.sqrt t) *
          Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) := by
      intro x
      apply abs_cubeMean_sub_cubeMean_succ_le
      intro x' hx' x'' hx''
      rw [mem_triadicCubeFinset_iff] at hx' hx''
      have hn : ∀ w, cubeIndex (k + 1) w = cubeIndex (k + 1) x →
          ‖(latticeEuclideanEmbedding w - latticeEuclideanEmbedding y) -
            (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y)‖ ≤ 2 * 3 ^ (k + 1) := by
        intro w hw
        rw [sub_sub_sub_cancel_right]
        exact (norm_sub_lt_of_cubeIndex_eq hw).le
      exact abs_gaussianHeat_sub_le_of_near hσ ht0 (by positivity) hL (hn x' hx') (hn x'' hx'')
    have hsum := sum_exp_neg_sq_div_le (c := 1 / (8 * σ)) (by positivity) ht1 y S
    calc ∑ x ∈ S, |cubeMean f k (cubeIndex k x) - cubeMean f (k + 1) (cubeIndex (k + 1) x)| *
          |cubeMean u k (cubeIndex k x)|
        ≤ ∑ x ∈ S, Kσ * (2 * 3 ^ (k + 1)) / (t * Real.sqrt t) *
            Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) * δ k :=
          Finset.sum_le_sum fun x hx => mul_le_mul (hosc x)
            (hδu k (Nat.le_of_succ_le hkK) x hx) (abs_nonneg _) (by positivity)
      _ = Kσ * (2 * 3 ^ (k + 1)) / (t * Real.sqrt t) * δ k *
            ∑ x ∈ S, Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ Kσ * (2 * 3 ^ (k + 1)) / (t * Real.sqrt t) * δ k * (L₀ * t) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 6 * Kσ * L₀ / Real.sqrt t * ((3 : ℝ) ^ k * δ k) := by
          field_simp
          ring
  -- the sum over scales
  have hT3 : ∑ k ∈ range K, (3 : ℝ) ^ k * δ k ≤ 3 * t ^ α / 2 + t ^ α / (q - 1) := by
    have hpt : ∀ k, (3 : ℝ) ^ k * δ k ≤
        (if t ^ α ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) + q ^ k := by
      intro k
      simp only [hδ]
      split_ifs with h
      · rw [pow_mul_rpow_sub_one, zero_add]
      · rw [mul_one]
        have : 0 ≤ q ^ k := by positivity
        linarith
    have hqK : q ^ K ≤ t ^ α := by
      rw [hq, Real.rpow_pow_comm (by norm_num)]
      calc ((3 : ℝ) ^ K) ^ α ≤ (Real.sqrt t) ^ α :=
            Real.rpow_le_rpow (by positivity) hK1 hα.le
        _ ≤ t ^ α := Real.rpow_le_rpow hst.le
            (by rw [Real.sqrt_le_left ht0.le]; nlinarith) hα.le
    calc ∑ k ∈ range K, (3 : ℝ) ^ k * δ k
        ≤ ∑ k ∈ range K, ((if t ^ α ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) + q ^ k) :=
          Finset.sum_le_sum fun k _ => hpt k
      _ = ∑ k ∈ range K, (if t ^ α ≤ (3 : ℝ) ^ k then 0 else (3 : ℝ) ^ k) +
            ∑ k ∈ range K, q ^ k := Finset.sum_add_distrib
      _ ≤ 3 * t ^ α / 2 + q ^ K / (q - 1) :=
          add_le_add (sum_ite_pow_lt_le hX0 K).2 (sum_rpow_pow_le hα K)
      _ ≤ 3 * t ^ α / 2 + t ^ α / (q - 1) := by
          gcongr
  -- the exponents
  have hE1 : ((3 : ℝ) ^ K) ^ (α - 1) ≤ 3 * t ^ (-(1 / 2 - α)) := by
    have hK3 : Real.sqrt t / 3 ≤ (3 : ℝ) ^ K := by
      rw [pow_succ] at hK2
      linarith
    calc ((3 : ℝ) ^ K) ^ (α - 1) ≤ (Real.sqrt t / 3) ^ (α - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hK3 (by linarith)
      _ = (Real.sqrt t) ^ (α - 1) * (3 : ℝ) ^ (1 - α) := by
          rw [Real.div_rpow hst.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
            neg_sub]
      _ ≤ t ^ (-(1 / 2 - α)) * 3 := by
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
            exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
          · calc (3 : ℝ) ^ (1 - α) ≤ 3 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 3 := Real.rpow_one 3
      _ = 3 * t ^ (-(1 / 2 - α)) := by ring
  have hE2 : t ^ α / Real.sqrt t = t ^ (-(1 / 2 - α)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub ht0]
    congr 1
    ring
  have hE0 : 0 ≤ t ^ (-(1 / 2 - α)) := Real.rpow_nonneg ht0.le _
  calc |∑ x ∈ S, latticeGaussian σ t x y * u x| = |∑ x ∈ S, f x * u x| := rfl
    _ ≤ ((3 : ℝ) ^ K) ^ (α - 1) * M +
          ∑ k ∈ range K, 6 * Kσ * L₀ / Real.sqrt t * ((3 : ℝ) ^ k * δ k) :=
        hmain.trans (add_le_add hT1 (Finset.sum_le_sum hT2))
    _ = ((3 : ℝ) ^ K) ^ (α - 1) * M +
          6 * Kσ * L₀ / Real.sqrt t * ∑ k ∈ range K, (3 : ℝ) ^ k * δ k := by
        rw [Finset.mul_sum]
    _ ≤ 3 * t ^ (-(1 / 2 - α)) * M +
          6 * Kσ * L₀ / Real.sqrt t * (3 * t ^ α / 2 + t ^ α / (q - 1)) := by
        gcongr
    _ = 3 * M * t ^ (-(1 / 2 - α)) +
          6 * Kσ * L₀ * (3 / 2 + 1 / (q - 1)) * (t ^ α / Real.sqrt t) := by
        field_simp
    _ = (3 * M + 6 * Kσ * L₀ * (3 / 2 + 1 / (q - 1))) * t ^ (-(1 / 2 - α)) := by
        rw [hE2]
        ring

end Rigidity.Green
