/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/WeakNorm/MultiscalePoincareCube.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Support.Lattice.Membership
import Rigidity.Vendor.LHCH.Support.WeakNorm.MultiscalePoincare

/-!
# The multiscale Poincaré inequality on any triadic cube

On `P + {0, …, 3^n}^d`, the mean square of
`u` minus its vertex-weighted mean is at most `C (Σ_{k≤n} 3^k blockSq_k(∇u)^{1/2} +
cubeAvg(|∇u|²)^{1/2})²`: `exists_vertexNorm_le_multiscale` translated to the corner `P` (block
means, face-weighted averages and vertex weights are translation invariant) and made unweighted (`w
≥ 2^{-d}`).
-/

open LatticeProb

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-- The vertex-weighted mean `L^{-d} Σ_{x ∈ Q} w_Q(x) u(x)` of `u` on `Q = P + {0, …, L}^d`. -/
def vertexMean (P : Site d) (L : ℕ) (u : Site d → ℝ) : ℝ :=
  ((L : ℝ) ^ d)⁻¹ * ∑ x ∈ latticeCube P L, vertexWeight L (x - P) * u x

/-- A sum over the cube `P + {0, …, L}^d` is the sum over `{0, …, L}^d` of the translated
summand. -/
theorem sum_latticeCube_translate (P : Site d) (L : ℕ) (f : Site d → ℝ) :
    ∑ x ∈ latticeCube P L, f x = ∑ y ∈ latticeCube 0 L, f (P + y) := by
  refine Finset.sum_nbij' (fun x => x - P) (fun y => P + y) (fun x hx => ?_) (fun y hy => ?_)
    (fun x _ => by simp) (fun y _ => by simp) (fun x _ => by simp)
  · rw [mem_latticeCube_iff_coord] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    simp only [Pi.sub_apply, Pi.zero_apply, zero_add]
    constructor <;> omega
  · rw [mem_latticeCube_iff_coord] at hy ⊢
    intro i
    obtain ⟨h1, h2⟩ := hy i
    simp only [Pi.add_apply, Pi.zero_apply, zero_add] at h1 h2 ⊢
    constructor <;> omega

/-- The block mean on a translated cube is the block mean of the translated field. -/
theorem blockMean_translate (P z : Site d) (L : ℕ) (F : Edge d → ℝ) :
    blockMean (P + z) L F = blockMean z L (fun e => F (P + e.1, e.2)) := by
  funext j
  unfold blockMean
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, sum_edgesOf_translate P z L]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [faceWeight_translate]

/-- The face-weighted average on a translated cube is that of the translated function. -/
theorem cubeAvg_translate (P z : Site d) (L : ℕ) (f : Edge d → ℝ) :
    cubeAvg (P + z) L f = cubeAvg z L (fun e => f (P + e.1, e.2)) := by
  unfold cubeAvg
  congr 1
  rw [sum_edgesOf_translate P z L]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [faceWeight_translate]

/-- The mean square of the block means on a translated cube is that of the translated field. -/
theorem blockSq_translate (P : Site d) (n k : ℕ) (G : Edge d → ℝ) :
    blockSq P n k G = blockSq 0 n k (fun e => G (P + e.1, e.2)) := by
  have hk : ∀ y ∈ triadicIndex d (n - k),
      dotProduct (blockMean (triadicCorner P k y) (3 ^ k) G)
        (blockMean (triadicCorner P k y) (3 ^ k) G) =
      dotProduct (blockMean (triadicCorner 0 k y) (3 ^ k) fun e => G (P + e.1, e.2))
        (blockMean (triadicCorner 0 k y) (3 ^ k) fun e => G (P + e.1, e.2)) := by
    intro y _
    have h : triadicCorner P k y = P + triadicCorner 0 k y := by
      simp only [triadicCorner, zero_add]
    rw [h, blockMean_translate]
  unfold blockSq blockPair
  rw [Finset.sum_congr rfl hk]

/-- The vertex weights of `{0, …, N}^d` sum to `N^d`. -/
theorem sum_vertexWeight_eq (N : ℕ) (hN : 0 < N) :
    ∑ y ∈ latticeCube (0 : Site d) N, vertexWeight N y = (N : ℝ) ^ d := by
  have h := sum_torusBox_reflectFun_mul N hN (fun _ : Site d => (1 : ℝ)) fun _ => 1
  simp only [reflectFun, mul_one, Finset.sum_const, nsmul_eq_mul] at h
  have hc : ((torusBox d N).card : ℝ) = (2 * (N : ℝ)) ^ d := by
    simp only [torusBox, Fintype.card_piFinset, Int.card_Ico, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    have h2 : (2 * (N : ℤ) - 0).toNat = 2 * N := by omega
    rw [h2]
    push_cast
    rfl
  refine mul_left_cancel₀ (pow_ne_zero d (two_ne_zero (α := ℝ))) ?_
  rw [← h, hc, mul_pow]

/-- The vertex weights are at least `2^{-d}`. -/
theorem le_vertexWeight (N : ℕ) (y : Site d) : (1 / 2 : ℝ) ^ d ≤ vertexWeight N y := by
  unfold vertexWeight
  refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
  calc _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
    _ = d := by simp

/-- **The multiscale Poincaré inequality on any triadic cube**:
`exists_vertexNorm_le_multiscale` translated to the corner `P` and
applied to `u − vertexMean`, in unweighted form (`w_Q ≥ 2^{-d}`). -/
theorem exists_sum_sq_sub_vertexMean_le_multiscale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Site d) (n : ℕ) (u : Site d → ℝ),
      (((3 : ℝ) ^ n) ^ d)⁻¹ * ∑ x ∈ latticeCube P (3 ^ n), (u x - vertexMean P (3 ^ n) u) ^ 2 ≤
        C * (∑ k ∈ Finset.range (n + 1),
              (3 : ℝ) ^ k * Real.sqrt (blockSq P n k (fun e => u e.tgt - u e.src)) +
            Real.sqrt (cubeAvg P (3 ^ n) (fun e => (u e.tgt - u e.src) ^ 2))) ^ 2 := by
  obtain ⟨C, hC, hmain⟩ := exists_vertexNorm_le_multiscale (d := d)
  refine ⟨2 ^ d * C ^ 2, by positivity, fun P n u => ?_⟩
  have hN : 0 < 3 ^ n := by positivity
  have hNr : (((3 ^ n : ℕ) : ℝ)) = (3 : ℝ) ^ n := by push_cast; rfl
  have hNd : (((3 : ℝ) ^ n) ^ d) ≠ 0 := by positivity
  have hsumw : ∑ y ∈ latticeCube (0 : Site d) (3 ^ n), vertexWeight (3 ^ n) y =
      ((3 : ℝ) ^ n) ^ d := by
    rw [sum_vertexWeight_eq _ hN, hNr]
  have hū : ∑ y ∈ latticeCube (0 : Site d) (3 ^ n), vertexWeight (3 ^ n) y * u (P + y) =
      ((3 : ℝ) ^ n) ^ d * vertexMean P (3 ^ n) u := by
    rw [vertexMean, sum_latticeCube_translate P, hNr]
    simp only [add_sub_cancel_left]
    field_simp
  set ū := vertexMean P (3 ^ n) u with hūdef
  set v : Site d → ℝ := fun y => u (P + y) - ū with hv
  have hmean : ∑ y ∈ latticeCube (0 : Site d) (3 ^ n), vertexWeight (3 ^ n) y * v y = 0 := by
    simp only [hv, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumw, hū]
    ring
  have h1 := hmain n v hmean
  have hG : (fun e : Edge d => v e.tgt - v e.src) =
      fun e : Edge d => (fun e : Edge d => u e.tgt - u e.src) (P + e.1, e.2) := by
    funext e
    simp only [hv, Edge.tgt, Edge.src, add_assoc]
    ring
  have hG2 : (fun e : Edge d => (v e.tgt - v e.src) ^ 2) =
      fun e : Edge d => (fun e : Edge d => (u e.tgt - u e.src) ^ 2) (P + e.1, e.2) := by
    funext e
    simp only [hv, Edge.tgt, Edge.src, add_assoc]
    ring
  have hbs : ∀ k, blockSq 0 n k (fun e : Edge d => v e.tgt - v e.src) =
      blockSq P n k (fun e => u e.tgt - u e.src) := fun k => by
    rw [blockSq_translate P n k]
    exact congrArg (blockSq 0 n k) hG
  have hca : cubeAvg 0 (3 ^ n) (fun e : Edge d => (v e.tgt - v e.src) ^ 2) =
      cubeAvg P (3 ^ n) (fun e => (u e.tgt - u e.src) ^ 2) := by
    have h := cubeAvg_translate P 0 (3 ^ n) (fun e : Edge d => (u e.tgt - u e.src) ^ 2)
    rw [add_zero] at h
    rw [h]
    exact congrArg (cubeAvg 0 (3 ^ n)) hG2
  simp only [hbs, hca] at h1
  set M := ∑ k ∈ Finset.range (n + 1),
      (3 : ℝ) ^ k * Real.sqrt (blockSq P n k (fun e => u e.tgt - u e.src)) +
    Real.sqrt (cubeAvg P (3 ^ n) (fun e => (u e.tgt - u e.src) ^ 2)) with hM
  have hM0 : 0 ≤ M := by positivity
  have h2 := (Real.sqrt_le_iff.1 h1).2
  have h3 : ∑ y ∈ latticeCube (0 : Site d) (3 ^ n), v y ^ 2 ≤
      2 ^ d * ∑ y ∈ latticeCube (0 : Site d) (3 ^ n), vertexWeight (3 ^ n) y * v y ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    have hw := le_vertexWeight (3 ^ n) y
    have h2d : (2 : ℝ) ^ d * (1 / 2) ^ d = 1 := by rw [← mul_pow]; norm_num
    calc v y ^ 2 = 2 ^ d * ((1 / 2) ^ d * v y ^ 2) := by rw [← mul_assoc, h2d, one_mul]
      _ ≤ 2 ^ d * (vertexWeight (3 ^ n) y * v y ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  have hK : 0 ≤ (((3 : ℝ) ^ n) ^ d)⁻¹ := by positivity
  rw [sum_latticeCube_translate P (3 ^ n) fun x => (u x - ū) ^ 2]
  calc _ = (((3 : ℝ) ^ n) ^ d)⁻¹ * ∑ y ∈ latticeCube (0 : Site d) (3 ^ n), v y ^ 2 := rfl
    _ ≤ (((3 : ℝ) ^ n) ^ d)⁻¹ * (2 ^ d * ∑ y ∈ latticeCube (0 : Site d) (3 ^ n),
          vertexWeight (3 ^ n) y * v y ^ 2) := mul_le_mul_of_nonneg_left h3 hK
    _ = 2 ^ d * ((((3 : ℝ) ^ n) ^ d)⁻¹ * ∑ y ∈ latticeCube (0 : Site d) (3 ^ n),
          vertexWeight (3 ^ n) y * v y ^ 2) := by ring
    _ ≤ 2 ^ d * (C * M) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end LatticeHC

end
