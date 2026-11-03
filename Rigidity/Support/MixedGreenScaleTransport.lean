import LatticeProb.Prob.Percolation.LatticeClusterBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Distance and decay transport for lattice Green estimates

These deterministic estimates transport Euclidean bounds to the lattice distance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LatticeProb.Percolation
open scoped BigOperators

namespace Rigidity.Support

/-- The lattice ℓ¹ distance is at most the dimension times Euclidean distance. -/
theorem latticeL1Dist_le_dim_mul_euclidean {d : ℕ} (x y : Vertex d) :
    (latticeL1Dist x y : ℝ) ≤ (d : ℝ) *
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ := by
  unfold latticeL1Dist
  push_cast
  calc
    ∑ i : Fin d, |(x i : ℝ) - (y i : ℝ)| ≤
        ∑ _i : Fin d, ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have h := PiLp.norm_apply_le
        (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y) i
      change |(x i : ℝ) - (y i : ℝ)| ≤ _ at h
      exact h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Transfer the Euclidean decay power to a comparable lattice distance. -/
theorem decay_rpow_le_lattice (d : ℕ) (hd : 2 ≤ d) (δ₀ δ D L : ℝ)
    (hδ₀ : 0 < δ₀) (hδhalf : δ₀ ≤ 1 / 2) (hδ : δ₀ ≤ δ)
    (hD : 0 < D) (hL : 1 ≤ L) (hLD : L ≤ (d : ℝ) * D) :
    Real.rpow D (-(d : ℝ) + δ₀) ≤ (d : ℝ) ^ d / Real.rpow L ((d : ℝ) - δ) := by
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let q : ℝ := (d : ℝ) - δ₀
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hqd : q ≤ (d : ℝ) := by dsimp [q]; linarith
  have hpow : (d : ℝ) ^ q ≤ (d : ℝ) ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hqd
  have hdist : ((d : ℝ) * D) ^ (-q) ≤ L ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hLpos hLD (neg_nonpos.mpr hq)
  have hident : D ^ (-q) = (d : ℝ) ^ q * ((d : ℝ) * D) ^ (-q) := by
    rw [Real.mul_rpow hdpos.le hD.le, Real.rpow_neg hdpos.le]
    have hne : (d : ℝ) ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hdpos q)
    field_simp
  have htarget : L ^ (-q) ≤ L ^ (-(d : ℝ) + δ) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    dsimp [q]
    linarith
  have hnonneg : 0 ≤ L ^ (-q) := Real.rpow_nonneg hLpos.le _
  have hlarge : 0 ≤ L ^ (-(d : ℝ) + δ) := Real.rpow_nonneg hLpos.le _
  change D ^ (-(d : ℝ) + δ₀) ≤ (d : ℝ) ^ d / L ^ ((d : ℝ) - δ)
  have hexp : -(d : ℝ) + δ₀ = -q := by dsimp [q]; ring
  rw [hexp, hident]
  calc
    _ ≤ (d : ℝ) ^ q * L ^ (-q) :=
      mul_le_mul_of_nonneg_left hdist (Real.rpow_nonneg hdpos.le _)
    _ ≤ (d : ℝ) ^ d * L ^ (-q) := mul_le_mul_of_nonneg_right hpow hnonneg
    _ ≤ (d : ℝ) ^ d * L ^ (-(d : ℝ) + δ) :=
      mul_le_mul_of_nonneg_left htarget (by positivity)
    _ = _ := by
      have he : -(d : ℝ) + δ = -((d : ℝ) - δ) := by ring
      rw [he, Real.rpow_neg hLpos.le, div_eq_mul_inv]

/-- A squared local-gradient estimate yields the required Euclidean decay rate. -/
theorem abs_le_of_squared_gradient_bound (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ : 0 < δ)
    (D m K CF N b : ℝ) (hD : 1 ≤ D) (hm : 0 ≤ m)
    (hmD : m ≤ Real.rpow D (min δ (1 / 2) / (2 * (d : ℝ))))
    (hK : 0 < K) (hCF : 0 < CF) (hN : 0 ≤ N)
    (hNbound : N ≤ CF * Real.rpow D (1 - (d : ℝ) + min δ (1 / 2) / 4))
    (hgrad : b ^ 2 ≤ K * m ^ d / (D / 4) ^ 2 * N ^ 2) :
    |b| ≤ 4 * Real.sqrt K * CF * Real.rpow D (-(d : ℝ) + min δ (1 / 2)) := by
  let δ₀ : ℝ := min δ (1 / 2)
  let α : ℝ := δ₀ / (2 * (d : ℝ))
  let η : ℝ := δ₀ / 4
  change m ≤ D ^ α at hmD
  change N ≤ CF * D ^ (1 - (d : ℝ) + η) at hNbound
  change |b| ≤ 4 * Real.sqrt K * CF * D ^ (-(d : ℝ) + δ₀)
  have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
  have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : 0 < (d : ℝ) := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hα : α * (d : ℝ) = δ₀ / 2 := by
    dsimp [α]
    field_simp
  have hmpow : m ^ d ≤ D ^ (δ₀ / 2) := by
    have h := pow_le_pow_left₀ hm hmD d
    rw [← Real.rpow_natCast (D ^ α) d, ← Real.rpow_mul hDpos.le, hα] at h
    exact h
  have hNpow : N ^ 2 ≤ (CF * D ^ (1 - (d : ℝ) + η)) ^ 2 := by
    apply (sq_le_sq₀ hN (by positivity)).2 hNbound
  have hgrad' : b ^ 2 ≤ K * D ^ (δ₀ / 2) / (D / 4) ^ 2 *
      (CF * D ^ (1 - (d : ℝ) + η)) ^ 2 := by
    calc
      _ ≤ K * m ^ d / (D / 4) ^ 2 * N ^ 2 := hgrad
      _ ≤ _ := by gcongr
  have hid : K * D ^ (δ₀ / 2) / (D / 4) ^ 2 *
      (CF * D ^ (1 - (d : ℝ) + η)) ^ 2 =
      16 * K * CF ^ 2 * D ^ (-2 * (d : ℝ) + δ₀) := by
    have hr : D ^ (δ₀ / 2) * (D ^ (1 - (d : ℝ) + η)) ^ 2 / D ^ 2 =
        D ^ (-2 * (d : ℝ) + δ₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le, ← Real.rpow_add hDpos,
        ← Real.rpow_natCast D 2, ← Real.rpow_sub hDpos]
      congr 1
      dsimp [η]
      ring
    have heq : (D / 4) ^ 2 = D ^ 2 / 16 := by ring
    rw [heq]
    calc
      _ = 16 * K * CF ^ 2 *
          (D ^ (δ₀ / 2) * (D ^ (1 - (d : ℝ) + η)) ^ 2 / D ^ 2) := by ring
      _ = _ := by rw [hr]
  have hpow : D ^ (-2 * (d : ℝ) + δ₀) ≤ D ^ (-2 * (d : ℝ) + 2 * δ₀) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hsqrt : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK.le
  have hrpow : (D ^ (-(d : ℝ) + δ₀)) ^ 2 = D ^ (-2 * (d : ℝ) + 2 * δ₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le]
    congr 1
    ring
  have hbound : b ^ 2 ≤ (4 * Real.sqrt K * CF * D ^ (-(d : ℝ) + δ₀)) ^ 2 := by
    calc
      _ ≤ K * D ^ (δ₀ / 2) / (D / 4) ^ 2 *
          (CF * D ^ (1 - (d : ℝ) + η)) ^ 2 := hgrad'
      _ = 16 * K * CF ^ 2 * D ^ (-2 * (d : ℝ) + δ₀) := hid
      _ ≤ 16 * K * CF ^ 2 * D ^ (-2 * (d : ℝ) + 2 * δ₀) := by gcongr
      _ = _ := by rw [← hrpow]; nlinarith [hsqrt]
  exact (sq_le_sq₀ (abs_nonneg b) (by positivity)).mp (by simpa only [sq_abs] using hbound)

end Rigidity.Support
