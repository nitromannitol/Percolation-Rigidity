import Rigidity.Percolation.Pisztora.GoodSubcube
import Rigidity.Percolation.IntegerCubeUniformCoalescenceRadius
import Rigidity.Percolation.SlabRadiusCrossing
import Rigidity.Percolation.SlabTriadicPartition

/-!
# Exponential estimates for a single cube

From uniform slab connectivity, every integer cube has a crossing component joining all its
open paths of large `ℓ¹`-radius, except with probability exponentially small in the radius
scale (`crossing_fail_le`). At the two overlap scales, cubes of side `20t + 1` and `10t + 1`
with the radius thresholds `8t` and `4t`, the failure probability is at most `A exp(-κ t)`,
uniformly in the cube (`exists_overlap_crossing_bounds`).
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open scoped ENNReal

variable {d : ℕ}

/-- Polynomial factors are absorbed into exponentials with half the rate. -/
theorem exists_pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
      (t + 1) ^ k * Real.exp (-(c * t)) ≤ K * Real.exp (-(c / 2 * t)) := by
  refine ⟨k.factorial * (2 / c) ^ k * Real.exp (c / 2), by positivity, fun t ht => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (x := c / 2 * (t + 1)) (by positivity) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hfac, mul_pow] at h1
  have h2 : (t + 1) ^ k ≤ k.factorial * (2 / c) ^ k * Real.exp (c / 2 * (t + 1)) := by
    have hck : (0 : ℝ) < (c / 2) ^ k := by positivity
    have : (t + 1) ^ k = (c / 2) ^ k * (t + 1) ^ k * (2 / c) ^ k := by
      rw [mul_comm ((c / 2) ^ k), mul_assoc, ← mul_pow]
      field_simp
      simp
    rw [this]
    calc (c / 2) ^ k * (t + 1) ^ k * (2 / c) ^ k
        ≤ Real.exp (c / 2 * (t + 1)) * k.factorial * (2 / c) ^ k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  calc (t + 1) ^ k * Real.exp (-(c * t))
      ≤ k.factorial * (2 / c) ^ k * Real.exp (c / 2 * (t + 1)) * Real.exp (-(c * t)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = k.factorial * (2 / c) ^ k * Real.exp (c / 2) * Real.exp (-(c / 2 * t)) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc _ (Real.exp (c / 2)), ← Real.exp_add]
        congr 2
        ring

/-- The slab parameters supplied by uniform slab connectivity. -/
def SlabParams (d : ℕ) (p : unitInterval) (width : ℕ) (ρ c : ℝ) : Prop :=
  0 < width ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧ 0 < c ∧ c ≤ ρ ∧ c ≤ (p : ℝ) * ρ ^ (2 * d) ∧
    c ≤ (p : ℝ) * ((p : ℝ) * ρ) ∧
    ∀ U : IntegerCube d, ∀ a : Fin d, ∀ k : ℕ, (k + 1) * width ≤ U.size →
      ∀ x ∈ U.slab a width k, ∀ y ∈ U.slab a width k,
        ρ ≤ (latticeBondLaw d p).real {ω | (openIn ω (U.slab a width k)).Reachable x y}

/-- Uniform slab connectivity supplies slab parameters. -/
theorem UniformCubeSlabConnectivity.exists_slabParams {p : unitInterval} (j : Fin d)
    (hp : 0 < (p : ℝ)) (h : UniformCubeSlabConnectivity d p) :
    ∃ width ρ c, SlabParams d p width ρ c := by
  obtain ⟨width, hwidth, ρ, c, hρ, hρ₁, hc, hcρ, hcroot, hctwo, hslab⟩ := h.exists_parameters j hp
  exact ⟨width, ρ, c, hwidth, hρ.le, hρ₁, hc, hcρ, hcroot, hctwo, hslab⟩

/-- **Crossing with joined large paths.** Every integer cube has a crossing component joining all
its open paths of `ℓ¹`-radius larger than `radius / 10`, except with probability at most
`(d + 2) (size + 1)^{2d+1} exp(-c (radius / (10 d width) - 1))`. -/
theorem crossing_fail_le {p : unitInterval} {width : ℕ} {ρ c : ℝ}
    (hP : SlabParams d p width ρ c) (hd : 0 < d) (j i : Fin d) (hij : i ≠ j)
    (T : IntegerCube d) (radius : ℕ) (hradius : 10 * d * width ≤ radius)
    (hfit : radius < 10 * d * T.size) :
    (latticeBondLaw d p) {ω | ¬ HasCrossingComponentConnectingPaths ω T.vertices
      (fun t => ↑(T.lowerFace t)) (fun t => ↑(T.upperFace t))
      (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
        (radius : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤
      ENNReal.ofReal ((d + 2) * ((T.size : ℝ) + 1) ^ (2 * d + 1) *
        Real.exp (-(c * ((radius / (10 * d * width) - 1 : ℕ) : ℝ)))) := by
  obtain ⟨hw, hρ, hρ₁, hc, hcρ, hcroot, hctwo, hslab⟩ := hP
  have h := T.measureReal_no_crossing_connecting_radius_le_scaled_exp hd j i hij width radius hw
    hradius hfit p ρ c hρ hρ₁ hc hcρ hcroot hctwo (fun t k hk x hx y hy => hslab T t k hk x hx y hy)
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity)))
  have hface : ((T.lowerFace j).card : ℝ) ≤ (T.size : ℝ) ^ d := by
    have := Finset.card_filter_le T.vertices (fun x => x j = T.corner j)
    rw [IntegerCube.card_vertices] at this
    exact_mod_cast this
  rw [IntegerCube.card_vertices]
  push_cast
  set s : ℝ := (T.size : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  have h1 : s ^ d ≤ (s + 1) ^ (2 * d + 1) :=
    (pow_le_pow_left₀ hs0 (by linarith) d).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have h2 : s * (s ^ d) ^ 2 ≤ (s + 1) ^ (2 * d + 1) := by
    rw [← pow_mul, show (2 * d + 1) = d * 2 + 1 by ring, pow_succ, mul_comm]
    exact mul_le_mul (pow_le_pow_left₀ hs0 (by linarith) _) (by linarith) hs0 (by positivity)
  have h3 : (1 : ℝ) ≤ (s + 1) ^ (2 * d + 1) := one_le_pow₀ (by linarith)
  have hd' : (0 : ℝ) ≤ d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hd']

/-- The natural-number scale of the crossing bound is at least the real ratio minus two. -/
theorem ratio_sub_one_ge (r q : ℕ) (hq : 0 < q) :
    (r : ℝ) / q - 2 ≤ ((r / q - 1 : ℕ) : ℝ) := by
  have h1 : ((r / q : ℕ) : ℝ) * q ≤ r := by exact_mod_cast Nat.div_mul_le_self r q
  have h2 : (r : ℝ) < ((r / q : ℕ) : ℝ) * q + q := by
    exact_mod_cast Nat.lt_div_mul_add (a := r) hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (r : ℝ) / q < ((r / q : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hq']
    linarith
  by_cases h : 1 ≤ r / q
  · rw [Nat.cast_sub h]
    push_cast
    linarith
  · push Not at h
    have : r / q = 0 := Nat.lt_one_iff.mp h
    rw [this] at h3 ⊢
    simp only [Nat.zero_sub, Nat.cast_zero]
    push_cast at h3
    linarith

/-- **Uniform crossing bounds at the overlap scales.** There are `A, κ > 0` and `t₀` such that every
cube of side `20t + 1` (resp. `10t + 1`), `t ≥ t₀`, has a crossing component joining its open paths
of `ℓ¹`-radius larger than `8t/10` (resp. `4t/10`), except with probability at most `A exp(-κ t)`. -/
theorem exists_overlap_crossing_bounds {p : unitInterval} {width : ℕ} {ρ c : ℝ}
    (hP : SlabParams d p width ρ c) (hd : 0 < d) (j i : Fin d) (hij : i ≠ j) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ T : IntegerCube d,
      ∀ (s r : ℕ), (T.size = s) → (s = 20 * t + 1 ∧ r = 8 * t ∨ s = 10 * t + 1 ∧ r = 4 * t) →
        (latticeBondLaw d p) {ω | ¬ HasCrossingComponentConnectingPaths ω T.vertices
          (fun a => ↑(T.lowerFace a)) (fun a => ↑(T.upperFace a))
          (fun n γ => ∀ z : Vertex d, ∃ a : Fin (n + 1),
            (r : ℤ) < 10 * ∑ k, |γ a k - z k|)} ≤ ENNReal.ofReal (A * Real.exp (-(κ * t))) := by
  obtain ⟨hw, -, -, hc, -⟩ := id hP
  set q : ℕ := 10 * d * width with hq
  have hq0 : 0 < q := by positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  set κ₀ : ℝ := c * 4 / q with hκ₀
  have hκ₀pos : 0 < κ₀ := by positivity
  obtain ⟨K, hK, hKb⟩ := exists_pow_mul_exp_neg_le hκ₀pos (2 * d + 1)
  refine ⟨(d + 2) * Real.exp (2 * c) * 21 ^ (2 * d + 1) * K, κ₀ / 2, by positivity, by positivity,
    q, fun t ht T s r hsize hsr => ?_⟩
  have ht0 : 0 < t := by
    have : 0 < q := hq0
    omega
  have hr : q ≤ r := by rcases hsr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hfit : r < 10 * d * T.size := by
    rw [hsize]
    have : 1 ≤ d := hd
    rcases hsr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> nlinarith
  refine (crossing_fail_le hP hd j i hij T r hr hfit).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hsize]
  have hs : (s : ℝ) + 1 ≤ 21 * ((t : ℝ) + 1) := by
    rcases hsr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> push_cast <;> linarith
  have hr4 : (4 * t : ℝ) ≤ r := by
    rcases hsr with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> push_cast <;> linarith
  have hexp : Real.exp (-(c * ((r / q - 1 : ℕ) : ℝ))) ≤
      Real.exp (2 * c) * Real.exp (-(κ₀ * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := ratio_sub_one_ge r q hq0
    have h2 : κ₀ * t ≤ c * (r / q) := by
      have : (4 * t : ℝ) / q ≤ (r : ℝ) / q := div_le_div_of_nonneg_right hr4 hq'.le
      calc κ₀ * t = c * ((4 * t : ℝ) / q) := by rw [hκ₀]; ring
        _ ≤ c * (r / q) := mul_le_mul_of_nonneg_left this hc.le
    nlinarith
  have hpow : ((s : ℝ) + 1) ^ (2 * d + 1) ≤ 21 ^ (2 * d + 1) * ((t : ℝ) + 1) ^ (2 * d + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hs _
  have hKt := hKb t (by positivity)
  calc ((d : ℝ) + 2) * ((s : ℝ) + 1) ^ (2 * d + 1) * Real.exp (-(c * ((r / q - 1 : ℕ) : ℝ)))
      ≤ ((d : ℝ) + 2) * (21 ^ (2 * d + 1) * ((t : ℝ) + 1) ^ (2 * d + 1)) *
          (Real.exp (2 * c) * Real.exp (-(κ₀ * t))) := by gcongr
    _ = ((d : ℝ) + 2) * Real.exp (2 * c) * 21 ^ (2 * d + 1) *
          (((t : ℝ) + 1) ^ (2 * d + 1) * Real.exp (-(κ₀ * t))) := by ring
    _ ≤ ((d : ℝ) + 2) * Real.exp (2 * c) * 21 ^ (2 * d + 1) *
          (K * Real.exp (-(κ₀ / 2 * t))) := by gcongr
    _ = _ := by ring

end Rigidity.Percolation
