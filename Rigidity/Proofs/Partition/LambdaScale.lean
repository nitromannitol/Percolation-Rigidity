import Rigidity.Proofs.Partition.LambdaTail

/-!
# The average of powers of partition sizes above a minimal scale

Armstrong and Dario, Proposition 2.4 (the first bound in its conclusion), proved by counting bad
cubes instead of by the independence of local partitions: for every `τ ∈ ℕ` there are a
constant `C` and a random scale `M` with a stretched-exponential moment such that, whenever
`M < 3ᵐ`, `∑_{x ∈ Q_m} 3^{τ n(x)} ≤ C 3^{d m}`, where `Q_m` is the triadic cube of scale `m`
centred at the origin and `n(x)` is the scale of the partition cube of `x`.

Let `J = ⌊m / K⌋`, `K = 2 (d + τ + 1)`. Bad cubes of scale at least `J` near `Q_m` are excluded by
a union bound. For `j0 ≤ j < J`, at most `3^{e_j}` bad cubes of scale `j`, `e_j = d (m - j) -
(τ + 1)(j + 1)`, occur in each of the `3ᵈ` residue classes, outside an event of probability at most
`exp(-3^{e_j})`; scales below `j0` are counted deterministically.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The cube of scale `m` centred at the origin. -/
def originCube (d m : ℕ) : TriadicCube d := ⟨m, 0⟩

open scoped Classical in
/-- **The deterministic count.** If no bad cube of scale at least `J ≤ m` is near the cube of
scale `m` centred at the origin, and for `j0 ≤ j < J` every residue class has fewer than `3^{e_j}`
bad cubes of scale `j` near it, `e_j = d (m - j) - (τ + 1)(j + 1)`, then
`∑_{x ∈ Q_m} 3^{τ n(x)} ≤ (j0 · 575ᵈ · 3^{τ j0} + 69ᵈ) 3^{d m}`. -/
theorem sum_pow_scale_le_of_counts {ω : Configuration d} (hP : PartitionEvent ω)
    (m J j0 τ : ℕ) (hJm : J ≤ m)
    (hexp : ∀ j < J, (τ + 1) * (j + 1) + d * j ≤ d * m)
    (hfar : ∀ T : TriadicCube d, J ≤ T.scale → T ∉ TriadicCube.goodCubes ω →
      ∀ x ∈ (originCube d m).vertices, ¬ ∀ i, |x i - T.center i| ≤ 11 * T.side)
    (hmid : ∀ j, j0 ≤ j → j < J → ∀ r,
      classBadCount ω m j r < 3 ^ (d * (m - j) - (τ + 1) * (j + 1))) :
    ∑ x ∈ (originCube d m).toIntegerCube.vertices, (3 : ℝ) ^ (τ * (partitionCube ω x).scale) ≤
      ((j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d) * 3 ^ (d * m) := by
  refine (sum_pow_scale_partitionCube_le hP m J τ hfar).trans ?_
  set g : ℕ → ℝ := fun j => if j < j0 then 575 ^ d * 3 ^ (τ * j0) * 3 ^ (d * m)
    else 69 ^ d * 3 ^ (d * m) * (1 / 3) ^ (j + 1) with hgdef
  have hterm : ∀ j ∈ Finset.range J, (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
      (((nearIndices d m j).filter
        fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card : ℝ) ≤ g j := by
    intro j hj
    have hjJ := Finset.mem_range.1 hj
    have hjm : j ≤ m := by omega
    have h3j : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
    have hA : 22 * (3 : ℝ) ^ j + 1 ≤ 23 * 3 ^ j := by linarith
    have hpowm : (3 : ℝ) ^ j * 3 ^ (m - j) = 3 ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' hjm]
    by_cases hj0 : j < j0
    · rw [hgdef]
      simp only [if_pos hj0]
      have hN : (((nearIndices d m j).filter
          fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card : ℝ) ≤
          (25 * (3 : ℝ) ^ (m - j)) ^ d := by
        have h1 : (((nearIndices d m j).filter
            fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card : ℝ) ≤
            (nearIndices d m j).card := by exact_mod_cast Finset.card_filter_le _ _
        rw [card_nearIndices] at h1
        refine h1.trans ?_
        have h3 : (1 : ℝ) ≤ 3 ^ (m - j) := one_le_pow₀ (by norm_num)
        gcongr
        linarith
      have hτ : (3 : ℝ) ^ (τ * (j + 1)) ≤ 3 ^ (τ * j0) :=
        pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hj0)
      calc (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
            (((nearIndices d m j).filter
              fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card : ℝ)
          ≤ 3 ^ (τ * j0) * (23 * 3 ^ j) ^ d * (25 * (3 : ℝ) ^ (m - j)) ^ d := by
            gcongr
        _ = 575 ^ d * 3 ^ (τ * j0) * 3 ^ (d * m) := by
            have h : (3 : ℝ) ^ (d * m) = ((3 : ℝ) ^ j) ^ d * ((3 : ℝ) ^ (m - j)) ^ d := by
              rw [pow_mul', ← hpowm, mul_pow]
            rw [h, show (575 : ℝ) = 23 * 25 by norm_num, mul_pow, mul_pow, mul_pow]
            ring
    · rw [hgdef]
      simp only [if_neg hj0]
      have hj0' : j0 ≤ j := not_lt.1 hj0
      set e := d * (m - j) - (τ + 1) * (j + 1) with hedef
      have hN : (((nearIndices d m j).filter
          fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card : ℝ) ≤
          3 ^ d * 3 ^ e := by
        rw [card_filter_bad_eq_sum_classBadCount]
        push_cast
        calc ∑ r : Fin d → Fin 3, (classBadCount ω m j r : ℝ)
            ≤ ∑ _r : Fin d → Fin 3, (3 : ℝ) ^ e :=
              Finset.sum_le_sum fun r _ => by
                have := hmid j hj0' hjJ r
                exact_mod_cast this.le
          _ = 3 ^ d * 3 ^ e := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                Fintype.card_fin, nsmul_eq_mul]
              push_cast
              ring
      have hexpj := hexp j hjJ
      have hsum : τ * (j + 1) + d * j + e + (j + 1) = d * m := by
        have h1 : d * (m - j) + d * j = d * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hjm]
        have h2 : τ * (j + 1) + (j + 1) = (τ + 1) * (j + 1) := by ring
        have hYX : (τ + 1) * (j + 1) ≤ d * (m - j) := by linarith
        have he : e + (τ + 1) * (j + 1) = d * (m - j) := Nat.sub_add_cancel hYX
        linarith
      have hpow : (3 : ℝ) ^ (τ * (j + 1)) * (3 ^ j) ^ d * 3 ^ e =
          3 ^ (d * m) * (1 / 3) ^ (j + 1) := by
        rw [← pow_mul, ← pow_add, ← pow_add, one_div, inv_pow, ← hsum]
        rw [pow_add (3 : ℝ) (τ * (j + 1) + d * j + e), mul_assoc, mul_inv_cancel₀ (by positivity),
          mul_one]
        ring_nf
      calc (3 : ℝ) ^ (τ * (j + 1)) * (22 * (3 : ℝ) ^ j + 1) ^ d *
            (((nearIndices d m j).filter
              fun ι => (⟨j, ι⟩ : TriadicCube d) ∉ TriadicCube.goodCubes ω).card : ℝ)
          ≤ 3 ^ (τ * (j + 1)) * (23 * 3 ^ j) ^ d * (3 ^ d * 3 ^ e) := by gcongr
        _ = 69 ^ d * ((3 : ℝ) ^ (τ * (j + 1)) * (3 ^ j) ^ d * 3 ^ e) := by
            rw [mul_pow, show (69 : ℝ) = 23 * 3 by norm_num, mul_pow]
            ring
        _ = 69 ^ d * 3 ^ (d * m) * (1 / 3) ^ (j + 1) := by rw [hpow]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  set A : ℝ := 575 ^ d * 3 ^ (τ * j0) * 3 ^ (d * m) with hAdef
  set B : ℕ → ℝ := fun j => 69 ^ d * 3 ^ (d * m) * (1 / 3) ^ (j + 1) with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : ∀ j, 0 ≤ B j := fun j => by positivity
  have hg : ∀ j, g j ≤ (if j < j0 then A else 0) + B j := by
    intro j
    rw [hgdef]
    by_cases h : j < j0
    · simp only [if_pos h]
      linarith [hB0 j]
    · simp only [if_neg h, zero_add, hBdef, le_refl]
  have hite : ∑ j ∈ Finset.range J, (if j < j0 then A else 0) ≤ j0 * A := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range J).filter (fun j => j < j0)).card ≤ j0 := by
      calc ((Finset.range J).filter (fun j => j < j0)).card ≤ (Finset.range j0).card :=
            Finset.card_le_card fun j hj => Finset.mem_range.2 (Finset.mem_filter.1 hj).2
        _ = j0 := Finset.card_range j0
    have hcard' : (((Finset.range J).filter (fun j => j < j0)).card : ℝ) ≤ j0 := by
      exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right hcard' hA0
  have hgeom : ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ (j + 1) ≤ 1 := by
    have h := geom_sum_eq (show (1 / 3 : ℝ) ≠ 1 by norm_num) J
    have h' : ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ (j + 1) =
        (1 / 3) * ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h', h]
    have hpos : (0 : ℝ) ≤ (1 / 3) ^ J := by positivity
    have hle : ((1 : ℝ) / 3) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : ((1 : ℝ) / 3) * (((1 / 3) ^ J - 1) / (1 / 3 - 1)) = (1 - (1 / 3) ^ J) / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  have hBsum : ∑ j ∈ Finset.range J, B j ≤ 69 ^ d * 3 ^ (d * m) := by
    rw [hBdef]
    simp only
    rw [← Finset.mul_sum]
    have h69 : (0 : ℝ) ≤ 69 ^ d * 3 ^ (d * m) := by positivity
    calc 69 ^ d * 3 ^ (d * m) * ∑ j ∈ Finset.range J, (1 / 3 : ℝ) ^ (j + 1)
        ≤ 69 ^ d * 3 ^ (d * m) * 1 := mul_le_mul_of_nonneg_left hgeom h69
      _ = 69 ^ d * 3 ^ (d * m) := mul_one _
  calc ∑ j ∈ Finset.range J, g j
      ≤ ∑ j ∈ Finset.range J, ((if j < j0 then A else 0) + B j) := Finset.sum_le_sum fun j _ => hg j
    _ = ∑ j ∈ Finset.range J, (if j < j0 then A else 0) + ∑ j ∈ Finset.range J, B j :=
        Finset.sum_add_distrib
    _ ≤ j0 * A + 69 ^ d * 3 ^ (d * m) := add_le_add hite hBsum
    _ = ((j0 : ℝ) * 575 ^ d * 3 ^ (τ * j0) + 69 ^ d) * 3 ^ (d * m) := by
        rw [hAdef]
        ring

end Rigidity.Percolation
