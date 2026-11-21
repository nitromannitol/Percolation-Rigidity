import Rigidity.Proofs.Percolation.PlanarGoodCube
import Rigidity.Proofs.Section5.VeryGoodProbability

/-!
# Stretched-exponential probability of good planar cubes

The polynomial number of strip crossings is absorbed into the exponential decay in the
square-root strip width.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Percolation

/-- The chosen integer strip width is within one of a hundredth of the square root. -/
theorem sqrt_le_meshWidth (N : ℕ) :
    Real.sqrt N ≤ 100 * (planarMeshWidth N : ℝ) + 100 := by
  have hNat : N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) :=
    Nat.sqrt_lt.mp (Nat.lt_succ_self _)
  have hSqrt : Real.sqrt N ≤ (Nat.sqrt N : ℝ) + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h : (N : ℝ) ≤ ((Nat.sqrt N : ℝ) + 1) * ((Nat.sqrt N : ℝ) + 1) := by
        exact_mod_cast hNat.le
      nlinarith
  have hmod := Nat.mod_lt (Nat.sqrt N) (by norm_num : 0 < 100)
  have hdiv := Nat.div_add_mod (Nat.sqrt N) 100
  have hNat' : Nat.sqrt N ≤ 100 * planarMeshWidth N + 99 := by
    dsimp [planarMeshWidth]
    omega
  have hR : (Nat.sqrt N : ℝ) ≤ 100 * (planarMeshWidth N : ℝ) + 99 := by
    exact_mod_cast hNat'
  linarith

/-- For radii at least one the square root is bounded by the radius. -/
theorem sqrt_nat_le_self (N : ℕ) (hN : 1 ≤ N) : Real.sqrt N ≤ N := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith

/-- Planar good-cube failure has a uniform stretched-exponential tail. -/
theorem goodSubcube_failure_bound (p : unitInterval) (hp : criticalProbability 2 < (p : ℝ)) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (N : ℕ),
      latticeBondLaw 2 p {ω | ¬ IsGoodSubcube ω x N} ≤
        ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ (1 / 2 : ℝ)))) := by
  obtain ⟨C₁, c₁, C₂, c₂, hC₁, hc₁, hC₂, hc₂, hraw⟩ := goodSubcube_failure_bound_raw p hp
  let a := min (c₁ / 100) c₂
  let K := 2 * C₁ * Real.exp c₁ + C₂
  let D := 9 + 216 * (2 / a) ^ 4
  let c := a / 2
  let C := max (K * D) (Real.exp (c * 100))
  have ha : 0 < a := lt_min (by positivity) hc₂
  have hK : 0 < K := by dsimp [K]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  refine ⟨C, c, hC, hc, fun x N => ?_⟩
  rw [← Real.sqrt_eq_rpow]
  by_cases hN : 10000 ≤ N
  · let t : ℝ := Real.sqrt N
    let r : ℝ := 2 * N + 1
    have ht : 0 ≤ t := Real.sqrt_nonneg _
    have hr : 1 ≤ r := by
      dsimp [r]
      have : (0 : ℝ) ≤ N := by positivity
      linarith
    have hwidth : t ≤ 100 * (planarMeshWidth N : ℝ) + 100 := sqrt_le_meshWidth N
    have hself : t ≤ N := sqrt_nat_le_self N (by omega)
    have ha₁ : a ≤ c₁ / 100 := min_le_left _ _
    have ha₂ : a ≤ c₂ := min_le_right _ _
    have he₁ : Real.exp (-(c₁ * (planarMeshWidth N : ℝ))) ≤
        Real.exp c₁ * Real.exp (-(a * t)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ha₁) ht]
    have he₂ : Real.exp (-(c₂ * (2 * N : ℕ))) ≤ Real.exp (-(a * t)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr ha₂) ht]
    have hfirst : (2 * r) * (C₁ * r * Real.exp (-(c₁ * (planarMeshWidth N : ℝ)))) ≤
        (2 * C₁ * Real.exp c₁) * r ^ 2 * Real.exp (-(a * t)) := by
      calc
        _ ≤ (2 * r) * (C₁ * r * (Real.exp c₁ * Real.exp (-(a * t)))) := by gcongr
        _ = _ := by ring
    have hsecond : C₂ * r * Real.exp (-(c₂ * (2 * N : ℕ))) ≤
        C₂ * r ^ 2 * Real.exp (-(a * t)) := by
      have hrr : r ≤ r ^ 2 := by nlinarith
      gcongr
    have hpoly : r ^ 2 * Real.exp (-(a * t)) ≤ D * Real.exp (-(c * t)) := by
      have h := Rigidity.Proofs.Section5.sq_mul_exp_le ha ht
      dsimp [r, t, D, c] at h ⊢
      rw [Real.sq_sqrt (Nat.cast_nonneg N)] at h
      exact h
    have hreal :
        (2 * r) * (C₁ * r * Real.exp (-(c₁ * (planarMeshWidth N : ℝ)))) +
          C₂ * r * Real.exp (-(c₂ * (2 * N : ℕ))) ≤
            C * Real.exp (-(c * t)) := by
      calc
        _ ≤ K * (r ^ 2 * Real.exp (-(a * t))) := by dsimp [K]; nlinarith
        _ ≤ K * (D * Real.exp (-(c * t))) := by gcongr
        _ ≤ C * Real.exp (-(c * t)) := by
          have := le_max_left (K * D) (Real.exp (c * 100))
          dsimp [C]
          nlinarith [Real.exp_pos (-(c * t))]
    refine (hraw x N hN).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [r, t, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hreal
  · have hsqrt : Real.sqrt N ≤ 100 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · have : (N : ℝ) ≤ 10000 := by exact_mod_cast (show N ≤ 10000 by omega)
        nlinarith
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (C * Real.exp (-(c * Real.sqrt N))) := by
      rw [ENNReal.one_le_ofReal]
      calc
        1 = Real.exp (c * 100) * Real.exp (-(c * 100)) := by rw [← Real.exp_add]; simp
        _ ≤ C * Real.exp (-(c * Real.sqrt N)) := by
          gcongr
          · exact le_max_right _ _
    calc
      _ ≤ (latticeBondLaw 2 p) Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ _ := hone

end Rigidity.Percolation
