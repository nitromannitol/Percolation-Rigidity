import Rigidity.Steps.Section5.LogGrowth
import Rigidity.Proofs.Section5.PotentialLimit

/-! # Proposition 5.5: logarithmic growth of a charged potential

Proofs of the steps of `Rigidity/Steps/Section5/LogGrowth.lean` and their composition with the
potential asymptotics of `Rigidity/Proofs/Section5/PotentialLimit.lean`: almost surely, if
`Σ f ≠ 0` then `u_f = Θ(log |x|)` (corrected draft L1544-1546). -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- The Euclidean norm of a planar lattice point, `|x|₂ = √(x₁² + x₂²)`. -/
theorem eucl_eq (x : Vertex 2) : eucl x = Real.sqrt ((x 0 : ℝ) ^ 2 + (x 1 : ℝ) ^ 2) := by
  rw [eucl, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [latticeEuclideanEmbedding]

/-- The `ℓ¹` norm of a planar lattice point, `|x| = |x₁| + |x₂|`. -/
theorem l1_eq (x : Vertex 2) : l1 x = |(x 0 : ℝ)| + |(x 1 : ℝ)| := by
  simp [l1, Fin.sum_univ_two]

/-- `|x|₂ ≤ |x| ≤ √2 |x|₂`. -/
theorem normComparison : NormComparisonStep := by
  intro x
  rw [eucl_eq, l1_eq]
  set a : ℝ := (x 0 : ℝ)
  set b : ℝ := (x 1 : ℝ)
  have hab := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨by positivity,
      by nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]⟩
  · rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_trans (le_abs_self _)
      (Real.abs_le_sqrt (by nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]))

/-- `|log |x| - log |x|₂| ≤ log 2` for `|x| ≥ 1`, from the norm comparison. -/
theorem logNormComparison_of_normComparison (h : NormComparisonStep) : LogNormComparisonStep := by
  intro x hx
  obtain ⟨h1, h2⟩ := h x
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have he : 0 < eucl x := by
    by_contra hne
    have : Real.sqrt 2 * eucl x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg 2) (not_lt.mp hne)
    linarith
  have hlo : Real.log (eucl x) ≤ Real.log (l1 x) := Real.log_le_log he h1
  have hhi : Real.log (l1 x) ≤ Real.log 2 + Real.log (eucl x) := by
    rw [← Real.log_mul two_ne_zero he.ne']
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- On an open component, `u - m Ḡ → L` at infinity with `m ≠ 0` gives
`(a/2) log |x| ≤ |u(x)| ≤ 2a log |x|` for `|x|` large, where `a = |m| / (2πκ)`. -/
theorem asymptoticLogBounds_of_logNormComparison (hN : LogNormComparisonStep) :
    AsymptoticLogBoundsStep := by
  intro ω C κ m u L hm hT
  have hden : 0 < 2 * Real.pi * κ.val := mul_pos (mul_pos two_pos Real.pi_pos) κ.prop
  set a : ℝ := |(m : ℝ)| / (2 * Real.pi * κ.val) with ha_def
  have ha : 0 < a := div_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hm)) hden
  have hev : ∀ᶠ x in cofinite, |u x - (m : ℝ) * greenLog κ x.val - L| ≤ 1 :=
    (Metric.tendsto_nhds.mp hT 1 one_pos).mono fun x hx => by
      rw [Real.dist_eq] at hx
      exact hx.le
  obtain ⟨B, hB⟩ := ((eventually_cofinite.mp hev).image (fun x : C => l1 x.val)).bddAbove
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  set T : ℝ := 2 * Real.log 2 + 2 * (|L| + 1) / a with hT_def
  have hT0 : 0 ≤ T := add_nonneg (by positivity) (by positivity)
  refine ⟨a / 2, 2 * a, max (B + 1) (Real.exp T), half_pos ha, by positivity, fun x hx => ?_⟩
  have hxS : |u x - (m : ℝ) * greenLog κ x.val - L| ≤ 1 := by
    by_contra hne
    have := hB ⟨x, hne, rfl⟩
    linarith [le_max_left (B + 1) (Real.exp T)]
  have hl1 : Real.exp T ≤ l1 x.val := le_trans (le_max_right _ _) hx
  have hℓ : T ≤ Real.log (l1 x.val) := by
    rw [← Real.log_exp T]
    exact Real.log_le_log (Real.exp_pos T) hl1
  have hlog := abs_le.mp (hN x.val (le_trans (Real.one_le_exp hT0) hl1))
  set ℓ := Real.log (l1 x.val)
  set e := Real.log (eucl x.val)
  have hmg : |(m : ℝ) * greenLog κ x.val| = a * |e| := by
    rw [greenLog, abs_mul, abs_div, abs_neg, abs_of_pos hden, ha_def]
    ring
  have hDL : |u x - (m : ℝ) * greenLog κ x.val| ≤ 1 + |L| := by
    have hD := abs_le.mp hxS
    exact abs_le.mpr ⟨by linarith [neg_abs_le L], by linarith [le_abs_self L]⟩
  have hup := abs_sub_abs_le_abs_sub (u x) ((m : ℝ) * greenLog κ x.val)
  have hlo := abs_sub_abs_le_abs_sub ((m : ℝ) * greenLog κ x.val) (u x)
  rw [abs_sub_comm] at hlo
  have he1 : a * (ℓ - Real.log 2) ≤ a * |e| :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self e]) ha.le
  have he2 : a * |e| ≤ a * (ℓ + Real.log 2) :=
    mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) ha.le
  have hℓa : a * T ≤ a * ℓ := mul_le_mul_of_nonneg_left hℓ ha.le
  have haT : a * T = 2 * (a * Real.log 2) + 2 * (|L| + 1) := by
    rw [hT_def]
    field_simp
  have hal := mul_nonneg ha.le hlog2
  constructor <;> nlinarith

/-- Proposition 5.5: almost surely, if `Σ f ≠ 0` then `u_f = Θ(log |x|)`. -/
theorem logGrowth (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative) {p : unitInterval}
    (hp : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : Vertex 2 → ℤ) :
    LogGrowthStmt p f :=
  logGrowth_of_steps (uniqueClusterAe hUq hp hp1) (potentialAsymptotic hGQ hp hp1)
    (asymptoticLogBounds_of_logNormComparison
      (logNormComparison_of_normComparison normComparison)) f

end Rigidity.Proofs.Section5
