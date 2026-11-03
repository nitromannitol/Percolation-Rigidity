import Rigidity.Steps.S2.GreenGradientHomogenization
import LatticeProb.Prob.Percolation.LatticeRadialScale

/-!
# Proposition 2.6, step:2.6-reduction: the minimal scale `M(y)` (union bound)

`MinimalScaleStep` (paper L563-576 of the corrected draft): for finitely many families of scales
`X i x` with uniform stretched exponential tails, there is `M(y) ≤ O_{s'}(C')` with
`A (X i x ∨ 2)^N < |x - y|` for every `i` and every `x` with `|x - y| ≥ M(y)`.

The scales are gathered into the single field `Z x = ∑ᵢ A (X i x ∨ 2)^N`, whose tail is a
stretched exponential with exponent `σ = (N + 1)⁻¹ (1 + ∑ᵢ sᵢ⁻¹)⁻¹` (`tail_scale_pow`,
`tail_sum_scale`). The union bound and Borel–Cantelli over `x ∈ ℤ^d` are
`LatticeProb.Percolation.exists_radial_scale_exp_moment`, at the Euclidean distance; the
`ℓ¹` distance is compared with it by `|z|₂ ≤ |z|₁ ≤ d |z|₂`.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

section Tail

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `1 ≤ B exp(-u / B)` when `2 ≤ B` and `0 ≤ 2u ≤ B`. -/
theorem one_le_mul_exp_neg_div {B u : ℝ} (hB : 2 ≤ B) (huB : 2 * u ≤ B) :
    1 ≤ B * Real.exp (-u / B) := by
  have hB0 : 0 < B := by linarith
  calc (1 : ℝ) ≤ B - u := by linarith
    _ = B * (-u / B + 1) := by field_simp; ring
    _ ≤ B * Real.exp (-u / B) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hB0.le

/-- `a exp(-x / b) ≤ B exp(-x / B)` when `a ≤ B`, `0 < b ≤ B` and `0 ≤ x`. -/
theorem mul_exp_neg_div_le {a b B x : ℝ} (ha : a ≤ B) (hb : 0 < b) (hbB : b ≤ B) (hx : 0 ≤ x) :
    a * Real.exp (-x / b) ≤ B * Real.exp (-x / B) := by
  refine mul_le_mul ha (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (hb.le.trans hbB)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hx hb hbB

/-- The tail of `A (X ∨ 2)^N` for `X` with tail `C exp(-R^s / C)`: it is at most
`B exp(-u^σ / B)` when `N σ ≤ s`. -/
theorem tail_scale_pow (s C A σ : ℝ) (N : ℕ) (hs : 0 < s) (hC : 0 < C) (hA : 0 < A)
    (hσ : 0 < σ) (hNσ : (N : ℝ) * σ ≤ s) :
    ∃ B : ℝ, 0 < B ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ),
      (∀ R : ℝ, 0 ≤ R →
        μ {ω | R ≤ X ω} ≤ ENNReal.ofReal (C * Real.exp (-Real.rpow R s / C))) →
      ∀ u : ℝ, 0 < u →
        μ {ω | u ≤ A * max (X ω) 2 ^ N} ≤ ENNReal.ofReal (B * Real.exp (-(u ^ σ) / B)) := by
  set B := max (max 2 (2 * (A * 2 ^ N) ^ σ)) (max C (A ^ σ * C)) with hBdef
  have hB2 : 2 ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hBA : 2 * (A * 2 ^ N) ^ σ ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hBC : C ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBAC : A ^ σ * C ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, by linarith, ?_⟩
  intro μ _ X hX u hu
  by_cases hu0 : u ≤ A * 2 ^ N
  · have h1 : 1 ≤ B * Real.exp (-(u ^ σ) / B) := by
      refine one_le_mul_exp_neg_div hB2 (le_trans ?_ hBA)
      have := Real.rpow_le_rpow hu.le hu0 hσ.le
      linarith
    calc μ {ω | u ≤ A * max (X ω) 2 ^ N} ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  · push Not at hu0
    have huA : 0 < u / A := div_pos hu hA
    have hsub : {ω | u ≤ A * max (X ω) 2 ^ N} ⊆ {ω | (u / A) ^ (σ / s) ≤ X ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have hX2 : 2 ≤ X ω := by
        by_contra h
        push Not at h
        rw [max_eq_right h.le] at hω
        linarith
      rw [max_eq_left hX2] at hω
      have hX1 : 1 ≤ X ω := by linarith
      have hle : u / A ≤ X ω ^ N := by
        rw [div_le_iff₀ hA]
        linarith
      calc (u / A) ^ (σ / s) ≤ (X ω ^ N) ^ (σ / s) :=
            Real.rpow_le_rpow huA.le hle (div_pos hσ hs).le
        _ = X ω ^ ((N : ℝ) * (σ / s)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        _ ≤ X ω ^ (1 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
            rw [← mul_div_assoc, div_le_one hs]
            exact hNσ
        _ = X ω := Real.rpow_one _
    refine (measure_mono hsub).trans
      ((hX _ (Real.rpow_nonneg huA.le _)).trans (ENNReal.ofReal_le_ofReal ?_))
    change C * Real.exp (-((u / A) ^ (σ / s)) ^ s / C) ≤ B * Real.exp (-(u ^ σ) / B)
    rw [← Real.rpow_mul huA.le, div_mul_cancel₀ σ hs.ne', Real.div_rpow hu.le hA.le,
      neg_div, div_div, ← neg_div]
    exact mul_exp_neg_div_le hBC (mul_pos (Real.rpow_pos_of_pos hA σ) hC) hBAC
      (Real.rpow_nonneg hu.le σ)

/-- The tail of `∑ᵢ A (Xᵢ ∨ 2)^N` for finitely many `Xᵢ` with tails `Cᵢ exp(-R^{sᵢ} / Cᵢ)`
(union bound), when `N σ ≤ sᵢ` for every `i`. -/
theorem tail_sum_scale (k : ℕ) (s C : Fin k → ℝ) (A σ : ℝ) (N : ℕ) (hs : ∀ i, 0 < s i)
    (hC : ∀ i, 0 < C i) (hA : 0 < A) (hσ : 0 < σ) (hNσ : ∀ i, (N : ℝ) * σ ≤ s i) :
    ∃ B : ℝ, 0 < B ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin k → Ω → ℝ),
      (∀ i, ∀ R : ℝ, 0 ≤ R →
        μ {ω | R ≤ X i ω} ≤ ENNReal.ofReal (C i * Real.exp (-Real.rpow R (s i) / C i))) →
      ∀ t : ℝ, 0 < t →
        μ {ω | t ≤ ∑ i, A * max (X i ω) 2 ^ N} ≤
          ENNReal.ofReal (B * Real.exp (-(t ^ σ) / B)) := by
  choose Bi hBi htail using fun i =>
    tail_scale_pow (Ω := Ω) (s i) (C i) A σ N (hs i) (hC i) hA hσ (hNσ i)
  set Bm := ∑ i, Bi i + 1 with hBm
  have hBim : ∀ i, Bi i ≤ Bm := fun i => by
    have := Finset.single_le_sum (f := Bi) (fun j _ => (hBi j).le) (Finset.mem_univ i)
    linarith
  have hBm0 : 0 < Bm := by
    have := Finset.sum_nonneg (s := Finset.univ) fun j _ => (hBi j).le
    linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkσ : 1 ≤ ((k : ℝ) + 1) ^ σ := Real.one_le_rpow (by linarith [k.cast_nonneg (α := ℝ)]) hσ.le
  refine ⟨((k : ℝ) + 1) * ((k : ℝ) + 1) ^ σ * Bm, by positivity, ?_⟩
  intro μ _ X hX t ht
  set T := t / ((k : ℝ) + 1) with hT
  have hT0 : 0 < T := div_pos ht hk1
  have hsub : {ω | t ≤ ∑ i, A * max (X i ω) 2 ^ N} ⊆
      ⋃ i, {ω | T ≤ A * max (X i ω) 2 ^ N} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hω ⊢
    by_contra hcon
    push Not at hcon
    have h1 : ∑ i, A * max (X i ω) 2 ^ N ≤ ∑ _i : Fin k, T :=
      Finset.sum_le_sum fun i _ => (hcon i).le
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 : (k : ℝ) * T < t := by
      rw [hT, mul_div_assoc', div_lt_iff₀ hk1]
      nlinarith
    linarith
  have hterm : ∀ i, μ {ω | T ≤ A * max (X i ω) 2 ^ N} ≤
      ENNReal.ofReal (Bm * Real.exp (-(T ^ σ) / Bm)) := fun i =>
    (htail i μ (X i) (hX i) T hT0).trans (ENNReal.ofReal_le_ofReal
      (mul_exp_neg_div_le (hBim i) (hBi i) (hBim i) (Real.rpow_nonneg hT0.le σ)))
  calc μ {ω | t ≤ ∑ i, A * max (X i ω) 2 ^ N}
      ≤ μ (⋃ i, {ω | T ≤ A * max (X i ω) 2 ^ N}) := measure_mono hsub
    _ ≤ ∑ i, μ {ω | T ≤ A * max (X i ω) 2 ^ N} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin k, ENNReal.ofReal (Bm * Real.exp (-(T ^ σ) / Bm)) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ENNReal.ofReal ((k : ℝ) * (Bm * Real.exp (-(T ^ σ) / Bm))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hT, Real.div_rpow ht.le hk1.le, neg_div, div_div, ← neg_div, ← mul_assoc]
        refine mul_exp_neg_div_le ?_ (mul_pos (by positivity) hBm0) ?_
          (Real.rpow_nonneg ht.le σ)
        · have : (k : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) ^ σ := by nlinarith
          exact mul_le_mul_of_nonneg_right this hBm0.le
        · rw [mul_assoc]
          exact le_mul_of_one_le_left (by positivity) (by linarith)

end Tail

variable {d : ℕ}

/-- The coordinates of `x - y` embedded in `ℝ^d`. -/
theorem norm_latticeEuclideanEmbedding_sub_apply (x y : Vertex d) (j : Fin d) :
    ‖latticeEuclideanEmbedding (x - y) j‖ = |((x j - y j : ℤ) : ℝ)| := by
  rw [Real.norm_eq_abs]
  rfl

/-- The Euclidean distance is at most the `ℓ¹` distance. -/
theorem norm_latticeEuclideanEmbedding_sub_le (x y : Vertex d) :
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ≤ Steps.S2.latticeL1Dist x y := by
  rw [← latticeEuclideanEmbedding_sub, EuclideanSpace.norm_eq]
  have hsum : Steps.S2.latticeL1Dist x y = ∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ :=
    Finset.sum_congr rfl fun j _ => (norm_latticeEuclideanEmbedding_sub_apply x y j).symm
  rw [hsum]
  calc √(∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ ^ 2)
      ≤ √((∑ j, ‖latticeEuclideanEmbedding (x - y) j‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _)
    _ = ∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ :=
        Real.sqrt_sq (Finset.sum_nonneg fun j _ => norm_nonneg _)

/-- The `ℓ¹` distance is at most `d` times the Euclidean distance. -/
theorem latticeL1Dist_le_mul_norm (x y : Vertex d) :
    Steps.S2.latticeL1Dist x y ≤
      d * ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ := by
  rw [← latticeEuclideanEmbedding_sub]
  calc Steps.S2.latticeL1Dist x y = ∑ j, ‖latticeEuclideanEmbedding (x - y) j‖ :=
        Finset.sum_congr rfl fun j _ => (norm_latticeEuclideanEmbedding_sub_apply x y j).symm
    _ ≤ ∑ _j : Fin d, ‖latticeEuclideanEmbedding (x - y)‖ :=
        Finset.sum_le_sum fun j _ => PiLp.norm_apply_le _ j
    _ = d * ‖latticeEuclideanEmbedding (x - y)‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- step:2.6-reduction (paper L563-576): the union bound. The scales are gathered into
`Z x = ∑ᵢ A (X i x ∨ 2)^N`, with a stretched exponential tail of exponent
`σ = (N + 1)⁻¹ (1 + ∑ᵢ sᵢ⁻¹)⁻¹`; `exists_radial_scale_exp_moment` gives `M ≥ 1` with
`E[exp((M / C₀)^σ)] ≤ 2` and `Z x < |x - y|₂` once `M ≤ |x - y|₂`; the minimal scale is
`(d + 1) M`. -/
theorem minimalScaleStep (d : ℕ) (p : unitInterval) : MinimalScaleStep d p := by
  intro k s C A N hs hC hA
  set σ : ℝ := ((N : ℝ) + 1)⁻¹ * (1 + ∑ i, (s i)⁻¹)⁻¹ with hσdef
  have hS : 0 < 1 + ∑ i, (s i)⁻¹ :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (inv_pos.mpr (hs i)).le)
  have hσ : 0 < σ := mul_pos (inv_pos.mpr (by positivity)) (inv_pos.mpr hS)
  have hNσ : ∀ i, (N : ℝ) * σ ≤ s i := by
    intro i
    have h1 : (s i)⁻¹ ≤ 1 + ∑ j, (s j)⁻¹ := by
      have := Finset.single_le_sum (f := fun j => (s j)⁻¹)
        (fun j _ => (inv_pos.mpr (hs j)).le) (Finset.mem_univ i)
      linarith
    have h2 : (1 + ∑ j, (s j)⁻¹)⁻¹ ≤ s i := by
      rw [inv_le_comm₀ hS (hs i)]
      exact h1
    have h3 : (N : ℝ) * ((N : ℝ) + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      linarith
    calc (N : ℝ) * σ = ((N : ℝ) * ((N : ℝ) + 1)⁻¹) * (1 + ∑ j, (s j)⁻¹)⁻¹ := by
          rw [hσdef]; ring
      _ ≤ 1 * s i := mul_le_mul h3 h2 (inv_nonneg.mpr hS.le) zero_le_one
      _ = s i := one_mul _
  obtain ⟨B, hB, hBtail⟩ := tail_sum_scale (Ω := Configuration d) k s C A σ N hs hC hA hσ hNσ
  obtain ⟨C₀, hC₀, hrad⟩ :=
    exists_radial_scale_exp_moment (d := d) (Ω := Configuration d) B σ 1 hB hσ one_pos
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hmax : 0 < max C₀ A := lt_max_of_lt_left hC₀
  refine ⟨σ, ((d : ℝ) + 1) * max C₀ A, hσ,
    (le_max_right C₀ A).trans (le_mul_of_one_le_left hmax.le (by linarith)), ?_⟩
  intro y X hXm hXtail
  let Z : Vertex d → Configuration d → ℝ := fun x ω => ∑ i, A * max (X i x ω) 2 ^ N
  have hZm : ∀ x, Measurable (Z x) := fun x =>
    Finset.measurable_sum _ fun i _ => (((hXm i x).max measurable_const).pow_const N).const_mul A
  have hZtail : ∀ x t, 0 < t → latticeBondLaw d p {ω | t ≤ Z x ω} ≤
      ENNReal.ofReal (B * Real.exp (-(t ^ σ) / B)) := fun x t ht =>
    hBtail (latticeBondLaw d p) (fun i => X i x) (fun i R hR => hXtail i x R hR) t ht
  obtain ⟨M, hM, hM1, hint, hmom, hgood⟩ := hrad (latticeBondLaw d p) Z hZm hZtail y
  simp only [one_mul] at hint hmom
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => zero_le_one.trans (hM1 ω)
  have heq : ∀ ω, Real.rpow (max (((d : ℝ) + 1) * M ω / (((d : ℝ) + 1) * max C₀ A)) 0) σ =
      (M ω / max C₀ A) ^ σ := by
    intro ω
    rw [mul_div_mul_left _ _ hd1.ne', max_eq_left (div_nonneg (hM0 ω) hmax.le)]
    rfl
  have hle : ∀ ω, Real.exp ((M ω / max C₀ A) ^ σ) ≤ Real.exp ((M ω / C₀) ^ σ) := fun ω =>
    Real.exp_le_exp.mpr (Real.rpow_le_rpow (div_nonneg (hM0 ω) hmax.le)
      (div_le_div_of_nonneg_left (hM0 ω) hC₀ (le_max_left _ _)) hσ.le)
  have hint' : Integrable (fun ω => Real.exp ((M ω / max C₀ A) ^ σ)) (latticeBondLaw d p) :=
    hint.mono' ((hM.div_const _).pow_const σ).exp.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle ω)
  refine ⟨fun ω => ((d : ℝ) + 1) * M ω, hM.const_mul _,
    fun ω => mul_nonneg hd1.le (hM0 ω), ⟨?_, ?_⟩, ?_⟩
  · simp_rw [heq]
    exact hint'
  · simp_rw [heq]
    exact (integral_mono hint' hint hle).trans hmom
  · filter_upwards [hgood] with ω hω x hx i
    have hL1 := latticeL1Dist_le_mul_norm x y
    have hE := norm_latticeEuclideanEmbedding_sub_le x y
    have hMx : M ω ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ := by
      have h1 : ((d : ℝ) + 1) * M ω ≤
          ((d : ℝ) + 1) * ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ := by
        nlinarith [norm_nonneg (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y)]
      exact le_of_mul_le_mul_left h1 hd1
    have hZ := hω x hMx
    rw [Real.rpow_one] at hZ
    have hterm : A * max (X i x ω) 2 ^ N ≤ Z x ω :=
      Finset.single_le_sum (f := fun j => A * max (X j x ω) 2 ^ N)
        (fun j _ => mul_nonneg hA.le (pow_nonneg (le_trans zero_le_two (le_max_right _ _)) N))
        (Finset.mem_univ i)
    linarith

end Rigidity.Proofs.S2
