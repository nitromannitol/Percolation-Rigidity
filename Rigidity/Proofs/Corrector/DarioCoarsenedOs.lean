import Rigidity.Proofs.Corrector.DarioOptimalCorrector

/-!
# The inputs of Dario's §5 in the stochastic-integrability form of the paper

Dario states the inputs of the proof of Theorem 1 with the `O_s` notation:

* (5.4), proved in Step 1 of the proof of Theorem 2:
  `(3^{-dm} ∑_{y ∈ □_m} |[χ]_𝒫(y) - ([χ]_𝒫)_{□_m}|^q)^{1/q} ≤ O_s(C q^k √m)`;
* (5.7): `|[χ]_{𝒫_y}(z) - [χ]_𝒫(z)| ≤ O_s(C)`.

By (5.1) these give the moment forms (5.5) and the moment form of (5.7) used
by Steps 1–4 (`LinftyIterationData`), with `k` replaced by `k + 1/s`
(`CoarsenedOsData.linftyIterationData`). Hence Theorem 1 follows from the inputs of the paper in
their printed form (`darioOptimalCorrectorTwo_of_coarsenedOs`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2
open scoped ENNReal

variable {p : unitInterval}

/-- **(5.1), as used for (5.5)**: if `S^{1/q} ≤ O_s(θ)` for a nonnegative `S`,
then `E[S] ≤ (2 θ (1/s)^{1/s} q^{1/s})^q`. -/
theorem lintegral_le_of_isOsBond_rpow_inv {S : Configuration 2 → ℝ} {s θ q : ℝ} (hs : 0 < s)
    (hθ : 0 < θ) (hq : 1 ≤ q) (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω)
    (h : IsOsBond 2 p (fun ω => S ω ^ (1 / q)) s θ) :
    ∫⁻ ω, ENNReal.ofReal (S ω) ∂latticeBondLaw 2 p ≤
      ENNReal.ofReal ((2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hint, hle⟩ := IsOsBond.integral_rpow_le hs hθ hq0 (hS.pow_const (1 / q))
    (fun ω => Real.rpow_nonneg (hS0 ω) _) h
  have hpow : ∀ ω, (S ω ^ (1 / q)) ^ q = S ω := fun ω => by
    rw [← Real.rpow_mul (hS0 ω), one_div_mul_cancel hq0.ne', Real.rpow_one]
  simp only [hpow] at hint hle
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hS0)]
  refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
  have he : Real.exp (-(q / s)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := div_pos hq0 hs; linarith)
  have he0 : 0 ≤ Real.exp (-(q / s)) := (Real.exp_pos _).le
  have hqs : (q / s) ^ (q / s) = ((1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul hq0.le, show 1 / s * q = q / s by ring, ← Real.mul_rpow (by positivity)
      hq0.le]
    congr 1
    ring
  have h2 : (2 : ℝ) ≤ 2 ^ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq
  have hexp : (2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q =
      2 ^ q * θ ^ q * ((1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q := by
    rw [mul_assoc (2 * θ), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hθ.le]
  rw [hexp, hqs]
  have hT : 0 ≤ θ ^ q := by positivity
  have hX : 0 ≤ ((1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q := by positivity
  have hTX := mul_nonneg hT hX
  nlinarith [mul_nonneg hTX (sub_nonneg.2 he), mul_nonneg hTX (sub_nonneg.2 h2),
    mul_nonneg hTX he0]

/-- **(5.1), as used for the moment form of (5.7)**: if `|f| ≤ O_s(θ)`, then
`E|f|^q ≤ (2 θ (1/s)^{1/s} q^{1/s})^q`. -/
theorem mom_le_of_isOsBond {f : Configuration 2 → ℝ} {s θ q : ℝ} (hs : 0 < s) (hθ : 0 < θ)
    (hq : 1 ≤ q) (hf : Measurable f) (h : IsOsBond 2 p (fun ω => |f ω|) s θ) :
    mom p f q ≤ ENNReal.ofReal ((2 * θ * (1 / s) ^ (1 / s) * q ^ (1 / s)) ^ q) := by
  have hq0 : 0 < q := by linarith
  refine lintegral_le_of_isOsBond_rpow_inv hs hθ hq (hf.abs.pow_const q)
    (fun ω => by positivity) ?_
  have : (fun ω => (|f ω| ^ q) ^ (1 / q)) = fun ω => |f ω| := funext fun ω => by
    rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hq0.ne', Real.rpow_one]
  rw [this]
  exact h

/-- **The inputs of Dario's §5 in the form printed in the paper**, for fields `F y z`
(`[χ]_{𝒫_y}(z)`): (5.4) at the origin, the stationarity (2.3) and the
comparison (5.7) of the translated partitions. -/
structure CoarsenedOsData (p : unitInterval) (F : Vertex 2 → Vertex 2 → Configuration 2 → ℝ)
    (s C k : ℝ) : Prop where
  hs : 0 < s
  hC : 0 < C
  hk : 0 ≤ k
  meas : ∀ y z, Measurable (F y z)
  step1 : ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ, 1 ≤ q →
    IsOsBond 2 p
      (fun ω => ((∑ z ∈ boxAt 0 m, |F 0 z ω - boxAvg (F 0) 0 m ω| ^ q) / 9 ^ m) ^ (1 / q)) s
      (C * q ^ k * Real.sqrt m)
  stat : ∀ y, ∃ T : Configuration 2 → Configuration 2,
    MeasurePreserving T (latticeBondLaw 2 p) (latticeBondLaw 2 p) ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ z w, F 0 z ω - F 0 w ω = F y (z + y) (T ω) - F y (w + y) (T ω)
  ppy : ∀ y z, IsOsBond 2 p (fun ω => |F y z ω - F 0 z ω|) s C

/-- (5.4) and (5.7) give (5.5) and the moment form of (5.7),
with `A = B = 2 C (1/s)^{1/s}` and the exponent `k + 1/s`. -/
theorem CoarsenedOsData.linftyIterationData {F : Vertex 2 → Vertex 2 → Configuration 2 → ℝ}
    {s C k : ℝ} (h : CoarsenedOsData p F s C k) :
    LinftyIterationData p F (2 * C * (1 / s) ^ (1 / s)) (2 * C * (1 / s) ^ (1 / s)) (k + 1 / s) where
  hA := by have := h.hs; have := h.hC; positivity
  hB := by have := h.hs; have := h.hC; positivity
  meas := h.meas
  thm2 := by
    intro m hm q hq
    have hs := h.hs
    have hC := h.hC
    have hq0 : 0 < q := by linarith
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hSm : Measurable fun ω => (∑ z ∈ boxAt 0 m, |F 0 z ω - boxAvg (F 0) 0 m ω| ^ q) / 9 ^ m :=
      (Finset.measurable_sum _ fun z _ =>
        ((h.meas 0 z).sub (measurable_boxAvg (h.meas 0) 0 m)).abs.pow_const q).div_const _
    refine (lintegral_le_of_isOsBond_rpow_inv hs (by positivity) hq hSm
      (fun ω => by positivity) (h.step1 m hm q hq)).trans (le_of_eq ?_)
    congr 1
    have hsq : Real.sqrt m ^ q = (m : ℝ) ^ (q / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm0.le]
      ring_nf
    rw [← hsq, ← Real.mul_rpow (by positivity) (by positivity), Real.rpow_add hq0]
    congr 1
    ring
  stat := h.stat
  comp := by
    intro y z q hq
    have hs := h.hs
    have hC := h.hC
    have hq0 : 0 < q := by linarith
    refine (mom_le_of_isOsBond hs hC hq ((h.meas y z).sub (h.meas 0 z)) (h.ppy y z)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    refine Real.rpow_le_rpow (by positivity) ?_ hq0.le
    have : q ^ (1 / s) ≤ q ^ (k + 1 / s) :=
      Real.rpow_le_rpow_of_exponent_le hq (by linarith [h.hk])
    have : 0 ≤ 2 * C * (1 / s) ^ (1 / s) := by positivity
    calc 2 * C * (1 / s) ^ (1 / s) * q ^ (1 / s) ≤ 2 * C * (1 / s) ^ (1 / s) * q ^ (k + 1 / s) :=
          mul_le_mul_of_nonneg_left (by assumption) this
      _ = _ := rfl

/-- **The coarsened corrector of Dario, §5, with the inputs in the printed form**: fields `G i y`
satisfying (5.4), (2.3) and (5.7) (`CoarsenedOsData`), and the
coarsening error of Step 6 (`CoarseningErrorTwo`). -/
def DarioCoarsenedCorrectorOsTwo (p : unitInterval) : Prop :=
  ∃ s C k s₆ C₆ : ℝ, 0 < s₆ ∧ 0 < C₆ ∧
    ∃ G : Fin 2 → Vertex 2 → Vertex 2 → Vertex 2 → Configuration 2 → ℝ,
      (∀ i y, CoarsenedOsData p (G i y) s C k) ∧ CoarseningErrorTwo p G s₆ C₆

theorem darioCoarsenedCorrectorTwo_of_os (h : DarioCoarsenedCorrectorOsTwo p) :
    DarioCoarsenedCorrectorTwo p := by
  obtain ⟨s, C, k, s₆, C₆, hs₆, hC₆, G, hG, hE⟩ := h
  exact ⟨_, _, _, s₆, C₆, hs₆, hC₆, G, fun i y => (hG i y).linftyIterationData, hE⟩

/-- **Dario's Theorem 1 in dimension two** from the inputs of §5 in their printed form and the
planar qualitative corrector input. -/
theorem darioOptimalCorrectorTwo_of_coarsenedOs
    (hG : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      DarioCoarsenedCorrectorOsTwo p)
    (hC : SupercriticalBondCorrectorInputTwo) : DarioOptimalCorrectorTwo :=
  darioOptimalCorrectorTwo_of_coarsened (fun p hpc hp1 => darioCoarsenedCorrectorTwo_of_os
    (hG p hpc hp1)) hC

end Rigidity.Corrector
