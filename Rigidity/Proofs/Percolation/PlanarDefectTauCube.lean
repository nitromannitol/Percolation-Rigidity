import Rigidity.Proofs.Percolation.PlanarFlatnessTools
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeBounds

/-!
# Lemma 5.4 of Armstrong and Dario for every triadic cube

Lemma 5.4 of Armstrong and Dario bounds the expected energy of the differences between the
restriction of the minimizer of `μ(□, q)` to the subcubes of scale `n` and the minimizers on these
subcubes. In the form proved for the cube `□_m` centred at the origin
(`exists_planarMuDefect_le_planarMuTau`), the bound is
`2 |q|² ∑_{k=n}^{m-1} τ^μ_k + C |q|₁² (∑_k ε_k + ε_n)`. For every triadic cube `□` of scale `m` the
same bound holds with an additional error `C |q|₁² exp(-c 3^m)`, from the approximate stationarity
of `E[-μ]` (`exists_lintegral_neg_planarMu_le_of_scale_eq`). With `τ^μ_k ≤ τ_k` and
`∑_{k ≥ n} ε_k ≤ C 3^{-n/4}` this is
`E[1{𝒫, □ resolved} D_n(□, q)] ≤ |□| C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`
(`exists_lintegral_planarMuDefect_le_tau`).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

set_option maxHeartbeats 400000 in
/-- **Lemma 5.4 of Armstrong and Dario for `μ`, on every triadic cube** (display (5.10), first
term, in dimension two). -/
theorem exists_lintegral_planarMuDefect_le_tau {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ q : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarMuDefect ω U n q) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (U.volume * (C * (q 0 ^ 2 + q 1 ^ 2) *
          (∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4)))) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hdef⟩ := exists_lintegral_planarMuDefect_le hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hst⟩ := exists_lintegral_neg_planarMu_le_of_scale_eq hpc
  obtain ⟨C₃, hC₃, c₃, hc₃, hsub⟩ := exists_planarMuMean_sub_le hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  set c := min c₁ (min c₂ c₃) with hcdef
  have hc : 0 < c := lt_min hc₁ (lt_min hc₂ hc₃)
  obtain ⟨Ce, hCe, herr⟩ := exists_sum_planarError_le hc
  set D : ℝ := C₁.toReal + C₂.toReal + C₃ with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨2 + 2 * D * Ce, by positivity, fun U n hn q => ?_⟩
  set m := U.scale with hm
  set μ := latticeBondLaw 2 p with hμ
  set Q := (|q 0| + |q 1|) ^ 2 with hQ
  set P := q 0 ^ 2 + q 1 ^ 2 with hPdef
  have hQ0 : 0 ≤ Q := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hQ2 : Q ≤ 2 * P := abs_add_abs_sq_le q
  have h := hdef U ⟨n, 0⟩ n hn rfl q
  have hs := hst U ⟨m, 0⟩ rfl q
  have hmeans := hsub n m hn q
  set IU := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
    ENNReal.ofReal (-planarMu ω U q) else 0) ∂μ with hIU
  set IW := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
    ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0) ∂μ with hIW
  set IO := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
    ENNReal.ofReal (-planarMu ω ⟨m, 0⟩ q) else 0) ∂μ with hIO
  have hfU : IU ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top) (hup U q)
  have hfW : IW ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top) (hup ⟨n, 0⟩ q)
  set A := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
    ENNReal.ofReal (planarMuDefect ω U n q) else 0) ∂μ with hA
  have hvol := U.volume_pos
  have hR : ENNReal.ofReal U.volume * IW + C₁ * ENNReal.ofReal (Q * U.volume *
      (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfW,
      ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top⟩
  have hAfin : A ≠ ∞ := ne_top_of_le_ne_top hR (le_trans le_self_add h)
  have hreal := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_add hAfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfU),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfW)
      (ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hvol.le, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hRs : IU + C₂ * ENNReal.ofReal (Q * Real.exp (-c₂ * (3 : ℝ) ^ m)) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hfU, ENNReal.mul_ne_top hC₂ ENNReal.ofReal_ne_top⟩
  have hsr := ENNReal.toReal_mono hRs hs
  rw [ENNReal.toReal_add hfU (ENNReal.mul_ne_top hC₂ ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hsr
  have hmW : planarMuMean p n q = IW.toReal := rfl
  have hmO : planarMuMean p m q = IO.toReal := rfl
  rw [hmW, hmO] at hmeans
  -- the error terms
  set E : ℝ := Ce * (3 : ℝ) ^ (-(n : ℝ) / 4) with hE
  set S : ℝ := ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))
    with hS
  set en : ℝ := 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) with hen
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have hen0 : 0 ≤ en := by positivity
  have hSE : S ≤ E := by have := herr n m; linarith
  have henE : en ≤ E := by have := herr n m; linarith
  have hε : ∀ k : ℕ, ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * (3 : ℝ) ^ k) ≤
      Real.exp (-c * (3 : ℝ) ^ k) := fun k c' hc' => by
    apply Real.exp_le_exp.2
    have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
    nlinarith
  have k1 : ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₃ * (3 : ℝ) ^ k)) ≤ S :=
    Finset.sum_le_sum fun k _ => add_le_add le_rfl
      (hε k c₃ ((min_le_right _ _).trans (min_le_right _ _)))
  have k2 : Real.exp (-c₂ * (3 : ℝ) ^ m) ≤ en := by
    have h1 : Real.exp (-c₂ * (3 : ℝ) ^ m) ≤ Real.exp (-c * (3 : ℝ) ^ m) :=
      hε m c₂ ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : Real.exp (-c * (3 : ℝ) ^ m) ≤ Real.exp (-c * (3 : ℝ) ^ n) := by
      apply Real.exp_le_exp.2
      have h3 : (3 : ℝ) ^ n ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hn
      nlinarith
    have h4 : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) := by positivity
    linarith
  have k3 : 1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n) ≤ en :=
    add_le_add le_rfl (hε n c₁ (min_le_left _ _))
  have hτμ : ∑ k ∈ Finset.Ico n m, planarMuTau p k ≤ ∑ k ∈ Finset.Ico n m, planarTau p k :=
    Finset.sum_le_sum fun k _ => le_add_of_nonneg_right (planarNuTau_nonneg p k)
  set T := ∑ k ∈ Finset.Ico n m, planarTau p k with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => planarTau_nonneg p k
  have hC₁0 : 0 ≤ C₁.toReal := ENNReal.toReal_nonneg
  have hC₂0 : 0 ≤ C₂.toReal := ENNReal.toReal_nonneg
  -- the means
  have hdiff : IW.toReal - IO.toReal ≤ 2 * P * T + C₃ * Q * S := by
    have h1 : C₃ * Q * ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₃ * (3 : ℝ) ^ k)) ≤ C₃ * Q * S :=
      mul_le_mul_of_nonneg_left k1 (by positivity)
    have h2 : 2 * P * ∑ k ∈ Finset.Ico n m, planarMuTau p k ≤ 2 * P * T :=
      mul_le_mul_of_nonneg_left hτμ (by positivity)
    linarith
  have hA1 : A.toReal ≤ U.volume * (IW.toReal - IO.toReal) +
      U.volume * (C₂.toReal * (Q * Real.exp (-c₂ * (3 : ℝ) ^ m))) +
      C₁.toReal * (Q * U.volume * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) := by
    have h1 : U.volume * IO.toReal ≤ U.volume * IU.toReal +
        U.volume * (C₂.toReal * (Q * Real.exp (-c₂ * (3 : ℝ) ^ m))) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hsr hvol.le
    linarith
  have hA2 : A.toReal ≤ U.volume * (2 * P * T + D * Q * E) := by
    have h1 : U.volume * (IW.toReal - IO.toReal) ≤ U.volume * (2 * P * T + C₃ * Q * S) :=
      mul_le_mul_of_nonneg_left hdiff hvol.le
    have h2 : C₂.toReal * (Q * Real.exp (-c₂ * (3 : ℝ) ^ m)) ≤ C₂.toReal * (Q * E) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (k2.trans henE) hQ0) hC₂0
    have h3 : C₁.toReal * (Q * U.volume * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n)))
        ≤ U.volume * (C₁.toReal * (Q * E)) := by
      have h7 := mul_le_mul_of_nonneg_left (k3.trans henE) (mul_nonneg hQ0 hvol.le)
      calc C₁.toReal * (Q * U.volume * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n)))
          ≤ C₁.toReal * (Q * U.volume * E) := mul_le_mul_of_nonneg_left h7 hC₁0
        _ = U.volume * (C₁.toReal * (Q * E)) := by ring
    have h4 : C₃ * Q * S ≤ C₃ * Q * E := mul_le_mul_of_nonneg_left hSE (by positivity)
    have h5 : U.volume * (C₂.toReal * (Q * Real.exp (-c₂ * (3 : ℝ) ^ m))) ≤
        U.volume * (C₂.toReal * (Q * E)) := mul_le_mul_of_nonneg_left h2 hvol.le
    have h6 : U.volume * (C₃ * Q * S) ≤ U.volume * (C₃ * Q * E) :=
      mul_le_mul_of_nonneg_left h4 hvol.le
    have e : U.volume * (2 * P * T + D * Q * E) = U.volume * (2 * P * T) +
        U.volume * (C₃ * Q * E) + U.volume * (C₂.toReal * (Q * E)) +
        U.volume * (C₁.toReal * (Q * E)) := by rw [hD]; ring
    have e2 : U.volume * (2 * P * T + C₃ * Q * S) = U.volume * (2 * P * T) +
        U.volume * (C₃ * Q * S) := by ring
    linarith
  have hE0 : 0 ≤ E := by positivity
  have hA3 : A.toReal ≤ U.volume * ((2 + 2 * D * Ce) * P * (T + (3 : ℝ) ^ (-(n : ℝ) / 4))) := by
    refine hA2.trans (mul_le_mul_of_nonneg_left ?_ hvol.le)
    have h1 : D * Q * E ≤ D * (2 * P) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ2 hD0) hE0
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(n : ℝ) / 4) := by positivity
    have h4 : 0 ≤ D * Ce := mul_nonneg hD0 hCe
    have e : D * (2 * P) * E = 2 * (D * Ce) * P * (3 : ℝ) ^ (-(n : ℝ) / 4) := by rw [hE]; ring
    have h5 : 0 ≤ D * Ce * P * T := mul_nonneg (mul_nonneg h4 hP0) hT0
    have h6 : 0 ≤ P * (3 : ℝ) ^ (-(n : ℝ) / 4) := mul_nonneg hP0 h3
    have expand : (2 + 2 * D * Ce) * P * (T + (3 : ℝ) ^ (-(n : ℝ) / 4)) = 2 * P * T +
        2 * (D * Ce) * P * (3 : ℝ) ^ (-(n : ℝ) / 4) + 2 * (D * Ce * P * T) +
        2 * (P * (3 : ℝ) ^ (-(n : ℝ) / 4)) := by ring
    rw [expand]
    linarith
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hA3

end Rigidity.Percolation
