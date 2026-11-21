import Rigidity.Proofs.Percolation.PlanarTauSummable

/-!
# Lemma 5.4 of Armstrong and Dario for `ν`

For `n ≤ m` and `q`, with `ξ = ā⁻¹ q` and `q̄ = (q₀, -q₁)`, the expected energy of the differences
between the maximizer of `ν(□_m, ξ)` restricted to the resolved subcubes of scale `n` and the
maximizers on these subcubes, divided by `|□_m|`, is at most

`2 |q|² ∑_{k=n}^{m-1} τ^ν_k + C (|ā⁻¹ q|₁² + |ā⁻¹ q̄|₁²) (∑_{k=n}^{m-1} ε_k + ε_n)`,

with `ε_k = 3 ^ (-k/2) + exp (-c 3 ^ k)` (display (5.10), second term, in dimension two). Since
`τ` is summable, the right side tends to zero as `n → ∞`, uniformly in `m`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- **Lemma 5.4 of Armstrong and Dario for `ν`** (display (5.10), second term, in dimension
two). -/
theorem exists_planarNuDefect_le_planarNuTau {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          ENNReal.ofReal (planarNuDefect ω ⟨m, 0⟩ n ((planarAhom p)⁻¹ *ᵥ q)) else 0)
          ∂(latticeBondLaw 2 p)).toReal / (⟨m, 0⟩ : TriadicCube 2).volume ≤
        2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarNuTau p k +
          C * ((|((planarAhom p)⁻¹ *ᵥ q) 0| + |((planarAhom p)⁻¹ *ᵥ q) 1|) ^ 2 +
            (|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
              |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2) *
          (∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
            (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hdef⟩ := exists_lintegral_planarNuDefect_le hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hsub⟩ := exists_planarNuMean_ahomInv_sub_le hpc
  set c := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨C₁.toReal + C₂, by positivity, c, hc, fun n m hnm q => ?_⟩
  set ξ := (planarAhom p)⁻¹ *ᵥ q with hξ
  have h := hdef ⟨m, 0⟩ ⟨n, 0⟩ n hnm rfl ξ
  have hmeans := hsub n m hnm q
  rw [← hξ] at hmeans
  have hfU := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p ⟨m, 0⟩ ξ)
  have hfW := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p ⟨n, 0⟩ ξ)
  set Qξ := (|ξ 0| + |ξ 1|) ^ 2 with hQξ
  set Qr := (|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
    |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2 with hQr
  have hQξ0 : 0 ≤ Qξ := by positivity
  have hQr0 : 0 ≤ Qr := by positivity
  have hvol := (⟨m, 0⟩ : TriadicCube 2).volume_pos
  have hε : ∀ k : ℕ, ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * (3 : ℝ) ^ k) ≤
      Real.exp (-c * (3 : ℝ) ^ k) := fun k c' hc' => by
    apply Real.exp_le_exp.2
    have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
    nlinarith
  set A := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (planarNuDefect ω ⟨m, 0⟩ n ξ) else 0) ∂(latticeBondLaw 2 p) with hA
  have hR : ENNReal.ofReal (⟨m, 0⟩ : TriadicCube 2).volume *
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
      ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) else 0) ∂(latticeBondLaw 2 p) +
      C₁ * ENNReal.ofReal (Qξ * (⟨m, 0⟩ : TriadicCube 2).volume *
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
  have hdiv : A.toReal / (⟨m, 0⟩ : TriadicCube 2).volume ≤
      (planarNuMean p n ξ - planarNuMean p m ξ) +
      C₁.toReal * (Qξ * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) := by
    rw [div_le_iff₀ hvol]
    simp only [planarNuMean]
    nlinarith
  set S := ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))
    with hSdef
  set e := 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) with hedef
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => by positivity
  have hS₂ : ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤ S :=
    Finset.sum_le_sum fun k _ => add_le_add le_rfl (hε k c₂ (min_le_right _ _))
  have he₁ := hε n c₁ (min_le_left _ _)
  have hen : 0 ≤ e := by positivity
  have hC₁0 : 0 ≤ C₁.toReal := ENNReal.toReal_nonneg
  have k1 : C₁.toReal * (Qξ * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) ≤
      C₁.toReal * (Qξ * e) := by
    rw [hedef]
    gcongr
  have k2 : C₂ * Qr * ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤ C₂ * Qr * S := by
    gcongr
  have hextra : 0 ≤ C₁.toReal * Qξ * S + C₁.toReal * Qr * (S + e) + C₂ * Qξ * (S + e) +
      C₂ * Qr * e := by positivity
  have hsplit : (C₁.toReal + C₂) * (Qξ + Qr) * (S + e) = C₁.toReal * (Qξ * e) + C₂ * Qr * S +
      (C₁.toReal * Qξ * S + C₁.toReal * Qr * (S + e) + C₂ * Qξ * (S + e) + C₂ * Qr * e) := by
    ring
  rw [hsplit]
  linarith

/-- **Lemma 5.4 of Armstrong and Dario for `ν`, qualitative form** (in dimension two). There is a
sequence `R_n → 0` such that for all `m ≥ n` and `q`, the expected energy of the differences
between the maximizer of `ν(□_m, ā⁻¹ q)` restricted to the resolved subcubes of scale `n` and the
maximizers on these subcubes, divided by `|□_m|`, is at most
`(|q|² + |ā⁻¹ q|₁² + |ā⁻¹ q̄|₁²) R_n`. -/
theorem exists_planarNuDefect_le_tendsto {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ R : ℕ → ℝ, Tendsto R atTop (𝓝 0) ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          ENNReal.ofReal (planarNuDefect ω ⟨m, 0⟩ n ((planarAhom p)⁻¹ *ᵥ q)) else 0)
          ∂(latticeBondLaw 2 p)).toReal / (⟨m, 0⟩ : TriadicCube 2).volume ≤
        (q 0 ^ 2 + q 1 ^ 2 +
          ((|((planarAhom p)⁻¹ *ᵥ q) 0| + |((planarAhom p)⁻¹ *ᵥ q) 1|) ^ 2 +
            (|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
              |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2)) * R n := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_planarNuDefect_le_planarNuTau hpc
  set ε : ℕ → ℝ := fun k => 1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k) with hεdef
  have hε0 : ∀ k, 0 ≤ ε k := fun k => by positivity
  have hεs : Summable ε := summable_planarError hc
  have hτs : Summable (planarNuTau p) :=
    Summable.of_nonneg_of_le (planarNuTau_nonneg p)
      (fun k => le_add_of_nonneg_left (planarMuTau_nonneg p k)) (summable_planarTau hpc)
  refine ⟨fun n => 2 * ∑' k, planarNuTau p (k + n) + C * (∑' k, ε (k + n) + ε n), ?_, ?_⟩
  · have h1 := tendsto_sum_nat_add (planarNuTau p)
    have h2 := tendsto_sum_nat_add ε
    have h3 : Tendsto ε atTop (𝓝 0) := hεs.tendsto_atTop_zero
    have := (h1.const_mul 2).add ((h2.add h3).const_mul C)
    simpa only [mul_zero, add_zero] using this
  · intro n m hnm q
    refine (h n m hnm q).trans ?_
    set Q := (|((planarAhom p)⁻¹ *ᵥ q) 0| + |((planarAhom p)⁻¹ *ᵥ q) 1|) ^ 2 +
      (|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
        |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2 with hQ
    have hT := sum_Ico_le_tsum_nat_add hτs (planarNuTau_nonneg p) n m
    have hE := sum_Ico_le_tsum_nat_add hεs hε0 n m
    have hTn : 0 ≤ ∑' k, planarNuTau p (k + n) := tsum_nonneg fun k => planarNuTau_nonneg p _
    have hEn : 0 ≤ ∑' k, ε (k + n) := tsum_nonneg fun k => hε0 _
    have hq2 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have k1 : 2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarNuTau p k ≤
        (q 0 ^ 2 + q 1 ^ 2) * (2 * ∑' k, planarNuTau p (k + n)) := by
      nlinarith
    have k2 : C * Q * (∑ k ∈ Finset.Ico n m, ε k + ε n) ≤
        Q * (C * (∑' k, ε (k + n) + ε n)) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hE (le_refl (ε n)))
        (mul_nonneg hC hQ0)
      linarith
    have k3 : 0 ≤ (q 0 ^ 2 + q 1 ^ 2) * (C * (∑' k, ε (k + n) + ε n)) :=
      mul_nonneg hq2 (mul_nonneg hC (add_nonneg hEn (hε0 n)))
    have k4 : 0 ≤ Q * (2 * ∑' k, planarNuTau p (k + n)) := by positivity
    have e : (q 0 ^ 2 + q 1 ^ 2 + Q) *
        (2 * ∑' k, planarNuTau p (k + n) + C * (∑' k, ε (k + n) + ε n)) =
        (q 0 ^ 2 + q 1 ^ 2) * (2 * ∑' k, planarNuTau p (k + n)) +
        Q * (C * (∑' k, ε (k + n) + ε n)) +
        (q 0 ^ 2 + q 1 ^ 2) * (C * (∑' k, ε (k + n) + ε n)) +
        Q * (2 * ∑' k, planarNuTau p (k + n)) := by ring
    rw [e]
    simp only [hεdef] at k2 ⊢
    linarith

end Rigidity.Percolation
