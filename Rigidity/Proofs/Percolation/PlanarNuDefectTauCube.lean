import Rigidity.Proofs.Percolation.PlanarDefectTauCube
import Rigidity.Proofs.Percolation.PlanarOmegaLimit

/-!
# Lemma 5.4 of Armstrong and Dario for `ν` on every triadic cube

As `exists_lintegral_planarMuDefect_le_tau` for the maximizers of `ν`: for every triadic cube `□`
of scale `m`, `n ≤ m` and every slope `ξ`,
`E[1{𝒫, □ resolved} D^ν_n(□, ξ)] ≤ |□| C |ξ|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`
(`exists_lintegral_planarNuDefect_le_tau`). The decrease of `E[ν]` between two scales is controlled
by `τ^ν` at the slopes `ā⁻¹ q` (`exists_planarNuMean_ahomInv_sub_le`); for a slope `ξ` take
`q = ā ξ`, `ā` being invertible, and bound `|q|` and `|ā⁻¹ q̄|` by the entries of `ā` and `ā⁻¹`.
The approximate stationarity of `E[ν]` (`exists_lintegral_planarNu_le_of_scale_eq`) passes from
the cube centred at the origin to every cube of the same scale.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- The entries of a matrix-vector product are bounded by the entries of the matrix. -/
theorem abs_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    |(A *ᵥ v) i| ≤ (∑ k, ∑ l, |A k l|) * (|v 0| + |v 1|) := by
  have hS : ∀ k l, |A k l| ≤ ∑ k, ∑ l, |A k l| := fun k l =>
    (Finset.single_le_sum (f := fun l => |A k l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, |A k l|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k))
  have e : (A *ᵥ v) i = A i 0 * v 0 + A i 1 * v 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e]
  calc |A i 0 * v 0 + A i 1 * v 1| ≤ |A i 0| * |v 0| + |A i 1| * |v 1| := by
        rw [← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ (∑ k, ∑ l, |A k l|) * |v 0| + (∑ k, ∑ l, |A k l|) * |v 1| := by
        gcongr
        · exact hS i 0
        · exact hS i 1
    _ = _ := by ring

theorem sum_abs_mulVec_sq_le (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    (|(A *ᵥ v) 0| + |(A *ᵥ v) 1|) ^ 2 ≤ 4 * (∑ k, ∑ l, |A k l|) ^ 2 * (|v 0| + |v 1|) ^ 2 := by
  have h0 := abs_mulVec_le A v 0
  have h1 := abs_mulVec_le A v 1
  have hS : 0 ≤ ∑ k, ∑ l, |A k l| := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hv : 0 ≤ |v 0| + |v 1| := by positivity
  have h2 : |(A *ᵥ v) 0| + |(A *ᵥ v) 1| ≤ 2 * ((∑ k, ∑ l, |A k l|) * (|v 0| + |v 1|)) := by
    linarith
  calc (|(A *ᵥ v) 0| + |(A *ᵥ v) 1|) ^ 2
      ≤ (2 * ((∑ k, ∑ l, |A k l|) * (|v 0| + |v 1|))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
    _ = _ := by ring

/-- The boundary errors at the three rates are at most `C 3^{-n/4}`. -/
theorem planarError_terms_le {c₁ c₂ c₃ Ce : ℝ} (hc : 0 < min c₁ (min c₂ c₃))
    (herr : ∀ k n : ℕ, ∑ l ∈ Finset.Ico k n, (1 / Real.sqrt ((3 : ℝ) ^ l) +
        Real.exp (-min c₁ (min c₂ c₃) * (3 : ℝ) ^ l)) +
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-min c₁ (min c₂ c₃) * (3 : ℝ) ^ k)) ≤
      Ce * (3 : ℝ) ^ (-(k : ℝ) / 4)) {n m : ℕ} (hn : n ≤ m) :
    ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₃ * (3 : ℝ) ^ k)) ≤
        Ce * (3 : ℝ) ^ (-(n : ℝ) / 4) ∧
      Real.exp (-c₂ * (3 : ℝ) ^ m) ≤ Ce * (3 : ℝ) ^ (-(n : ℝ) / 4) ∧
      1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n) ≤ Ce * (3 : ℝ) ^ (-(n : ℝ) / 4) := by
  set c := min c₁ (min c₂ c₃) with hcdef
  have h := herr n m
  have hε : ∀ k : ℕ, ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * (3 : ℝ) ^ k) ≤
      Real.exp (-c * (3 : ℝ) ^ k) := fun k c' hc' => by
    apply Real.exp_le_exp.2
    have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
    nlinarith
  have hS0 : 0 ≤ ∑ l ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ l) +
      Real.exp (-c * (3 : ℝ) ^ l)) := Finset.sum_nonneg fun k _ => by positivity
  have hen0 : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have k1 : ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₃ * (3 : ℝ) ^ k)) ≤
        ∑ l ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ l) + Real.exp (-c * (3 : ℝ) ^ l)) :=
      Finset.sum_le_sum fun k _ => add_le_add le_rfl
        (hε k c₃ ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  · have h1 : Real.exp (-c₂ * (3 : ℝ) ^ m) ≤ Real.exp (-c * (3 : ℝ) ^ m) :=
      hε m c₂ ((min_le_right _ _).trans (min_le_left _ _))
    have h2 : Real.exp (-c * (3 : ℝ) ^ m) ≤ Real.exp (-c * (3 : ℝ) ^ n) := by
      apply Real.exp_le_exp.2
      have h3 : (3 : ℝ) ^ n ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) hn
      nlinarith
    have h4 : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) := by positivity
    linarith
  · have k3 : 1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n) ≤
        1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) :=
      add_le_add le_rfl (hε n c₁ (min_le_left _ _))
    linarith

/-- The arithmetic of the final bound of Lemma 5.4 for `ν`. -/
theorem nuDefect_arith {A vol W O C₁ C₂ C₃ Qξ e₁ e₂ Pq Qb Tν T S P Sa Sb Ce x : ℝ}
    (hvol : 0 ≤ vol) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hCe : 0 ≤ Ce) (hx : 0 ≤ x)
    (hP : 0 ≤ P) (hT : 0 ≤ T) (hS0 : 0 ≤ S) (he₁0 : 0 ≤ e₁) (he₂0 : 0 ≤ e₂)
    (hTν0 : 0 ≤ Tν)
    (hA1 : A ≤ vol * (W - O) + vol * (C₂ * (Qξ * e₂)) + C₁ * (Qξ * vol * e₁))
    (hmeans : W - O ≤ 2 * Pq * Tν + C₃ * Qb * S) (hτ : Tν ≤ T) (hS : S ≤ Ce * x)
    (he₂ : e₂ ≤ Ce * x) (he₁ : e₁ ≤ Ce * x) (hPq : Pq ≤ 8 * Sa ^ 2 * P)
    (hQb : Qb ≤ 32 * Sa ^ 2 * Sb ^ 2 * P) (hQξ : Qξ ≤ 2 * P) :
    A ≤ vol * ((16 * Sa ^ 2 + (32 * Sa ^ 2 * Sb ^ 2 * C₃ + 2 * C₂ + 2 * C₁) * Ce) * P * (T + x)) := by
  have hE0 : 0 ≤ Ce * x := mul_nonneg hCe hx
  have h1 : W - O ≤ 2 * (8 * Sa ^ 2 * P) * T + C₃ * (32 * Sa ^ 2 * Sb ^ 2 * P) * (Ce * x) := by
    have ha : 2 * Pq * Tν ≤ 2 * (8 * Sa ^ 2 * P) * T :=
      mul_le_mul (by linarith) hτ hTν0 (by positivity)
    have hb : C₃ * Qb * S ≤ C₃ * (32 * Sa ^ 2 * Sb ^ 2 * P) * (Ce * x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hQb hC₃) hS hS0 (by positivity)
    linarith
  have h2 : C₂ * (Qξ * e₂) ≤ C₂ * (2 * P * (Ce * x)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hQξ he₂ he₂0 (by positivity)) hC₂
  have h3 : C₁ * (Qξ * e₁) ≤ C₁ * (2 * P * (Ce * x)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hQξ he₁ he₁0 (by positivity)) hC₁
  have hk1 := mul_le_mul_of_nonneg_left h1 hvol
  have hk2 := mul_le_mul_of_nonneg_left h2 hvol
  have hk3 := mul_le_mul_of_nonneg_left h3 hvol
  have e1 : C₁ * (Qξ * vol * e₁) = vol * (C₁ * (Qξ * e₁)) := by ring
  have key : A ≤ vol * (2 * (8 * Sa ^ 2 * P) * T + C₃ * (32 * Sa ^ 2 * Sb ^ 2 * P) * (Ce * x) +
      C₂ * (2 * P * (Ce * x)) + C₁ * (2 * P * (Ce * x))) := by
    have e2 : vol * (2 * (8 * Sa ^ 2 * P) * T + C₃ * (32 * Sa ^ 2 * Sb ^ 2 * P) * (Ce * x) +
        C₂ * (2 * P * (Ce * x)) + C₁ * (2 * P * (Ce * x))) =
        vol * (2 * (8 * Sa ^ 2 * P) * T + C₃ * (32 * Sa ^ 2 * Sb ^ 2 * P) * (Ce * x)) +
        vol * (C₂ * (2 * P * (Ce * x))) + vol * (C₁ * (2 * P * (Ce * x))) := by ring
    rw [e2]
    linarith
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hvol)
  have h5 : 0 ≤ 16 * Sa ^ 2 * P * x := by positivity
  have h6 : 0 ≤ (32 * Sa ^ 2 * Sb ^ 2 * C₃ + 2 * C₂ + 2 * C₁) * Ce * P * T := by positivity
  have expand : (16 * Sa ^ 2 + (32 * Sa ^ 2 * Sb ^ 2 * C₃ + 2 * C₂ + 2 * C₁) * Ce) * P * (T + x) =
      (2 * (8 * Sa ^ 2 * P) * T + C₃ * (32 * Sa ^ 2 * Sb ^ 2 * P) * (Ce * x) +
        C₂ * (2 * P * (Ce * x)) + C₁ * (2 * P * (Ce * x))) + 16 * Sa ^ 2 * P * x +
      (32 * Sa ^ 2 * Sb ^ 2 * C₃ + 2 * C₂ + 2 * C₁) * Ce * P * T := by ring
  rw [expand]
  linarith

/-- The probabilistic part of Lemma 5.4 for `ν` on every triadic cube: the energy of the
differences in terms of the decrease of `E[ν]`, with the stationarity error. -/
theorem exists_planarNuDefect_toReal_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin 2 → ℝ,
      (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) ∂(latticeBondLaw 2 p)) ≠ ∞ ∧
      (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) ∂(latticeBondLaw 2 p)).toReal ≤
        U.volume * (planarNuMean p n ξ - planarNuMean p U.scale ξ) +
        U.volume * (C₂ * ((|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c₂ * (3 : ℝ) ^ U.scale))) +
        C₁ * ((|ξ 0| + |ξ 1|) ^ 2 * U.volume *
          (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hdef⟩ := exists_lintegral_planarNuDefect_le hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hst⟩ := exists_lintegral_planarNu_le_of_scale_eq hpc
  refine ⟨C₁.toReal, ENNReal.toReal_nonneg, c₁, hc₁, C₂.toReal, ENNReal.toReal_nonneg, c₂, hc₂,
    fun U n hn ξ => ?_⟩
  have hup : ∀ V : TriadicCube 2, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
      ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) := by
    intro V
    calc ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω V then
          ENNReal.ofReal (planarNu ω V ξ) else 0) ∂(latticeBondLaw 2 p)
        ≤ ∫⁻ _ω, ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) ∂(latticeBondLaw 2 p) :=
          lintegral_mono fun ω => by
            split_ifs
            · exact ENNReal.ofReal_le_ofReal (planarNu_le ξ)
            · exact zero_le
      _ = ENNReal.ofReal (9 / 4 * (|ξ 0| + |ξ 1|) ^ 2) := by
          rw [lintegral_const, measure_univ, mul_one]
  have h := hdef U ⟨n, 0⟩ n hn rfl ξ
  have hs := hst U ⟨U.scale, 0⟩ rfl ξ
  have hfU := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup U)
  have hfW := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup ⟨n, 0⟩)
  have hvol := U.volume_pos
  have hR := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := U.volume)) hfW,
    ENNReal.mul_ne_top hC₁ (ENNReal.ofReal_ne_top (r := (|ξ 0| + |ξ 1|) ^ 2 * U.volume *
      (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))))⟩
  have hAfin := ne_top_of_le_ne_top hR (le_trans le_self_add h)
  refine ⟨hAfin, ?_⟩
  have hreal := ENNReal.toReal_mono hR h
  rw [ENNReal.toReal_add hAfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfU),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfW)
      (ENNReal.mul_ne_top hC₁ ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hvol.le, ENNReal.toReal_ofReal (by positivity)] at hreal
  have hRs := ENNReal.add_ne_top.2 ⟨hfU, ENNReal.mul_ne_top hC₂ (ENNReal.ofReal_ne_top
    (r := (|ξ 0| + |ξ 1|) ^ 2 * Real.exp (-c₂ * (3 : ℝ) ^ U.scale)))⟩
  have hsr := ENNReal.toReal_mono hRs hs
  rw [ENNReal.toReal_add hfU (ENNReal.mul_ne_top hC₂ ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hsr
  have hmW : planarNuMean p n ξ = (∫⁻ ω, (if PlanarPartitionEvent ω ∧
      PlanarResolved ω ⟨n, 0⟩ then ENNReal.ofReal (planarNu ω ⟨n, 0⟩ ξ) else 0)
      ∂(latticeBondLaw 2 p)).toReal := rfl
  have hmO : planarNuMean p U.scale ξ = (∫⁻ ω, (if PlanarPartitionEvent ω ∧
      PlanarResolved ω ⟨U.scale, 0⟩ then ENNReal.ofReal (planarNu ω ⟨U.scale, 0⟩ ξ) else 0)
      ∂(latticeBondLaw 2 p)).toReal := rfl
  rw [hmW, hmO]
  have h1 := mul_le_mul_of_nonneg_left hsr hvol.le
  rw [mul_add] at h1
  linarith

/-- **Lemma 5.4 of Armstrong and Dario for `ν`, on every triadic cube** (display (5.10), second
term, in dimension two). -/
theorem exists_lintegral_planarNuDefect_le_tau {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : TriadicCube 2) (n : ℕ), n ≤ U.scale → ∀ ξ : Fin 2 → ℝ,
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) ∂(latticeBondLaw 2 p) ≤
        ENNReal.ofReal (U.volume * (C * (ξ 0 ^ 2 + ξ 1 ^ 2) *
          (∑ k ∈ Finset.Ico n U.scale, planarTau p k + (3 : ℝ) ^ (-(n : ℝ) / 4)))) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, C₂, hC₂, c₂, hc₂, hA⟩ := exists_planarNuDefect_toReal_le hpc
  obtain ⟨C₃, hC₃, c₃, hc₃, hsub⟩ := exists_planarNuMean_ahomInv_sub_le hpc
  have hc : 0 < min c₁ (min c₂ c₃) := lt_min hc₁ (lt_min hc₂ hc₃)
  obtain ⟨Ce, hCe, herr⟩ := exists_sum_planarError_le hc
  set Sa : ℝ := ∑ k, ∑ l, |planarAhom p k l| with hSa
  set Sb : ℝ := ∑ k, ∑ l, |(planarAhom p)⁻¹ k l| with hSb
  have hSa0 : 0 ≤ Sa := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdet := planarAhom_det_ne_zero hpc
  refine ⟨16 * Sa ^ 2 + (32 * Sa ^ 2 * Sb ^ 2 * C₃ + 2 * C₂ + 2 * C₁) * Ce, by positivity,
    fun U n hn ξ => ?_⟩
  obtain ⟨hAfin, hA1⟩ := hA U n hn ξ
  set q : Fin 2 → ℝ := planarAhom p *ᵥ ξ with hqdef
  have hbq : (planarAhom p)⁻¹ *ᵥ q = ξ := by
    rw [hqdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have hmeans := hsub n U.scale hn q
  rw [hbq] at hmeans
  have hQξ2 : (|ξ 0| + |ξ 1|) ^ 2 ≤ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := abs_add_abs_sq_le ξ
  have hqsq : (|q 0| + |q 1|) ^ 2 ≤ 4 * Sa ^ 2 * (|ξ 0| + |ξ 1|) ^ 2 := sum_abs_mulVec_sq_le _ ξ
  have hPq8 : q 0 ^ 2 + q 1 ^ 2 ≤ 8 * Sa ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
    have h1 : q 0 ^ 2 + q 1 ^ 2 ≤ (|q 0| + |q 1|) ^ 2 := by
      have := sq_abs (q 0)
      have := sq_abs (q 1)
      nlinarith [abs_nonneg (q 0), abs_nonneg (q 1)]
    have h2 := mul_le_mul_of_nonneg_left hQξ2 (by positivity : (0 : ℝ) ≤ 4 * Sa ^ 2)
    linarith
  have hQb : (|((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 0| +
      |((planarAhom p)⁻¹ *ᵥ ![q 0, -q 1]) 1|) ^ 2 ≤ 32 * Sa ^ 2 * Sb ^ 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
    have h1 := sum_abs_mulVec_sq_le (planarAhom p)⁻¹ ![q 0, -q 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_neg] at h1
    have h2 := mul_le_mul_of_nonneg_left hqsq (by positivity : (0 : ℝ) ≤ 4 * Sb ^ 2)
    have h3 := mul_le_mul_of_nonneg_left hQξ2 (by positivity : (0 : ℝ) ≤ 4 * Sb ^ 2 * (4 * Sa ^ 2))
    nlinarith
  obtain ⟨hS, he₂, he₁⟩ := planarError_terms_le (c₃ := c₃) hc herr hn
  have hτν : ∑ k ∈ Finset.Ico n U.scale, planarNuTau p k ≤
      ∑ k ∈ Finset.Ico n U.scale, planarTau p k :=
    Finset.sum_le_sum fun k _ => le_add_of_nonneg_left (planarMuTau_nonneg p k)
  have hfinal := nuDefect_arith U.volume_pos.le hC₁ hC₂ hC₃ hCe (by positivity : (0 : ℝ) ≤
      (3 : ℝ) ^ (-(n : ℝ) / 4)) (by positivity : (0 : ℝ) ≤ ξ 0 ^ 2 + ξ 1 ^ 2)
    (Finset.sum_nonneg fun k _ => planarTau_nonneg p k) (Finset.sum_nonneg fun k _ => by positivity)
    (by positivity) (Real.exp_pos _).le
    (Finset.sum_nonneg fun k _ => planarNuTau_nonneg p k)
    hA1 hmeans hτν hS he₂ he₁ hPq8 hQb hQξ2
  calc _ = ENNReal.ofReal (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω U then
          ENNReal.ofReal (planarNuDefect ω U n ξ) else 0) ∂(latticeBondLaw 2 p)).toReal :=
        (ENNReal.ofReal_toReal hAfin).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfinal

end Rigidity.Percolation
