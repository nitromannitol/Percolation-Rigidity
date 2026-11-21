import Rigidity.Proofs.Percolation.PlanarFiniteVolumeInverse
import Rigidity.Proofs.Percolation.PlanarNuIncrements
import Rigidity.Proofs.Percolation.PlanarQuadraticTrace

/-!
# The decrease of `D_n` along `τ_n`

Following Step 1 of the proof of Lemma 5.10 of Armstrong and Dario, let

`D_n = ∑ᵢ (E[ν(□_n, eᵢ)] - E[μ(□_n, ā_{□_n} eᵢ)] - eᵢ · ā_{□_n} eᵢ)`.

Testing the minimum characterization of `ā_{□_{n+1}} eᵢ` with `ā_{□_n} eᵢ` gives
`D_{n+1} ≤ D_n - ∑ᵢ J_n(eᵢ) - ∑ᵢ I_n(ā_{□_n} eᵢ)`, where `I_n`, `J_n` are the increments of `E[-μ]`
and `E[ν]`. These are almost nonnegative quadratic forms, and comparing their sums over the bases
`(eᵢ)`, `(ā_{□_n} eᵢ)` and `(ā⁻¹ eᵢ)` gives, for `n ≥ N`,

`D_{n+1} ≤ D_n - c τ_n + C (3^(-n/2) + exp (-c' 3ⁿ))`

(the inequality of Step 1 of the proof of Lemma 5.10 of Armstrong and Dario, in dimension two).
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix

namespace Rigidity.Percolation

/-- The quantity `D_n` of Armstrong and Dario (proof of Lemma 5.10), in dimension two. -/
noncomputable def planarOmegaD (p : unitInterval) (n : ℕ) : ℝ :=
  ∑ i : Fin 2, (planarNuMean p n (Pi.single i 1) +
    planarMuMean p n (planarAhomFinite p n *ᵥ Pi.single i 1) -
    (planarAhomFinite p n *ᵥ Pi.single i 1) i)

theorem sum_single_mul (i : Fin 2) (x : Fin 2 → ℝ) :
    ∑ j, (Pi.single i 1 : Fin 2 → ℝ) j * x j = x i := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem isPlanarQuadratic_planarMuIncrement {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (k : ℕ) : IsPlanarQuadratic (planarMuIncrement p k) := by
  intro r s a b
  simp only [planarMuIncrement]
  rw [planarMuMean_smul_add_smul hpc k, planarMuMean_smul_add_smul hpc (k + 1)]
  ring

theorem isPlanarQuadratic_planarNuIncrement (p : unitInterval) (k : ℕ) :
    IsPlanarQuadratic (planarNuIncrement p k) := by
  intro r s a b
  simp only [planarNuIncrement]
  rw [planarNuMean_smul_add_smul p k, planarNuMean_smul_add_smul p (k + 1)]
  ring

theorem IsPlanarQuadratic.add_sq {g : (Fin 2 → ℝ) → ℝ} (hg : IsPlanarQuadratic g) (K : ℝ) :
    IsPlanarQuadratic fun q => g q + K * (q 0 ^ 2 + q 1 ^ 2) := by
  intro r s a b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hg]
  ring

/-- `|q|₁² ≤ 2 |q|²`, the almost nonnegativity of a quadratic form in the Euclidean form. -/
theorem add_two_mul_nonneg_of_neg_le {g : (Fin 2 → ℝ) → ℝ} {K : ℝ}
    (h : ∀ q, -(K * (|q 0| + |q 1|) ^ 2) ≤ g q) (hK : 0 ≤ K) (q : Fin 2 → ℝ) :
    0 ≤ g q + 2 * K * (q 0 ^ 2 + q 1 ^ 2) := by
  have h1 := h q
  have h2 := mul_le_mul_of_nonneg_left (abs_add_abs_sq_le q) hK
  linarith

/-- **The decrease of `D_n` along `τ_n`** (Armstrong and Dario, Step 1 of the proof of Lemma 5.10,
in dimension two). -/
theorem exists_planarOmegaD_succ_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      planarOmegaD p (n + 1) ≤ planarOmegaD p n - c * planarTau p n +
        C * (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c' * (3 : ℝ) ^ n)) := by
  obtain ⟨Cb, hCb, N, hN⟩ := exists_planarAhomInvFinite_mulVec_planarAhomFinite hpc
  obtain ⟨Cμ, hCμ, cμ, hcμ, hIμ⟩ := exists_neg_le_planarMuIncrement hpc
  obtain ⟨Cν, hCν, cν, hcν, hJν⟩ := exists_neg_le_planarNuIncrement hpc
  set F := ∑ i : Fin 2, ((planarAhomInvSingle p i) 0 ^ 2 + (planarAhomInvSingle p i) 1 ^ 2)
    with hFdef
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => by positivity
  set H := 16 * Cb ^ 2 + 1 with hHdef
  have hH : 0 < H := by positivity
  set c' := min cμ cν with hc'def
  have hc' : 0 < c' := lt_min hcμ hcν
  refine ⟨min (1 / (2 * H)) (1 / (2 * F + 1)), by positivity, 1296 * Cμ + 4 * Cν, by positivity,
    c', hc', N, fun n hn => ?_⟩
  obtain ⟨hinv, hinv', hb⟩ := hN n hn
  obtain ⟨hinv1, -, hb1⟩ := hN (n + 1) (by omega)
  set A := planarAhomFinite p n with hAdef
  set B := planarAhomInvFinite p n with hBdef
  set ε := 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c' * (3 : ℝ) ^ n) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hεμ : 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-cμ * (3 : ℝ) ^ n) ≤ ε := by
    refine add_le_add le_rfl (Real.exp_le_exp.2 ?_)
    have : (0 : ℝ) ≤ 3 ^ n := by positivity
    nlinarith [min_le_left cμ cν]
  have hεν : 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-cν * (3 : ℝ) ^ n) ≤ ε := by
    refine add_le_add le_rfl (Real.exp_le_exp.2 ?_)
    have : (0 : ℝ) ≤ 3 ^ n := by positivity
    nlinarith [min_le_right cμ cν]
  -- Step (a): the minimum characterization at scale `n + 1`
  have hstep : planarOmegaD p (n + 1) ≤ planarOmegaD p n -
      ∑ i : Fin 2, planarNuIncrement p n (Pi.single i 1) -
      ∑ i : Fin 2, planarMuIncrement p n (A *ᵥ Pi.single i 1) := by
    have hmin : ∀ i : Fin 2,
        planarMuMean p (n + 1) (planarAhomFinite p (n + 1) *ᵥ Pi.single i 1) -
          (planarAhomFinite p (n + 1) *ᵥ Pi.single i 1) i ≤
        planarMuMean p (n + 1) (A *ᵥ Pi.single i 1) - (A *ᵥ Pi.single i 1) i := by
      intro i
      have h := planarMuMean_planarAhomFinite_sub_le hpc hinv1 (Pi.single i 1)
        (A *ᵥ Pi.single i 1)
      rwa [sum_single_mul, sum_single_mul] at h
    simp only [planarOmegaD, planarNuIncrement, planarMuIncrement, ← hAdef, Fin.sum_univ_two]
    linarith [hmin 0, hmin 1]
  -- Step (b): the `μ` part
  set gI : (Fin 2 → ℝ) → ℝ := fun q =>
    planarMuIncrement p n q + 2 * (Cμ * ε) * (q 0 ^ 2 + q 1 ^ 2) with hgI
  have hgI0 : ∀ q, 0 ≤ gI q := fun q => by
    have h := add_two_mul_nonneg_of_neg_le (g := planarMuIncrement p n) (K := Cμ * ε)
      (fun q => by
        have := hIμ n q
        have : Cμ * ((|q 0| + |q 1|) ^ 2 *
            (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-cμ * (3 : ℝ) ^ n))) ≤
            Cμ * ε * (|q 0| + |q 1|) ^ 2 := by
          have hq : 0 ≤ (|q 0| + |q 1|) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hεμ (mul_nonneg hCμ hq)
          linarith
        linarith) (by positivity) q
    simpa [hgI] using h
  have hgIq : IsPlanarQuadratic gI := (isPlanarQuadratic_planarMuIncrement hpc n).add_sq _
  have hBA : ∀ i : Fin 2, A *ᵥ (B *ᵥ Pi.single i 1) = Pi.single i 1 := fun i => hinv' _
  have htr := hgIq.sum_single_le hgI0 A (hBA 0) (hBA 1)
  -- bound on the columns of `B`
  have hBe : ∀ a i : Fin 2, (B *ᵥ Pi.single i 1) a ^ 2 ≤ 4 * Cb ^ 2 := by
    have u10 : planarMuMean p n ![1, 0] ≤ Cb := by simpa using (hb ![1, 0]).2
    have u01 : planarMuMean p n ![0, 1] ≤ Cb := by simpa using (hb ![0, 1]).2
    have u11 : planarMuMean p n ![1, 1] ≤ 2 * Cb := by
      have := (hb ![1, 1]).2
      norm_num at this
      linarith
    have z10 : 0 ≤ planarMuMean p n ![1, 0] := ENNReal.toReal_nonneg
    have z01 : 0 ≤ planarMuMean p n ![0, 1] := ENNReal.toReal_nonneg
    have z11 : 0 ≤ planarMuMean p n ![1, 1] := ENNReal.toReal_nonneg
    have hcol : ∀ a i : Fin 2, (B *ᵥ Pi.single i 1) a = B a i := fun a i => by
      simp [Matrix.mulVec]
    have b00 : B 0 0 = 2 * planarMuMean p n ![1, 0] := rfl
    have b01 : B 0 1 = planarMuMean p n ![1, 1] - planarMuMean p n ![1, 0] -
      planarMuMean p n ![0, 1] := rfl
    have b10 : B 1 0 = planarMuMean p n ![1, 1] - planarMuMean p n ![1, 0] -
      planarMuMean p n ![0, 1] := rfl
    have b11 : B 1 1 = 2 * planarMuMean p n ![0, 1] := rfl
    have h2 : 4 * Cb ^ 2 = (2 * Cb) ^ 2 := by ring
    intro a i
    rw [hcol, h2]
    fin_cases a <;> fin_cases i
    · exact sq_le_sq' (by simp only [Fin.zero_eta]; rw [b00]; linarith)
        (by simp only [Fin.zero_eta]; rw [b00]; linarith)
    · exact sq_le_sq' (by simp only [Fin.zero_eta, Fin.mk_one]; rw [b01]; linarith)
        (by simp only [Fin.zero_eta, Fin.mk_one]; rw [b01]; linarith)
    · exact sq_le_sq' (by simp only [Fin.zero_eta, Fin.mk_one]; rw [b10]; linarith)
        (by simp only [Fin.zero_eta, Fin.mk_one]; rw [b10]; linarith)
    · exact sq_le_sq' (by simp only [Fin.mk_one]; rw [b11]; linarith)
        (by simp only [Fin.mk_one]; rw [b11]; linarith)
  have hH' : 2 * (((B *ᵥ Pi.single 0 1) 0 ^ 2 + (B *ᵥ Pi.single 0 1) 1 ^ 2) +
      ((B *ᵥ Pi.single 1 1) 0 ^ 2 + (B *ᵥ Pi.single 1 1) 1 ^ 2)) ≤ 2 * H := by
    have := hBe 0 0
    have := hBe 1 0
    have := hBe 0 1
    have := hBe 1 1
    rw [hHdef]
    linarith
  have hAe : ∀ i : Fin 2, (A *ᵥ Pi.single i 1) 0 ^ 2 + (A *ᵥ Pi.single i 1) 1 ^ 2 ≤ 324 :=
    fun i => planarAhomFinite_single_sq_le hpc hinv (fun q => (hb q).1) i
  have hsumA0 : 0 ≤ gI (A *ᵥ Pi.single 0 1) + gI (A *ᵥ Pi.single 1 1) :=
    add_nonneg (hgI0 _) (hgI0 _)
  have hτμ : planarMuTau p n ≤ gI (Pi.single 0 1) + gI (Pi.single 1 1) := by
    rw [planarMuTau, Fin.sum_univ_two]
    have e0 : gI (Pi.single 0 1) = planarMuIncrement p n (Pi.single 0 1) + 2 * (Cμ * ε) := by
      simp [hgI]
    have e1 : gI (Pi.single 1 1) = planarMuIncrement p n (Pi.single 1 1) + 2 * (Cμ * ε) := by
      simp [hgI]
    have hCε : 0 ≤ 2 * (Cμ * ε) := by positivity
    refine add_le_add (max_le ?_ (hgI0 _)) (max_le ?_ (hgI0 _)) <;> linarith
  have hμpart : -∑ i : Fin 2, planarMuIncrement p n (A *ᵥ Pi.single i 1) ≤
      -(planarMuTau p n / (2 * H)) + 1296 * Cμ * ε := by
    have k1 : planarMuTau p n ≤ 2 * H * (gI (A *ᵥ Pi.single 0 1) + gI (A *ᵥ Pi.single 1 1)) :=
      hτμ.trans (htr.trans (mul_le_mul_of_nonneg_right hH' hsumA0))
    have k2 : gI (A *ᵥ Pi.single 0 1) + gI (A *ᵥ Pi.single 1 1) ≤
        ∑ i : Fin 2, planarMuIncrement p n (A *ᵥ Pi.single i 1) + 1296 * (Cμ * ε) := by
      rw [Fin.sum_univ_two]
      simp only [hgI]
      have hCε : 0 ≤ Cμ * ε := by positivity
      have := mul_le_mul_of_nonneg_left (hAe 0) hCε
      have := mul_le_mul_of_nonneg_left (hAe 1) hCε
      linarith
    have k3 : planarMuTau p n / (2 * H) ≤
        gI (A *ᵥ Pi.single 0 1) + gI (A *ᵥ Pi.single 1 1) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  -- Step (c): the `ν` part
  set gJ : (Fin 2 → ℝ) → ℝ := fun q =>
    planarNuIncrement p n q + 2 * (Cν * ε) * (q 0 ^ 2 + q 1 ^ 2) with hgJ
  have hgJ0 : ∀ q, 0 ≤ gJ q := fun q => by
    have h := add_two_mul_nonneg_of_neg_le (g := planarNuIncrement p n) (K := Cν * ε)
      (fun q => by
        have := hJν n q
        have : Cν * ((|q 0| + |q 1|) ^ 2 *
            (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-cν * (3 : ℝ) ^ n))) ≤
            Cν * ε * (|q 0| + |q 1|) ^ 2 := by
          have hq : 0 ≤ (|q 0| + |q 1|) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hεν (mul_nonneg hCν hq)
          linarith
        linarith) (by positivity) q
    simpa [hgJ] using h
  have hgJq : IsPlanarQuadratic gJ := (isPlanarQuadratic_planarNuIncrement p n).add_sq _
  have hτν : planarNuTau p n ≤ 2 * F * (gJ (Pi.single 0 1) + gJ (Pi.single 1 1)) := by
    rw [planarNuTau, Fin.sum_univ_two, hFdef, Fin.sum_univ_two]
    have k0 := hgJq.le_of_nonneg hgJ0 (planarAhomInvSingle p 0)
    have k1 := hgJq.le_of_nonneg hgJ0 (planarAhomInvSingle p 1)
    have m0 : max (planarNuIncrement p n (planarAhomInvSingle p 0)) 0 ≤
        gJ (planarAhomInvSingle p 0) := by
      refine max_le ?_ (hgJ0 _)
      simp only [hgJ]
      have : 0 ≤ 2 * (Cν * ε) * ((planarAhomInvSingle p 0) 0 ^ 2 +
        (planarAhomInvSingle p 0) 1 ^ 2) := by positivity
      linarith
    have m1 : max (planarNuIncrement p n (planarAhomInvSingle p 1)) 0 ≤
        gJ (planarAhomInvSingle p 1) := by
      refine max_le ?_ (hgJ0 _)
      simp only [hgJ]
      have : 0 ≤ 2 * (Cν * ε) * ((planarAhomInvSingle p 1) 0 ^ 2 +
        (planarAhomInvSingle p 1) 1 ^ 2) := by positivity
      linarith
    linarith
  have hνpart : -∑ i : Fin 2, planarNuIncrement p n (Pi.single i 1) ≤
      -(planarNuTau p n / (2 * F + 1)) + 4 * Cν * ε := by
    have e0 : gJ (Pi.single 0 1) = planarNuIncrement p n (Pi.single 0 1) + 2 * (Cν * ε) := by
      simp [hgJ]
    have e1 : gJ (Pi.single 1 1) = planarNuIncrement p n (Pi.single 1 1) + 2 * (Cν * ε) := by
      simp [hgJ]
    have hX0 : 0 ≤ gJ (Pi.single 0 1) + gJ (Pi.single 1 1) := add_nonneg (hgJ0 _) (hgJ0 _)
    have k3 : planarNuTau p n / (2 * F + 1) ≤ gJ (Pi.single 0 1) + gJ (Pi.single 1 1) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    rw [Fin.sum_univ_two]
    linarith
  -- Step (d): conclusion
  have hτ := planarTau_nonneg p n
  have hτμ0 := planarMuTau_nonneg p n
  have hτν0 := planarNuTau_nonneg p n
  have hcμ' : min (1 / (2 * H)) (1 / (2 * F + 1)) * planarMuTau p n ≤ planarMuTau p n / (2 * H) :=
    calc min (1 / (2 * H)) (1 / (2 * F + 1)) * planarMuTau p n
        ≤ 1 / (2 * H) * planarMuTau p n := mul_le_mul_of_nonneg_right (min_le_left _ _) hτμ0
      _ = planarMuTau p n / (2 * H) := by ring
  have hcν' : min (1 / (2 * H)) (1 / (2 * F + 1)) * planarNuTau p n ≤
      planarNuTau p n / (2 * F + 1) :=
    calc min (1 / (2 * H)) (1 / (2 * F + 1)) * planarNuTau p n
        ≤ 1 / (2 * F + 1) * planarNuTau p n := mul_le_mul_of_nonneg_right (min_le_right _ _) hτν0
      _ = planarNuTau p n / (2 * F + 1) := by ring
  have htau : planarTau p n = planarMuTau p n + planarNuTau p n := rfl
  rw [htau, mul_add]
  linarith

end Rigidity.Percolation
