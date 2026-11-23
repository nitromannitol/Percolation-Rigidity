import Rigidity.Proofs.Cluster.GeneralTauIncrements

/-!
# The finite-volume matrices `ā_{□_n}⁻¹` of Armstrong and Dario, in every dimension

Armstrong and Dario define `ā_{□_n}⁻¹` as the matrix of the quadratic form
`q ↦ 2 E[-μ(□_n, q)]` (display (5.21)). Here `cubeAhomInvFinite p n` is the polarization matrix
`(E[-μ(□_n, eᵢ + eⱼ)] - E[-μ(□_n, eᵢ)] - E[-μ(□_n, eⱼ)])ᵢⱼ` of `q ↦ E[-μ(□_n, q)]`
(`cubeMuMean`, on the event that the partition exists and resolves `□_n`), so that
`(1/2) q · ā_{□_n}⁻¹ q = E[-μ(□_n, q)]` (`half_sum_mul_cubeAhomInvFinite_eq`).

Summing the increments of `E[-μ]` between the scales `n ≤ m`, bounded above through `τ_k` by
display (5.9) and below by the approximate monotonicity (4.48),

`|E[-μ(□_n, q)] - E[-μ(□_m, q)]| ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`

(`exists_abs_cubeMuMean_sub_le`), and by polarization every entry of `ā_{□_m}⁻¹ - ā_{□_n}⁻¹` is
at most `C (∑_{k=n}^{m-1} τ_k + 3^{-n/4})` (`exists_abs_cubeAhomInvFinite_sub_le`, display (5.24) of
Armstrong and Dario, in every dimension `d ≥ 2`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **The matrix `ā_{□_n}⁻¹`** of Armstrong and Dario (display (5.21)): the polarization matrix of
`q ↦ E[-μ(□_n, q)]`. -/
noncomputable def cubeAhomInvFinite (p : unitInterval) (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => slopePolar (cubeMuMean (d := d) p n) i j

theorem cubeAhomInvFinite_symm (p : unitInterval) (n : ℕ) (i j : Fin d) :
    cubeAhomInvFinite p n i j = cubeAhomInvFinite p n j i :=
  slopePolar_comm _ i j

/-- **Display (5.21)**: `(1/2) q · ā_{□_n}⁻¹ q = E[-μ(□_n, q)]`. -/
theorem half_sum_mul_cubeAhomInvFinite_eq [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (n : ℕ) (q : Fin d → ℝ) :
    1 / 2 * ∑ i, q i * (cubeAhomInvFinite p n *ᵥ q) i = cubeMuMean p n q := by
  rw [isSlopeQuadratic_cubeMuMean hd hpc n q]
  simp only [Matrix.mulVec, dotProduct, cubeAhomInvFinite, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The change of `E[-μ]` between two scales**:
`|E[-μ(□_n, q)] - E[-μ(□_m, q)]| ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})` for `n ≤ m`. -/
theorem exists_abs_cubeMuMean_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (q : Fin d → ℝ), n ≤ m →
      |cubeMuMean p n q - cubeMuMean p m q| ≤
        C * (∑ i, q i ^ 2) * (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k +
          1 / √(√((3 : ℝ) ^ n))) := by
  obtain ⟨C₂, hC₂, c₂, hc₂, hinc⟩ := exists_cubeMuIncrement_le hd hpc
  obtain ⟨C₀, hC₀, c₀, hc₀, hlow⟩ := exists_neg_le_cubeMuIncrement hd hpc
  set r := 1 / √(√(3 : ℝ)) with hr
  have hr1 : r < 1 := one_div_sqrt_sqrt_three_lt_one
  have hr0 : 0 < 1 - r := by linarith
  set K := d * (C₂ * (1 + 1 / c₂)) * (1 / (1 - r)) + d * (C₀ * (1 + 1 / c₀)) * (1 / (1 - r))
    with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨d + K, by positivity, fun n m q hnm => ?_⟩
  set N := ∑ i, q i ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set ρn := 1 / √(√((3 : ℝ) ^ n)) with hρn
  have hρn0 : 0 ≤ ρn := by positivity
  have hτ0 : 0 ≤ ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k :=
    Finset.sum_nonneg fun k _ => cubeTau_nonneg p k
  have hg := sum_Ico_one_div_sqrt_sqrt_three_pow_le n m
  have hdN : 0 ≤ (d : ℝ) * N := by positivity
  have hQ : (∑ i, |q i|) ^ 2 ≤ d * N := sq_sum_abs_le_card_mul q
  rw [cubeMuMean_sub_eq_sum p hnm, abs_le]
  constructor
  · have hterm : ∀ k ∈ Finset.Ico n m,
        -(d * N * (C₀ * (1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k))))) ≤ cubeMuIncrement p k q := by
      intro k _
      have h1 := hlow k q
      have h2 := exp_neg_mul_three_pow_le hc₀ k
      have h3 : C₀ * ((∑ i, |q i|) ^ 2 * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k)))
          ≤ d * N * (C₀ * (1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k)))) := by
        have h4 : 1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k) ≤
            (1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k))) := by linarith
        have h5 : 0 ≤ 1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k) := by positivity
        calc C₀ * ((∑ i, |q i|) ^ 2 * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k)))
            ≤ C₀ * ((d * N) * ((1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k))))) := by gcongr
          _ = _ := by ring
      linarith
    have hs := Finset.sum_le_sum hterm
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by positivity :
      (0 : ℝ) ≤ C₀ * (1 + 1 / c₀))) hdN
    have k1 : 0 ≤ (d + K) * N * (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k) := by positivity
    have k2 : 0 ≤ (d * (C₂ * (1 + 1 / c₂)) * (1 / (1 - r)) + d) * N * ρn := by positivity
    have e : d * N * (C₀ * (1 + 1 / c₀) * (1 / (1 - r) * ρn)) =
        d * (C₀ * (1 + 1 / c₀)) * (1 / (1 - r)) * N * ρn := by ring
    nlinarith
  · have hterm : ∀ k ∈ Finset.Ico n m, cubeMuIncrement p k q ≤
        d * N * cubeTau (d := d) p k + d * N * (C₂ * (1 + 1 / c₂) * (1 / √(√((3 : ℝ) ^ k)))) := by
      intro k _
      have h1 := hinc k q
      have h2 := exp_neg_mul_three_pow_le hc₂ k
      have h3 : cubeMuTau (d := d) p k ≤ cubeTau (d := d) p k :=
        le_add_of_nonneg_right (cubeNuTau_nonneg p k)
      have h4 : C₂ * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤
          C₂ * (1 + 1 / c₂) * (1 / √(√((3 : ℝ) ^ k))) := by
        have := mul_le_mul_of_nonneg_left h2 hC₂
        nlinarith
      have := mul_le_mul_of_nonneg_left (add_le_add h3 h4) hdN
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by positivity :
      (0 : ℝ) ≤ C₂ * (1 + 1 / c₂))) hdN
    have k1 : 0 ≤ K * N * (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k) := by positivity
    have k2 : 0 ≤ (d * (C₀ * (1 + 1 / c₀)) * (1 / (1 - r)) + d) * N * ρn := by positivity
    have e : d * N * (C₂ * (1 + 1 / c₂) * (1 / (1 - r) * ρn)) =
        d * (C₂ * (1 + 1 / c₂)) * (1 / (1 - r)) * N * ρn := by ring
    nlinarith

theorem sum_sq_single_add_single_le (i j : Fin d) :
    ∑ k, (Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) k ^ 2 ≤ 4 := by
  have h : ∀ k, (Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) k ^ 2 ≤
      2 * (Pi.single i 1 : Fin d → ℝ) k ^ 2 + 2 * (Pi.single j 1 : Fin d → ℝ) k ^ 2 := fun k => by
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg ((Pi.single i 1 : Fin d → ℝ) k - (Pi.single j 1 : Fin d → ℝ) k)]
  have hs : ∀ a : Fin d, ∑ k, (Pi.single a 1 : Fin d → ℝ) k ^ 2 = 1 := fun a => by
    rw [Finset.sum_eq_single a (fun k _ hk => by simp [hk]) (by simp)]
    simp
  calc _ ≤ ∑ k, (2 * (Pi.single i 1 : Fin d → ℝ) k ^ 2 + 2 * (Pi.single j 1 : Fin d → ℝ) k ^ 2) :=
        Finset.sum_le_sum fun k _ => h k
    _ = 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hs]
        norm_num

/-- **Display (5.24)** (every dimension `d ≥ 2`): every entry of `ā_{□_m}⁻¹ - ā_{□_n}⁻¹` is at
most `C (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`, `n ≤ m`. -/
theorem exists_abs_cubeAhomInvFinite_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ), n ≤ m → ∀ i j : Fin d,
      |cubeAhomInvFinite p m i j - cubeAhomInvFinite p n i j| ≤
        C * (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n))) := by
  obtain ⟨C, hC, h⟩ := exists_abs_cubeMuMean_sub_le hd hpc
  refine ⟨6 * C, by positivity, fun n m hnm i j => ?_⟩
  set T := ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n)) with hT
  have hT0 : 0 ≤ T := add_nonneg (Finset.sum_nonneg fun k _ => cubeTau_nonneg p k)
    (by positivity)
  have hs : ∀ a : Fin d, ∑ k, (Pi.single a 1 : Fin d → ℝ) k ^ 2 = 1 := fun a => by
    rw [Finset.sum_eq_single a (fun k _ hk => by simp [hk]) (by simp)]
    simp
  have h1 := h n m (Pi.single i 1 + Pi.single j 1) hnm
  have h2 := h n m (Pi.single i 1) hnm
  have h3 := h n m (Pi.single j 1) hnm
  rw [hs] at h2 h3
  have h1' : |cubeMuMean p n (Pi.single i 1 + Pi.single j 1) -
      cubeMuMean p m (Pi.single i 1 + Pi.single j 1)| ≤ C * 4 * T :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (sum_sq_single_add_single_le i j) hC) hT0)
  have e : cubeAhomInvFinite p m i j - cubeAhomInvFinite p n i j =
      -((cubeMuMean p n (Pi.single i 1 + Pi.single j 1) -
          cubeMuMean p m (Pi.single i 1 + Pi.single j 1)) -
        (cubeMuMean p n (Pi.single i 1) - cubeMuMean p m (Pi.single i 1)) -
        (cubeMuMean p n (Pi.single j 1) - cubeMuMean p m (Pi.single j 1))) := by
    simp only [cubeAhomInvFinite, slopePolar]
    ring
  rw [e, abs_neg]
  rw [abs_le] at h1' h2 h3 ⊢
  constructor <;> linarith [h1'.1, h1'.2, h2.1, h2.2, h3.1, h3.2]

theorem sum_range_one_div_sqrt_sqrt_three_pow_le (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / √(√((3 : ℝ) ^ k)) ≤ 1 / (1 - 1 / √(√(3 : ℝ))) := by
  have h := sum_Ico_one_div_sqrt_sqrt_three_pow_le 0 K
  rw [← Finset.range_eq_Ico] at h
  refine h.trans (le_of_eq ?_)
  simp

/-- **`τ_k` is summable** (every dimension `d ≥ 2`): the increments of `E[-μ]` and `E[ν]`
telescope, and their negative parts are summable by the approximate monotonicity. -/
theorem summable_cubeTau [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : Summable (cubeTau (d := d) p) := by
  obtain ⟨C₀, hC₀, c₀, hc₀, hlowμ⟩ := exists_neg_le_cubeMuIncrement hd hpc
  obtain ⟨C₁, hC₁, hlowν⟩ := exists_neg_le_cubeNuIncrement hd hpc
  have hr1 : 1 / √(√(3 : ℝ)) < 1 := one_div_sqrt_sqrt_three_lt_one
  have hr0 : 0 < 1 - 1 / √(√(3 : ℝ)) := by linarith
  set G := 1 / (1 - 1 / √(√(3 : ℝ))) with hG
  have hG0 : 0 ≤ G := by positivity
  set f : Fin d → Fin d → ℝ := fun i => (cubeAhom (d := d) p)⁻¹ *ᵥ Pi.single i 1 with hf
  set Aμ : Fin d → ℝ := fun i => (∑ j, |(Pi.single i 1 : Fin d → ℝ) j|) ^ 2 with hAμ
  set Aν : Fin d → ℝ := fun i => (∑ j, |f i j|) ^ 2 with hAν
  refine summable_of_sum_range_le (fun k => cubeTau_nonneg p k)
    (c := ∑ i, (cubeMuMean p 0 (Pi.single i 1) + C₀ * Aμ i * ((1 + 1 / c₀) * G) +
      (cubeNuMean p 0 (f i) + C₁ * Aν i * G))) fun K => ?_
  have hterm : ∀ k, cubeTau (d := d) p k ≤ ∑ i,
      ((cubeMuIncrement p k (Pi.single i 1) +
          C₀ * (Aμ i * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k)))) +
        (cubeNuIncrement p k (f i) + C₁ * Aν i * (1 / √3 ^ k))) := by
    intro k
    unfold cubeTau cubeMuTau cubeNuTau
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
    · have h := hlowμ k (Pi.single i 1)
      have h0 : 0 ≤ C₀ * (Aμ i * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k))) := by
        simp only [hAμ]
        positivity
      have e : C₀ * ((∑ j, |(Pi.single i 1 : Fin d → ℝ) j|) ^ 2 *
          (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k))) =
          C₀ * (Aμ i * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k))) := rfl
      rw [e] at h
      exact max_le (by linarith) (by linarith)
    · have h := hlowν k (f i)
      have h0 : 0 ≤ C₁ * Aν i * (1 / √3 ^ k) := by
        simp only [hAν]
        positivity
      have e : C₁ * (∑ j, |f i j|) ^ 2 / √3 ^ k = C₁ * Aν i * (1 / √3 ^ k) := by
        simp only [hAν]
        ring
      rw [e] at h
      exact max_le (by linarith) (by linarith)
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hμsum : ∑ k ∈ Finset.range K, cubeMuIncrement p k (Pi.single i 1) ≤
      cubeMuMean p 0 (Pi.single i 1) := by
    rw [Finset.range_eq_Ico, ← cubeMuMean_sub_eq_sum p (Nat.zero_le K)]
    have : 0 ≤ cubeMuMean p K (Pi.single i 1) := ENNReal.toReal_nonneg
    linarith
  have hνsum : ∑ k ∈ Finset.range K, cubeNuIncrement p k (f i) ≤ cubeNuMean p 0 (f i) := by
    rw [Finset.range_eq_Ico, ← cubeNuMean_sub_eq_sum p (Nat.zero_le K)]
    have : 0 ≤ cubeNuMean p K (f i) := integral_nonneg fun ω => cubeNu_nonneg _
    linarith
  have hAμ0 : 0 ≤ Aμ i := by simp only [hAμ]; positivity
  have hAν0 : 0 ≤ Aν i := by simp only [hAν]; positivity
  have hg := sum_range_one_div_sqrt_sqrt_three_pow_le K
  have hb1 : ∑ k ∈ Finset.range K,
      C₀ * (Aμ i * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k))) ≤
      C₀ * Aμ i * ((1 + 1 / c₀) * G) := by
    have hk : ∀ k ∈ Finset.range K,
        C₀ * (Aμ i * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k))) ≤
        C₀ * Aμ i * (1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k))) := by
      intro k _
      have h2 := exp_neg_mul_three_pow_le hc₀ k
      have h3 : Aμ i * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₀ * (3 : ℝ) ^ k)) ≤
          Aμ i * ((1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k)))) :=
        mul_le_mul_of_nonneg_left (by linarith) hAμ0
      calc _ ≤ C₀ * (Aμ i * ((1 + 1 / c₀) * (1 / √(√((3 : ℝ) ^ k))))) :=
            mul_le_mul_of_nonneg_left h3 hC₀
        _ = _ := by ring
    refine (Finset.sum_le_sum hk).trans ?_
    rw [← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ C₀ * Aμ i * (1 + 1 / c₀))
    linarith
  have hb2 : ∑ k ∈ Finset.range K, C₁ * Aν i * (1 / √3 ^ k) ≤ C₁ * Aν i * G := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun k _ =>
      one_div_sqrt_three_pow_le k).trans hg) (by positivity)
  linarith

end Rigidity.Percolation
