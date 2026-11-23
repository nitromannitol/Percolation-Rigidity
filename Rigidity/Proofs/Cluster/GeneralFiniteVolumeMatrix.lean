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

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
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

/-- The limit of the matrices `ā_{□_n}⁻¹`: the polarization matrix of `q ↦ lim_n E[-μ(□_n, q)]`. -/
noncomputable def cubeAhomInvLimit (p : unitInterval) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => slopePolar (cubeMuLimit (d := d) p) i j

theorem tendsto_cubeAhomInvFinite [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (i j : Fin d) :
    Tendsto (fun n => cubeAhomInvFinite p n i j) atTop (𝓝 (cubeAhomInvLimit p i j)) := by
  simp only [cubeAhomInvFinite, cubeAhomInvLimit, slopePolar]
  exact ((tendsto_cubeMuLimit hd hpc _).sub (tendsto_cubeMuLimit hd hpc _)).sub
    (tendsto_cubeMuLimit hd hpc _)

/-- **The rate of `ā_{□_n}⁻¹`** (display (5.24) with `m → ∞`, every dimension `d ≥ 2`): every
entry of `lim ā_{□_m}⁻¹ - ā_{□_n}⁻¹` is at most `C (∑_{k ≥ n} τ_k + 3^{-n/4})`. -/
theorem exists_abs_cubeAhomInvLimit_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (i j : Fin d),
      |cubeAhomInvLimit p i j - cubeAhomInvFinite p n i j| ≤
        C * (∑' k, cubeTau (d := d) p (k + n) + 1 / √(√((3 : ℝ) ^ n))) := by
  obtain ⟨C, hC, h⟩ := exists_abs_cubeAhomInvFinite_sub_le hd hpc
  refine ⟨C, hC, fun n i j => ?_⟩
  have hs : Summable fun k => cubeTau (d := d) p (k + n) :=
    (summable_nat_add_iff n).2 (summable_cubeTau hd hpc)
  have hbound : ∀ m, n ≤ m → |cubeAhomInvFinite p m i j - cubeAhomInvFinite p n i j| ≤
      C * (∑' k, cubeTau (d := d) p (k + n) + 1 / √(√((3 : ℝ) ^ n))) := by
    intro m hnm
    refine (h n m hnm i j).trans (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hC)
    rw [Finset.sum_Ico_eq_sum_range]
    calc ∑ k ∈ Finset.range (m - n), cubeTau (d := d) p (n + k)
        = ∑ k ∈ Finset.range (m - n), cubeTau (d := d) p (k + n) :=
          Finset.sum_congr rfl fun k _ => by rw [add_comm]
      _ ≤ ∑' k, cubeTau (d := d) p (k + n) :=
          hs.sum_le_tsum _ fun k _ => cubeTau_nonneg p _
  have ht : Tendsto (fun m => |cubeAhomInvFinite p m i j - cubeAhomInvFinite p n i j|) atTop
      (𝓝 |cubeAhomInvLimit p i j - cubeAhomInvFinite p n i j|) :=
    ((tendsto_cubeAhomInvFinite hd hpc i j).sub_const _).abs
  exact le_of_tendsto ht (eventually_atTop.2 ⟨n, hbound⟩)

/-- `q ↦ lim E[-μ(□_n, q)]` is quadratic, with matrix `(1/2) lim ā_{□_n}⁻¹`. -/
theorem isSlopeQuadratic_cubeMuLimit [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) : IsSlopeQuadratic (cubeMuLimit (d := d) p) := by
  intro q
  have e : (fun n => cubeMuMean p n q) = fun n =>
      1 / 2 * ∑ i, ∑ j, q i * q j * cubeAhomInvFinite p n i j :=
    funext fun n => isSlopeQuadratic_cubeMuMean hd hpc n q
  have h : Tendsto (fun n => cubeMuMean p n q) atTop
      (𝓝 (1 / 2 * ∑ i, ∑ j, q i * q j * cubeAhomInvLimit p i j)) := by
    rw [e]
    exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      Tendsto.const_mul _ (tendsto_cubeAhomInvFinite hd hpc i j))
  exact tendsto_nhds_unique (tendsto_cubeMuLimit hd hpc q) h

/-- **Display (5.22)** (every dimension `d ≥ 2`): from some scale on,
`c |q|² ≤ (1/2) q · ā_{□_n}⁻¹ q ≤ C |q|²`. -/
theorem exists_cubeAhomInvFinite_bounds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ q : Fin d → ℝ,
      c * ∑ i, q i ^ 2 ≤ 1 / 2 * ∑ i, q i * (cubeAhomInvFinite p n *ᵥ q) i ∧
        1 / 2 * ∑ i, q i * (cubeAhomInvFinite p n *ᵥ q) i ≤ C * ∑ i, q i ^ 2 := by
  obtain ⟨c, C, hc, hC, hlim⟩ := exists_cubeMuLimit_two_sided hd hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_cubeMu_le hd hpc
  have hT : Tendsto (fun n => ∑ i, ∑ j,
      |(cubeAhomInvFinite p n i j - cubeAhomInvLimit (d := d) p i j) / 2|) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
        (((tendsto_cubeAhomInvFinite hd hpc i j).sub_const (cubeAhomInvLimit p i j)).div_const
          2).abs
    simpa using h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < c / 2)))
  refine ⟨c / 2, C₀ * d, by positivity, by positivity, N, fun n hn q => ?_⟩
  rw [half_sum_mul_cubeAhomInvFinite_eq hd hpc n q]
  have hg : IsSlopeQuadratic fun x : Fin d → ℝ => cubeMuMean p n x - cubeMuLimit p x :=
    (isSlopeQuadratic_cubeMuMean hd hpc n).sub (isSlopeQuadratic_cubeMuLimit hd hpc)
  have hM : ∀ i j : Fin d,
      slopeMatrix (fun x : Fin d → ℝ => cubeMuMean p n x - cubeMuLimit p x) i j =
      (cubeAhomInvFinite p n i j - cubeAhomInvLimit p i j) / 2 := by
    intro i j
    simp only [slopeMatrix, slopePolar, cubeAhomInvFinite, cubeAhomInvLimit]
    ring
  have habs := hg.abs_le q
  beta_reduce at habs
  simp only [hM] at habs
  have hq0 : 0 ≤ ∑ i, q i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor
  · have h1 := (hlim q).1
    have h2 : |cubeMuMean p n q - cubeMuLimit p q| ≤ c / 2 * ∑ i, q i ^ 2 :=
      habs.trans (mul_le_mul_of_nonneg_right (hN n hn).le hq0)
    rw [abs_le] at h2
    linarith [h2.1]
  · have h1 : cubeMuMean p n q ≤ C₀ * (∑ i, |q i|) ^ 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hup ⟨n, 0⟩ q)
    have h2 := sq_sum_abs_le_card_mul q
    have := mul_le_mul_of_nonneg_left h2 hC₀
    nlinarith

/-- The polarization of a quadratic function:
`g(x + y) - g(x) - g(y) = ∑_{i,j} xᵢ yⱼ (g(eᵢ + eⱼ) - g(eᵢ) - g(eⱼ))`. -/
theorem IsSlopeQuadratic.add_sub_sub_eq {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (x y : Fin d → ℝ) :
    g (x + y) - g x - g y = ∑ i, ∑ j, x i * y j * slopePolar g i j := by
  have hsym : ∑ i, ∑ j, y i * x j * slopePolar g i j = ∑ i, ∑ j, x i * y j * slopePolar g i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [slopePolar_comm]
      ring
  have hexp : ∑ i, ∑ j, (x + y) i * (x + y) j * slopePolar g i j =
      ∑ i, ∑ j, x i * x j * slopePolar g i j + ∑ i, ∑ j, y i * y j * slopePolar g i j +
        ∑ i, ∑ j, x i * y j * slopePolar g i j + ∑ i, ∑ j, y i * x j * slopePolar g i j := by
    have hterm : ∀ i j, (x + y) i * (x + y) j * slopePolar g i j =
        x i * x j * slopePolar g i j + y i * y j * slopePolar g i j +
          x i * y j * slopePolar g i j + y i * x j * slopePolar g i j := fun i j => by
      simp only [Pi.add_apply]
      ring
    simp only [hterm, Finset.sum_add_distrib]
  rw [hg (x + y), hg x, hg y, hexp, hsym]
  ring

/-- On a resolved cube, the coarse pairing of the minimizer of `μ(U, q)` against `q'` is the
polarization of `-μ(U, ·)`: `|U|⁻¹ ⟨q', ∇[u(·, U, q)]_𝒫⟩ = -(μ(U, q + q') - μ(U, q) - μ(U, q'))`. -/
theorem cubeCoarsePairing_cubeMuMinimizer_div (hd : 0 < d) {ω : Configuration d}
    (hP : PartitionEvent ω) {U : TriadicCube d} (hU : PartitionResolved ω U) (q q' : Fin d → ℝ) :
    cubeCoarsePairing ω U q' (cubeMuMinimizer ω U q) / U.latticeVolume =
      -(cubeMu ω U (q + q') - cubeMu ω U q - cubeMu ω U q') := by
  obtain ⟨hu, hvu⟩ := cubeMuMinimizer_spec hd hP hU q
  obtain ⟨hv, hvv⟩ := cubeMuMinimizer_spec hd hP hU q'
  set u := cubeMuMinimizer ω U q
  set v := cubeMuMinimizer ω U q'
  have hvol := U.latticeVolume_pos
  have h1 : cubeMu ω U q = -(cubeForm ω U u u / 2) / U.latticeVolume :=
    cubeMu_eq_of_forall_cubeForm_eq hd hP hU hu hvu
  have h2 : cubeMu ω U q' = -(cubeForm ω U v v / 2) / U.latticeVolume :=
    cubeMu_eq_of_forall_cubeForm_eq hd hP hU hv hvv
  have h3 : cubeMu ω U (q + q') = -(cubeForm ω U (u + v) (u + v) / 2) / U.latticeVolume := by
    refine cubeMu_eq_of_forall_cubeForm_eq hd hP hU (Submodule.add_mem _ hu hv) fun w hw => ?_
    rw [map_add, hvu w hw, hvv w hw]
    have h := cubeCoarsePairing_smul_add_smul (ω := ω) (U := U) q q' 1 1 w
    simp only [one_smul, one_mul] at h
    rw [h]
  have h4 : cubeCoarsePairing ω U q' u = cubeForm ω U u v := (hvv u hu).symm
  rw [h1, h2, h3, h4]
  simp only [map_add, LinearMap.add_apply]
  rw [cubeForm_symm v u]
  field_simp
  ring

/-- **Display (5.23)** (every dimension `d ≥ 2`): `q' · ā_{□_n}⁻¹ q` is the expected spatial
average `E[|□_n|⁻¹ ⟨q', ∇[u(·, □_n, q)]_𝒫⟩]` of the coarsened gradient of the minimizer of
`μ(□_n, q)` (on the event that the partition exists and resolves `□_n`). -/
theorem integral_cubeCoarsePairing_cubeMuMinimizer [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (n : ℕ) (q q' : Fin d → ℝ) :
    ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
        cubeCoarsePairing ω ⟨n, 0⟩ q' (cubeMuMinimizer ω ⟨n, 0⟩ q) /
          (⟨n, 0⟩ : TriadicCube d).latticeVolume else 0) ∂(latticeBondLaw d p) =
      ∑ i, q' i * (cubeAhomInvFinite p n *ᵥ q) i := by
  have hd0 : 0 < d := by omega
  set f : (Fin d → ℝ) → Configuration d → ℝ := fun η ω =>
    if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
      -cubeMu ω ⟨n, 0⟩ η else 0 with hf
  have hint : ∀ η, Integrable (f η) (latticeBondLaw d p) := fun η =>
    integrable_neg_cubeMu_indicator hd hpc _ η
  have hpt : ∀ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨n, 0⟩ : TriadicCube d) then
      cubeCoarsePairing ω ⟨n, 0⟩ q' (cubeMuMinimizer ω ⟨n, 0⟩ q) /
        (⟨n, 0⟩ : TriadicCube d).latticeVolume else 0) = f (q + q') ω - f q ω - f q' ω := by
    intro ω
    simp only [hf]
    split_ifs with h
    · rw [cubeCoarsePairing_cubeMuMinimizer_div hd0 h.1 h.2]
      ring
    · ring
  have h12 : Integrable (fun ω => f (q + q') ω - f q ω) (latticeBondLaw d p) :=
    (hint _).sub (hint _)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub h12 (hint _),
    integral_sub (hint _) (hint _)]
  have hM : ∀ η, ∫ ω, f η ω ∂(latticeBondLaw d p) = cubeMuMean p n η := fun η =>
    (cubeMuMean_eq_integral hd0 p n η).symm
  rw [hM, hM, hM, (isSlopeQuadratic_cubeMuMean hd hpc n).add_sub_sub_eq]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, cubeAhomInvFinite]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [slopePolar_comm]
    ring

/-- **The matrix `ā_{□_n}`**: the inverse of `ā_{□_n}⁻¹`. -/
noncomputable def cubeAhomFinite (p : unitInterval) (n : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (cubeAhomInvFinite (d := d) p n)⁻¹

/-- A matrix with `c |q|² ≤ q · A q`, `c > 0`, is invertible. -/
theorem isUnit_det_of_le_sum_mul {A : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ q : Fin d → ℝ, c * ∑ i, q i ^ 2 ≤ ∑ i, q i * (A *ᵥ q) i) : IsUnit A.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : A *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have h1 := h (x - y)
  rw [h0] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h1
  have h2 : ∑ i, (x - y) i ^ 2 = 0 := le_antisymm
    (by nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg ((x - y) i)])
    (Finset.sum_nonneg fun i _ => sq_nonneg _)
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ((x - y) j)).1 h2 i
    (Finset.mem_univ i)
  have h3 : (x - y) i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  simpa [sub_eq_zero] using h3

/-- **Invertibility of `ā_{□_n}⁻¹` from some scale on**: `ā_{□_n}⁻¹ ā_{□_n} = 1`. -/
theorem exists_cubeAhomInvFinite_mul_cubeAhomFinite [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ N : ℕ, ∀ n, N ≤ n → cubeAhomInvFinite p n * cubeAhomFinite (d := d) p n = 1 ∧
      cubeAhomFinite (d := d) p n * cubeAhomInvFinite p n = 1 := by
  obtain ⟨c, C, hc, -, N, hN⟩ := exists_cubeAhomInvFinite_bounds hd hpc
  refine ⟨N, fun n hn => ?_⟩
  have hdet : IsUnit (cubeAhomInvFinite (d := d) p n).det := by
    refine isUnit_det_of_le_sum_mul (c := 2 * c) (by positivity) fun q => ?_
    have := (hN n hn q).1
    linarith
  exact ⟨Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet⟩

/-- **The minimum characterization of `ā_{□_n} ξ`**: when `ā_{□_n}⁻¹ ā_{□_n} = 1`, the function
`x ↦ E[-μ(□_n, x)] - ξ · x` is minimal at `x = ā_{□_n} ξ`. -/
theorem cubeMuMean_cubeAhomFinite_sub_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {n : ℕ}
    (hinv : cubeAhomInvFinite p n * cubeAhomFinite (d := d) p n = 1) (ξ x : Fin d → ℝ) :
    cubeMuMean p n (cubeAhomFinite p n *ᵥ ξ) - ∑ i, ξ i * (cubeAhomFinite p n *ᵥ ξ) i ≤
      cubeMuMean p n x - ∑ i, ξ i * x i := by
  set y := cubeAhomFinite (d := d) p n *ᵥ ξ with hy
  set w := x - y with hw
  have hx : x = y + w := by rw [hw]; abel
  have hBy : cubeAhomInvFinite p n *ᵥ y = ξ := by
    rw [hy, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hpol := (isSlopeQuadratic_cubeMuMean hd hpc n).add_sub_sub_eq y w
  have hP : ∑ i, ∑ j, y i * w j * slopePolar (cubeMuMean p n) i j = ∑ j, ξ j * w j := by
    rw [← hBy, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, cubeAhomInvFinite, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [slopePolar_comm]
    ring
  have hw0 : 0 ≤ cubeMuMean p n w := ENNReal.toReal_nonneg
  have hξx : ∑ i, ξ i * x i = ∑ i, ξ i * y i + ∑ i, ξ i * w i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hx, Pi.add_apply]; ring
  rw [hξx, hx]
  linarith

/-- The quantity `D_n = ∑ᵢ (E[ν(□_n, eᵢ)] + E[-μ(□_n, ā_{□_n} eᵢ)] - eᵢ · ā_{□_n} eᵢ)` of Armstrong
and Dario (proof of Lemma 5.10), in every dimension. -/
noncomputable def cubeOmegaD (p : unitInterval) (n : ℕ) : ℝ :=
  ∑ i : Fin d, (cubeNuMean p n (Pi.single i 1) +
    cubeMuMean p n (cubeAhomFinite p n *ᵥ Pi.single i 1) -
    (cubeAhomFinite p n *ᵥ Pi.single i 1) i)

theorem sum_single_mul_eq (i : Fin d) (x : Fin d → ℝ) :
    ∑ j, (Pi.single i 1 : Fin d → ℝ) j * x j = x i := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- **Step 1 of the proof of Lemma 5.10, first part** (every dimension `d ≥ 2`): when
`ā_{□_{n+1}}⁻¹` is invertible, testing the minimum characterization of `ā_{□_{n+1}} eᵢ` with
`ā_{□_n} eᵢ` gives `D_{n+1} ≤ D_n - ∑ᵢ J_n(eᵢ) - ∑ᵢ I_n(ā_{□_n} eᵢ)`, with `I_n`, `J_n` the
increments of `E[-μ]` and `E[ν]`. -/
theorem cubeOmegaD_succ_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) {n : ℕ}
    (hinv : cubeAhomInvFinite p (n + 1) * cubeAhomFinite (d := d) p (n + 1) = 1) :
    cubeOmegaD (d := d) p (n + 1) ≤ cubeOmegaD (d := d) p n -
      ∑ i : Fin d, cubeNuIncrement p n (Pi.single i 1) -
      ∑ i : Fin d, cubeMuIncrement p n (cubeAhomFinite p n *ᵥ Pi.single i 1) := by
  have hmin : ∀ i : Fin d,
      cubeMuMean p (n + 1) (cubeAhomFinite p (n + 1) *ᵥ Pi.single i 1) -
        (cubeAhomFinite p (n + 1) *ᵥ Pi.single i 1) i ≤
      cubeMuMean p (n + 1) (cubeAhomFinite p n *ᵥ Pi.single i 1) -
        (cubeAhomFinite p n *ᵥ Pi.single i 1) i := by
    intro i
    have h := cubeMuMean_cubeAhomFinite_sub_le hd hpc hinv (Pi.single i 1)
      (cubeAhomFinite p n *ᵥ Pi.single i 1)
    rwa [sum_single_mul_eq, sum_single_mul_eq] at h
  unfold cubeOmegaD cubeNuIncrement cubeMuIncrement
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => by linarith [hmin i]

end Rigidity.Percolation
