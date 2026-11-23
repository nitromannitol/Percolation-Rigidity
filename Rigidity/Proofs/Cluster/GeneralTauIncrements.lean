import Rigidity.Proofs.Cluster.GeneralMuEnergyDefect
import Rigidity.Proofs.Cluster.GeneralMinimalSet

/-!
# The quantity `τ_k` and display (5.9) of Armstrong and Dario, in every dimension

Let `M_k(q) = E[-μ(□_k, q)]` (on the event that the partition exists and resolves `□_k`,
`cubeMuMean`) and `N_k(ξ) = E[ν(□_k, ξ)]` (`cubeNuMean`). The increments
`I^μ_k(q) = M_k(q) - M_{k+1}(q) = E[μ(□_{k+1}, q)] - E[μ(□_k, q)]` and
`I^ν_k(ξ) = N_k(ξ) - N_{k+1}(ξ)` are quadratic forms (`isSlopeQuadratic_integral`), almost
nonnegative by the approximate monotonicity of `E[-μ]` ((4.48)) and of `E[ν]`. The quantity `τ_k`
of Armstrong and Dario (Section 5, before Lemma 5.4) is

`τ_k = ∑ᵢ (I^μ_k(eᵢ))₊ + ∑ᵢ (I^ν_k(ā⁻¹ eᵢ))₊` (`cubeTau`).

Since a nonnegative quadratic form is controlled by its values on a basis
(`IsSlopeQuadratic.le_of_nonneg`), applied to `I_k + C d |·|² ε_k`,

`I^μ_k(q) ≤ d |q|² (τ_k + C ε_k)` and `I^ν_k(ā⁻¹ q) ≤ d |q|² (τ_k + C 3^{-k/2})`,

`ε_k = 3^{-k/4} + exp(-c 3ᵏ)` (`exists_cubeMuIncrement_le`, `exists_cubeNuIncrement_le`; display
(5.9) of Armstrong and Dario, in every dimension `d ≥ 2`).
-/

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **An integral of quadratic functions is quadratic.** -/
theorem isSlopeQuadratic_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : (Fin d → ℝ) → Ω → ℝ} (hF : ∀ ω, IsSlopeQuadratic fun η => F η ω)
    (hint : ∀ η, Integrable (F η) μ) : IsSlopeQuadratic fun η => ∫ ω, F η ω ∂μ := by
  intro x
  beta_reduce
  have hpt : ∀ ω, F x ω = 1 / 2 * ∑ i, ∑ j, x i * x j * slopePolar (fun η => F η ω) i j :=
    fun ω => hF ω x
  rw [integral_congr_ae (ae_of_all _ hpt)]
  simp only [slopePolar]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, integral_sub, integral_sub]
      all_goals first | exact hint _ | exact (hint _).sub (hint _)
    · intro j _
      exact (((hint _).sub (hint _)).sub (hint _)).const_mul _
  · intro i _
    exact integrable_finsetSum _ fun j _ => (((hint _).sub (hint _)).sub (hint _)).const_mul _

/-- `q ↦ E[-μ(□_m, q)]` is quadratic. -/
theorem isSlopeQuadratic_cubeMuMean [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (m : ℕ) :
    IsSlopeQuadratic (cubeMuMean (d := d) p m) := by
  have hd0 : 0 < d := by omega
  have e : cubeMuMean (d := d) p m = fun q => ∫ ω, (if PartitionEvent ω ∧
      PartitionResolved ω ⟨m, 0⟩ then -cubeMu ω ⟨m, 0⟩ q else 0) ∂(latticeBondLaw d p) := by
    funext q
    exact cubeMuMean_eq_integral hd0 p m q
  rw [e]
  refine isSlopeQuadratic_integral (fun ω => ?_)
    (fun η => integrable_neg_cubeMu_indicator hd hpc _ η)
  by_cases h : PartitionEvent ω ∧ PartitionResolved ω ⟨m, 0⟩
  · simp only [if_pos h]
    exact (isSlopeQuadratic_cubeMu hd0 h.1 h.2).neg
  · simp only [if_neg h]
    exact isSlopeQuadratic_zero

/-- `ξ ↦ E[ν(□_m, ξ)]` is quadratic. -/
theorem isSlopeQuadratic_cubeNuMean (p : unitInterval) (m : ℕ) :
    IsSlopeQuadratic (cubeNuMean (d := d) p m) :=
  isSlopeQuadratic_integral (fun ω => isSlopeQuadratic_cubeNu ω _)
    (fun η => integrable_cubeNu p _ η)

/-- The increment `E[-μ(□_k, q)] - E[-μ(□_{k+1}, q)] = E[μ(□_{k+1}, q)] - E[μ(□_k, q)]`. -/
noncomputable def cubeMuIncrement (p : unitInterval) (k : ℕ) (q : Fin d → ℝ) : ℝ :=
  cubeMuMean p k q - cubeMuMean p (k + 1) q

/-- The increment `E[ν(□_k, ξ)] - E[ν(□_{k+1}, ξ)]`. -/
noncomputable def cubeNuIncrement (p : unitInterval) (k : ℕ) (ξ : Fin d → ℝ) : ℝ :=
  cubeNuMean p k ξ - cubeNuMean p (k + 1) ξ

/-- The part `∑ᵢ (E[μ(□_{k+1}, eᵢ)] - E[μ(□_k, eᵢ)])₊` of `τ_k` coming from `μ`. -/
noncomputable def cubeMuTau (p : unitInterval) (k : ℕ) : ℝ :=
  ∑ i : Fin d, max (cubeMuIncrement p k (Pi.single i 1)) 0

/-- The part `∑ᵢ (E[ν(□_k, ā⁻¹ eᵢ)] - E[ν(□_{k+1}, ā⁻¹ eᵢ)])₊` of `τ_k` coming from `ν`. -/
noncomputable def cubeNuTau (p : unitInterval) (k : ℕ) : ℝ :=
  ∑ i : Fin d, max (cubeNuIncrement p k ((cubeAhom p)⁻¹ *ᵥ Pi.single i 1)) 0

/-- **The quantity `τ_k` of Armstrong and Dario** (Section 5, before Lemma 5.4), in every
dimension. -/
noncomputable def cubeTau (p : unitInterval) (k : ℕ) : ℝ :=
  cubeMuTau (d := d) p k + cubeNuTau (d := d) p k

theorem cubeMuTau_nonneg (p : unitInterval) (k : ℕ) : 0 ≤ cubeMuTau (d := d) p k :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem cubeNuTau_nonneg (p : unitInterval) (k : ℕ) : 0 ≤ cubeNuTau (d := d) p k :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem cubeTau_nonneg (p : unitInterval) (k : ℕ) : 0 ≤ cubeTau (d := d) p k :=
  add_nonneg (cubeMuTau_nonneg p k) (cubeNuTau_nonneg p k)

/-- The increments of `E[-μ]` are almost nonnegative ((4.48)). -/
theorem exists_neg_le_cubeMuIncrement [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (q : Fin d → ℝ),
      -(C * ((∑ i, |q i|) ^ 2 *
        (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c * (3 : ℝ) ^ k)))) ≤ cubeMuIncrement p k q := by
  obtain ⟨C, hC, c, hc, hmono⟩ := exists_lintegral_neg_cubeMu_le_of_scale_le hd hpc
  obtain ⟨C₀, -, hup⟩ := exists_lintegral_neg_cubeMu_le hd hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun k q => ?_⟩
  have hfin : ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω ⟨k, 0⟩ then
      ENNReal.ofReal (-cubeMu ω ⟨k, 0⟩ q) else 0) ∂(latticeBondLaw d p) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup _ q)
  have h := hmono ⟨k + 1, 0⟩ ⟨k, 0⟩ (Nat.le_succ k) q
  have h' := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top⟩) h
  rw [ENNReal.toReal_add hfin (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'
  unfold cubeMuIncrement cubeMuMean
  linarith

/-- The increments of `E[ν]` are almost nonnegative. -/
theorem exists_neg_le_cubeNuIncrement [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (ξ : Fin d → ℝ),
      -(C * (∑ i, |ξ i|) ^ 2 / √3 ^ k) ≤ cubeNuIncrement p k ξ := by
  obtain ⟨C, hC, h⟩ := exists_integral_cubeNu_le_of_scale_le hd hpc
  refine ⟨C, hC, fun k ξ => ?_⟩
  have h1 := h ⟨k + 1, 0⟩ ⟨k, 0⟩ ξ (Nat.le_succ k)
  unfold cubeNuIncrement cubeNuMean
  linarith

/-- **Display (5.9) for `μ`** (every dimension `d ≥ 2`):
`E[μ(□_{k+1}, q)] - E[μ(□_k, q)] ≤ d |q|² (τ^μ_k + C (3^{-k/4} + exp(-c 3ᵏ)))`. -/
theorem exists_cubeMuIncrement_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (q : Fin d → ℝ),
      cubeMuIncrement p k q ≤ d * (∑ i, q i ^ 2) *
        (cubeMuTau (d := d) p k + C * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c * (3 : ℝ) ^ k))) := by
  obtain ⟨C, hC, c, hc, hlow⟩ := exists_neg_le_cubeMuIncrement hd hpc
  refine ⟨d * d * C, by positivity, c, hc, fun k q => ?_⟩
  set ε := 1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c * (3 : ℝ) ^ k) with hε
  have hε0 : 0 ≤ ε := by positivity
  set G : (Fin d → ℝ) → ℝ := fun x => cubeMuIncrement p k x + C * ε * d * ∑ i, x i ^ 2 with hG
  have hGq : IsSlopeQuadratic G :=
    ((isSlopeQuadratic_cubeMuMean hd hpc k).sub (isSlopeQuadratic_cubeMuMean hd hpc (k + 1))).add
      (isSlopeQuadratic_sum_sq.const_mul (C * ε * d))
  have hG0 : ∀ x, 0 ≤ G x := fun x => by
    have h1 := hlow k x
    have h2 := sq_sum_abs_le_card_mul x
    have h3 : C * ((∑ i, |x i|) ^ 2 * ε) ≤ C * ε * d * ∑ i, x i ^ 2 := by
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hε0)
      nlinarith
    simp only [hG]
    linarith
  have hle := hGq.le_of_nonneg hG0 q
  have hsingle : ∀ i : Fin d, ∑ j, (Pi.single i 1 : Fin d → ℝ) j ^ 2 = 1 := fun i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hsum : ∑ i, G (Pi.single i 1) ≤ cubeMuTau (d := d) p k + d * d * C * ε := by
    simp only [hG, hsingle, mul_one, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : ∑ i : Fin d, cubeMuIncrement p k (Pi.single i 1) ≤ cubeMuTau (d := d) p k :=
      Finset.sum_le_sum fun i _ => le_max_left _ _
    nlinarith
  have hq0 : 0 ≤ (d : ℝ) * ∑ i, q i ^ 2 := by positivity
  have hGq' : cubeMuIncrement p k q ≤ G q := by
    simp only [hG]
    have : 0 ≤ C * ε * d * ∑ i, q i ^ 2 := by positivity
    linarith
  calc cubeMuIncrement p k q ≤ G q := hGq'
    _ ≤ d * (∑ i, q i ^ 2) * ∑ i, G (Pi.single i 1) := hle
    _ ≤ d * (∑ i, q i ^ 2) * (cubeMuTau (d := d) p k + d * d * C * ε) :=
        mul_le_mul_of_nonneg_left hsum hq0

/-- **Display (5.9) for `ν`** (every dimension `d ≥ 2`):
`E[ν(□_k, ā⁻¹ q)] - E[ν(□_{k+1}, ā⁻¹ q)] ≤ d |q|² (τ^ν_k + C 3^{-k/2})`. -/
theorem exists_cubeNuIncrement_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (q : Fin d → ℝ),
      cubeNuIncrement p k ((cubeAhom p)⁻¹ *ᵥ q) ≤ d * (∑ i, q i ^ 2) *
        (cubeNuTau (d := d) p k + C / √3 ^ k) := by
  obtain ⟨C, hC, hlow⟩ := exists_neg_le_cubeNuIncrement hd hpc
  set B := (cubeAhom (d := d) p)⁻¹ with hB
  set S₂ := ∑ i : Fin d, ∑ j, (B *ᵥ Pi.single i 1) j ^ 2 with hS₂
  have hS₂0 : 0 ≤ S₂ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨C * d * S₂, by positivity, fun k q => ?_⟩
  set ε := 1 / √3 ^ k with hε
  have hε0 : 0 ≤ ε := by positivity
  set G : (Fin d → ℝ) → ℝ := fun x => cubeNuIncrement p k x + C * ε * d * ∑ i, x i ^ 2 with hG
  have hGq : IsSlopeQuadratic G :=
    ((isSlopeQuadratic_cubeNuMean p k).sub (isSlopeQuadratic_cubeNuMean p (k + 1))).add
      (isSlopeQuadratic_sum_sq.const_mul (C * ε * d))
  have hG0 : ∀ x, 0 ≤ G x := fun x => by
    have h1 := hlow k x
    have h2 := sq_sum_abs_le_card_mul x
    have h3 : C * (∑ i, |x i|) ^ 2 / √3 ^ k ≤ C * ε * d * ∑ i, x i ^ 2 := by
      have e : C * (∑ i, |x i|) ^ 2 / √3 ^ k = C * ε * (∑ i, |x i|) ^ 2 := by
        rw [hε]
        ring
      rw [e]
      have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC hε0)
      nlinarith
    simp only [hG]
    linarith
  have hle := (hGq.comp_mulVec B).le_of_nonneg (fun x => hG0 _) q
  have hsum : ∑ i, G (B *ᵥ Pi.single i 1) ≤ cubeNuTau (d := d) p k + C * ε * d * S₂ := by
    simp only [hG, Finset.sum_add_distrib]
    have h1 : ∑ i : Fin d, cubeNuIncrement p k (B *ᵥ Pi.single i 1) ≤
        cubeNuTau (d := d) p k := Finset.sum_le_sum fun i _ => le_max_left _ _
    have e : ∑ i : Fin d, C * ε * d * ∑ j, (B *ᵥ Pi.single i 1) j ^ 2 = C * ε * d * S₂ := by
      rw [hS₂, Finset.mul_sum]
    linarith
  have hq0 : 0 ≤ (d : ℝ) * ∑ i, q i ^ 2 := by positivity
  calc cubeNuIncrement p k (B *ᵥ q) ≤ G (B *ᵥ q) := by
        simp only [hG]
        have : 0 ≤ C * ε * d * ∑ i, (B *ᵥ q) i ^ 2 := by positivity
        linarith
    _ ≤ d * (∑ i, q i ^ 2) * ∑ i, G (B *ᵥ Pi.single i 1) := hle
    _ ≤ d * (∑ i, q i ^ 2) * (cubeNuTau (d := d) p k + C * ε * d * S₂) :=
        mul_le_mul_of_nonneg_left hsum hq0
    _ = d * (∑ i, q i ^ 2) * (cubeNuTau (d := d) p k + C * d * S₂ / √3 ^ k) := by
        rw [hε]
        ring

theorem cubeMuMean_sub_eq_sum (p : unitInterval) {n m : ℕ} (h : n ≤ m) (q : Fin d → ℝ) :
    cubeMuMean p n q - cubeMuMean p m q = ∑ k ∈ Finset.Ico n m, cubeMuIncrement p k q := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [Finset.sum_Ico_succ_top hnm, ← ih]
    unfold cubeMuIncrement
    ring

theorem cubeNuMean_sub_eq_sum (p : unitInterval) {n m : ℕ} (h : n ≤ m) (ξ : Fin d → ℝ) :
    cubeNuMean p n ξ - cubeNuMean p m ξ = ∑ k ∈ Finset.Ico n m, cubeNuIncrement p k ξ := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [Finset.sum_Ico_succ_top hnm, ← ih]
    unfold cubeNuIncrement
    ring

theorem sqrt_pow_eq_pow_sqrt {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : √(x ^ k) = √x ^ k := by
  rw [show x ^ k = (√x ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx],
    Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) k)]

/-- `3^{-k/4} = r^k` with `r = 3^{-1/4}`. -/
theorem one_div_sqrt_sqrt_three_pow (k : ℕ) :
    1 / √(√((3 : ℝ) ^ k)) = (1 / √(√(3 : ℝ))) ^ k := by
  rw [sqrt_pow_eq_pow_sqrt (by norm_num), sqrt_pow_eq_pow_sqrt (Real.sqrt_nonneg _), one_div_pow]

theorem one_div_sqrt_sqrt_three_lt_one : 1 / √(√(3 : ℝ)) < 1 := by
  have h : 1 < √(√(3 : ℝ)) :=
    (Real.lt_sqrt zero_le_one).2 (by rw [one_pow]; exact (Real.lt_sqrt zero_le_one).2 (by norm_num))
  rw [div_lt_one (by linarith)]
  exact h

theorem one_third_le_one_div_sqrt_sqrt_three : (1 / 3 : ℝ) ≤ 1 / √(√(3 : ℝ)) := by
  have h1 : (0 : ℝ) < √(√(3 : ℝ)) := Real.sqrt_pos.2 (Real.sqrt_pos.2 (by norm_num))
  have h2 : √(√(3 : ℝ)) ≤ 3 := Real.sqrt_le_iff.2 ⟨by norm_num,
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩⟩
  exact one_div_le_one_div_of_le h1 h2

/-- `exp(-c 3ᵏ) ≤ c⁻¹ 3^{-k/4}`. -/
theorem exp_neg_mul_three_pow_le {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Real.exp (-c * (3 : ℝ) ^ k) ≤ 1 / c * (1 / √(√((3 : ℝ) ^ k))) := by
  have hy : 0 < c * (3 : ℝ) ^ k := by positivity
  have h1 : Real.exp (-c * (3 : ℝ) ^ k) ≤ 1 / (c * (3 : ℝ) ^ k) := by
    have h2 : c * (3 : ℝ) ^ k + 1 ≤ Real.exp (c * (3 : ℝ) ^ k) := Real.add_one_le_exp _
    have h3 : Real.exp (-c * (3 : ℝ) ^ k) = 1 / Real.exp (c * (3 : ℝ) ^ k) := by
      rw [neg_mul, Real.exp_neg, one_div]
    rw [h3]
    exact one_div_le_one_div_of_le hy (by linarith)
  calc Real.exp (-c * (3 : ℝ) ^ k) ≤ 1 / (c * (3 : ℝ) ^ k) := h1
    _ = 1 / c * (1 / 3 : ℝ) ^ k := by rw [one_div_pow, one_div_mul_one_div]
    _ ≤ 1 / c * (1 / √(√((3 : ℝ) ^ k))) := by
        rw [one_div_sqrt_sqrt_three_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num)
          one_third_le_one_div_sqrt_sqrt_three k) (by positivity)

/-- `∑_{k ∈ [n, m)} 3^{-k/4} ≤ C 3^{-n/4}`. -/
theorem sum_Ico_one_div_sqrt_sqrt_three_pow_le (n m : ℕ) :
    ∑ k ∈ Finset.Ico n m, 1 / √(√((3 : ℝ) ^ k)) ≤
      1 / (1 - 1 / √(√(3 : ℝ))) * (1 / √(√((3 : ℝ) ^ n))) := by
  simp only [one_div_sqrt_sqrt_three_pow]
  refine (geom_sum_Ico_le_of_lt_one (by positivity) one_div_sqrt_sqrt_three_lt_one).trans
    (le_of_eq ?_)
  ring

theorem integral_neg_cubeMu_indicator_eq_cubeMuMean (hd : 0 < d) (p : unitInterval) (m : ℕ)
    (q : Fin d → ℝ) :
    ∫ ω, (if PartitionEvent ω ∧ PartitionResolved ω (⟨m, 0⟩ : TriadicCube d) then
      -cubeMu ω ⟨m, 0⟩ q else 0) ∂(latticeBondLaw d p) = cubeMuMean p m q :=
  integral_neg_cubeMu_indicator_eq_toReal hd p ⟨m, 0⟩ q

/-- **Lemma 5.4 of Armstrong and Dario for `μ`** (display (5.10), first term, every dimension
`d ≥ 2`): for `n ≤ m`,
`E[|□_m|⁻¹ D^μ_n(□_m, q)] ≤ C |q|² (∑_{k=n}^{m-1} τ_k + 3^{-n/4})`. -/
theorem exists_lintegral_cubeMuDefect_le_tau [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m : ℕ) (q : Fin d → ℝ), n ≤ m →
      ∫⁻ ω, ENNReal.ofReal (cubeMuDefect ω ⟨m, 0⟩ n q) ∂(latticeBondLaw d p) ≤
        ENNReal.ofReal ((⟨m, 0⟩ : TriadicCube d).latticeVolume * (C * (∑ i, q i ^ 2) *
          (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k + 1 / √(√((3 : ℝ) ^ n))))) := by
  have hd0 : 0 < d := by omega
  obtain ⟨C₁, hC₁, c₁, hc₁, hdef⟩ := exists_lintegral_cubeMuDefect_le hd hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hinc⟩ := exists_cubeMuIncrement_le hd hpc
  set r := 1 / √(√(3 : ℝ)) with hr
  have hr1 : r < 1 := one_div_sqrt_sqrt_three_lt_one
  have hr0 : 0 < 1 - r := by linarith
  set K := d * (C₂ * (1 + 1 / c₂)) * (1 / (1 - r)) + C₁ * d * (1 + 1 / c₁) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨d + K, by positivity, fun n m q hnm => ?_⟩
  set V := (⟨m, 0⟩ : TriadicCube d).latticeVolume with hV
  have hV0 : 0 < V := TriadicCube.latticeVolume_pos _
  have h := hdef ⟨m, 0⟩ ⟨n, 0⟩ q hnm
  rw [integral_neg_cubeMu_indicator_eq_cubeMuMean hd0, integral_neg_cubeMu_indicator_eq_cubeMuMean hd0]
    at h
  refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hV0.le))
  change cubeMuMean p n q - cubeMuMean p m q + C₁ * (∑ i, |q i|) ^ 2 *
      (1 / √(√((3 : ℝ) ^ n)) + Real.exp (-c₁ * (3 : ℝ) ^ n)) ≤ _
  set N := ∑ i, q i ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set ρn := 1 / √(√((3 : ℝ) ^ n)) with hρn
  have hρn0 : 0 ≤ ρn := by positivity
  have hτ0 : 0 ≤ ∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k :=
    Finset.sum_nonneg fun k _ => cubeTau_nonneg p k
  -- the decrease of `E[-μ]`
  have hdec : cubeMuMean p n q - cubeMuMean p m q ≤
      d * N * (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k) +
        d * N * (C₂ * (1 + 1 / c₂) * (1 / (1 - r) * ρn)) := by
    rw [cubeMuMean_sub_eq_sum p hnm]
    have hterm : ∀ k ∈ Finset.Ico n m, cubeMuIncrement p k q ≤
        d * N * cubeTau (d := d) p k +
          d * N * (C₂ * (1 + 1 / c₂) * (1 / √(√((3 : ℝ) ^ k)))) := by
      intro k _
      have h1 := hinc k q
      have h2 := exp_neg_mul_three_pow_le hc₂ k
      have h3 : cubeMuTau (d := d) p k ≤ cubeTau (d := d) p k :=
        le_add_of_nonneg_right (cubeNuTau_nonneg p k)
      have h4 : C₂ * (1 / √(√((3 : ℝ) ^ k)) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤
          C₂ * (1 + 1 / c₂) * (1 / √(√((3 : ℝ) ^ k))) := by
        have := mul_le_mul_of_nonneg_left h2 hC₂
        nlinarith
      have hdN : 0 ≤ (d : ℝ) * N := by positivity
      have := mul_le_mul_of_nonneg_left (add_le_add h3 h4) hdN
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have hg := sum_Ico_one_div_sqrt_sqrt_three_pow_le n m
    have hdN : 0 ≤ (d : ℝ) * N := by positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (by positivity :
      (0 : ℝ) ≤ C₂ * (1 + 1 / c₂))) hdN
    linarith
  have hQ : (∑ i, |q i|) ^ 2 ≤ d * N := sq_sum_abs_le_card_mul q
  have he := exp_neg_mul_three_pow_le hc₁ n
  have herr : C₁ * (∑ i, |q i|) ^ 2 * (ρn + Real.exp (-c₁ * (3 : ℝ) ^ n)) ≤
      C₁ * d * (1 + 1 / c₁) * N * ρn := by
    have h1 : ρn + Real.exp (-c₁ * (3 : ℝ) ^ n) ≤ (1 + 1 / c₁) * ρn := by
      rw [hρn]; linarith
    have h2 : 0 ≤ ρn + Real.exp (-c₁ * (3 : ℝ) ^ n) := by positivity
    calc C₁ * (∑ i, |q i|) ^ 2 * (ρn + Real.exp (-c₁ * (3 : ℝ) ^ n))
        ≤ C₁ * (d * N) * ((1 + 1 / c₁) * ρn) := by gcongr
      _ = C₁ * d * (1 + 1 / c₁) * N * ρn := by ring
  have hfin : d * N * (C₂ * (1 + 1 / c₂) * (1 / (1 - r) * ρn)) + C₁ * d * (1 + 1 / c₁) * N * ρn =
      K * N * ρn := by
    rw [hK]
    ring
  have k1 : 0 ≤ K * N * (∑ k ∈ Finset.Ico n m, cubeTau (d := d) p k) := by positivity
  have k2 : 0 ≤ d * N * ρn := by positivity
  nlinarith

end Rigidity.Percolation
