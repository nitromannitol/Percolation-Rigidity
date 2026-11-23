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

end Rigidity.Percolation
