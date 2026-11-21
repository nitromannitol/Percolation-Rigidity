import Rigidity.Proofs.Percolation.PlanarMuEnergyDefect
import Rigidity.Proofs.Percolation.PlanarLimitCubes

/-!
# The increments of the expectation of `μ` between successive triadic scales

Let `M_k(q) = E[-μ(□_k, q)]` (on the partition event and the resolution of `□_k`). The increment
`I_k(q) = M_k(q) - M_{k+1}(q) = E[μ(□_{k+1}, q)] - E[μ(□_k, q)]` is a quadratic form in `q`, almost
nonnegative by the approximate monotonicity of `M`:
`I_k(q) ≥ -C |q|₁² (3 ^ (-k/2) + exp (-c 3 ^ k))`. Let
`τ^μ_k = ∑_i (I_k(e_i))⁺` be the part of the quantity `τ_k` of Armstrong and Dario (Section 5,
before Lemma 5.4) coming from `μ`. Since `I_k(q) + I_k(q₀, -q₁) = 2 (q₀² I_k(e₀) + q₁² I_k(e₁))`,

`I_k(q) ≤ 2 |q|² τ^μ_k + C |q|₁² (3 ^ (-k/2) + exp (-c 3 ^ k))`

(the part of display (5.9) of Armstrong and Dario coming from `μ`, in dimension two). Summing the
increments from `n` to `m` and inserting the bound on the energy of the differences between the
minimizers at the scales `m` and `n` gives Lemma 5.4 for `μ` in the form

`E[D_n(□_m, q)] / |□_m| ≤ 2 |q|² ∑_{k=n}^{m-1} τ^μ_k + C |q|₁² (∑_{k=n}^{m-1} ε_k + ε_n)`,

with `ε_k = 3 ^ (-k/2) + exp (-c 3 ^ k)` (display (5.10), first term, in dimension two).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- The increment `E[-μ(□_k, q)] - E[-μ(□_{k+1}, q)] = E[μ(□_{k+1}, q)] - E[μ(□_k, q)]`. -/
noncomputable def planarMuIncrement (p : unitInterval) (k : ℕ) (q : Fin 2 → ℝ) : ℝ :=
  planarMuMean p k q - planarMuMean p (k + 1) q

/-- The part `∑_i (E[μ(□_{k+1}, e_i)] - E[μ(□_k, e_i)])⁺` of the quantity `τ_k` of Armstrong and
Dario coming from `μ`. -/
noncomputable def planarMuTau (p : unitInterval) (k : ℕ) : ℝ :=
  ∑ i : Fin 2, max (planarMuIncrement p k (Pi.single i 1)) 0

theorem planarMuTau_nonneg (p : unitInterval) (k : ℕ) : 0 ≤ planarMuTau p k :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- The decomposition of a planar vector along the unit vectors. -/
theorem eq_smul_single_add_smul_single (q : Fin 2 → ℝ) :
    q = q 0 • (Pi.single 0 1 : Fin 2 → ℝ) + q 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;> simp

/-- **Parallelogram identity for the increments.** -/
theorem planarMuIncrement_add_reflect {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (k : ℕ) (a b : ℝ) :
    planarMuIncrement p k (a • (Pi.single 0 1 : Fin 2 → ℝ) + b • (Pi.single 1 1 : Fin 2 → ℝ)) +
      planarMuIncrement p k (a • (Pi.single 0 1 : Fin 2 → ℝ) +
        (-b) • (Pi.single 1 1 : Fin 2 → ℝ)) =
      2 * (a ^ 2 * planarMuIncrement p k (Pi.single 0 1) +
        b ^ 2 * planarMuIncrement p k (Pi.single 1 1)) := by
  simp only [planarMuIncrement]
  rw [planarMuMean_smul_add_smul hpc k, planarMuMean_smul_add_smul hpc (k + 1),
    planarMuMean_smul_add_smul hpc k, planarMuMean_smul_add_smul hpc (k + 1)]
  ring

/-- **Approximate nonnegativity of the increments** (approximate monotonicity of `E[-μ]`). -/
theorem exists_neg_le_planarMuIncrement {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (q : Fin 2 → ℝ),
      -(C * ((|q 0| + |q 1|) ^ 2 *
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)))) ≤
        planarMuIncrement p k q := by
  obtain ⟨C, hC, c, hc, hmono⟩ := exists_lintegral_neg_planarMu_le_of_scale_le hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  refine ⟨C.toReal, ENNReal.toReal_nonneg, c, hc, fun k q => ?_⟩
  have h := hmono ⟨k + 1, 0⟩ ⟨k, 0⟩ (Nat.le_succ k) q
  have hfin := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top)
    (hup ⟨k, 0⟩ q)
  have h' := toReal_le_toReal_add_of_lintegral_le hfin hC (by positivity) h
  simp only [planarMuIncrement, planarMuMean]
  linarith

/-- **Sums control suprema for the increments** (the part of display (5.9) of Armstrong and Dario
coming from `μ`, in dimension two). -/
theorem exists_planarMuIncrement_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (q : Fin 2 → ℝ),
      planarMuIncrement p k q ≤ 2 * (q 0 ^ 2 + q 1 ^ 2) * planarMuTau p k +
        C * ((|q 0| + |q 1|) ^ 2 *
          (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))) := by
  obtain ⟨C, hC, c, hc, hlow⟩ := exists_neg_le_planarMuIncrement hpc
  refine ⟨C, hC, c, hc, fun k q => ?_⟩
  have hpar := planarMuIncrement_add_reflect hpc k (q 0) (q 1)
  rw [← eq_smul_single_add_smul_single q] at hpar
  set r : Fin 2 → ℝ := q 0 • (Pi.single 0 1 : Fin 2 → ℝ) + (-q 1) • (Pi.single 1 1 : Fin 2 → ℝ)
    with hr
  have hr0 : r 0 = q 0 := by simp [hr]
  have hr1 : r 1 = -q 1 := by simp [hr]
  have hlr := hlow k r
  rw [hr0, hr1, abs_neg] at hlr
  set I₀ := planarMuIncrement p k (Pi.single 0 1)
  set I₁ := planarMuIncrement p k (Pi.single 1 1)
  have hτ : planarMuTau p k = max I₀ 0 + max I₁ 0 := by
    rw [planarMuTau, Fin.sum_univ_two]
  have h0 : q 0 ^ 2 * I₀ ≤ q 0 ^ 2 * max I₀ 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
  have h1 : q 1 ^ 2 * I₁ ≤ q 1 ^ 2 * max I₁ 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg _)
  have h0' : 0 ≤ q 1 ^ 2 * max I₀ 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have h1' : 0 ≤ q 0 ^ 2 * max I₁ 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
  rw [hτ]
  linarith

/-- The difference of the expectations of `-μ` at two scales is the sum of the increments. -/
theorem planarMuMean_sub_planarMuMean_eq_sum (p : unitInterval) {n m : ℕ} (hnm : n ≤ m)
    (q : Fin 2 → ℝ) :
    planarMuMean p n q - planarMuMean p m q = ∑ k ∈ Finset.Ico n m, planarMuIncrement p k q := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [Finset.sum_Ico_succ_top hnm, ← ih, planarMuIncrement]
    ring

/-- **The decrease of `E[-μ]` between two scales is controlled by `τ^μ`.** -/
theorem exists_planarMuMean_sub_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      planarMuMean p n q - planarMuMean p m q ≤
        2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarMuTau p k +
          C * (|q 0| + |q 1|) ^ 2 * ∑ k ∈ Finset.Ico n m,
            (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) := by
  obtain ⟨C, hC, c, hc, hinc⟩ := exists_planarMuIncrement_le hpc
  refine ⟨C, hC, c, hc, fun n m hnm q => ?_⟩
  rw [planarMuMean_sub_planarMuMean_eq_sum p hnm q, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => (hinc k q).trans (le_of_eq ?_)
  ring

/-- **Lemma 5.4 of Armstrong and Dario for `μ`** (display (5.10), first term, in dimension two).
For `n ≤ m`, the expected energy of the differences between the minimizer of `μ(□_m, q)` restricted
to the resolved subcubes of scale `n` and the minimizers on these subcubes, divided by `|□_m|`, is
at most `2 |q|² ∑_{k=n}^{m-1} τ^μ_k + C |q|₁² (∑_{k=n}^{m-1} ε_k + ε_n)`, where
`ε_k = 3 ^ (-k/2) + exp (-c 3 ^ k)`. -/
theorem exists_planarMuDefect_le_planarMuTau {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          ENNReal.ofReal (planarMuDefect ω ⟨m, 0⟩ n q) else 0) ∂(latticeBondLaw 2 p)).toReal /
          (⟨m, 0⟩ : TriadicCube 2).volume ≤
        2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarMuTau p k +
          C * (|q 0| + |q 1|) ^ 2 * (∑ k ∈ Finset.Ico n m,
            (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
            (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) := by
  obtain ⟨C₁, hC₁, c₁, hc₁, hdef⟩ := exists_lintegral_planarMuDefect_le hpc
  obtain ⟨C₂, hC₂, c₂, hc₂, hsub⟩ := exists_planarMuMean_sub_le hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  set c := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨C₁.toReal + C₂, by positivity, c, hc, fun n m hnm q => ?_⟩
  have h := hdef ⟨m, 0⟩ ⟨n, 0⟩ n hnm rfl q
  have hmeans := hsub n m hnm q
  have hfU := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top) (hup ⟨m, 0⟩ q)
  have hfW := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top) (hup ⟨n, 0⟩ q)
  set Q := (|q 0| + |q 1|) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hvol := (⟨m, 0⟩ : TriadicCube 2).volume_pos
  have hε : ∀ k : ℕ, ∀ c' : ℝ, c ≤ c' → Real.exp (-c' * (3 : ℝ) ^ k) ≤
      Real.exp (-c * (3 : ℝ) ^ k) := fun k c' hc' => by
    apply Real.exp_le_exp.2
    have h3 : (0 : ℝ) ≤ 3 ^ k := by positivity
    nlinarith
  set A := ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
      ENNReal.ofReal (planarMuDefect ω ⟨m, 0⟩ n q) else 0) ∂(latticeBondLaw 2 p) with hA
  have hR : ENNReal.ofReal (⟨m, 0⟩ : TriadicCube 2).volume *
      ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨n, 0⟩ then
      ENNReal.ofReal (-planarMu ω ⟨n, 0⟩ q) else 0) ∂(latticeBondLaw 2 p) +
      C₁ * ENNReal.ofReal (Q * (⟨m, 0⟩ : TriadicCube 2).volume *
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
  have hdiv : A.toReal / (⟨m, 0⟩ : TriadicCube 2).volume ≤ (planarMuMean p n q - planarMuMean p m q) +
      C₁.toReal * (Q * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) := by
    rw [div_le_iff₀ hvol]
    simp only [planarMuMean]
    nlinarith
  have hS : 0 ≤ ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hS₂ : ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤
      ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) :=
    Finset.sum_le_sum fun k _ => add_le_add le_rfl (hε k c₂ (min_le_right _ _))
  have he₁ := hε n c₁ (min_le_left _ _)
  have hen : 0 ≤ 1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n) := by positivity
  have hC₁0 : 0 ≤ C₁.toReal := ENNReal.toReal_nonneg
  have k1 : C₁.toReal * (Q * (1 / Real.sqrt (3 ^ n) + Real.exp (-c₁ * (3 : ℝ) ^ n))) ≤
      C₁.toReal * (Q * (1 / Real.sqrt (3 ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) := by
    gcongr
  have k2 : C₂ * Q * ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c₂ * (3 : ℝ) ^ k)) ≤
      C₂ * Q * ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) := by
    gcongr
  have k3 : 0 ≤ C₂ * Q * (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n)) := by
    positivity
  have k4 : 0 ≤ C₁.toReal * Q * ∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) := by positivity
  have e : (C₁.toReal + C₂) * Q * (∑ k ∈ Finset.Ico n m,
      (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
      (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) =
      C₁.toReal * (Q * (1 / Real.sqrt (3 ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) +
      C₂ * Q * ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
      C₂ * Q * (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n)) +
      C₁.toReal * Q * ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) := by ring
  rw [e]
  linarith

end Rigidity.Percolation
