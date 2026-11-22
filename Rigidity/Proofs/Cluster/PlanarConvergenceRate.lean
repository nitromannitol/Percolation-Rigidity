import Rigidity.Proofs.Cluster.PlanarRHWeakConv
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeRate

/-!
# The rate of Proposition 5.2 of Armstrong and Dario in expectation, in dimension two

For `p > p_c(2)`, Lemma 5.9 of Armstrong and Dario holds in the form of the hypothesis `h59` of
`exists_planarOmegaD_le_pow_of_decay`, `exists_planarTau_le_pow_of_decay` and
`exists_abs_planarAhomInvLimit_sub_le_of_decay` (`exists_planarOmegaD_decay` with Lemmas 5.5 and
5.7, which are theorems in dimension two). Hence `D_n`, `τ_n` and the distance from `ā_{□_n}⁻¹` to
`ā⁻¹` decay geometrically (Lemma 5.10, Steps 3 and 4), and the expectations of `μ` and `ν` converge
at an algebraic rate: there are `α ∈ (0, 1/4]` and `C` with

`|E[μ(□_n, q)] + (1/2) q · ā⁻¹ q| + |E[ν(□_n, p)] - (1/2) p · ā p| ≤ C (|p|² + |q|²) 3^{-nα}`

for every `n` and all `p, q` (display (5.3) of Armstrong and Dario, which they state for some
`α(d, 𝔭, λ) > 0`; the bound `α ≤ 1/4` is that of Proposition 5.2).

The rate for `μ` is the rate of the finite-volume matrices `ā_{□_n}⁻¹`. The rate for `ν` is the sum
of the increments `E[ν(□_k, ξ)] - E[ν(□_{k+1}, ξ)]` over `k ≥ n`: each increment is bounded below by
the approximate monotonicity of `E[ν]` and above by `τ_k` through display (5.9), and `τ_k` decays
geometrically. Armstrong and Dario derive display (5.3) from Lemma 5.3 and the bound (5.4) on
`E[ω(□_n, ·)₊]`; the route here uses only the decay of `τ_k`, as in Step 4 of their proof of
Lemma 5.10 for the matrices `ā_{□_n}`.

The expectations are those of `E[-μ(□_n, q)]` and `E[ν(□_n, ξ)]` on the event that the partition
exists and resolves `□_n` (`planarMuMean`, `planarNuMean`), and `|q|² = q₀² + q₁²`.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Percolation
  Rigidity.External Rigidity.Proofs.Section5
open scoped Classical Matrix

/-- **Lemma 5.9 of Armstrong and Dario in the form `h59`** (dimension two, `p > p_c(2)`):
`D_n ≤ C σⁿ + C ∑_{l ≤ n} ρ^{n-l} τ_l` with `σ = 3^{-1/10}` and `ρ = 1/3`, from some scale on. -/
theorem exists_planarOmegaD_decay_holds {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → planarOmegaD p n ≤
      C * ((3 : ℝ) ^ (-(1 / 10 : ℝ))) ^ n +
        C * ∑ l ∈ Finset.range (n + 1), (1 / 3 : ℝ) ^ (n - l) * planarTau p l :=
  exists_planarOmegaD_decay hpc (planarWeakConvergence_holds hpc)
    (planarRestrictQuadCoarsenMu_holds hpc) (planarRestrictQuadCoarsenNu_holds hpc)

theorem three_rpow_neg_one_div_ten_lt_one : (3 : ℝ) ^ (-(1 / 10 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- **Geometric decay of `D_n`** (Armstrong and Dario, Lemma 5.10, (5.36), in dimension two,
`p > p_c(2)`). -/
theorem exists_planarOmegaD_le_geometric {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → planarOmegaD p n ≤ K * l ^ n := by
  obtain ⟨C, hC, N, h⟩ := exists_planarOmegaD_decay_holds hpc
  exact exists_planarOmegaD_le_pow_of_decay hpc hC (by positivity)
    three_rpow_neg_one_div_ten_lt_one (by norm_num) (by norm_num) h

/-- **Geometric decay of `τ_n`** (Armstrong and Dario, Lemma 5.10, Step 4, in dimension two,
`p > p_c(2)`). -/
theorem exists_planarTau_le_geometric {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → planarTau p n ≤ K * l ^ n := by
  obtain ⟨C, hC, N, h⟩ := exists_planarOmegaD_decay_holds hpc
  exact exists_planarTau_le_pow_of_decay hpc hC (by positivity)
    three_rpow_neg_one_div_ten_lt_one (by norm_num) (by norm_num) h

/-- The limit of the finite-volume matrices `ā_{□_n}⁻¹` is `ā⁻¹` (dimension two, `p > p_c(2)`). -/
theorem planarAhomInvLimit_eq_inv {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    planarAhomInvLimit p = (planarAhom p)⁻¹ :=
  (forall_planarOmegaLimit_eq_zero_iff hpc).1 fun q =>
    (planarMuLimit_eq_iff_planarOmegaLimit_eq_zero hpc q).1 (planarMuLimit_eq hpc q)

/-- **Geometric convergence of `ā_{□_n}⁻¹` to `ā⁻¹`** (Armstrong and Dario, Lemma 5.10, Step 4,
in dimension two, `p > p_c(2)`), entrywise. -/
theorem exists_abs_planarAhom_inv_sub_planarAhomInvFinite_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ i j : Fin 2,
      |(planarAhom p)⁻¹ i j - planarAhomInvFinite p n i j| ≤ K * l ^ n := by
  obtain ⟨C, hC, N, h⟩ := exists_planarOmegaD_decay_holds hpc
  have h' := exists_abs_planarAhomInvLimit_sub_le_of_decay hpc hC (by positivity)
    three_rpow_neg_one_div_ten_lt_one (by norm_num) (by norm_num) h
  rwa [planarAhomInvLimit_eq_inv hpc] at h'

/-- The `ℓ¹` norm of `M v` is at most the sum of the absolute values of the entries of `M` times
the `ℓ¹` norm of `v`. -/
theorem abs_mulVec_add_abs_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    |(M *ᵥ v) 0| + |(M *ᵥ v) 1| ≤
      (|M 0 0| + |M 0 1| + |M 1 0| + |M 1 1|) * (|v 0| + |v 1|) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 := abs_add_le (M 0 0 * v 0) (M 0 1 * v 1)
  have h1 := abs_add_le (M 1 0 * v 0) (M 1 1 * v 1)
  rw [abs_mul, abs_mul] at h0 h1
  nlinarith [mul_nonneg (abs_nonneg (M 0 0)) (abs_nonneg (v 1)),
    mul_nonneg (abs_nonneg (M 0 1)) (abs_nonneg (v 0)),
    mul_nonneg (abs_nonneg (M 1 0)) (abs_nonneg (v 1)),
    mul_nonneg (abs_nonneg (M 1 1)) (abs_nonneg (v 0))]

/-- **Geometric rate of `E[-μ(□_n, q)]`** (dimension two, `p > p_c(2)`): from some scale on,
`|E[-μ(□_n, q)] - (1/2) q · ā⁻¹ q| ≤ K |q|² lⁿ`. -/
theorem exists_abs_planarMuMean_sub_le_geometric {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ q : Fin 2 → ℝ,
      |planarMuMean p n q - 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
        K * (q 0 ^ 2 + q 1 ^ 2) * l ^ n := by
  obtain ⟨K, l, hl0, hl1, N, h⟩ := exists_abs_planarAhom_inv_sub_planarAhomInvFinite_le hpc
  have hK : 0 ≤ K := by
    have h00 := (abs_nonneg _).trans (h N le_rfl 0 0)
    exact nonneg_of_mul_nonneg_left h00 (pow_pos hl0 N)
  refine ⟨K, l, hK, hl0, hl1, N, fun n hn q => ?_⟩
  set t := K * l ^ n with ht
  have hEt : ∀ i j, |planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j| ≤ t := fun i j => by
    rw [abs_sub_comm]
    exact h n hn i j
  have he : planarMuMean p n q - 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i =
      1 / 2 * ∑ i, ∑ j, q i * (planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j) * q j := by
    rw [planarMuMean_eq_planarAhomInvFinite hpc n q]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have key : ∀ i j, |q i * (planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j) * q j| ≤
      |q i| * |q j| * t := fun i j => by
    rw [abs_mul, abs_mul]
    calc |q i| * |planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j| * |q j| =
          |q i| * |q j| * |planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j| := by ring
      _ ≤ |q i| * |q j| * t := mul_le_mul_of_nonneg_left (hEt i j) (by positivity)
  have hsum : |∑ i, ∑ j, q i * (planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j) * q j| ≤
      ∑ i, ∑ j, |q i| * |q j| * t :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => key i j))
  have hval : ∑ i, ∑ j, |q i| * |q j| * t = (|q 0| + |q 1|) ^ 2 * t := by
    simp only [Fin.sum_univ_two]
    ring
  have ht0 : 0 ≤ t := mul_nonneg hK (pow_nonneg hl0.le n)
  have hq := abs_add_abs_sq_le q
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc 1 / 2 * |∑ i, ∑ j, q i * (planarAhomInvFinite p n i j - (planarAhom p)⁻¹ i j) * q j| ≤
        1 / 2 * ((|q 0| + |q 1|) ^ 2 * t) := by
        rw [← hval]
        linarith
    _ ≤ K * (q 0 ^ 2 + q 1 ^ 2) * l ^ n := by
        have := mul_le_mul_of_nonneg_right hq ht0
        rw [ht] at this ⊢
        nlinarith

/-- **Tail bound for a convergent sequence with geometric increments.** If `a_k → L` and
`|a_k - a_{k+1}| ≤ B lᵏ` for `k ≥ N`, then `|a_n - L| ≤ B lⁿ / (1 - l)` for `n ≥ N`. -/
theorem abs_sub_le_of_abs_sub_succ_le {a : ℕ → ℝ} {L B l : ℝ} {N : ℕ}
    (ha : Tendsto a atTop (𝓝 L)) (hB : 0 ≤ B) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (h : ∀ k, N ≤ k → |a k - a (k + 1)| ≤ B * l ^ k) {n : ℕ} (hn : N ≤ n) :
    |a n - L| ≤ B * (l ^ n / (1 - l)) := by
  have hm : ∀ m, n ≤ m → |a n - a m| ≤ B * (l ^ n / (1 - l)) := by
    intro m hm
    have e : a n - a m = ∑ k ∈ Finset.Ico n m, (a k - a (k + 1)) := by
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hnm ih =>
        rw [Finset.sum_Ico_succ_top hnm, ← ih]
        ring
    rw [e]
    calc |∑ k ∈ Finset.Ico n m, (a k - a (k + 1))| ≤ ∑ k ∈ Finset.Ico n m, |a k - a (k + 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico n m, B * l ^ k :=
          Finset.sum_le_sum fun k hk => h k (hn.trans (Finset.mem_Ico.1 hk).1)
      _ = B * ∑ k ∈ Finset.Ico n m, l ^ k := by rw [Finset.mul_sum]
      _ ≤ B * (l ^ n / (1 - l)) := mul_le_mul_of_nonneg_left (sum_Ico_pow_le hl0 hl1 n m) hB
  have hlim : Tendsto (fun m => |a n - a m|) atTop (𝓝 |a n - L|) :=
    (tendsto_const_nhds.sub ha).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, hm⟩)

theorem planarAhom_inv_mulVec_mulVec {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (ξ : Fin 2 → ℝ) : (planarAhom p)⁻¹ *ᵥ (planarAhom p *ᵥ ξ) = ξ := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (planarAhom_det_ne_zero hpc)),
    Matrix.one_mulVec]

/-- A bound for the `ℓ¹` norm of `M v` by that of `v`. -/
theorem exists_abs_mulVec_le (M : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ v : Fin 2 → ℝ, |(M *ᵥ v) 0| + |(M *ᵥ v) 1| ≤ S * (|v 0| + |v 1|) :=
  ⟨_, by positivity, abs_mulVec_add_abs_mulVec_le M⟩

/-- **Geometric bound for the increments of `E[ν]`** (dimension two, `p > p_c(2)`): from some
scale on, `|E[ν(□_k, ξ)] - E[ν(□_{k+1}, ξ)]| ≤ B (|ξ₀| + |ξ₁|)² σᵏ`. -/
theorem exists_abs_planarNuIncrement_le_geometric {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ B σ : ℝ, 0 ≤ B ∧ 0 < σ ∧ σ < 1 ∧ ∃ N : ℕ, ∀ k, N ≤ k → ∀ ξ : Fin 2 → ℝ,
      |planarNuIncrement p k ξ| ≤ B * (|ξ 0| + |ξ 1|) ^ 2 * σ ^ k := by
  obtain ⟨Kτ, lτ, hlτ0, hlτ1, Nτ, hτ⟩ := exists_planarTau_le_geometric hpc
  obtain ⟨C, hC, c, hc, hup⟩ := exists_planarNuIncrement_ahomInv_le hpc
  obtain ⟨C', hC', c', hc', hlow⟩ := exists_neg_le_planarNuIncrement hpc
  obtain ⟨SA, hSA0, hSAb⟩ := exists_abs_mulVec_le (planarAhom p)
  obtain ⟨SI, hSI0, hSIb⟩ := exists_abs_mulVec_le (planarAhom p)⁻¹
  have hsq3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr1 : 1 / Real.sqrt 3 < 1 := (div_lt_one (by positivity)).2 hsq3
  have he1 : Real.exp (-c) < 1 := by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 hc)
  have he1' : Real.exp (-c') < 1 := by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 hc')
  set σ := max lτ (max (1 / Real.sqrt 3) (max (Real.exp (-c)) (Real.exp (-c')))) with hσdef
  have hσ1 : σ < 1 := max_lt hlτ1 (max_lt hr1 (max_lt he1 he1'))
  have hσ0 : 0 < σ := lt_of_lt_of_le hlτ0 (le_max_left _ _)
  have hlσ : lτ ≤ σ := le_max_left _ _
  have hrσ : 1 / Real.sqrt 3 ≤ σ := le_max_of_le_right (le_max_left _ _)
  have heσ : Real.exp (-c) ≤ σ := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have heσ' : Real.exp (-c') ≤ σ := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  obtain ⟨K, hK0, hKτ⟩ : ∃ K : ℝ, 0 ≤ K ∧ Kτ ≤ K := ⟨max Kτ 0, le_max_right _ _, le_max_left _ _⟩
  have hB : 0 ≤ 2 * SA ^ 2 * K + 2 * C * (SI * SA) ^ 2 + 2 * C' :=
    add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg SA)) hK0)
      (mul_nonneg (mul_nonneg (by norm_num) hC) (pow_two_nonneg _))) (mul_nonneg (by norm_num) hC')
  refine ⟨2 * SA ^ 2 * K + 2 * C * (SI * SA) ^ 2 + 2 * C', σ, hB, hσ0, hσ1, Nτ,
    fun k hk ξ => ?_⟩
  have hs0 : 0 ≤ (|ξ 0| + |ξ 1|) ^ 2 := by positivity
  have hσk : 0 ≤ σ ^ k := pow_nonneg hσ0.le k
  have hε := planarError_le_two_mul_pow hc hrσ heσ k
  have hε' := planarError_le_two_mul_pow hc' hrσ heσ' k
  -- the lower bound
  have hl := hlow k ξ
  have hlo : -(2 * C' * (|ξ 0| + |ξ 1|) ^ 2 * σ ^ k) ≤ planarNuIncrement p k ξ := by
    have := mul_le_mul_of_nonneg_left hε' (mul_nonneg hC' hs0)
    linarith
  -- the upper bound
  have hu := hup k (planarAhom p *ᵥ ξ)
  rw [planarAhom_inv_mulVec_mulVec hpc ξ] at hu
  set w := planarAhom p *ᵥ ξ with hw
  have hw1 : |w 0| + |w 1| ≤ SA * (|ξ 0| + |ξ 1|) := hSAb ξ
  have hw2 : w 0 ^ 2 + w 1 ^ 2 ≤ SA ^ 2 * (|ξ 0| + |ξ 1|) ^ 2 := by
    have h0 : w 0 ^ 2 + w 1 ^ 2 ≤ (|w 0| + |w 1|) ^ 2 := by
      nlinarith [sq_abs (w 0), sq_abs (w 1), abs_nonneg (w 0), abs_nonneg (w 1)]
    have h1 : (|w 0| + |w 1|) ^ 2 ≤ (SA * (|ξ 0| + |ξ 1|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hw1 2
    calc w 0 ^ 2 + w 1 ^ 2 ≤ (|w 0| + |w 1|) ^ 2 := h0
      _ ≤ (SA * (|ξ 0| + |ξ 1|)) ^ 2 := h1
      _ = SA ^ 2 * (|ξ 0| + |ξ 1|) ^ 2 := by ring
  have hv1 : |((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 0| + |((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 1| ≤
      SI * (SA * (|ξ 0| + |ξ 1|)) := by
    refine (hSIb _).trans ?_
    have e : |(![w 0, -w 1] : Fin 2 → ℝ) 0| + |(![w 0, -w 1] : Fin 2 → ℝ) 1| =
        |w 0| + |w 1| := by simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hw1 hSI0
  have hv2 : (|((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 0| +
      |((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 1|) ^ 2 ≤ (SI * SA) ^ 2 * (|ξ 0| + |ξ 1|) ^ 2 := by
    calc (|((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 0| +
        |((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 1|) ^ 2 ≤ (SI * (SA * (|ξ 0| + |ξ 1|))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hv1 2
      _ = (SI * SA) ^ 2 * (|ξ 0| + |ξ 1|) ^ 2 := by ring
  have hτk : planarNuTau p k ≤ K * σ ^ k := by
    have a := hτ k hk
    have b : planarNuTau p k ≤ planarTau p k :=
      le_add_of_nonneg_left (planarMuTau_nonneg p k)
    have c1 : Kτ * lτ ^ k ≤ K * σ ^ k := by
      have hl' : 0 ≤ lτ ^ k := pow_nonneg hlτ0.le k
      calc Kτ * lτ ^ k ≤ K * lτ ^ k := mul_le_mul_of_nonneg_right hKτ hl'
        _ ≤ K * σ ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlτ0.le hlσ k) hK0
    linarith
  have hup' : planarNuIncrement p k ξ ≤
      (2 * SA ^ 2 * K + 2 * C * (SI * SA) ^ 2) * (|ξ 0| + |ξ 1|) ^ 2 * σ ^ k := by
    have t1 : 2 * (w 0 ^ 2 + w 1 ^ 2) * planarNuTau p k ≤
        2 * (SA ^ 2 * (|ξ 0| + |ξ 1|) ^ 2) * (K * σ ^ k) :=
      mul_le_mul (by linarith) hτk (planarNuTau_nonneg p k)
        (mul_nonneg (by norm_num) (mul_nonneg (pow_two_nonneg _) hs0))
    have t2 : C * ((|((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 0| +
        |((planarAhom p)⁻¹ *ᵥ ![w 0, -w 1]) 1|) ^ 2 *
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))) ≤
        C * (((SI * SA) ^ 2 * (|ξ 0| + |ξ 1|) ^ 2) * (2 * σ ^ k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hv2 hε (by positivity)
        (mul_nonneg (pow_two_nonneg _) hs0)) hC
    have e : (2 * SA ^ 2 * K + 2 * C * (SI * SA) ^ 2) * (|ξ 0| + |ξ 1|) ^ 2 * σ ^ k =
        2 * (SA ^ 2 * (|ξ 0| + |ξ 1|) ^ 2) * (K * σ ^ k) +
          C * (((SI * SA) ^ 2 * (|ξ 0| + |ξ 1|) ^ 2) * (2 * σ ^ k)) := by
      ring
    rw [e]
    linarith
  have hA0 : 0 ≤ (2 * SA ^ 2 * K + 2 * C * (SI * SA) ^ 2) * (|ξ 0| + |ξ 1|) ^ 2 * σ ^ k :=
    mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg SA))
      hK0) (mul_nonneg (mul_nonneg (by norm_num) hC) (pow_two_nonneg _))) hs0) hσk
  have hA1 : 0 ≤ 2 * C' * (|ξ 0| + |ξ 1|) ^ 2 * σ ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC') hs0) hσk
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **Geometric rate of `E[ν(□_n, ξ)]`** (dimension two, `p > p_c(2)`): from some scale on,
`|E[ν(□_n, ξ)] - (1/2) ξ · ā ξ| ≤ K |ξ|² lⁿ`. -/
theorem exists_abs_planarNuMean_sub_le_geometric {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ K l : ℝ, 0 ≤ K ∧ 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ ξ : Fin 2 → ℝ,
      |planarNuMean p n ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
        K * (ξ 0 ^ 2 + ξ 1 ^ 2) * l ^ n := by
  obtain ⟨B, σ, hB, hσ0, hσ1, N, h⟩ := exists_abs_planarNuIncrement_le_geometric hpc
  refine ⟨2 * B / (1 - σ), σ, div_nonneg (mul_nonneg (by norm_num) hB) (sub_pos.2 hσ1).le, hσ0,
    hσ1, N, fun n hn ξ => ?_⟩
  have hlim := tendsto_planarNuLimit hpc ξ
  have hL : planarNuLimit p ξ = 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i := by
    rw [planarNuLimit_eq_planarAhom hpc]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hL] at hlim
  have hs0 : 0 ≤ (|ξ 0| + |ξ 1|) ^ 2 := by positivity
  have hb := abs_sub_le_of_abs_sub_succ_le hlim (mul_nonneg hB hs0) hσ0.le hσ1
    (fun k hk => h k hk ξ) hn
  have hq := abs_add_abs_sq_le ξ
  have h1σ : 0 < 1 - σ := sub_pos.2 hσ1
  refine hb.trans ?_
  have e : 2 * B / (1 - σ) * (ξ 0 ^ 2 + ξ 1 ^ 2) * σ ^ n =
      B * (2 * (ξ 0 ^ 2 + ξ 1 ^ 2)) * (σ ^ n / (1 - σ)) := by
    ring
  rw [e]
  have hσn : 0 ≤ σ ^ n / (1 - σ) := div_nonneg (pow_nonneg hσ0.le n) h1σ.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hB) hσn

/-- `lⁿ ≤ 3^{-nα}` for `α = min (1/4) (-log l / log 3)`. -/
theorem exists_pow_le_three_rpow {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ ∀ n : ℕ, l ^ n ≤ (3 : ℝ) ^ (-(n : ℝ) * α) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogl : Real.log l < 0 := Real.log_neg hl0 hl1
  set α := min (1 / 4 : ℝ) (-Real.log l / Real.log 3) with hα
  have hα0 : 0 < α := lt_min (by norm_num) (div_pos (neg_pos.2 hlogl) hlog3)
  refine ⟨α, hα0, min_le_left _ _, fun n => ?_⟩
  have h3 : l ≤ (3 : ℝ) ^ (-α) := by
    rw [← Real.exp_log hl0, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    have h := min_le_right (1 / 4 : ℝ) (-Real.log l / Real.log 3)
    rw [← hα, le_div_iff₀ hlog3] at h
    linarith
  calc l ^ n ≤ ((3 : ℝ) ^ (-α)) ^ n := pow_le_pow_left₀ hl0.le h3 n
    _ = (3 : ℝ) ^ (-(n : ℝ) * α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        ring

/-- **From a geometric rate from some scale on and a uniform bound to the algebraic rate at every
scale.** -/
theorem exists_le_three_rpow_of_geometric {ι : Type*} {x : ι → ℕ → ℝ} {w : ι → ℝ} {K l M : ℝ}
    {N : ℕ} (hw : ∀ i, 0 ≤ w i) (hl0 : 0 < l) (hl1 : l < 1)
    (hK : ∀ n, N ≤ n → ∀ i, x i n ≤ K * w i * l ^ n) (hM : ∀ n i, x i n ≤ M * w i) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ ∀ n i, x i n ≤ C * w i * (3 : ℝ) ^ (-(n : ℝ) * α) := by
  obtain ⟨α, hα0, hα, hpow⟩ := exists_pow_le_three_rpow hl0 hl1
  set C := max K 0 + max M 0 * (3 : ℝ) ^ ((N : ℝ) * α) with hC
  have h3N : 0 ≤ (3 : ℝ) ^ ((N : ℝ) * α) := by positivity
  refine ⟨α, C, hα0, hα, by positivity, fun n i => ?_⟩
  have h3n : 0 < (3 : ℝ) ^ (-(n : ℝ) * α) := by positivity
  have hwi := hw i
  rcases le_or_gt N n with hn | hn
  · have a := hK n hn i
    have b : K * w i * l ^ n ≤ max K 0 * w i * (3 : ℝ) ^ (-(n : ℝ) * α) := by
      calc K * w i * l ^ n ≤ max K 0 * w i * l ^ n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hwi)
              (pow_nonneg hl0.le n)
        _ ≤ max K 0 * w i * (3 : ℝ) ^ (-(n : ℝ) * α) :=
            mul_le_mul_of_nonneg_left (hpow n) (mul_nonneg (le_max_right _ _) hwi)
    have c : max K 0 * w i * (3 : ℝ) ^ (-(n : ℝ) * α) ≤ C * w i * (3 : ℝ) ^ (-(n : ℝ) * α) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hwi) h3n.le
      rw [hC]
      have : 0 ≤ max M 0 * (3 : ℝ) ^ ((N : ℝ) * α) := mul_nonneg (le_max_right _ _) h3N
      linarith
    linarith
  · have a := hM n i
    have h1 : 1 ≤ (3 : ℝ) ^ ((N : ℝ) * α) * (3 : ℝ) ^ (-(n : ℝ) * α) := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.one_le_rpow (by norm_num)
      have : (n : ℝ) ≤ N := by exact_mod_cast hn.le
      nlinarith
    have b : M * w i ≤ max M 0 * w i := mul_le_mul_of_nonneg_right (le_max_left _ _) hwi
    have c : max M 0 * w i ≤
        max M 0 * (3 : ℝ) ^ ((N : ℝ) * α) * w i * (3 : ℝ) ^ (-(n : ℝ) * α) := by
      have hmw : 0 ≤ max M 0 * w i := mul_nonneg (le_max_right _ _) hwi
      calc max M 0 * w i = max M 0 * w i * 1 := (mul_one _).symm
        _ ≤ max M 0 * w i * ((3 : ℝ) ^ ((N : ℝ) * α) * (3 : ℝ) ^ (-(n : ℝ) * α)) :=
            mul_le_mul_of_nonneg_left h1 hmw
        _ = _ := by ring
    have d : max M 0 * (3 : ℝ) ^ ((N : ℝ) * α) * w i * (3 : ℝ) ^ (-(n : ℝ) * α) ≤
        C * w i * (3 : ℝ) ^ (-(n : ℝ) * α) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hwi) h3n.le
      rw [hC]
      have : 0 ≤ max K 0 := le_max_right _ _
      linarith
    linarith

/-- `0 ≤ E[-μ(□_n, q)] ≤ C |q|²` and the same for the limit, uniformly in `n`. -/
theorem exists_planarMuMean_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (q : Fin 2 → ℝ), planarMuMean p n q ≤ C * (q 0 ^ 2 + q 1 ^ 2) := by
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  refine ⟨2 * C₀.toReal, by positivity, fun n q => ?_⟩
  have h := hup ⟨n, 0⟩ q
  have h' : planarMuMean p n q ≤ C₀.toReal * (|q 0| + |q 1|) ^ 2 := by
    rw [planarMuMean]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (le_of_eq ?_))
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC₀]
  have hq := abs_add_abs_sq_le q
  have := mul_le_mul_of_nonneg_left hq (ENNReal.toReal_nonneg : 0 ≤ C₀.toReal)
  linarith

theorem planarMuMean_nonneg (p : unitInterval) (n : ℕ) (q : Fin 2 → ℝ) : 0 ≤ planarMuMean p n q :=
  ENNReal.toReal_nonneg

theorem planarNuMean_nonneg (p : unitInterval) (n : ℕ) (ξ : Fin 2 → ℝ) : 0 ≤ planarNuMean p n ξ :=
  ENNReal.toReal_nonneg

theorem planarNuMean_le (p : unitInterval) (n : ℕ) (ξ : Fin 2 → ℝ) :
    planarNuMean p n ξ ≤ 9 / 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := by
  have h : planarNuMean p n ξ ≤ 9 / 4 * (|ξ 0| + |ξ 1|) ^ 2 := by
    rw [planarNuMean]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_planarNu_le p ⟨n, 0⟩ ξ)
  have hq := abs_add_abs_sq_le ξ
  linarith

/-- `|a - b| ≤ 2 M` for `a, b ∈ [0, M]`. -/
theorem abs_sub_le_two_mul_of_nonneg_of_le {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M)
    (hbM : b ≤ M) : |a - b| ≤ 2 * M := by
  rw [abs_le]
  constructor <;> linarith

/-- **Display (5.3) of Armstrong and Dario, the rate of Proposition 5.2 in expectation**
(dimension two, `p > p_c(2)`, no other hypothesis). There are `α ∈ (0, 1/4]` and `C` such that
for every `n` and all `p, q`,
`|E[μ(□_n, q)] + (1/2) q · ā⁻¹ q| + |E[ν(□_n, p)] - (1/2) p · ā p| ≤ C (|p|² + |q|²) 3^{-nα}`;
here `planarMuMean p n q = E[-μ(□_n, q)]`. -/
theorem planar_convexp {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 4 ∧ 0 ≤ C ∧ ∀ (n : ℕ) (ξ q : Fin 2 → ℝ),
      |planarMuMean p n q - 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| +
        |planarNuMean p n ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
        C * ((ξ 0 ^ 2 + ξ 1 ^ 2) + (q 0 ^ 2 + q 1 ^ 2)) * (3 : ℝ) ^ (-(n : ℝ) * α) := by
  obtain ⟨K₁, l₁, hK₁, hl₁0, hl₁1, N₁, h₁⟩ := exists_abs_planarMuMean_sub_le_geometric hpc
  obtain ⟨K₂, l₂, hK₂, hl₂0, hl₂1, N₂, h₂⟩ := exists_abs_planarNuMean_sub_le_geometric hpc
  obtain ⟨Cμ, hCμ, hμ⟩ := exists_planarMuMean_le hpc
  set l := max l₁ l₂ with hl
  have hl0 : 0 < l := lt_of_lt_of_le hl₁0 (le_max_left _ _)
  have hl1 : l < 1 := max_lt hl₁1 hl₂1
  -- the limits are in the same ranges as the means
  have hμL : ∀ q : Fin 2 → ℝ, 0 ≤ 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i ∧
      1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i ≤ Cμ * (q 0 ^ 2 + q 1 ^ 2) := fun q => by
    have ht := tendsto_planarMuLimit hpc q
    rw [planarMuLimit_eq hpc q] at ht
    exact ⟨ge_of_tendsto' ht fun n => planarMuMean_nonneg p n q,
      le_of_tendsto' ht fun n => hμ n q⟩
  have hνL : ∀ ξ : Fin 2 → ℝ, 0 ≤ 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i ∧
      1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i ≤ 9 / 2 * (ξ 0 ^ 2 + ξ 1 ^ 2) := fun ξ => by
    have ht := tendsto_planarNuLimit hpc ξ
    have hL : planarNuLimit p ξ = 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i := by
      rw [planarNuLimit_eq_planarAhom hpc]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hL] at ht
    exact ⟨ge_of_tendsto' ht fun n => planarNuMean_nonneg p n ξ,
      le_of_tendsto' ht fun n => planarNuMean_le p n ξ⟩
  set x : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℕ → ℝ := fun v n =>
    |planarMuMean p n v.2 - 1 / 2 * ∑ i, v.2 i * ((planarAhom p)⁻¹ *ᵥ v.2) i| +
      |planarNuMean p n v.1 - 1 / 2 * ∑ i, v.1 i * (planarAhom p *ᵥ v.1) i| with hx
  set w : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ℝ := fun v =>
    (v.1 0 ^ 2 + v.1 1 ^ 2) + (v.2 0 ^ 2 + v.2 1 ^ 2) with hw
  have hw0 : ∀ v, 0 ≤ w v := fun v => by positivity
  have hK : ∀ n, max N₁ N₂ ≤ n → ∀ v, x v n ≤ (K₁ + K₂) * w v * l ^ n := by
    intro n hn v
    have a := h₁ n (le_trans (le_max_left _ _) hn) v.2
    have b := h₂ n (le_trans (le_max_right _ _) hn) v.1
    have hl₁ : l₁ ^ n ≤ l ^ n := pow_le_pow_left₀ hl₁0.le (le_max_left _ _) n
    have hl₂ : l₂ ^ n ≤ l ^ n := pow_le_pow_left₀ hl₂0.le (le_max_right _ _) n
    have a' : K₁ * (v.2 0 ^ 2 + v.2 1 ^ 2) * l₁ ^ n ≤ K₁ * (v.2 0 ^ 2 + v.2 1 ^ 2) * l ^ n :=
      mul_le_mul_of_nonneg_left hl₁ (by positivity)
    have b' : K₂ * (v.1 0 ^ 2 + v.1 1 ^ 2) * l₂ ^ n ≤ K₂ * (v.1 0 ^ 2 + v.1 1 ^ 2) * l ^ n :=
      mul_le_mul_of_nonneg_left hl₂ (by positivity)
    have hln : 0 ≤ l ^ n := pow_nonneg hl0.le n
    have c : K₁ * (v.2 0 ^ 2 + v.2 1 ^ 2) * l ^ n + K₂ * (v.1 0 ^ 2 + v.1 1 ^ 2) * l ^ n ≤
        (K₁ + K₂) * w v * l ^ n := by
      rw [hw]
      have : 0 ≤ K₁ * (v.1 0 ^ 2 + v.1 1 ^ 2) * l ^ n + K₂ * (v.2 0 ^ 2 + v.2 1 ^ 2) * l ^ n := by
        positivity
      nlinarith
    simp only [hx]
    linarith
  have hM : ∀ n v, x v n ≤ (2 * Cμ + 9) * w v := by
    intro n v
    have a := abs_sub_le_two_mul_of_nonneg_of_le (planarMuMean_nonneg p n v.2) (hμL v.2).1
      (hμ n v.2) (hμL v.2).2
    have b := abs_sub_le_two_mul_of_nonneg_of_le (planarNuMean_nonneg p n v.1) (hνL v.1).1
      (planarNuMean_le p n v.1) (hνL v.1).2
    simp only [hx, hw]
    have h1 : 0 ≤ v.1 0 ^ 2 + v.1 1 ^ 2 := by positivity
    have h2 : 0 ≤ v.2 0 ^ 2 + v.2 1 ^ 2 := by positivity
    nlinarith
  obtain ⟨α, C, hα0, hα, hC, h⟩ := exists_le_three_rpow_of_geometric hw0 hl0 hl1 hK hM
  exact ⟨α, C, hα0, hα, hC, fun n ξ q => h n (ξ, q)⟩

end Rigidity.Proofs.Cluster
