import Rigidity.Proofs.Percolation.PlanarNuIncrements

/-!
# Summability of `τ_k` and the vanishing of the energy of the differences

The quantities `τ_k` of Armstrong and Dario (Section 5, before Lemma 5.4) are summable: the
positive part of an almost nonnegative increment `I_k = M_k - M_{k+1}` with `I_k ≥ -ε_k` is at
most `I_k + ε_k`, the increments telescope, `M ≥ 0`, and `∑ ε_k < ∞` for
`ε_k = 3 ^ (-k/2) + exp (-c 3 ^ k)`. Consequently the tail sums `∑_{k ≥ n} τ_k` tend to zero,
and by Lemma 5.4 the expected energy of the differences between the minimizers of `μ` at the
scales `m ≥ n` and `n`, divided by the volume, tends to zero as `n → ∞`, uniformly in `m`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- `√(3 ^ k) = √3 ^ k`. -/
theorem sqrt_three_pow (k : ℕ) : Real.sqrt ((3 : ℝ) ^ k) = Real.sqrt 3 ^ k := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg 3) k), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt (by norm_num)]

/-- The errors `3 ^ (-k/2) + exp (-c 3 ^ k)` are summable for `c > 0`. -/
theorem summable_planarError {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => 1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k) := by
  have h3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hg1 : Summable fun k : ℕ => (1 / Real.sqrt 3) ^ k :=
    summable_geometric_of_lt_one (by positivity) ((div_lt_one (by positivity)).2 h3)
  have hg2 : Summable fun k : ℕ => Real.exp (-c) ^ k :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 hc))
  refine Summable.add ?_ ?_
  · refine hg1.congr fun k => ?_
    rw [sqrt_three_pow, one_div_pow]
  · refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hg2
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hk : (k : ℝ) ≤ 3 ^ k := by exact_mod_cast (Nat.lt_pow_self (by norm_num)).le
    nlinarith

/-- **Positive parts of almost nonnegative telescoping increments.** -/
theorem sum_range_max_le_of_neg_le {M ε : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k)
    (hlow : ∀ k, -ε k ≤ M k - M (k + 1)) (hε0 : ∀ k, 0 ≤ ε k) (N : ℕ) :
    ∑ k ∈ Finset.range N, max (M k - M (k + 1)) 0 ≤ M 0 + ∑ k ∈ Finset.range N, ε k := by
  have h : ∀ k, max (M k - M (k + 1)) 0 ≤ (M k - M (k + 1)) + ε k := fun k =>
    max_le (by linarith [hε0 k]) (by linarith [hlow k])
  calc ∑ k ∈ Finset.range N, max (M k - M (k + 1)) 0
      ≤ ∑ k ∈ Finset.range N, ((M k - M (k + 1)) + ε k) := Finset.sum_le_sum fun k _ => h k
    _ = M 0 - M N + ∑ k ∈ Finset.range N, ε k := by
        rw [Finset.sum_add_distrib, Finset.sum_range_sub']
    _ ≤ M 0 + ∑ k ∈ Finset.range N, ε k := by linarith [hM N]

/-- Summability of the positive parts of almost nonnegative telescoping increments. -/
theorem summable_max_of_neg_le {M ε : ℕ → ℝ} (hM : ∀ k, 0 ≤ M k)
    (hlow : ∀ k, -ε k ≤ M k - M (k + 1)) (hε : Summable ε) (hε0 : ∀ k, 0 ≤ ε k) :
    Summable fun k => max (M k - M (k + 1)) 0 :=
  summable_of_sum_range_le (c := M 0 + ∑' k, ε k) (fun _ => le_max_right _ _) fun N =>
    (sum_range_max_le_of_neg_le hM hlow hε0 N).trans
      (add_le_add le_rfl (hε.sum_le_tsum _ fun k _ => hε0 k))

/-- **Summability of `τ_k`** (in dimension two). -/
theorem summable_planarTau {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    Summable (planarTau p) := by
  obtain ⟨Cμ, hCμ, cμ, hcμ, hμ⟩ := exists_neg_le_planarMuIncrement hpc
  obtain ⟨Cν, hCν, cν, hcν, hν⟩ := exists_neg_le_planarNuIncrement hpc
  have hmu : ∀ i : Fin 2, Summable fun k => max (planarMuIncrement p k (Pi.single i 1)) 0 := by
    intro i
    set ξ : Fin 2 → ℝ := Pi.single i 1
    have hε := (summable_planarError hcμ).mul_left (Cμ * (|ξ 0| + |ξ 1|) ^ 2)
    refine summable_max_of_neg_le (M := fun k => planarMuMean p k ξ) (fun k => ENNReal.toReal_nonneg)
      (fun k => ?_) hε (fun k => by positivity)
    have h := hμ k ξ
    simp only [planarMuIncrement] at h
    linarith
  have hnu : ∀ i : Fin 2, Summable fun k =>
      max (planarNuIncrement p k (planarAhomInvSingle p i)) 0 := by
    intro i
    set ξ : Fin 2 → ℝ := planarAhomInvSingle p i
    have hε := (summable_planarError hcν).mul_left (Cν * (|ξ 0| + |ξ 1|) ^ 2)
    refine summable_max_of_neg_le (M := fun k => planarNuMean p k ξ) (fun k => ENNReal.toReal_nonneg)
      (fun k => ?_) hε (fun k => by positivity)
    have h := hν k ξ
    simp only [planarNuIncrement] at h
    linarith
  exact (summable_sum fun i _ => hmu i).add (summable_sum fun i _ => hnu i)

/-- Finite sums of `τ` beyond `n` are at most the tail sum `∑_{k ≥ 0} τ_{k + n}`. -/
theorem sum_Ico_le_tsum_nat_add {f : ℕ → ℝ} (hf : Summable f) (hf0 : ∀ k, 0 ≤ f k) (n m : ℕ) :
    ∑ k ∈ Finset.Ico n m, f k ≤ ∑' k, f (k + n) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : Summable fun k => f (k + n) := (summable_nat_add_iff n).2 hf
  calc ∑ k ∈ Finset.range (m - n), f (n + k) = ∑ k ∈ Finset.range (m - n), f (k + n) :=
        Finset.sum_congr rfl fun k _ => by rw [add_comm]
    _ ≤ ∑' k, f (k + n) := hs.sum_le_tsum _ fun k _ => hf0 _

/-- **Lemma 5.4 of Armstrong and Dario for `μ`, qualitative form** (in dimension two). There is a
sequence `R_n → 0` such that for all `m ≥ n` and `q`, the expected energy of the differences
between the minimizer of `μ(□_m, q)` restricted to the resolved subcubes of scale `n` and the
minimizers on these subcubes, divided by `|□_m|`, is at most `(|q|² + |q|₁²) R_n`. -/
theorem exists_planarMuDefect_le_tendsto {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ R : ℕ → ℝ, Tendsto R atTop (𝓝 0) ∧ ∀ (n m : ℕ), n ≤ m → ∀ q : Fin 2 → ℝ,
      (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω ⟨m, 0⟩ then
          ENNReal.ofReal (planarMuDefect ω ⟨m, 0⟩ n q) else 0) ∂(latticeBondLaw 2 p)).toReal /
          (⟨m, 0⟩ : TriadicCube 2).volume ≤
        (q 0 ^ 2 + q 1 ^ 2 + (|q 0| + |q 1|) ^ 2) * R n := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_planarMuDefect_le_planarMuTau hpc
  set ε : ℕ → ℝ := fun k => 1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k) with hεdef
  have hε0 : ∀ k, 0 ≤ ε k := fun k => by positivity
  have hεs : Summable ε := summable_planarError hc
  have hτs : Summable (planarMuTau p) :=
    Summable.of_nonneg_of_le (planarMuTau_nonneg p)
      (fun k => le_add_of_nonneg_right (planarNuTau_nonneg p k)) (summable_planarTau hpc)
  refine ⟨fun n => 2 * ∑' k, planarMuTau p (k + n) + C * (∑' k, ε (k + n) + ε n), ?_, ?_⟩
  · have h1 := tendsto_sum_nat_add (planarMuTau p)
    have h2 := tendsto_sum_nat_add ε
    have h3 : Tendsto ε atTop (𝓝 0) := hεs.tendsto_atTop_zero
    have := (h1.const_mul 2).add ((h2.add h3).const_mul C)
    simpa only [mul_zero, add_zero] using this
  · intro n m hnm q
    refine (h n m hnm q).trans ?_
    have hT := sum_Ico_le_tsum_nat_add hτs (planarMuTau_nonneg p) n m
    have hE := sum_Ico_le_tsum_nat_add hεs hε0 n m
    have hTn : 0 ≤ ∑' k, planarMuTau p (k + n) := tsum_nonneg fun k => planarMuTau_nonneg p _
    have hEn : 0 ≤ ∑' k, ε (k + n) := tsum_nonneg fun k => hε0 _
    have hq2 : 0 ≤ q 0 ^ 2 + q 1 ^ 2 := by positivity
    have hQ : 0 ≤ (|q 0| + |q 1|) ^ 2 := by positivity
    have k1 : 2 * (q 0 ^ 2 + q 1 ^ 2) * ∑ k ∈ Finset.Ico n m, planarMuTau p k ≤
        (q 0 ^ 2 + q 1 ^ 2) * (2 * ∑' k, planarMuTau p (k + n)) := by
      nlinarith
    have k2 : C * (|q 0| + |q 1|) ^ 2 * (∑ k ∈ Finset.Ico n m, ε k + ε n) ≤
        (|q 0| + |q 1|) ^ 2 * (C * (∑' k, ε (k + n) + ε n)) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hE (le_refl (ε n)))
        (mul_nonneg hC hQ)
      linarith
    have k3 : 0 ≤ (q 0 ^ 2 + q 1 ^ 2) * (C * (∑' k, ε (k + n) + ε n)) :=
      mul_nonneg hq2 (mul_nonneg hC (add_nonneg hEn (hε0 n)))
    have k4 : 0 ≤ (|q 0| + |q 1|) ^ 2 * (2 * ∑' k, planarMuTau p (k + n)) := by positivity
    have e : (q 0 ^ 2 + q 1 ^ 2 + (|q 0| + |q 1|) ^ 2) *
        (2 * ∑' k, planarMuTau p (k + n) + C * (∑' k, ε (k + n) + ε n)) =
        (q 0 ^ 2 + q 1 ^ 2) * (2 * ∑' k, planarMuTau p (k + n)) +
        (|q 0| + |q 1|) ^ 2 * (C * (∑' k, ε (k + n) + ε n)) +
        (q 0 ^ 2 + q 1 ^ 2) * (C * (∑' k, ε (k + n) + ε n)) +
        (|q 0| + |q 1|) ^ 2 * (2 * ∑' k, planarMuTau p (k + n)) := by ring
    rw [e]
    simp only [hεdef] at k2 ⊢
    linarith

end Rigidity.Percolation
