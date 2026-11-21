import Rigidity.Proofs.Percolation.PlanarOmegaDecayIteration
import Rigidity.Proofs.Percolation.PlanarFiniteVolumeClose

/-!
# Geometric convergence of the finite-volume matrices

Under the bound of Lemma 5.9 of Armstrong and Dario, `τ_n` decays geometrically; by the closeness of
the finite-volume matrices at two scales (display (5.24)), the matrices `ā_{□_n}⁻¹` then converge
geometrically to their limit `L`: `|L - ā_{□_n}⁻¹| ≤ K λⁿ` entrywise (Step 4 of the proof of
Lemma 5.10, in dimension two).
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical Matrix

namespace Rigidity.Percolation

/-- Tails of geometric sums. -/
theorem sum_Ico_pow_le {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) (n m : ℕ) :
    ∑ k ∈ Finset.Ico n m, l ^ k ≤ l ^ n / (1 - l) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl0 n)
  have hs := summable_geometric_of_lt_one hl0 hl1
  calc ∑ k ∈ Finset.range (m - n), l ^ k ≤ ∑' k, l ^ k :=
        hs.sum_le_tsum _ fun k _ => pow_nonneg hl0 k
    _ = 1 / (1 - l) := by rw [tsum_geometric_of_lt_one hl0 hl1, one_div]

/-- **Geometric convergence of the finite-volume matrices under the bound of Lemma 5.9** (Armstrong
and Dario, Step 4 of the proof of Lemma 5.10, in dimension two). -/
theorem exists_abs_planarAhomInvLimit_sub_le_of_decay {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) {C₉ σ₉ ρ₉ : ℝ} {N₉ : ℕ} (hC₉ : 0 ≤ C₉) (hσ₉ : 0 ≤ σ₉)
    (hσ₉1 : σ₉ < 1) (hρ₉ : 0 ≤ ρ₉) (hρ₉1 : ρ₉ < 1)
    (h59 : ∀ n, N₉ ≤ n → planarOmegaD p n ≤
      C₉ * σ₉ ^ n + C₉ * ∑ l ∈ Finset.range (n + 1), ρ₉ ^ (n - l) * planarTau p l) :
    ∃ K l : ℝ, 0 < l ∧ l < 1 ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ i j : Fin 2,
      |planarAhomInvLimit p i j - planarAhomInvFinite p n i j| ≤ K * l ^ n := by
  obtain ⟨Kτ, lτ, hlτ0, hlτ1, Nτ, hτ⟩ :=
    exists_planarTau_le_pow_of_decay hpc hC₉ hσ₉ hσ₉1 hρ₉ hρ₉1 h59
  obtain ⟨C, hC, c, hc, hclose⟩ := exists_abs_planarAhomInvFinite_sub_le hpc
  have hsq3 : 1 < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hr1 : 1 / Real.sqrt 3 < 1 := (div_lt_one (by positivity)).2 hsq3
  have he1 : Real.exp (-c) < 1 := by simpa using Real.exp_lt_exp.2 (neg_lt_zero.2 hc)
  set σ := max lτ (max (1 / Real.sqrt 3) (Real.exp (-c))) with hσdef
  have hσ1 : σ < 1 := max_lt hlτ1 (max_lt hr1 he1)
  have hσ0 : 0 < σ := lt_of_lt_of_le hlτ0 (le_max_left _ _)
  have hlσ : lτ ≤ σ := le_max_left _ _
  have hrσ : 1 / Real.sqrt 3 ≤ σ := le_max_of_le_right (le_max_left _ _)
  have heσ : Real.exp (-c) ≤ σ := le_max_of_le_right (le_max_right _ _)
  have h1σ : 0 < 1 - σ := sub_pos.2 hσ1
  set B := C * (max Kτ 0 / (1 - σ) + 2 / (1 - σ) + 2) with hBdef
  refine ⟨B, σ, hσ0, hσ1, Nτ, fun n hn i j => ?_⟩
  have hσn : 0 ≤ σ ^ n := pow_nonneg hσ0.le n
  -- the bound for every `m ≥ n`
  have hbound : ∀ m, n ≤ m →
      |planarAhomInvFinite p m i j - planarAhomInvFinite p n i j| ≤ B * σ ^ n := by
    intro m hm
    refine (hclose n m hm i j).trans ?_
    have hT : ∑ k ∈ Finset.Ico n m, planarMuTau p k ≤ max Kτ 0 * (σ ^ n / (1 - σ)) := by
      calc ∑ k ∈ Finset.Ico n m, planarMuTau p k
          ≤ ∑ k ∈ Finset.Ico n m, max Kτ 0 * σ ^ k := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk' : n ≤ k := (Finset.mem_Ico.1 hk).1
            have a := hτ k (le_trans hn hk')
            have b : planarMuTau p k ≤ planarTau p k :=
              le_add_of_nonneg_right (planarNuTau_nonneg p k)
            have c1 : Kτ * lτ ^ k ≤ max Kτ 0 * σ ^ k := by
              have hl : 0 ≤ lτ ^ k := pow_nonneg hlτ0.le k
              calc Kτ * lτ ^ k ≤ max Kτ 0 * lτ ^ k :=
                    mul_le_mul_of_nonneg_right (le_max_left _ _) hl
                _ ≤ max Kτ 0 * σ ^ k :=
                    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlτ0.le hlσ k) (le_max_right _ _)
            linarith
        _ = max Kτ 0 * ∑ k ∈ Finset.Ico n m, σ ^ k := by rw [Finset.mul_sum]
        _ ≤ max Kτ 0 * (σ ^ n / (1 - σ)) :=
            mul_le_mul_of_nonneg_left (sum_Ico_pow_le hσ0.le hσ1 n m) (le_max_right _ _)
    have hE : ∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) ≤ 2 * (σ ^ n / (1 - σ)) := by
      calc ∑ k ∈ Finset.Ico n m, (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k))
          ≤ ∑ k ∈ Finset.Ico n m, 2 * σ ^ k :=
            Finset.sum_le_sum fun k _ => planarError_le_two_mul_pow hc hrσ heσ k
        _ = 2 * ∑ k ∈ Finset.Ico n m, σ ^ k := by rw [Finset.mul_sum]
        _ ≤ 2 * (σ ^ n / (1 - σ)) := by
            have := sum_Ico_pow_le hσ0.le hσ1 n m
            linarith
    have hen := planarError_le_two_mul_pow hc hrσ heσ n
    have hsum : ∑ k ∈ Finset.Ico n m, planarMuTau p k + (∑ k ∈ Finset.Ico n m,
        (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
        (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n))) ≤
        (max Kτ 0 / (1 - σ) + 2 / (1 - σ) + 2) * σ ^ n := by
      have e : (max Kτ 0 / (1 - σ) + 2 / (1 - σ) + 2) * σ ^ n =
          max Kτ 0 * (σ ^ n / (1 - σ)) + 2 * (σ ^ n / (1 - σ)) + 2 * σ ^ n := by
        field_simp
      rw [e]
      linarith
    calc C * (∑ k ∈ Finset.Ico n m, planarMuTau p k + (∑ k ∈ Finset.Ico n m,
          (1 / Real.sqrt ((3 : ℝ) ^ k) + Real.exp (-c * (3 : ℝ) ^ k)) +
          (1 / Real.sqrt ((3 : ℝ) ^ n) + Real.exp (-c * (3 : ℝ) ^ n))))
        ≤ C * ((max Kτ 0 / (1 - σ) + 2 / (1 - σ) + 2) * σ ^ n) :=
          mul_le_mul_of_nonneg_left hsum hC
      _ = B * σ ^ n := by rw [hBdef]; ring
  -- pass to the limit `m → ∞`
  have hlim : Tendsto (fun m => |planarAhomInvFinite p m i j - planarAhomInvFinite p n i j|)
      atTop (𝓝 |planarAhomInvLimit p i j - planarAhomInvFinite p n i j|) :=
    ((tendsto_planarAhomInvFinite hpc i j).sub tendsto_const_nhds).abs
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, hbound⟩)

end Rigidity.Percolation
