import Rigidity.Proofs.Percolation.BondShells

/-!
# Summation over lattice bond shells

A nonnegative bond function dominated on each shell by a summable radial envelope is summable,
with its sum bounded by the inner box and the shell envelopes.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- Every finite bond family lies in one of the nested boxes. -/
theorem finite_bond_family_subset_box (d : ℕ) (z : Vertex d) (R : ℕ) (S : Finset (Bond d)) :
    ∃ N : ℕ, S ⊆ bondBox d z (R + N) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert e S he ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := exists_mem_bondBox d z e
    refine ⟨N + M, ?_⟩
    intro f hf
    simp only [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact bondBox_mono d z (by omega : M ≤ R + (N + M)) hM
    · exact bondBox_mono d z (by omega : R + N ≤ R + (N + M)) (hN hf)

/-- Summable nonnegative shell envelopes give a summable function on all lattice bonds. -/
theorem summable_of_bondShell_bound (d : ℕ) (z : Vertex d) (R : ℕ)
    (f : Bond d → ℝ) (g : ℕ → ℝ) (hf : ∀ e, 0 ≤ f e) (hg : ∀ n, 0 ≤ g n)
    (hs : Summable fun n => (2 * d * (2 * (R + n + 1) + 1) ^ d : ℕ) * g n)
    (hShell : ∀ n e, e ∈ bondShell d z R n → f e ≤ g n) :
    Summable f ∧
      (∑' e, f e) ≤ (∑ e ∈ bondBox d z R, f e) +
        ∑' n, (2 * d * (2 * (R + n + 1) + 1) ^ d : ℕ) * g n := by
  classical
  let H : ℕ → ℝ := fun n => (2 * d * (2 * (R + n + 1) + 1) ^ d : ℕ) * g n
  have hH (n : ℕ) : 0 ≤ H n := mul_nonneg (Nat.cast_nonneg _) (hg n)
  have hShellSum (n : ℕ) : (∑ e ∈ bondShell d z R n, f e) ≤ H n := by
    calc
      _ ≤ ∑ _e ∈ bondShell d z R n, g n := Finset.sum_le_sum fun e he => hShell n e he
      _ = ((bondShell d z R n).card : ℝ) * g n := by simp
      _ ≤ H n := by
        dsimp [H]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_bondShell_le d z R n) (hg n)
  have hPartial (N : ℕ) : (∑ e ∈ bondBox d z (R + N), f e) ≤
      (∑ e ∈ bondBox d z R, f e) + ∑ n ∈ Finset.range N, H n := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hsub : bondBox d z (R + N) ⊆ bondBox d z (R + N + 1) :=
        bondBox_mono d z (by omega)
      have hdiff := Finset.sum_sdiff (f := f) hsub
      change (∑ e ∈ bondShell d z R N, f e) +
        (∑ e ∈ bondBox d z (R + N), f e) =
        ∑ e ∈ bondBox d z (R + N + 1), f e at hdiff
      rw [show R + (N + 1) = R + N + 1 by omega, ← hdiff, Finset.sum_range_succ]
      linarith [hShellSum N]
  have hFinite (S : Finset (Bond d)) : (∑ e ∈ S, f e) ≤
      (∑ e ∈ bondBox d z R, f e) + ∑' n, H n := by
    obtain ⟨N, hN⟩ := finite_bond_family_subset_box d z R S
    calc
      _ ≤ ∑ e ∈ bondBox d z (R + N), f e :=
        Finset.sum_le_sum_of_subset_of_nonneg hN (fun e _ _ => hf e)
      _ ≤ (∑ e ∈ bondBox d z R, f e) + ∑ n ∈ Finset.range N, H n := hPartial N
      _ ≤ (∑ e ∈ bondBox d z R, f e) + ∑' n, H n :=
        add_le_add le_rfl (hs.sum_le_tsum _ (fun n _ => hH n))
  have hfs : Summable f := summable_of_sum_le hf hFinite
  exact ⟨hfs, hfs.tsum_le_of_sum_le hFinite⟩

end Rigidity.Percolation
