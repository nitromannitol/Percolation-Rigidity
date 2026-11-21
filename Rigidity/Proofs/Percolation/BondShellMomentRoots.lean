import Rigidity.Proofs.Percolation.BondShellStretchedExponential

/-!
# Moment-root summation over planar bond shells

Taking a positive power of a stretched-exponential shell bound preserves summability, with the
rate adjusted by that power.
-/

namespace Rigidity.Percolation

open LatticeProb.Percolation

/-- Positive powers of a stretched-exponentially localized bond field are summable. -/
theorem summable_planar_bond_shells_rpow (z : Vertex 2) (R : ℕ) (f : Bond 2 → ℝ)
    (K c t : ℝ) (hK : 0 ≤ K) (hc : 0 < c) (ht : 0 < t) (hf : ∀ e, 0 ≤ f e)
    (hglobal : ∀ e, f e ≤ K)
    (hdecay : ∀ n, 1 ≤ n → ∀ e ∈ bondShell 2 z R n,
      f e ≤ K * Real.exp (-c * Real.sqrt n)) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * Real.exp (-(c * t) * Real.sqrt n)) ∧
    Summable (fun e => (f e) ^ t) ∧
      (∑' e, (f e) ^ t) ≤ 36 * ((R : ℝ) + 1) ^ 2 * K ^ t *
        (1 + ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * Real.exp (-(c * t) * Real.sqrt n)) := by
  have hglobal' (e : Bond 2) : (f e) ^ t ≤ K ^ t :=
    Real.rpow_le_rpow (hf e) (hglobal e) ht.le
  have hdecay' (n : ℕ) (hn : 1 ≤ n) (e : Bond 2) (he : e ∈ bondShell 2 z R n) :
      (f e) ^ t ≤ K ^ t * Real.exp (-(c * t) * Real.sqrt n) := by
    have h := Real.rpow_le_rpow (hf e) (hdecay n hn e he) ht.le
    rw [Real.mul_rpow hK (Real.exp_pos _).le, ← Real.exp_mul] at h
    convert h using 1; congr 2; ring
  exact summable_planar_bond_shells z R (fun e => (f e) ^ t) (K ^ t) (c * t)
    (Real.rpow_nonneg hK _) (mul_pos hc ht) (fun e => Real.rpow_nonneg (hf e) _)
    hglobal' hdecay'

end Rigidity.Percolation
