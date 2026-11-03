import Rigidity.Steps.S2.GreenGradientHomogenization
import LatticeProb.Prob.FiniteTailMax

/-!
# Proposition 2.6, step:2.6-inputs: the stretched exponential tail of an `O_s` variable

`TailOfOsStep`: if `X ≤ O_s(θ)`, that is `E[exp((X/θ ∨ 0)^s)] ≤ 2`, then
`P[X ≥ R] ≤ 2 exp(-(R/θ)^s) ≤ C exp(-R^s / C)` with `C = max 2 θ^s` (Markov's inequality
applied to `exp((X/θ ∨ 0)^s)`, `LatticeProb.measure_ge_le_of_exp_rpow_moment`).
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Steps.S2

/-- step:2.6-inputs, tails: `X ≤ O_s(θ)` has the stretched exponential tail
`P[X ≥ R] ≤ C exp(-R^s / C)` with `C = max 2 θ^s`. -/
theorem tailOfOsStep (d : ℕ) (p : unitInterval) : TailOfOsStep d p := by
  intro s θ hs hθ
  refine ⟨max 2 (θ ^ s), lt_max_of_lt_left two_pos, ?_⟩
  intro X _hX hOs R hR
  obtain ⟨hint, hmom⟩ := hOs
  have heq : ∀ ω, Real.rpow (max (X ω / θ) 0) s = (max (X ω) 0 / θ) ^ s := by
    intro ω
    rw [← max_div_div_right hθ.le, zero_div]
    rfl
  simp_rw [heq] at hint hmom
  have hmark := LatticeProb.measure_ge_le_of_exp_rpow_moment (latticeBondLaw d p)
    (fun ω => max (X ω) 0) θ s hθ hs hint hmom hR
  have hsub : {ω | R ≤ X ω} ⊆ {ω | R ≤ max (X ω) 0} := fun ω hω =>
    le_trans (Set.mem_setOf_eq ▸ hω) (le_max_left _ _)
  refine (measure_mono hsub).trans (hmark.trans (ENNReal.ofReal_le_ofReal ?_))
  have hRs : 0 ≤ R ^ s := Real.rpow_nonneg hR s
  have hθs : 0 < θ ^ s := Real.rpow_pos_of_pos hθ s
  have hC : 0 < max 2 (θ ^ s) := lt_max_of_lt_left two_pos
  rw [Real.div_rpow hR hθ.le]
  change 2 * Real.exp (-(R ^ s / θ ^ s)) ≤ max 2 (θ ^ s) * Real.exp (-(R ^ s) / max 2 (θ ^ s))
  rw [neg_div]
  refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC.le
  exact neg_le_neg (div_le_div_of_nonneg_left hRs hθs (le_max_right _ _))

end Rigidity.Proofs.S2
