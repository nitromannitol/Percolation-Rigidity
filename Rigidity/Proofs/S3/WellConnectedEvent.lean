import Rigidity.Steps.S3.NotLipschitz

/-!
# `step:3.2-event`, well-connected part

`WellConnectedEventStep` (corrected draft L982): the cube `Q_N` is well-connected with probability
tending to one. This is Proposition 2.3 (the literature input `Rigidity.External.WellConnectedInput`,
Pisztora; Penrose-Pisztora), which bounds the probability of the complement by `C exp(-c N^s)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology LatticeProb LatticeProb.Percolation

namespace Rigidity.Proofs.S3

variable (d : ℕ) [NeZero d]

/-- `step:3.2-event`, well-connected part: by Proposition 2.3 the probability that `Q_N` is not
well-connected is at most `C exp(-c N^s)`, which tends to zero. -/
theorem wellConnectedEventStep (p : unitInterval) : Rigidity.Steps.S3.WellConnectedEventStep d p := by
  intro hW hd hpc hp1
  obtain ⟨c, C, s, hc, -, hs, hbound⟩ := hW d hd p hpc hp1
  have hpow : Tendsto (fun N : ℕ => c * (N : ℝ) ^ s) atTop atTop :=
    ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hexp : Tendsto (fun N : ℕ => C * Real.exp (-(c * (N : ℝ) ^ s))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp hpow).const_mul C
  have hlim := ENNReal.tendsto_ofReal hexp
  rw [ENNReal.ofReal_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun N => hbound 0 N

end Rigidity.Proofs.S3
