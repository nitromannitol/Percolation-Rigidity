import Rigidity.Proofs.Regularity.PlanarFlatnessDecay
import Rigidity.Proofs.Cluster.PlanarRHRestrictQuad

/-!
# Lemma 5.8, (5.33), with a minimal scale of class `O_s`

`PlanarNuSubaddOsTwo p` is the part of Proposition 5.2 of Armstrong and Dario
(arXiv:1609.09431v2) for `ν` in the form `O_s`: for every triadic cube `V` the error
`|ν(V, ξ) - ½ ξ · ā ξ|` (with `ν = 0` off the event that the partition exists and resolves `V`) is at
most `Z_V |ξ|²` with `Z_V ≤ O_r(C 3^{-α scale V})` measurable.

`exists_planarNuFlatness_os`: from it, there are `μ < 1` and a minimal scale `Y ≤ O_s(θ)` such that
almost surely, whenever `Y < 3^n`, the flatness error of the coarsened maximizer of
`ν(□_{n+1}, e_i)` is at most `2 · 9^n μ^n` for `i = 0, 1`. Outside an event `E_n` the reach is at
most `(3^{n+1})^{1/40}` on `□_{n+1}`, the configuration avoids the bad events of Lemma 5.5 at the
scales `k ∈ [⌊(9(n+1)+9)/10⌋, n]`, and the subadditivity errors of `□_{n+1}` and of its subcubes of
these scales are at most `(3^{n+1})^{-α/2}`; then the pathwise bound
(`exists_planarFlatness_le_of_reach`) decays (`exists_flatnessBound_le`). The probability of `E_n` is
at most `C exp(-c 3^{n σ})` (union bounds over the vertices, the subcubes and the scales), and the
supremum of the `3^n` with `ω ∈ E_n` is the minimal scale (`exists_isOsBond_of_events`).
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Cluster Rigidity.Proofs.Section5
open scoped Classical ENNReal Matrix

/-- **Proposition 5.2 of Armstrong and Dario for `ν` in the form `O_s`** (dimension two). -/
def PlanarNuSubaddOsTwo (p : unitInterval) : Prop :=
  ∃ r α C : ℝ, 0 < r ∧ 0 < α ∧ 0 < C ∧ ∀ V : TriadicCube 2,
    ∃ Z : Configuration 2 → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
      IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(V.scale : ℝ) * α)) ∧
      ∀ (ω : Configuration 2) (ξ : Fin 2 → ℝ),
        |(if PlanarPartitionEvent ω ∧ PlanarResolved ω V then planarNu ω V ξ else 0) -
          1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤ Z ω * (ξ 0 ^ 2 + ξ 1 ^ 2)

/-- The rate of the subadditivity errors against `(3^m)^{-α/2}` at a scale `k ≥ 9m/10`. -/
theorem subadd_ratio_ge {m k : ℕ} (hmk : 9 * m ≤ 10 * k) {α C : ℝ} (hα : 0 < α) (hC : 0 < C) :
    C⁻¹ * ((3 : ℝ) ^ m) ^ (2 * α / 5) ≤
      ((3 : ℝ) ^ m) ^ (-(α / 2)) / (C * (3 : ℝ) ^ (-(k : ℝ) * α)) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : ((3 : ℝ) ^ m) ^ (2 * α / 5) * (3 : ℝ) ^ (-(k : ℝ) * α) ≤
      ((3 : ℝ) ^ m) ^ (-(α / 2)) := by
    rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h : (9 * m : ℝ) ≤ 10 * k := by exact_mod_cast hmk
    nlinarith
  calc C⁻¹ * ((3 : ℝ) ^ m) ^ (2 * α / 5) * (C * (3 : ℝ) ^ (-(k : ℝ) * α))
      = (C⁻¹ * C) * (((3 : ℝ) ^ m) ^ (2 * α / 5) * (3 : ℝ) ^ (-(k : ℝ) * α)) := by ring
    _ ≤ 1 * ((3 : ℝ) ^ m) ^ (-(α / 2)) := by
        rw [inv_mul_cancel₀ hC.ne']; exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = _ := one_mul _

/-- **The tail of a subadditivity error** at a scale `k ≥ 9m/10` against `(3^m)^{-α/2}`. -/
theorem measure_subadd_gt_le {p : unitInterval} {Z : Configuration 2 → ℝ} {r α C : ℝ}
    (hr : 0 < r) (hα : 0 < α) (hC : 0 < C) {k m : ℕ} (hmk : 9 * m ≤ 10 * k)
    (hZ : IsOsBond 2 p Z r (C * (3 : ℝ) ^ (-(k : ℝ) * α))) :
    latticeBondLaw 2 p {ω | ((3 : ℝ) ^ m) ^ (-(α / 2)) < Z ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(C⁻¹ ^ r) * ((3 : ℝ) ^ m) ^ (2 * α / 5 * r))) := by
  refine (measure_lt_le_of_isOsBond hr (by positivity) (by positivity) hZ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
  have h := subadd_ratio_ge hmk hα hC
  have h2 := Real.rpow_le_rpow (by positivity) h hr.le
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)] at h2
  linarith

end Rigidity.Proofs.Regularity
