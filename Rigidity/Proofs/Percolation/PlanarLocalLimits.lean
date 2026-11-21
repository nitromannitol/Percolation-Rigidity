import Rigidity.Proofs.Percolation.PlanarMuLocal
import Rigidity.Proofs.Percolation.PlanarLimitCubes

/-!
# Limits of the local versions of `ν` and `μ`

Since the local versions differ from `1{P, V res} ν(V, ξ)` and `1{P, V res} (-μ(V, q))` in
expectation by at most `C |ξ|₁² exp (-c 3ⁿ)`, their expectations along any sequence of triadic
cubes `V_m` of scale `m` converge to the same limits: `E[ν_loc(V_m, ξ)] → (1/2) ξ · ā ξ` and
`E[μ_loc(V_m, q)] → lim E[-μ(□_m, q)]`.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- **Limit of the local version of `ν`.** -/
theorem tendsto_lintegral_planarNuLoc_of_scale {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (V : ℕ → TriadicCube 2) (hV : ∀ m, (V m).scale = m)
    (ξ : Fin 2 → ℝ) :
    Tendsto (fun m => (∫⁻ ω, planarNuLoc (V m) ξ ω ∂(latticeBondLaw 2 p)).toReal) atTop
      (𝓝 (planarNuLimit p ξ)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_planarNuLoc_localization hpc
  set s := (|ξ 0| + |ξ 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hfin : ∀ W : TriadicCube 2, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
      ENNReal.ofReal (planarNu ω W ξ) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun W => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p W ξ)
  have hfinl : ∀ W : TriadicCube 2, ∫⁻ ω, planarNuLoc W ξ ω ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun W => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((lintegral_mono fun ω => planarNuLoc_le W ξ ω).trans
        (by rw [lintegral_const, measure_univ, mul_one]))
  have hK : ENNReal.ofReal (9 / 4) * C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC
  refine tendsto_of_abs_sub_le (tendsto_lintegral_planarNu_of_scale hpc V hV ξ)
    (ε := fun m => (ENNReal.ofReal (9 / 4) * C).toReal * (s * Real.exp (-c * (3 : ℝ) ^ m)))
    ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul
      (ENNReal.ofReal (9 / 4) * C).toReal
  · have h1 := (h (V m) ξ).2.1
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfin _) hK (by positivity) h1
  · have h1 := (h (V m) ξ).2.2
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfinl _) hK (by positivity) h1

/-- **Limit of the local version of `μ`.** -/
theorem tendsto_lintegral_planarMuLoc_of_scale {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (V : ℕ → TriadicCube 2) (hV : ∀ m, (V m).scale = m)
    (q : Fin 2 → ℝ) :
    Tendsto (fun m => (∫⁻ ω, planarMuLoc (V m) q ω ∂(latticeBondLaw 2 p)).toReal) atTop
      (𝓝 (planarMuLimit p q)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_planarMuLoc_localization hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hfin : ∀ W : TriadicCube 2, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
      ENNReal.ofReal (-planarMu ω W q) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun W => ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top) (hup W q)
  have hfinl : ∀ W : TriadicCube 2, ∫⁻ ω, planarMuLoc W q ω ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun W => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((lintegral_mono fun ω => planarMuLoc_le W q ω).trans
        (by rw [lintegral_const, measure_univ, mul_one]))
  refine tendsto_of_abs_sub_le (tendsto_lintegral_neg_planarMu_of_scale hpc V hV q)
    (ε := fun m => C.toReal * (s * Real.exp (-c * (3 : ℝ) ^ m))) ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul
      C.toReal
  · have h1 := (h (V m) q).1
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfin _) hC (by positivity) h1
  · have h1 := (h (V m) q).2
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfinl _) hC (by positivity) h1

end Rigidity.Percolation
