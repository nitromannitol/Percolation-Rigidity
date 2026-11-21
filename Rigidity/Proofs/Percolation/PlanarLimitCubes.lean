import Rigidity.Proofs.Percolation.PlanarMuLimitBounds

/-!
# The limits along arbitrary triadic cubes

By the approximate stationarity of `ν` and `μ`, the expectations on any triadic cube of scale `m`
differ from those on the cube `□_m` centred at the origin by at most `C |ξ|₁² exp (-c 3ᵐ)`. Hence
for every sequence of triadic cubes `V_m` of scale `m`,
`E[ν(V_m, ξ); P, V_m res] → (1/2) ξ · ā ξ` and `E[-μ(V_m, q); P, V_m res]` converges to the limit
of `-μ` on the cubes centred at the origin.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped ENNReal Classical

namespace Rigidity.Percolation

/-- Two real sequences whose differences are bounded by a null sequence have the same limit. -/
theorem tendsto_of_abs_sub_le {a b ε : ℕ → ℝ} {L : ℝ} (hb : Tendsto b atTop (𝓝 L))
    (hε : Tendsto ε atTop (𝓝 0)) (h₁ : ∀ m, a m ≤ b m + ε m) (h₂ : ∀ m, b m ≤ a m + ε m) :
    Tendsto a atTop (𝓝 L) := by
  have hup : Tendsto (fun m => b m + ε m) atTop (𝓝 L) := by
    simpa only [add_zero] using hb.add hε
  have hlow : Tendsto (fun m => b m - ε m) atTop (𝓝 L) := by
    simpa only [sub_zero] using hb.sub hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun m => by linarith [h₂ m])
    (fun m => h₁ m)

/-- A two-sided comparison of expectations on cubes of the same scale, in real form. -/
theorem toReal_le_toReal_add_of_lintegral_le {A B K : ℝ≥0∞} {x : ℝ} (hB : B ≠ ∞) (hK : K ≠ ∞)
    (hx : 0 ≤ x) (h : A ≤ B + K * ENNReal.ofReal x) : A.toReal ≤ B.toReal + K.toReal * x := by
  have h' := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨hB, ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top⟩) h
  rwa [ENNReal.toReal_add hB (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hx] at h'

/-- **Limit of `E[ν]` along arbitrary cubes.** -/
theorem tendsto_lintegral_planarNu_of_scale {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (V : ℕ → TriadicCube 2) (hV : ∀ m, (V m).scale = m)
    (ξ : Fin 2 → ℝ) :
    Tendsto (fun m => (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (V m) then
      ENNReal.ofReal (planarNu ω (V m) ξ) else 0) ∂(latticeBondLaw 2 p)).toReal) atTop
      (𝓝 (planarNuLimit p ξ)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_planarNu_le_of_scale_eq hpc
  set s := (|ξ 0| + |ξ 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hfin : ∀ W : TriadicCube 2, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
      ENNReal.ofReal (planarNu ω W ξ) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun W => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_planarNu_le p W ξ)
  refine tendsto_of_abs_sub_le (tendsto_planarNuLimit hpc ξ)
    (ε := fun m => C.toReal * (s * Real.exp (-c * (3 : ℝ) ^ m))) ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul C.toReal
  · have h1 := h ⟨m, 0⟩ (V m) (hV m).symm ξ
    rw [← hs] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfin _) hC (by positivity) h1
  · have h1 := h (V m) ⟨m, 0⟩ (hV m) ξ
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfin _) hC (by positivity) h1

/-- **Limit of `E[-μ]` along arbitrary cubes.** -/
theorem tendsto_lintegral_neg_planarMu_of_scale {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (V : ℕ → TriadicCube 2) (hV : ∀ m, (V m).scale = m)
    (q : Fin 2 → ℝ) :
    Tendsto (fun m => (∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω (V m) then
      ENNReal.ofReal (-planarMu ω (V m) q) else 0) ∂(latticeBondLaw 2 p)).toReal) atTop
      (𝓝 (planarMuLimit p q)) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_neg_planarMu_le_of_scale_eq hpc
  obtain ⟨C₀, hC₀, hup⟩ := exists_lintegral_neg_planarMu_le hpc
  set s := (|q 0| + |q 1|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hfin : ∀ W : TriadicCube 2, ∫⁻ ω, (if PlanarPartitionEvent ω ∧ PlanarResolved ω W then
      ENNReal.ofReal (-planarMu ω W q) else 0) ∂(latticeBondLaw 2 p) ≠ ∞ :=
    fun W => ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top) (hup W q)
  refine tendsto_of_abs_sub_le (tendsto_planarMuLimit hpc q)
    (ε := fun m => C.toReal * (s * Real.exp (-c * (3 : ℝ) ^ m))) ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul C.toReal
  · have h1 := h ⟨m, 0⟩ (V m) (hV m).symm q
    rw [← hs] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfin _) hC (by positivity) h1
  · have h1 := h (V m) ⟨m, 0⟩ (hV m) q
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (hfin _) hC (by positivity) h1

end Rigidity.Percolation
