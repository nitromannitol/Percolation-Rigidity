import Rigidity.Proofs.Cluster.GeneralMuStationary
import Rigidity.Proofs.Percolation.PlanarLimitCubes

/-!
# Limits of the local versions of `μ` in every dimension

The local version `μ_loc(V, q)` and the stationary local version of `-μ(V, q)` have expectations
within `C |q|₁² exp(-c 3ⁿ)` of `E[-μ(V, q); P, V res]`, `n` the scale of `V`
(`exists_cubeMuLoc_localization`, `exists_cubeMuStat_localization`). Hence along any sequence of
triadic cubes `V_m` of scale `m`, whenever the expectations of `1{P, V_m res} (-μ(V_m, q))`
converge, those of the local versions converge to the same limit. The approximate stationarity of
`μ` (`exists_lintegral_neg_cubeMu_le_of_scale_eq`) shows that the limit, when it exists along one
sequence of cubes, exists along every sequence and does not depend on it.
-/

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Percolation

variable {d : ℕ}

theorem lintegral_cubeMu_indicator_ne_top [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (V : TriadicCube d) (q : Fin d → ℝ) :
    ∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω V then
      ENNReal.ofReal (-cubeMu ω V q) else 0) ∂(latticeBondLaw d p) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((lintegral_mono fun ω =>
    cubeMu_indicator_le (by omega) V q ω).trans (by rw [lintegral_const, measure_univ, mul_one]))

theorem lintegral_cubeMuLoc_ne_top [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (V : TriadicCube d) (q : Fin d → ℝ) :
    ∫⁻ ω, cubeMuLoc V q ω ∂(latticeBondLaw d p) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((lintegral_mono fun ω =>
    cubeMuLoc_le (by omega) V q ω).trans (by rw [lintegral_const, measure_univ, mul_one]))

theorem lintegral_cubeMuStat_ne_top [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (V : TriadicCube d) (q : Fin d → ℝ) :
    ∫⁻ ω, cubeMuStat V q ω ∂(latticeBondLaw d p) ≠ ∞ := by
  rw [lintegral_cubeMuStat_eq]
  exact lintegral_cubeMuLoc_ne_top hd _ q

/-- **Limit of the local version of `μ`.** -/
theorem tendsto_lintegral_cubeMuLoc_of_tendsto [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : ℕ → TriadicCube d) (hV : ∀ m, (V m).scale = m)
    (q : Fin d → ℝ) {L : ℝ}
    (hL : Tendsto (fun m => (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω (V m) then
      ENNReal.ofReal (-cubeMu ω (V m) q) else 0) ∂(latticeBondLaw d p)).toReal) atTop (𝓝 L)) :
    Tendsto (fun m => (∫⁻ ω, cubeMuLoc (V m) q ω ∂(latticeBondLaw d p)).toReal) atTop
      (𝓝 L) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_cubeMuLoc_localization hd hpc
  set s := (∑ i, |q i|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  refine tendsto_of_abs_sub_le hL (ε := fun m => C.toReal * (s * Real.exp (-c * (3 : ℝ) ^ m)))
    ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul
      C.toReal
  · have h1 := (h (V m) q).1
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (lintegral_cubeMu_indicator_ne_top hd _ q) hC
      (by positivity) h1
  · have h1 := (h (V m) q).2
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (lintegral_cubeMuLoc_ne_top hd _ q) hC
      (by positivity) h1

/-- **Limit of the stationary local version of `μ`.** -/
theorem tendsto_lintegral_cubeMuStat_of_tendsto [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V : ℕ → TriadicCube d) (hV : ∀ m, (V m).scale = m)
    (q : Fin d → ℝ) {L : ℝ}
    (hL : Tendsto (fun m => (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω (V m) then
      ENNReal.ofReal (-cubeMu ω (V m) q) else 0) ∂(latticeBondLaw d p)).toReal) atTop (𝓝 L)) :
    Tendsto (fun m => (∫⁻ ω, cubeMuStat (V m) q ω ∂(latticeBondLaw d p)).toReal) atTop
      (𝓝 L) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_cubeMuStat_localization hd hpc
  set s := (∑ i, |q i|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  refine tendsto_of_abs_sub_le hL (ε := fun m => C.toReal * (s * Real.exp (-c * (3 : ℝ) ^ m)))
    ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul
      C.toReal
  · have h1 := (h (V m) q).1
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (lintegral_cubeMu_indicator_ne_top hd _ q) hC
      (by positivity) h1
  · have h1 := (h (V m) q).2
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (lintegral_cubeMuStat_ne_top hd _ q) hC
      (by positivity) h1

/-- **The limit does not depend on the sequence of cubes.** If the expectations of
`1{P, V_m res} (-μ(V_m, q))` converge to `L` along one sequence of triadic cubes of scale `m`, they
converge to `L` along every such sequence. -/
theorem tendsto_lintegral_neg_cubeMu_of_tendsto [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (V W : ℕ → TriadicCube d) (hV : ∀ m, (V m).scale = m)
    (hW : ∀ m, (W m).scale = m) (q : Fin d → ℝ) {L : ℝ}
    (hL : Tendsto (fun m => (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω (V m) then
      ENNReal.ofReal (-cubeMu ω (V m) q) else 0) ∂(latticeBondLaw d p)).toReal) atTop (𝓝 L)) :
    Tendsto (fun m => (∫⁻ ω, (if PartitionEvent ω ∧ PartitionResolved ω (W m) then
      ENNReal.ofReal (-cubeMu ω (W m) q) else 0) ∂(latticeBondLaw d p)).toReal) atTop
      (𝓝 L) := by
  obtain ⟨C, hC, c, hc, h⟩ := exists_lintegral_neg_cubeMu_le_of_scale_eq hd hpc
  set s := (∑ i, |q i|) ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  refine tendsto_of_abs_sub_le hL (ε := fun m => C.toReal * (s * Real.exp (-c * (3 : ℝ) ^ m)))
    ?_ (fun m => ?_) (fun m => ?_)
  · simpa only [mul_zero] using ((tendsto_exp_neg_mul_three_pow hc).const_mul s).const_mul
      C.toReal
  · have h1 := h (V m) (W m) ((hV m).trans (hW m).symm) q
    rw [← hs, hV m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (lintegral_cubeMu_indicator_ne_top hd _ q) hC
      (by positivity) h1
  · have h1 := h (W m) (V m) ((hW m).trans (hV m).symm) q
    rw [← hs, hW m] at h1
    exact toReal_le_toReal_add_of_lintegral_le (lintegral_cubeMu_indicator_ne_top hd _ q) hC
      (by positivity) h1

end Rigidity.Percolation
