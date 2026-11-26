import Rigidity.Proofs.Green.TimeSliceOscillationD

/-!
# Exit times of the cluster balls of `ℤ^d`

* `boundaryAccessible_of_infiniteD`: every finite set of an infinite open component is boundary
  accessible (the `d`-dimensional form of `boundaryAccessible_of_infinite`);
* `exitHyp_clusterBallD`: if `p_τ(z, w) ≤ C_B τ^{-d/2}` for the points `z, w` of `V_ρ(y)` and
  `τ ≥ ρ²`, for every `ρ ≥ r ≥ 1`, then for `ρ ≥ r` the heat kernel started in the interior of
  `V_ρ(y)` keeps at most `1/2` of its mass there at time `A ρ²`, `A = (2 · 5^d C_B + 1)^{2/d}`:
  the volume bound `|V_ρ| ≤ (5ρ)^d` and `5^d C_B A^{-d/2} ≤ 1/2`.
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

variable {d : ℕ} {ω : Configuration d}

theorem boundaryAccessible_of_infiniteD {K : OpenComponent ω} (hK : K.supp.Infinite)
    {A : Finset (Vertex d)} (hA : ∀ v ∈ A, v ∈ K.supp) :
    LatticeProb.Network.BoundaryAccessible (openGraph ω) A := by
  intro v hv
  obtain ⟨w, hwK, hwA⟩ := (hK.sdiff A.finite_toSet).nonempty
  refine ⟨w, hwA, ?_⟩
  exact SimpleGraph.ConnectedComponent.exact
    (((SimpleGraph.ConnectedComponent.mem_supp_iff K v).1 (hA v hv)).trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff K w).1 hwK).symm)

/-- The exit-time constant `A = (2 · 5^d C_B + 1)^{2/d}`. -/
noncomputable def exitConstD (d : ℕ) (CB : ℝ) : ℝ := (2 * 5 ^ d * CB + 1) ^ ((2 : ℝ) / d)

/-- **The exit time of the cluster balls.** -/
theorem exitHyp_clusterBallD [NeZero d] {CB : ℝ} (hCB : 0 ≤ CB) {K : OpenComponent ω}
    {y : Vertex d} {r : ℝ} (hr1 : 1 ≤ r)
    (hB : ∀ ρ, r ≤ ρ → ∀ z ∈ clusterBall K y ρ, ∀ w ∈ clusterBall K y ρ, ∀ τ, ρ ^ 2 ≤ τ →
      vsrwHeat (openGraph ω) (2 * d) τ z w ≤ CB * τ ^ (-((d : ℝ) / 2))) :
    ∀ ρ, r ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (exitConstD d CB * ρ ^ 2) z w ≤ 1 / 2 := by
  intro ρ hρ z hz
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hρ1 : 1 ≤ ρ := hr1.trans hρ
  set A := exitConstD d CB with hA
  have hbase : 1 ≤ 2 * 5 ^ d * CB + 1 := by
    have : 0 ≤ 2 * 5 ^ d * CB := by positivity
    linarith
  have hA1 : 1 ≤ A := Real.one_le_rpow hbase (by positivity)
  have hA0 : 0 < A := by linarith
  have hτ : 0 < A * ρ ^ 2 := by positivity
  have hAd : A ^ ((d : ℝ) / 2) = 2 * 5 ^ d * CB + 1 := by
    rw [hA, exitConstD, ← Real.rpow_mul (by linarith)]
    rw [show (2 : ℝ) / d * (d / 2) = 1 by field_simp, Real.rpow_one]
  have hρpow : (ρ ^ 2) ^ ((d : ℝ) / 2) = ρ ^ d := by
    rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul (by linarith),
      show ((2 : ℕ) : ℝ) * ((d : ℝ) / 2) = ((d : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast ρ d
  have hτpow : (A * ρ ^ 2) ^ (-((d : ℝ) / 2)) = ((2 * 5 ^ d * CB + 1) * ρ ^ d)⁻¹ := by
    rw [Real.rpow_neg hτ.le, Real.mul_rpow (by linarith) (by positivity), hAd, hρpow]
  have hzK := interiorOf_subset _ hz
  have hterm : ∀ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ CB * ((2 * 5 ^ d * CB + 1) * ρ ^ d)⁻¹ := by
    intro w hw
    have h1 := hB ρ hρ z hzK w (interiorOf_subset _ hw) (A * ρ ^ 2)
      (le_mul_of_one_le_left (sq_nonneg ρ) hA1)
    rwa [hτpow] at h1
  have hc1 : ((interiorOf (openGraph ω) (clusterBall K y ρ)).card : ℝ) ≤
      (clusterBall K y ρ).card := by
    exact_mod_cast Finset.card_le_card (interiorOf_subset _)
  have hcard := hc1.trans (card_clusterBall_le K y hρ1)
  have hρd : 0 < ρ ^ d := by positivity
  calc ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w
      ≤ ∑ _w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
          CB * ((2 * 5 ^ d * CB + 1) * ρ ^ d)⁻¹ := Finset.sum_le_sum hterm
    _ = (interiorOf (openGraph ω) (clusterBall K y ρ)).card *
          (CB * ((2 * 5 ^ d * CB + 1) * ρ ^ d)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (5 * ρ) ^ d * (CB * ((2 * 5 ^ d * CB + 1) * ρ ^ d)⁻¹) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 5 ^ d * CB / (2 * 5 ^ d * CB + 1) := by rw [mul_pow]; field_simp; try ring
    _ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith

end Rigidity.Green
