import Rigidity.Proofs.Green.DisplacementTailD

/-!
# One term of the passage from smooth initial data to a point source

For a summable, square summable `δ` of mass zero, a time `σ ∈ [t/2, t]`, a radius `l ≥ 1` with
`2l ≤ √t` above the minimal scale of the order-zero estimate at the pole `y`, and the diagonal bound
`p_r(z, z) ≤ Λ` for `z ∈ V_{√t}(y)` and `r ∈ [t/4, 2t]`,

  `‖P_σ δ‖ ≤ (5l)^{d/2} η ‖δ‖ + (2 + η) Σ_{x ∉ V_l(y)} |δ(x)|`,  `η = κ l Λ^{1/2} t^{-1/2}`

(`l2norm_heatFlowG_le_of_scale`), with `κ = (C₀ + (10C₀ + 32)A)(1 + √8)` from the order-zero
constant `C₀` and the exit-time constant `A`. This is `l2norm_heatFlowG_le_of_ball` with `R = √t`
and the volume bound `|V_l| ≤ (5l)^d`.
-/

open scoped Classical
open LatticeProb.Percolation Rigidity.WeakPoincare

namespace Rigidity.Green

variable {d : ℕ} [NeZero d] {ω : Configuration d}

/-- `√(8 (2σ)^{-2} Λ) ≤ √8 √Λ / t` for `2σ ≥ t > 0`. -/
theorem sqrt_eight_div_le {t σ Λ : ℝ} (ht : 0 < t) (hσt : t ≤ σ + σ) (hΛ : 0 ≤ Λ) :
    Real.sqrt (8 / (σ + σ) ^ 2 * Λ) ≤ Real.sqrt 8 * Real.sqrt Λ / t := by
  have h1 : 8 / (σ + σ) ^ 2 * Λ ≤ 8 / t ^ 2 * Λ := by
    apply mul_le_mul_of_nonneg_right _ hΛ
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ ht.le hσt 2)
  have h2 : 8 / t ^ 2 * Λ = (Real.sqrt 8 * Real.sqrt Λ / t) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hΛ]
    ring
  calc _ ≤ Real.sqrt (8 / t ^ 2 * Λ) := Real.sqrt_le_sqrt h1
    _ = _ := by rw [h2, Real.sqrt_sq (by positivity)]

/-- **One term**: the heat flow of a signed measure of mass zero at a time `σ ∈ [t/2, t]`. -/
theorem l2norm_heatFlowG_le_of_scale {K : OpenComponent ω} {y : Vertex d} (hy : y ∈ K.supp)
    (hacc : ∀ ρ, LatticeProb.Network.BoundaryAccessible (openGraph ω)
      (interiorOf (openGraph ω) (clusterBall K y ρ)))
    {X C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOZ : ∀ R', 2 * X ≤ R' → ∀ u : Vertex d → ℝ,
      (∀ x ∈ interiorOf (openGraph ω) (clusterBall K y R'),
        LatticeProb.Graph.laplacian (openGraph ω) u x = 0) →
      ∃ c : ℝ, ∀ r, X ≤ r → r ≤ R' / 2 →
        nL2 (clusterBall K y r) (fun x => u x - c) ≤ C₀ * (r / R') * nL2 (clusterBall K y R') u)
    {A ρ₀ : ℝ} (hA : 0 ≤ A)
    (hHK : ∀ ρ, ρ₀ ≤ ρ → ∀ z ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
      ∑ w ∈ interiorOf (openGraph ω) (clusterBall K y ρ),
        vsrwHeat (openGraph ω) (2 * d) (A * ρ ^ 2) z w ≤ 1 / 2)
    {t σ : ℝ} (ht : 0 < t) (hσt : t / 2 ≤ σ) (hσt' : σ ≤ t)
    {δ : Vertex d → ℝ} (hδ1 : Summable fun x => |δ x|)
    (hδ2 : Summable fun x => δ x ^ 2) (hδ0 : ∑' x, δ x = 0)
    {l Λ N T : ℝ} (hXl : X ≤ l) (hl : 1 ≤ l) (hρ₀ : ρ₀ ≤ 2 * l) (hlt : 2 * l ≤ Real.sqrt t)
    (hΛ : 0 ≤ Λ)
    (hdiag : ∀ z ∈ clusterBall K y (Real.sqrt t), ∀ r, t / 4 ≤ r → r ≤ 2 * t →
      vsrwHeat (openGraph ω) (2 * d) r z z ≤ Λ)
    (hN : l2norm δ ≤ N)
    (hT : ∑' x, (if x ∈ clusterBall K y l then 0 else |δ x|) ≤ T) :
    l2norm (heatFlowG (openGraph ω) (2 * d) σ δ) ≤
      Real.sqrt ((5 * l) ^ d) *
          ((C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * l * Real.sqrt Λ / Real.sqrt t) * N +
        (2 + (C₀ + (10 * C₀ + 32) * A) * (1 + Real.sqrt 8) * l * Real.sqrt Λ / Real.sqrt t) *
          T := by
  have hσ : 0 < σ := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hne : (clusterBall K y l).Nonempty :=
    ⟨y, mem_clusterBall.2 ⟨hy, by
      have : Rigidity.WeakPoincare.latticeDist y y = 0 := by
        simp [Rigidity.WeakPoincare.latticeDist]
      rw [this]; linarith⟩⟩
  have h := l2norm_heatFlowG_le_of_ball hacc hC₀ hOZ hA hHK hσ hδ1 hδ2 hδ0 hXl
    (by linarith) hρ₀ hlt hΛ hΛ
    (fun z hz => hdiag z hz _ (by linarith) (by linarith))
    (fun z hz => hdiag z hz _ (by linarith) (by linarith)) hne
  set Kc := C₀ + (10 * C₀ + 32) * A with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  -- the factor `η`
  have hη : Kc * l * (Real.sqrt Λ / Real.sqrt t +
      Real.sqrt t * Real.sqrt (8 / (σ + σ) ^ 2 * Λ)) ≤
      Kc * (1 + Real.sqrt 8) * l * Real.sqrt Λ / Real.sqrt t := by
    have h8 := sqrt_eight_div_le ht (by linarith : t ≤ σ + σ) hΛ
    have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
    have h9 : Real.sqrt t * Real.sqrt (8 / (σ + σ) ^ 2 * Λ) ≤
        Real.sqrt 8 * Real.sqrt Λ / Real.sqrt t := by
      calc _ ≤ Real.sqrt t * (Real.sqrt 8 * Real.sqrt Λ / t) :=
            mul_le_mul_of_nonneg_left h8 hst.le
        _ = Real.sqrt t * (Real.sqrt 8 * Real.sqrt Λ / (Real.sqrt t * Real.sqrt t)) := by
            rw [htt]
        _ = _ := by field_simp
    have hsum : Real.sqrt Λ / Real.sqrt t + Real.sqrt t * Real.sqrt (8 / (σ + σ) ^ 2 * Λ) ≤
        (1 + Real.sqrt 8) * Real.sqrt Λ / Real.sqrt t := by
      have : (1 + Real.sqrt 8) * Real.sqrt Λ / Real.sqrt t =
          Real.sqrt Λ / Real.sqrt t + Real.sqrt 8 * Real.sqrt Λ / Real.sqrt t := by ring
      rw [this]
      linarith
    calc _ ≤ Kc * l * ((1 + Real.sqrt 8) * Real.sqrt Λ / Real.sqrt t) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have hη0 : 0 ≤ Kc * l * (Real.sqrt Λ / Real.sqrt t +
      Real.sqrt t * Real.sqrt (8 / (σ + σ) ^ 2 * Λ)) := by positivity
  have hcard : Real.sqrt ((clusterBall K y l).card) ≤ Real.sqrt ((5 * l) ^ d) :=
    Real.sqrt_le_sqrt (card_clusterBall_le K y hl)
  have hin : Real.sqrt (∑ x ∈ clusterBall K y l, δ x ^ 2) ≤ N :=
    (Real.sqrt_le_sqrt (hδ2.sum_le_tsum _ fun x _ => sq_nonneg _)).trans hN
  have hT0 : 0 ≤ ∑' x, (if x ∈ clusterBall K y l then 0 else |δ x|) :=
    tsum_nonneg fun x => by split_ifs <;> simp
  refine h.trans (add_le_add ?_ ?_)
  · calc _ ≤ Real.sqrt ((5 * l) ^ d) * (Kc * (1 + Real.sqrt 8) * l * Real.sqrt Λ /
          Real.sqrt t) * Real.sqrt (∑ x ∈ clusterBall K y l, δ x ^ 2) := by
          gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hin (by positivity)
  · calc _ ≤ (2 + Kc * (1 + Real.sqrt 8) * l * Real.sqrt Λ / Real.sqrt t) *
          ∑' x, (if x ∈ clusterBall K y l then 0 else |δ x|) := by
          gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)

end Rigidity.Green
