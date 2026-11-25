import Rigidity.Proofs.Green.TimeSliceOscillationD
import Rigidity.Proofs.Green.HeatFlowPairing

/-!
# The heat flow of a signed measure of mass zero on the cluster of `ℤ^d`

`l2norm_heatFlowG_le_of_ball` combines the pairing bound `l2norm_heatFlowG_le_of_osc` with the
oscillation of the time slices on the balls of the cluster (`exists_nL2_heatFlowG_sub_le`): for a
summable and square summable `δ` of mass zero,

  `‖P_σ δ‖ ≤ ε (Σ_{V_l} δ²)^{1/2} + (2 + η) Σ_{x ∉ V_l} |δ(x)|`,

with `η = K l (A₁^{1/2}/R + R (8 A₂)^{1/2}/(2σ))` and `ε = |V_l|^{1/2} η`, where `V_l = 𝒞_∞ ∩ B_l(y)` and
`A₁`, `A₂` bound the diagonal of the heat kernel at the times `2σ` and `σ/2` on `B_R(y)`.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ} {ω : Configuration d}

theorem l2norm_eq_sqrt {V : Type*} (f : V → ℝ) : l2norm f = Real.sqrt (∑' x, f x ^ 2) := rfl

open Rigidity.WeakPoincare in
/-- **The heat flow of a signed measure of mass zero**, on the balls of the cluster of `ℤ^d`. -/
theorem l2norm_heatFlowG_le_of_ball [NeZero d] {K : OpenComponent ω} {y : Vertex d}
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
    {σ : ℝ} (hσ : 0 < σ) {δ : Vertex d → ℝ} (hδ1 : Summable fun x => |δ x|)
    (hδ2 : Summable fun x => δ x ^ 2) (hδ0 : ∑' x, δ x = 0)
    {l R A₁ A₂ : ℝ} (hXl : X ≤ l) (hl : 0 < l) (hρ₀ : ρ₀ ≤ 2 * l) (hlR : 2 * l ≤ R)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hdiag1 : ∀ z ∈ clusterBall K y R, vsrwHeat (openGraph ω) (2 * d) (σ + σ) z z ≤ A₁)
    (hdiag2 : ∀ z ∈ clusterBall K y R, vsrwHeat (openGraph ω) (2 * d) ((σ + σ) / 4) z z ≤ A₂)
    (hne : (clusterBall K y l).Nonempty) :
    l2norm (heatFlowG (openGraph ω) (2 * d) σ δ) ≤
      Real.sqrt ((clusterBall K y l).card) * ((C₀ + (10 * C₀ + 32) * A) * l *
          (Real.sqrt A₁ / R + R * Real.sqrt (8 / (σ + σ) ^ 2 * A₂))) *
          Real.sqrt (∑ x ∈ clusterBall K y l, δ x ^ 2) +
        (2 + (C₀ + (10 * C₀ + 32) * A) * l *
          (Real.sqrt A₁ / R + R * Real.sqrt (8 / (σ + σ) ^ 2 * A₂))) *
          ∑' x, (if x ∈ clusterBall K y l then 0 else |δ x|) := by
  have hD : 0 < 2 * d := by have := NeZero.pos d; omega
  have hdeg : ∀ z, (openGraph ω).degree z ≤ 2 * d := openGraph_degree_le ω
  set ψ := heatFlowG (openGraph ω) (2 * d) σ δ with hψdef
  have hψ2 : Summable fun w => ψ w ^ 2 := summable_sq_heatFlowG hD hdeg hσ.le hδ2
  set η := (C₀ + (10 * C₀ + 32) * A) * l *
    (Real.sqrt A₁ / R + R * Real.sqrt (8 / (σ + σ) ^ 2 * A₂)) with hη
  have hR : 0 < R := by linarith
  have hη0 : 0 ≤ η := by
    have : 0 ≤ C₀ + (10 * C₀ + 32) * A := by positivity
    positivity
  obtain ⟨c, hc⟩ := exists_nL2_heatFlowG_sub_le hacc hC₀ hOZ hA hHK hσ hψ2 hXl hl hρ₀ hlR
    hdiag1 hdiag2
  have hS : 0 ≤ ∑' w, ψ w ^ 2 := tsum_nonneg fun w => sq_nonneg _
  have hfac : Real.sqrt (A₁ * ∑' w, ψ w ^ 2) / R +
      R * Real.sqrt (8 / (σ + σ) ^ 2 * A₂ * ∑' w, ψ w ^ 2) =
      (Real.sqrt A₁ / R + R * Real.sqrt (8 / (σ + σ) ^ 2 * A₂)) * l2norm ψ := by
    rw [l2norm_eq_sqrt, Real.sqrt_mul hA₁, Real.sqrt_mul (by positivity)]
    ring
  rw [hfac, ← mul_assoc, ← hη] at hc
  set F := heatFlowG (openGraph ω) (2 * d) σ ψ with hF
  have hcard : (0 : ℝ) < (clusterBall K y l).card := by exact_mod_cast hne.card_pos
  -- the oscillation in `ℓ²` on the ball
  have hSl : Real.sqrt (∑ x ∈ clusterBall K y l, (F x - c) ^ 2) ≤
      Real.sqrt ((clusterBall K y l).card) * η * l2norm ψ := by
    have e : ∑ x ∈ clusterBall K y l, (F x - c) ^ 2 =
        (clusterBall K y l).card * nL2 (clusterBall K y l) (fun x => F x - c) ^ 2 := by
      unfold nL2
      rw [Real.sq_sqrt (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hcard.le)]
      field_simp
    rw [e, Real.sqrt_mul hcard.le, Real.sqrt_sq (nL2_nonneg _ _), mul_assoc]
    exact mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
  -- the sup bound
  have hFsup : ∀ x, |F x| ≤ l2norm ψ := by
    intro x
    have h1 := sq_heatFlowG_le_diag hD hdeg hσ.le hψ2 x
    have h2 := vsrwHeat_le_one hD hdeg (by linarith : (0 : ℝ) ≤ σ + σ) x x
    rw [← Real.sqrt_sq_eq_abs, l2norm_eq_sqrt]
    exact Real.sqrt_le_sqrt (h1.trans (mul_le_of_le_one_left hS h2))
  have hcabs : |c| ≤ (1 + η) * l2norm ψ := by
    have hc1 : nL2 (clusterBall K y l) (fun _ => c) = |c| := by
      unfold nL2
      have e : (clusterBall K y l).card • c ^ 2 / ((clusterBall K y l).card : ℝ) = c ^ 2 := by
        rw [nsmul_eq_mul]; field_simp
      rw [Finset.sum_const, e, Real.sqrt_sq_eq_abs]
    have htri := nL2_add_le (clusterBall K y l) (f := F) (g := fun x => -(F x - c))
      (k := fun _ => c) (fun x _ => by ring)
    have hneg : nL2 (clusterBall K y l) (fun x => -(F x - c)) =
        nL2 (clusterBall K y l) (fun x => F x - c) := by
      unfold nL2; simp_rw [neg_sq]
    have hFn : nL2 (clusterBall K y l) F ≤ l2norm ψ :=
      nL2_le_of_abs_le (l2norm_nonneg _) fun x _ => hFsup x
    rw [hc1, hneg] at htri
    linarith
  have hall : ∀ x, |F x - c| ≤ (2 + η) * l2norm ψ := by
    intro x
    calc |F x - c| ≤ |F x| + |c| := abs_sub _ _
      _ ≤ l2norm ψ + (1 + η) * l2norm ψ := add_le_add (hFsup x) hcabs
      _ = (2 + η) * l2norm ψ := by ring
  have h := l2norm_heatFlowG_le_of_osc hD hdeg hσ.le hδ1 hδ2 hδ0 (clusterBall K y l)
    (ε := Real.sqrt ((clusterBall K y l).card) * η) (B := 2 + η) (c := c)
    (by positivity) (by positivity) hSl hall
  convert h

end Rigidity.Green
