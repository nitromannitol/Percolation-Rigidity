import Rigidity.Proofs.Green.LocalNash
import Rigidity.Proofs.Green.TransientGreen
import LatticeProb.Graph.HeatVanishing
import Mathlib.Analysis.PSeries

/-!
# Off-diagonal transition bounds from Faber-Krahn inequalities on growing balls

Let `G` be an infinite connected graph with degrees at most `Δ` and `y` a vertex. Suppose that
for every `R ≥ R₀` the graph ball of radius `R` around `y` satisfies the Faber-Krahn inequality of
dimension `D` with constant `a₀ R^{-η}`. For `n ≥ max R₀ 2` and a vertex `x` within distance `n`
of `y`, write `n = a + b` with `a = ⌊n/2⌋`. The balls of radius `a` around `x` and of radius `b`
around `y` lie in the ball of radius `2n` around `y`, so the on-diagonal bound of
`LocalNash.lean` applies at both points at the scale `R = 2n`, and the Cauchy-Schwarz inequality
for the transition kernel gives

  `p_n(x, y) ≤ K n^{-(D/2)(1 - η)}`.

When `(D/2)(1 - η) > 1` the bound is summable, so the Green function with pole `y` is finite,
solves the unit-pole equation and tends to zero at infinity (`TransientGreen.lean`).
-/

open scoped Classical

namespace Rigidity.Green

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The scale computation: for `n ≤ 3m`,
`(k (2n)^{-η} m)^{-D/2} ≤ (k 2^{-η}/3)^{-D/2} n^{-(D/2)(1-η)}`. -/
theorem rpow_scale_le {k η D : ℝ} (hk : 0 < k) (hD : 0 < D) {n m : ℕ} (hn : 1 ≤ n)
    (hm : n ≤ 3 * m) :
    (k * (2 * (n : ℝ)) ^ (-η) * m) ^ (-(D / 2)) ≤
      (k / 3 * (2 : ℝ) ^ (-η)) ^ (-(D / 2)) * (n : ℝ) ^ (-(D / 2 * (1 - η))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (n : ℝ) / 3 ≤ m := by
    have : (n : ℝ) ≤ 3 * m := by exact_mod_cast hm
    linarith
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (-η) := Real.rpow_pos_of_pos (by norm_num) _
  have hnη : (0 : ℝ) < (n : ℝ) ^ (-η) := Real.rpow_pos_of_pos hnpos _
  have hsplit : (2 * (n : ℝ)) ^ (-η) = (2 : ℝ) ^ (-η) * (n : ℝ) ^ (-η) :=
    Real.mul_rpow (by norm_num) hnpos.le
  have hpow1 : (n : ℝ) ^ (-η) * n = (n : ℝ) ^ (1 - η) := by
    rw [show (1 - η) = -η + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
  set Y := k / 3 * (2 : ℝ) ^ (-η) * (n : ℝ) ^ (1 - η) with hY
  have hYpos : 0 < Y := by
    have := Real.rpow_pos_of_pos hnpos (1 - η)
    positivity
  have hYX : Y ≤ k * (2 * (n : ℝ)) ^ (-η) * m := by
    rw [hY, hsplit, ← hpow1]
    have hc : 0 ≤ k * ((2 : ℝ) ^ (-η) * (n : ℝ) ^ (-η)) := by positivity
    calc k / 3 * (2 : ℝ) ^ (-η) * ((n : ℝ) ^ (-η) * n)
        = k * ((2 : ℝ) ^ (-η) * (n : ℝ) ^ (-η)) * ((n : ℝ) / 3) := by ring
      _ ≤ k * ((2 : ℝ) ^ (-η) * (n : ℝ) ^ (-η)) * m := mul_le_mul_of_nonneg_left hm' hc
  have hmono := Real.rpow_le_rpow_of_nonpos hYpos hYX (by linarith : -(D / 2) ≤ 0)
  refine hmono.trans_eq ?_
  rw [hY, Real.mul_rpow (by positivity) (Real.rpow_nonneg hnpos.le _), ← Real.rpow_mul hnpos.le]
  congr 2
  ring

/-- **Transition bounds from Faber-Krahn inequalities on growing balls.** -/
theorem heatDominated_of_faberKrahn_balls [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {D a₀ η : ℝ} (hD : 0 < D) (ha₀ : 0 < a₀) {R₀ : ℕ} (y : V)
    (hFK : ∀ R : ℕ, R₀ ≤ R → FaberKrahnOn G {v | G.dist y v ≤ R} D (a₀ * (R : ℝ) ^ (-η))) :
    ∃ K : ℝ, HeatDominated G y (max R₀ 2) (fun n => K * (n : ℝ) ^ (-(D / 2 * (1 - η)))) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hΔpos : (0 : ℝ) < Δ := by
    have := (hdeg y).trans_le (hΔ y)
    exact_mod_cast this
  set Q := 8 * (Δ : ℝ) * (16 : ℝ) ^ (2 / D) with hQ
  have hQpos : 0 < Q := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 16) (2 / D)
    positivity
  set k := a₀ / Q * (2 / D) with hk
  have hkpos : 0 < k := by positivity
  refine ⟨Δ * (k / 3 * (2 : ℝ) ^ (-η)) ^ (-(D / 2)), ?_⟩
  intro x n hn hxn
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hnR : R₀ ≤ 2 * n := by have := le_of_max_le_left hn; omega
  set a := n / 2 with ha
  set b := n - n / 2 with hb
  have hab : a + b = n := by omega
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hna : n ≤ 3 * a := by omega
  have hnb : n ≤ 3 * b := by omega
  have hFKn := hFK (2 * n) hnR
  have haR : 0 < a₀ * ((2 * n : ℕ) : ℝ) ^ (-η) := by
    have : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
    have := Real.rpow_pos_of_pos this (-η)
    positivity
  have hBx : ∀ v, G.dist x v ≤ a → v ∈ {v | G.dist y v ≤ 2 * n} := by
    intro v hv
    have htri := hG.dist_triangle (u := y) (v := x) (w := v)
    rw [SimpleGraph.dist_comm (u := y) (v := x)] at htri
    show G.dist y v ≤ 2 * n
    omega
  have hBy : ∀ v, G.dist y v ≤ b → v ∈ {v | G.dist y v ≤ 2 * n} := by
    intro v hv
    show G.dist y v ≤ 2 * n
    omega
  have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hexpr : ∀ m : ℕ, a₀ * ((2 * n : ℕ) : ℝ) ^ (-η) / Q * (2 / D) * m =
      k * (2 * (n : ℝ)) ^ (-η) * m := by
    intro m; rw [hcast, hk]; ring
  set φ := (k / 3 * (2 : ℝ) ^ (-η)) ^ (-(D / 2)) * (n : ℝ) ^ (-(D / 2 * (1 - η))) with hφ
  have hφnn : 0 ≤ φ := by
    have h1 := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k / 3 * (2 : ℝ) ^ (-η)) (-(D / 2))
    have h2 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(D / 2 * (1 - η)))
    positivity
  have hsx : heat G (a + a) x x / (G.degree x : ℝ) ≤ φ := by
    have h := heat_even_le_of_faberKrahnOn hG hΔ hD haR hFKn x ha1 hBx
    rw [hexpr] at h
    have hdx : (0 : ℝ) < G.degree x := by exact_mod_cast hdeg x
    rw [div_le_iff₀ hdx]
    calc heat G (a + a) x x ≤ (G.degree x : ℝ) * (k * (2 * (n : ℝ)) ^ (-η) * a) ^ (-(D / 2)) := h
      _ ≤ (G.degree x : ℝ) * φ :=
          mul_le_mul_of_nonneg_left (rpow_scale_le hkpos hD (by omega) hna) hdx.le
      _ = φ * (G.degree x : ℝ) := by ring
  have hsy : heat G (b + b) y y / (G.degree y : ℝ) ≤ φ := by
    have h := heat_even_le_of_faberKrahnOn hG hΔ hD haR hFKn y hb1 hBy
    rw [hexpr] at h
    have hdy : (0 : ℝ) < G.degree y := by exact_mod_cast hdeg y
    rw [div_le_iff₀ hdy]
    calc heat G (b + b) y y ≤ (G.degree y : ℝ) * (k * (2 * (n : ℝ)) ^ (-η) * b) ^ (-(D / 2)) := h
      _ ≤ (G.degree y : ℝ) * φ :=
          mul_le_mul_of_nonneg_left (rpow_scale_le hkpos hD (by omega) hnb) hdy.le
      _ = φ * (G.degree y : ℝ) := by ring
  have hcs := heat_div_le_sqrt_two_time hG a b x y
  rw [hab] at hcs
  have hsq : Real.sqrt (heat G (a + a) x x / (G.degree x : ℝ)) *
      Real.sqrt (heat G (b + b) y y / (G.degree y : ℝ)) ≤ φ := by
    calc _ ≤ Real.sqrt φ * Real.sqrt φ :=
          mul_le_mul (Real.sqrt_le_sqrt hsx) (Real.sqrt_le_sqrt hsy) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = φ := Real.mul_self_sqrt hφnn
  have hdy : (0 : ℝ) < G.degree y := by exact_mod_cast hdeg y
  have hdyΔ : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
  have h1 : heat G n x y ≤ (G.degree y : ℝ) * φ := by
    have := hcs.trans hsq
    rw [div_le_iff₀ hdy] at this
    linarith
  calc heat G n x y ≤ (G.degree y : ℝ) * φ := h1
    _ ≤ Δ * φ := mul_le_mul_of_nonneg_right hdyΔ hφnn
    _ = Δ * (k / 3 * (2 : ℝ) ^ (-η)) ^ (-(D / 2)) * (n : ℝ) ^ (-(D / 2 * (1 - η))) := by
        rw [hφ]; ring

/-- The bound of `heatDominated_of_faberKrahn_balls` is summable when `(D/2)(1 - η) > 1`. -/
theorem summable_rpow_mul (K : ℝ) {γ : ℝ} (hγ : 1 < γ) :
    Summable (fun n : ℕ => K * (n : ℝ) ^ (-γ)) :=
  (Real.summable_nat_rpow.2 (by linarith)).mul_left K

end Rigidity.Green
