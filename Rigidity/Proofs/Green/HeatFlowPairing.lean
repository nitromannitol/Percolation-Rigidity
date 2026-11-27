import Rigidity.Proofs.Green.HeatFlowTelescope

/-!
# The heat flow of a signed measure of mass zero

For a locally finite graph `G` with degrees at most `D > 0`, a summable and square summable `δ`
with `Σ_x δ(x) = 0`, `σ ≥ 0` and `ψ = P_σ δ`,

  `‖ψ‖² = Σ_x δ(x) (P_σ ψ)(x) = Σ_x δ(x) ((P_σ ψ)(x) - c)`

for every constant `c` (symmetry and the semigroup property). If `P_σ ψ` oscillates by at most
`ε ‖ψ‖` in `ℓ²` on a finite set `S` around `c`, and by at most `B ‖ψ‖` everywhere, then

  `‖P_σ δ‖ ≤ ε (Σ_{x ∈ S} δ(x)²)^{1/2} + B Σ_{x ∉ S} |δ(x)|`

(`l2norm_heatFlowG_le_of_osc`). This is the pairing of the differences `D_s` of the normalized
Gaussian kernels with the time slices `P_σ φ` in the passage from smooth initial data to a point
source in the proof of Theorem 2 of Dario–Gu given here.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

/-- Splitting a sum into a finite set and its complement. -/
theorem tsum_eq_sum_add_tsum_ite {f : V → ℝ} (hf : Summable f) (S : Finset V) :
    ∑' x, f x = ∑ x ∈ S, f x + ∑' x, (if x ∈ S then 0 else f x) := by
  have h1 : Summable fun x => if x ∈ S then f x else 0 :=
    summable_of_ne_finset_zero (s := S) fun x hx => if_neg hx
  have h2 : Summable fun x => if x ∈ S then 0 else f x :=
    (hf.sub h1).congr fun x => by split_ifs <;> simp
  have e1 : ∑' x, f x = ∑' x, ((if x ∈ S then f x else 0) + (if x ∈ S then 0 else f x)) :=
    tsum_congr fun x => by split_ifs <;> simp
  rw [e1, h1.tsum_add h2, tsum_eq_sum (s := S) fun x hx => if_neg hx]
  congr 1
  exact Finset.sum_congr rfl fun x hx => if_pos hx

/-- **The heat flow of a signed measure of mass zero.** -/
theorem l2norm_heatFlowG_le_of_osc (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {σ : ℝ}
    (hσ : 0 ≤ σ) {δ : V → ℝ} (hδ1 : Summable fun x => |δ x|) (hδ2 : Summable fun x => δ x ^ 2)
    (hδ0 : ∑' x, δ x = 0) (S : Finset V) {ε B c : ℝ} (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (hS : Real.sqrt (∑ x ∈ S, (heatFlowG G D σ (heatFlowG G D σ δ) x - c) ^ 2) ≤
      ε * l2norm (heatFlowG G D σ δ))
    (hall : ∀ x, |heatFlowG G D σ (heatFlowG G D σ δ) x - c| ≤ B * l2norm (heatFlowG G D σ δ)) :
    l2norm (heatFlowG G D σ δ) ≤
      ε * Real.sqrt (∑ x ∈ S, δ x ^ 2) + B * ∑' x, (if x ∈ S then 0 else |δ x|) := by
  set ψ := heatFlowG G D σ δ with hψ
  set F := heatFlowG G D σ ψ with hF
  have hψ2 : Summable fun x => ψ x ^ 2 := summable_sq_heatFlowG hD hdeg hσ hδ2
  have hn0 := l2norm_nonneg ψ
  -- `‖ψ‖² = Σ δ (F - c)`
  have hpair : l2norm ψ ^ 2 = ∑' x, δ x * (F x - c) := by
    rw [sq_l2norm]
    have h1 : ∑' x, ψ x ^ 2 = ∑' x, ψ x * ψ x := tsum_congr fun x => sq _
    have h2 := tsum_heatFlowG_mul_eq hD hdeg hσ hδ2 hψ2
    have hδc : Summable fun x => δ x * c := (hδ1.of_norm_bounded fun x => by
      rw [Real.norm_eq_abs]).mul_right c
    have hδF : Summable fun x => δ x * F x :=
      summable_mul_of_sq' hδ2 (summable_sq_heatFlowG hD hdeg hσ hψ2)
    rw [h1, h2, show (∑' x, δ x * (F x - c)) = ∑' x, (δ x * F x - δ x * c) from
      tsum_congr fun x => by ring, hδF.tsum_sub hδc, tsum_mul_right, hδ0, zero_mul, sub_zero]
  -- splitting at `S`
  have hsum1 : Summable fun x => δ x * (F x - c) := by
    have hδF : Summable fun x => δ x * F x :=
      summable_mul_of_sq' hδ2 (summable_sq_heatFlowG hD hdeg hσ hψ2)
    have hδc : Summable fun x => δ x * c := (hδ1.of_norm_bounded fun x => by
      rw [Real.norm_eq_abs]).mul_right c
    exact (hδF.sub hδc).congr fun x => by ring
  have hsplit := tsum_eq_sum_add_tsum_ite hsum1 S
  have hin : ∑ x ∈ S, δ x * (F x - c) ≤ Real.sqrt (∑ x ∈ S, δ x ^ 2) * (ε * l2norm ψ) := by
    calc ∑ x ∈ S, δ x * (F x - c) ≤ Real.sqrt (∑ x ∈ S, δ x ^ 2) *
          Real.sqrt (∑ x ∈ S, (F x - c) ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt S _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _)
  have hout : ∑' x, (if x ∈ S then 0 else δ x * (F x - c)) ≤
      (∑' x, (if x ∈ S then 0 else |δ x|)) * (B * l2norm ψ) := by
    have hT : Summable fun x => if x ∈ S then (0 : ℝ) else |δ x| :=
      hδ1.of_nonneg_of_le (fun x => by split_ifs <;> simp) (fun x => by split_ifs <;> simp)
    rw [← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun x => ?_) ?_ (hT.mul_right _)
    · split_ifs
      · simp
      · calc δ x * (F x - c) ≤ |δ x * (F x - c)| := le_abs_self _
          _ = |δ x| * |F x - c| := abs_mul _ _
          _ ≤ |δ x| * (B * l2norm ψ) := mul_le_mul_of_nonneg_left (hall x) (abs_nonneg _)
    · exact Summable.of_norm_bounded (g := fun x => |δ x * (F x - c)|) hsum1.abs fun x => by
        rw [Real.norm_eq_abs]
        split_ifs
        · simp only [abs_zero]; exact abs_nonneg _
        · exact le_rfl
  have hmain : l2norm ψ ^ 2 ≤ (ε * Real.sqrt (∑ x ∈ S, δ x ^ 2) +
      B * ∑' x, (if x ∈ S then 0 else |δ x|)) * l2norm ψ := by
    rw [hpair, hsplit]
    nlinarith [hin, hout]
  rcases eq_or_lt_of_le hn0 with h0 | hpos
  · rw [← h0]
    have := Real.sqrt_nonneg (∑ x ∈ S, δ x ^ 2)
    have : 0 ≤ ∑' x, (if x ∈ S then (0 : ℝ) else |δ x|) :=
      tsum_nonneg fun x => by split_ifs <;> simp
    positivity
  · rw [sq] at hmain
    exact le_of_mul_le_mul_right hmain hpos

end Rigidity.Green
