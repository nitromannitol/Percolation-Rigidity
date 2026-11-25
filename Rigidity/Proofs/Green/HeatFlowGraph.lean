import Rigidity.Proofs.Green.HarmonicReplacement

/-!
# The heat semigroup of a graph of bounded degree on square summable functions

For a locally finite graph `G` with degrees at most `D > 0` and its heat kernel `p_t = vsrwHeat G D t`
(the variable speed random walk), `heatFlowG G D t f (x) = Σ_w p_t(x, w) f(w)`. For `t ≥ 0` and square
summable `f`:

* `sq_heatFlowG_le`: `(P_t f)(x)² ≤ Σ_w p_t(x, w) f(w)²` (Jensen's inequality, as `Σ_w p_t(x, w) = 1`);
* `hasSum_sq_heatFlowG_le`: `P_t` is a contraction of `ℓ²`;
* `sq_heatFlowG_le_diag`: `(P_t f)(z)² ≤ p_{2t}(z, z) ‖f‖²`;
* `laplacian_heatFlowG` and `sq_laplacian_heatFlowG_le`: `Δ(P_t f)(z) = Σ_w ∂_t p_t(z, w) f(w)` and
  `(Δ P_t f)(z)² ≤ 8 (2t)^{-2} p_{t/2}(z, z) ‖f‖²` (from `heatDeriv_two_le`).

These are the bounds `|P_σ φ| ≤ C t^{-d/4}` and `|Δ P_σ φ| ≤ C t^{-d/4-1}` of the elliptic estimate (2)
for the time slices of the heat semigroup, written with the diagonal of the heat kernel.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

variable (G D) in
/-- `P_t f(x) = Σ_w p_t(x, w) f(w)`. -/
noncomputable def heatFlowG (t : ℝ) (f : V → ℝ) (x : V) : ℝ :=
  ∑' w, vsrwHeat G D t x w * f w

theorem summable_vsrwHeat_mul_sq (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (x : V) :
    Summable fun w => vsrwHeat G D t x w * f w ^ 2 :=
  hf.of_nonneg_of_le (fun w => mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w) (sq_nonneg _))
    (fun w => mul_le_of_le_one_left (sq_nonneg _) (vsrwHeat_le_one hD hdeg ht x w))

theorem summable_vsrwHeat_mul_l2 (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (x : V) :
    Summable fun w => vsrwHeat G D t x w * f w := by
  have h1 := (hasSum_vsrwHeat hD hdeg ht x).summable
  have h2 := summable_vsrwHeat_mul_sq hD hdeg ht hf x
  refine ((h1.add h2).div_const 2).of_norm_bounded (fun w => ?_)
  rw [Real.norm_eq_abs]
  have hp := vsrwHeat_nonneg hD hdeg ht x w
  rw [abs_mul, abs_of_nonneg hp]
  nlinarith [sq_nonneg (|f w| - 1), abs_nonneg (f w), sq_abs (f w)]

/-- **Jensen's inequality**: `(P_t f)(x)² ≤ Σ_w p_t(x, w) f(w)²`. -/
theorem sq_heatFlowG_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (x : V) :
    heatFlowG G D t f x ^ 2 ≤ ∑' w, vsrwHeat G D t x w * f w ^ 2 := by
  set c := heatFlowG G D t f x with hc
  have h1 := hasSum_vsrwHeat hD hdeg ht x
  have h2 := (summable_vsrwHeat_mul_l2 hD hdeg ht hf x).hasSum
  have h3 := (summable_vsrwHeat_mul_sq hD hdeg ht hf x).hasSum
  have e : (fun w => vsrwHeat G D t x w * (f w - c) ^ 2) = fun w =>
      vsrwHeat G D t x w * f w ^ 2 - 2 * c * (vsrwHeat G D t x w * f w) +
        c ^ 2 * vsrwHeat G D t x w := funext fun w => by ring
  have h4 : HasSum (fun w => vsrwHeat G D t x w * (f w - c) ^ 2)
      ((∑' w, vsrwHeat G D t x w * f w ^ 2) - 2 * c * c + c ^ 2 * 1) := by
    rw [e]
    exact (h3.sub (h2.mul_left (2 * c))).add (h1.mul_left (c ^ 2))
  have h5 := h4.nonneg fun w => mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w) (sq_nonneg _)
  nlinarith

/-- **`P_t` is a contraction of `ℓ²`**: `Σ_x (P_t f)(x)² ≤ Σ_w f(w)²`. -/
theorem hasSum_sq_heatFlowG_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) :
    Summable (fun x => heatFlowG G D t f x ^ 2) ∧
      ∑' x, heatFlowG G D t f x ^ 2 ≤ ∑' w, f w ^ 2 := by
  -- the double sum `Σ_x Σ_w p_t(x, w) f(w)² = Σ_w f(w)²`
  have hswap : HasSum (fun x => ∑' w, vsrwHeat G D t x w * f w ^ 2) (∑' w, f w ^ 2) := by
    refine hasSum_of_tsum_ofReal_eq (fun x => tsum_nonneg fun w =>
      mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w) (sq_nonneg _))
      (tsum_nonneg fun w => sq_nonneg _) ?_
    have h1 : ∀ x, ENNReal.ofReal (∑' w, vsrwHeat G D t x w * f w ^ 2) =
        ∑' w, ENNReal.ofReal (vsrwHeat G D t x w * f w ^ 2) := fun x =>
      ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w)
        (sq_nonneg _)) (summable_vsrwHeat_mul_sq hD hdeg ht hf x)
    simp_rw [h1]
    rw [ENNReal.tsum_comm, ENNReal.ofReal_tsum_of_nonneg (fun w => sq_nonneg _) hf]
    refine tsum_congr fun w => ?_
    have h2 : ∀ x, ENNReal.ofReal (vsrwHeat G D t x w * f w ^ 2) =
        ENNReal.ofReal (vsrwHeat G D t w x) * ENNReal.ofReal (f w ^ 2) := fun x => by
      rw [vsrwHeat_symm hD hdeg t x w, ENNReal.ofReal_mul (vsrwHeat_nonneg hD hdeg ht w x)]
    simp_rw [h2]
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
      (fun x => vsrwHeat_nonneg hD hdeg ht w x) (hasSum_vsrwHeat hD hdeg ht w).summable,
      (hasSum_vsrwHeat hD hdeg ht w).tsum_eq, ENNReal.ofReal_one, one_mul]
  have hle : ∀ x, heatFlowG G D t f x ^ 2 ≤ ∑' w, vsrwHeat G D t x w * f w ^ 2 :=
    sq_heatFlowG_le hD hdeg ht hf
  have hs : Summable (fun x => heatFlowG G D t f x ^ 2) :=
    hswap.summable.of_nonneg_of_le (fun x => sq_nonneg _) hle
  exact ⟨hs, (hs.tsum_le_tsum hle hswap.summable).trans_eq hswap.tsum_eq⟩

/-- `(P_t f)(z)² ≤ p_{2t}(z, z) Σ_w f(w)²`. -/
theorem sq_heatFlowG_le_diag (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (z : V) :
    heatFlowG G D t f z ^ 2 ≤ vsrwHeat G D (t + t) z z * ∑' w, f w ^ 2 := by
  have hA : HasSum (fun w => heatDeriv G D 0 t z w ^ 2) (heatDeriv G D (0 + 0) (t + t) z z) :=
    hasSum_heatDeriv_sq hD hdeg 0 ht z
  have hP : HasSum (fun w => heatDeriv G D 0 t z w * f w) (heatFlowG G D t f z) :=
    (summable_vsrwHeat_mul_l2 hD hdeg ht hf z).hasSum
  exact sq_le_mul_of_hasSum hP hA hf.hasSum

/-- `Δ(P_t f)(z) = Σ_w ∂_t p_t(z, w) f(w)`. -/
theorem laplacian_heatFlowG (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (z : V) :
    HasSum (fun w => heatDeriv G D 1 t z w * f w)
      (LatticeProb.Graph.laplacian G (heatFlowG G D t f) z) := by
  unfold LatticeProb.Graph.laplacian heatFlowG
  have hfun : (fun w => heatDeriv G D 1 t z w * f w) = fun w =>
      ∑ z' ∈ G.neighborFinset z, (vsrwHeat G D t z' w * f w - vsrwHeat G D t z w * f w) := by
    funext w
    rw [heatDeriv_succ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z' _ => by rw [heatDeriv_zero, heatDeriv_zero]; ring
  rw [hfun]
  exact hasSum_sum fun z' _ =>
    (summable_vsrwHeat_mul_l2 hD hdeg ht hf z').hasSum.sub (summable_vsrwHeat_mul_l2 hD hdeg ht hf z).hasSum

/-- `(Δ P_t f)(z)² ≤ 8 (2t)^{-2} p_{t/2}(z, z) Σ_w f(w)²` for `t > 0`. -/
theorem sq_laplacian_heatFlowG_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 < t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (z : V) :
    LatticeProb.Graph.laplacian G (heatFlowG G D t f) z ^ 2 ≤
      8 / (t + t) ^ 2 * vsrwHeat G D ((t + t) / 4) z z * ∑' w, f w ^ 2 := by
  have hA : HasSum (fun w => heatDeriv G D 1 t z w ^ 2) (heatDeriv G D (1 + 1) (t + t) z z) :=
    hasSum_heatDeriv_sq hD hdeg 1 ht.le z
  have hcs := sq_le_mul_of_hasSum (laplacian_heatFlowG hD hdeg ht.le hf z) hA hf.hasSum
  have h2 := heatDeriv_two_le hD hdeg (by linarith : 0 < t + t) z
  have hs : 0 ≤ ∑' w, f w ^ 2 := tsum_nonneg fun w => sq_nonneg (f w)
  calc _ ≤ heatDeriv G D (1 + 1) (t + t) z z * ∑' w, f w ^ 2 := hcs
    _ ≤ 8 / (t + t) ^ 2 * vsrwHeat G D ((t + t) / 4) z z * ∑' w, f w ^ 2 :=
        mul_le_mul_of_nonneg_right h2 hs

end Rigidity.Green
