import Rigidity.Proofs.Green.HeatFlowGraph

/-!
# The algebra of the heat semigroup of a graph on square summable functions

For a locally finite graph `G` with degrees at most `D > 0`, `a, b, t ≥ 0` and square summable
`f`, `g`:

* `heatFlowG_heatFlowG`: the semigroup property `P_a (P_b f) = P_{a+b} f`;
* `tsum_heatFlowG_mul_eq`: `P_t` is symmetric, `Σ_x (P_t f)(x) g(x) = Σ_x f(x) (P_t g)(x)`;
* `tsum_heatFlowG_eq`: `P_t` preserves the mass of summable `f`, `Σ_x (P_t f)(x) = Σ_x f(x)`.

The interchanges of the sums are justified by domination (`tsum_comm_of_abs_le`).
-/

open scoped Classical
open Finset

namespace Rigidity.Green

/-- Interchange of two sums under a summable domination of the absolute values. -/
theorem tsum_comm_of_abs_le {α β : Type*} {f g : α → β → ℝ}
    (hfg : ∀ a b, |f a b| ≤ g a b) (hg : Summable (Function.uncurry g)) :
    ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b := by
  have hf : Summable (Function.uncurry f) :=
    hg.of_norm_bounded fun q => by rw [Real.norm_eq_abs]; exact hfg q.1 q.2
  exact hf.tsum_comm.symm

/-- Summability on a product from the summability of the inner and outer sums (`g ≥ 0`). -/
theorem summable_uncurry_of_nonneg {α β : Type*} {g : α → β → ℝ} (hg0 : ∀ a b, 0 ≤ g a b)
    (h1 : ∀ a, Summable (g a)) (h2 : Summable fun a => ∑' b, g a b) :
    Summable (Function.uncurry g) :=
  (summable_prod_of_nonneg (f := Function.uncurry g) fun q => hg0 q.1 q.2).2 ⟨h1, h2⟩

/-- Summability on a product from the summability of the sums in the other order (`g ≥ 0`). -/
theorem summable_uncurry_of_nonneg' {α β : Type*} {g : α → β → ℝ} (hg0 : ∀ a b, 0 ≤ g a b)
    (h1 : ∀ b, Summable fun a => g a b) (h2 : Summable fun b => ∑' a, g a b) :
    Summable (Function.uncurry g) := by
  have h := summable_uncurry_of_nonneg (g := fun b a => g a b) (fun b a => hg0 a b) h1 h2
  exact (Equiv.prodComm β α).summable_iff.1 (h.congr fun q => rfl)

theorem summable_mul_of_sq' {α : Type*} {u v : α → ℝ} (hu : Summable fun a => u a ^ 2)
    (hv : Summable fun a => v a ^ 2) : Summable fun a => u a * v a :=
  ((hu.add hv).div_const 2).of_norm_bounded fun a => by
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|u a| - |v a|), sq_abs (u a), sq_abs (v a)]

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

theorem summable_sq_abs {f : V → ℝ} (hf : Summable fun w => f w ^ 2) :
    Summable fun w => |f w| ^ 2 := by simpa [sq_abs] using hf

theorem abs_heatFlowG_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (x : V) :
    |heatFlowG G D t f x| ≤ heatFlowG G D t (fun w => |f w|) x := by
  unfold heatFlowG
  have hs := summable_vsrwHeat_mul_l2 hD hdeg ht (summable_sq_abs hf) x
  have hn : Summable fun w => ‖vsrwHeat G D t x w * f w‖ := hs.congr fun w => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg ht x w)]
  calc |∑' w, vsrwHeat G D t x w * f w| = ‖∑' w, vsrwHeat G D t x w * f w‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' w, ‖vsrwHeat G D t x w * f w‖ := norm_tsum_le_tsum_norm hn
    _ = ∑' w, vsrwHeat G D t x w * |f w| := tsum_congr fun w => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg ht x w)]

theorem heatFlowG_nonneg (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf0 : ∀ w, 0 ≤ f w) (x : V) : 0 ≤ heatFlowG G D t f x :=
  tsum_nonneg fun w => mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w) (hf0 w)

/-- **The semigroup property** `P_a (P_b f) = P_{a+b} f` on `ℓ²`. -/
theorem heatFlowG_heatFlowG (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) {f : V → ℝ} (hf : Summable fun w => f w ^ 2) (x : V) :
    heatFlowG G D a (heatFlowG G D b f) x = heatFlowG G D (a + b) f x := by
  have hfa := summable_sq_abs hf
  have hPb := (hasSum_sq_heatFlowG_le hD hdeg hb hfa).1
  have hpa : Summable fun w => vsrwHeat G D a x w ^ 2 := by
    have := hasSum_heatDeriv_sq hD hdeg 0 ha x
    exact this.summable
  unfold heatFlowG
  have e1 : ∀ w, vsrwHeat G D a x w * ∑' u, vsrwHeat G D b w u * f u =
      ∑' u, vsrwHeat G D a x w * (vsrwHeat G D b w u * f u) := fun w => (tsum_mul_left).symm
  simp_rw [e1]
  rw [tsum_comm_of_abs_le (g := fun w u => vsrwHeat G D a x w * (vsrwHeat G D b w u * |f u|))
    (fun w u => by
      rw [abs_mul, abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg ha x w),
        abs_of_nonneg (vsrwHeat_nonneg hD hdeg hb w u)])
    (summable_uncurry_of_nonneg (fun w u => mul_nonneg (vsrwHeat_nonneg hD hdeg ha x w)
      (mul_nonneg (vsrwHeat_nonneg hD hdeg hb w u) (abs_nonneg _)))
      (fun w => (summable_vsrwHeat_mul_l2 hD hdeg hb hfa w).mul_left _)
      (by
        have h := summable_mul_of_sq' hpa hPb
        refine h.congr fun w => ?_
        rw [tsum_mul_left]
        rfl))]
  refine tsum_congr fun u => ?_
  have e2 : (fun w => vsrwHeat G D a x w * (vsrwHeat G D b w u * f u)) =
      fun w => vsrwHeat G D a x w * vsrwHeat G D b w u * f u := funext fun w => by ring
  rw [e2, tsum_mul_right, (hasSum_vsrwHeat_mul hD hdeg ha hb x u).tsum_eq]

/-- **Symmetry**: `Σ_x (P_t f)(x) g(x) = Σ_x f(x) (P_t g)(x)` on `ℓ²`. -/
theorem tsum_heatFlowG_mul_eq (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f g : V → ℝ} (hf : Summable fun w => f w ^ 2) (hg : Summable fun w => g w ^ 2) :
    ∑' x, heatFlowG G D t f x * g x = ∑' x, f x * heatFlowG G D t g x := by
  have hfa := summable_sq_abs hf
  have hPf := (hasSum_sq_heatFlowG_le hD hdeg ht hfa).1
  unfold heatFlowG
  have e1 : ∀ x, (∑' w, vsrwHeat G D t x w * f w) * g x =
      ∑' w, vsrwHeat G D t x w * f w * g x := fun x => (tsum_mul_right).symm
  simp_rw [e1]
  rw [tsum_comm_of_abs_le (g := fun x w => vsrwHeat G D t x w * |f w| * |g x|)
    (fun x w => by
      rw [abs_mul, abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg ht x w)])
    (summable_uncurry_of_nonneg (fun x w => mul_nonneg (mul_nonneg
      (vsrwHeat_nonneg hD hdeg ht x w) (abs_nonneg _)) (abs_nonneg _))
      (fun x => (summable_vsrwHeat_mul_l2 hD hdeg ht hfa x).mul_right _)
      (by
        have h := summable_mul_of_sq' hPf (summable_sq_abs hg)
        refine h.congr fun x => ?_
        rw [tsum_mul_right]
        rfl))]
  refine tsum_congr fun w => ?_
  have e2 : (fun x => vsrwHeat G D t x w * f w * g x) =
      fun x => f w * (vsrwHeat G D t w x * g x) := funext fun x => by
    rw [vsrwHeat_symm hD hdeg t x w]; ring
  rw [e2, tsum_mul_left]

/-- **Conservation of mass**: `Σ_x (P_t f)(x) = Σ_x f(x)` for summable, square summable `f`. -/
theorem tsum_heatFlowG_eq (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    {f : V → ℝ} (hf1 : Summable fun w => |f w|) :
    ∑' x, heatFlowG G D t f x = ∑' w, f w := by
  unfold heatFlowG
  rw [tsum_comm_of_abs_le (g := fun x w => vsrwHeat G D t x w * |f w|)
    (fun x w => by rw [abs_mul, abs_of_nonneg (vsrwHeat_nonneg hD hdeg ht x w)])
    (summable_uncurry_of_nonneg' (fun x w => mul_nonneg (vsrwHeat_nonneg hD hdeg ht x w)
      (abs_nonneg _))
      (fun w => by
        have h := ((hasSum_vsrwHeat hD hdeg ht w).summable).mul_right |f w|
        refine h.congr fun x => ?_
        rw [vsrwHeat_symm hD hdeg t w x])
      (by
        refine hf1.congr fun w => ?_
        rw [tsum_mul_right]
        have h := hasSum_vsrwHeat hD hdeg ht w
        rw [show (∑' x, vsrwHeat G D t x w) = ∑' x, vsrwHeat G D t w x from
          tsum_congr fun x => vsrwHeat_symm hD hdeg t x w, h.tsum_eq, one_mul]))]
  refine tsum_congr fun w => ?_
  rw [tsum_mul_right]
  rw [show (∑' x, vsrwHeat G D t x w) = ∑' x, vsrwHeat G D t w x from
    tsum_congr fun x => vsrwHeat_symm hD hdeg t x w, (hasSum_vsrwHeat hD hdeg ht w).tsum_eq,
    one_mul]

end Rigidity.Green
