import Rigidity.Proofs.Green.DarioGuTwoScaleFluxDuality

/-!
# One scale of the multiscale estimate of Step 3 of Proposition 4.3 of Dario–Gu

In Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines 2370-2397 of the source), the flux is
tested against `φ = A u` with `A = (η_m - η_{m-1}) D_i D_k p̄ ψ` and `u = ψ w`, and the `H̲¹` norm
of `φ` is estimated by the product rule (the terms `I_1` and `I_2`). This file proves the
estimate for general `A` and `u`: if `‖g‖_{H̲^{-1}(V)} ≤ B`, `|V| ≤ Λ`, `|A| ≤ a`,
`|A(x + e_i) - A(x)| ≤ b` and `A u` vanishes outside `int_a(V)`, then
`-Σ_x g A u ≤ B (a ‖u‖₂ + Λ^{1/2} (4 a E(u)^{1/2} + 6 b ‖u‖₂))`
(`neg_tsum_le_of_weakNormLe_coeff`), where `E(u) = Σ_x Σ_i a_i(x) (u(x + e_i) - u(x))²` is the
energy of the open graph.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

theorem summable_edge_sq (ω : Configuration 2) {u : Vertex 2 → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    Summable fun x => ∑ i : Fin 2, openCond ω i x * (u (x + unit i) - u x) ^ 2 := by
  refine summable_sum fun i _ => ?_
  exact Summable.of_nonneg_of_le (fun x => mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _))
    (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCond_le_one ω i x))
    (summable_sq_sub (summable_sq_add_shift hu (unit i)) hu)

theorem summable_edge_sq_back (ω : Configuration 2) {u : Vertex 2 → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    Summable fun x => ∑ i : Fin 2, openCond ω i (x - unit i) * (u (x - unit i) - u x) ^ 2 := by
  refine summable_sum fun i _ => ?_
  exact Summable.of_nonneg_of_le
    (fun x => mul_nonneg (openCond_nonneg ω i _) (sq_nonneg _))
    (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCond_le_one ω i _))
    (summable_sq_sub (summable_sq_sub_shift hu (unit i)) hu)

/-- The backward edges are the forward edges. -/
theorem tsum_edge_sq_back_eq (ω : Configuration 2) {u : Vertex 2 → ℝ}
    (hu : Summable fun x => u x ^ 2) :
    ∑' x, ∑ i : Fin 2, openCond ω i (x - unit i) * (u (x - unit i) - u x) ^ 2 =
      ∑' x, ∑ i : Fin 2, openCond ω i x * (u (x + unit i) - u x) ^ 2 := by
  have hb : ∀ i : Fin 2, Summable fun x => openCond ω i (x - unit i) * (u (x - unit i) - u x) ^ 2 :=
    fun i => Summable.of_nonneg_of_le
      (fun x => mul_nonneg (openCond_nonneg ω i _) (sq_nonneg _))
      (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCond_le_one ω i _))
      (summable_sq_sub (summable_sq_sub_shift hu (unit i)) hu)
  have hf : ∀ i : Fin 2, Summable fun x => openCond ω i x * (u (x + unit i) - u x) ^ 2 :=
    fun i => Summable.of_nonneg_of_le (fun x => mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _))
      (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCond_le_one ω i x))
      (summable_sq_sub (summable_sq_add_shift hu (unit i)) hu)
  rw [Summable.tsum_finsetSum fun i _ => hb i, Summable.tsum_finsetSum fun i _ => hf i]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (Equiv.addRight (unit i)).tsum_eq
    (fun x => openCond ω i (x - unit i) * (u (x - unit i) - u x) ^ 2)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
  rw [← this]
  exact tsum_congr fun x => by ring

/-- **One scale of Step 3**: the duality with the weak norm and the product rule. -/
theorem neg_tsum_le_of_weakNormLe_coeff {ω : Configuration 2} {V : Finset (Vertex 2)}
    {g A u : Vertex 2 → ℝ} {B Λ a b : ℝ} (h : WeakNormLe ω V g B) (hB : 0 ≤ B)
    (hΛ : (V.card : ℝ) ≤ Λ) (hu : Summable fun x => u x ^ 2) (ha : ∀ x, |A x| ≤ a)
    (hb : ∀ x i, |A (x + unit i) - A x| ≤ b)
    (hsupp : ∀ x, A x * u x ≠ 0 → x ∈ V ∧ x ∈ openInterior ω V) :
    -(∑' x, g x * (A x * u x)) ≤ B * (a * Real.sqrt (∑' x, u x ^ 2) +
      Real.sqrt Λ * (4 * a * Real.sqrt (openEnergy ω u) + 6 * b * Real.sqrt (∑' x, u x ^ 2))) := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb 0 0)
  set φ : Vertex 2 → ℝ := fun x => A x * u x with hφdef
  have hφ2 : ∀ x, φ x ^ 2 ≤ a ^ 2 * u x ^ 2 := fun x => by
    have hA : A x ^ 2 ≤ a ^ 2 := by
      have := ha x
      nlinarith [abs_nonneg (A x), sq_abs (A x)]
    rw [hφdef, mul_pow]
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  have hφs : Summable fun x => φ x ^ 2 :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _) hφ2 (hu.mul_left _)
  have hU0 : 0 ≤ ∑' x, u x ^ 2 := tsum_nonneg fun x => sq_nonneg _
  have hE0 : 0 ≤ openEnergy ω u :=
    tsum_nonneg fun x => Finset.sum_nonneg fun i _ =>
      mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _)
  -- the sum is over `V`
  have hsumV : ∑' x, g x * (A x * u x) = ∑ x ∈ V, g x * φ x := by
    refine tsum_eq_sum fun x hx => ?_
    by_cases h0 : A x * u x = 0
    · rw [h0, mul_zero]
    · exact absurd (hsupp x h0).1 hx
  have hbd : ∀ x ∈ V, x ∉ openInterior ω V → φ x = 0 := by
    intro x _ hx
    by_contra h0
    exact hx (hsupp x h0).2
  have hmain := neg_sum_le_of_weakNormLe h hB hΛ hbd
  rw [hsumV]
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hB)
  -- the `L²` part
  have hL2 : Real.sqrt (∑ x ∈ V, φ x ^ 2) ≤ a * Real.sqrt (∑' x, u x ^ 2) := by
    have h1 : ∑ x ∈ V, φ x ^ 2 ≤ a ^ 2 * ∑' x, u x ^ 2 :=
      (hφs.sum_le_tsum V fun x _ => sq_nonneg _).trans
        ((Summable.tsum_le_tsum hφ2 hφs (hu.mul_left _)).trans (le_of_eq tsum_mul_left))
    calc Real.sqrt (∑ x ∈ V, φ x ^ 2) ≤ Real.sqrt (a ^ 2 * ∑' x, u x ^ 2) := Real.sqrt_le_sqrt h1
      _ = a * Real.sqrt (∑' x, u x ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha0]
  -- the gradient part
  have hedge : ∀ x (i : Fin 2), openCond ω i x * (φ (x + unit i) - φ x) ^ 2 ≤
      2 * a ^ 2 * (openCond ω i x * (u (x + unit i) - u x) ^ 2) + 2 * b ^ 2 * u x ^ 2 := by
    intro x i
    have hc0 := openCond_nonneg ω i x
    have hc1 := openCond_le_one ω i x
    have e : φ (x + unit i) - φ x =
        A (x + unit i) * (u (x + unit i) - u x) + (A (x + unit i) - A x) * u x := by
      rw [hφdef]
      ring
    have hA2 : A (x + unit i) ^ 2 ≤ a ^ 2 := by
      have := ha (x + unit i)
      nlinarith [abs_nonneg (A (x + unit i)), sq_abs (A (x + unit i))]
    have hB2 : (A (x + unit i) - A x) ^ 2 ≤ b ^ 2 := by
      have := hb x i
      nlinarith [abs_nonneg (A (x + unit i) - A x), sq_abs (A (x + unit i) - A x)]
    have hsq : (φ (x + unit i) - φ x) ^ 2 ≤
        2 * (A (x + unit i) ^ 2 * (u (x + unit i) - u x) ^ 2) +
          2 * ((A (x + unit i) - A x) ^ 2 * u x ^ 2) := by
      rw [e]
      nlinarith [sq_nonneg (A (x + unit i) * (u (x + unit i) - u x) -
        (A (x + unit i) - A x) * u x)]
    have h1 : A (x + unit i) ^ 2 * (u (x + unit i) - u x) ^ 2 ≤
        a ^ 2 * (u (x + unit i) - u x) ^ 2 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
    have h2 : (A (x + unit i) - A x) ^ 2 * u x ^ 2 ≤ b ^ 2 * u x ^ 2 :=
      mul_le_mul_of_nonneg_right hB2 (sq_nonneg _)
    have h3 : openCond ω i x * (φ (x + unit i) - φ x) ^ 2 ≤
        openCond ω i x * (2 * (a ^ 2 * (u (x + unit i) - u x) ^ 2) + 2 * (b ^ 2 * u x ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hc0
    have h4 : openCond ω i x * (2 * (b ^ 2 * u x ^ 2)) ≤ 2 * b ^ 2 * u x ^ 2 := by
      have : 0 ≤ 2 * (b ^ 2 * u x ^ 2) := by positivity
      nlinarith
    nlinarith
  have hsF := summable_edge_sq ω hφs
  have hsB := summable_edge_sq_back ω hφs
  have hsU := summable_edge_sq ω hu
  have hgrad : ∑ x ∈ V, openGradNorm ω V φ x ^ 2 ≤
      16 * a ^ 2 * openEnergy ω u + 32 * b ^ 2 * ∑' x, u x ^ 2 := by
    have h1 : ∑ x ∈ V, openGradNorm ω V φ x ^ 2 ≤ ∑ x ∈ V, 4 * ∑ i : Fin 2,
        (openCond ω i x * (φ (x + unit i) - φ x) ^ 2 +
          openCond ω i (x - unit i) * (φ (x - unit i) - φ x) ^ 2) :=
      Finset.sum_le_sum fun x _ => openGradNorm_sq_le ω V φ x
    have hs2 : Summable fun x => 4 * ∑ i : Fin 2,
        (openCond ω i x * (φ (x + unit i) - φ x) ^ 2 +
          openCond ω i (x - unit i) * (φ (x - unit i) - φ x) ^ 2) := by
      refine (hsF.add hsB).mul_left 4 |>.congr fun x => ?_
      rw [Finset.sum_add_distrib]
    have h2 := hs2.sum_le_tsum V fun x _ =>
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
        add_nonneg (mul_nonneg (openCond_nonneg ω i _) (sq_nonneg _))
          (mul_nonneg (openCond_nonneg ω i _) (sq_nonneg _)))
    have e2 : ∑' x, 4 * ∑ i : Fin 2,
        (openCond ω i x * (φ (x + unit i) - φ x) ^ 2 +
          openCond ω i (x - unit i) * (φ (x - unit i) - φ x) ^ 2) =
        8 * ∑' x, ∑ i : Fin 2, openCond ω i x * (φ (x + unit i) - φ x) ^ 2 := by
      rw [tsum_mul_left]
      simp only [Finset.sum_add_distrib]
      rw [hsF.tsum_add hsB, tsum_edge_sq_back_eq ω hφs]
      ring
    have h3 : ∑' x, ∑ i : Fin 2, openCond ω i x * (φ (x + unit i) - φ x) ^ 2 ≤
        2 * a ^ 2 * openEnergy ω u + 4 * b ^ 2 * ∑' x, u x ^ 2 := by
      have hpt : ∀ x, ∑ i : Fin 2, openCond ω i x * (φ (x + unit i) - φ x) ^ 2 ≤
          2 * a ^ 2 * ∑ i : Fin 2, openCond ω i x * (u (x + unit i) - u x) ^ 2 +
            4 * b ^ 2 * u x ^ 2 := by
        intro x
        rw [Fin.sum_univ_two, Fin.sum_univ_two]
        have := hedge x 0
        have := hedge x 1
        linarith
      have hsR : Summable fun x => 2 * a ^ 2 * ∑ i : Fin 2,
          openCond ω i x * (u (x + unit i) - u x) ^ 2 + 4 * b ^ 2 * u x ^ 2 :=
        (hsU.mul_left _).add (hu.mul_left _)
      calc ∑' x, ∑ i : Fin 2, openCond ω i x * (φ (x + unit i) - φ x) ^ 2
          ≤ ∑' x, (2 * a ^ 2 * ∑ i : Fin 2, openCond ω i x * (u (x + unit i) - u x) ^ 2 +
              4 * b ^ 2 * u x ^ 2) := Summable.tsum_le_tsum hpt hsF hsR
        _ = 2 * a ^ 2 * openEnergy ω u + 4 * b ^ 2 * ∑' x, u x ^ 2 := by
            rw [(hsU.mul_left _).tsum_add (hu.mul_left _), tsum_mul_left, tsum_mul_left]
            rfl
    calc ∑ x ∈ V, openGradNorm ω V φ x ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := e2
      _ ≤ 8 * (2 * a ^ 2 * openEnergy ω u + 4 * b ^ 2 * ∑' x, u x ^ 2) := by linarith
      _ = 16 * a ^ 2 * openEnergy ω u + 32 * b ^ 2 * ∑' x, u x ^ 2 := by ring
  have hsqrt : Real.sqrt (∑ x ∈ V, openGradNorm ω V φ x ^ 2) ≤
      4 * a * Real.sqrt (openEnergy ω u) + 6 * b * Real.sqrt (∑' x, u x ^ 2) := by
    refine (Real.sqrt_le_sqrt hgrad).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    have hsE := Real.sq_sqrt hE0
    have hsU2 := Real.sq_sqrt hU0
    have p1 : 0 ≤ Real.sqrt (openEnergy ω u) := Real.sqrt_nonneg _
    have p2 : 0 ≤ Real.sqrt (∑' x, u x ^ 2) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (mul_nonneg ha0 hb0) (mul_nonneg p1 p2)]
  have hΛs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
  have := mul_le_mul_of_nonneg_left hsqrt hΛs
  linarith

end Rigidity.Green
