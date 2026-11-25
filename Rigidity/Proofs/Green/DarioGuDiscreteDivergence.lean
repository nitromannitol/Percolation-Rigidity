import Rigidity.Proofs.Green.ClusterTwoScaleTerms
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The term (3.25)-a of Dario–Gu: discrete and continuous divergence

The term (3.25)-a of the decomposition in Step 3 of the proof of Theorem 5 of Dario–Gu (lines
1503-1507 of the source) is the difference between the continuous divergence `∇·(Υ∇ū)` and its
discrete version, "a difference between a discrete derivative and a continuous derivative; it can be
estimated in terms of the third derivative of `ū`". Along the line `s ↦ x + s e_k`, with
`φ(s) = Υ(x + s e_k)` and `ψ(s) = ū(x + s e_k)`, the discrete divergence of
`timeDeriv_sub_openLaplacian_cutoffTwoScale` is `D_k(Υ D_k ū)(x) = φ(1)(ψ(2) - ψ(1)) - φ(0)(ψ(1) - ψ(0))`
and the continuous one is `∂_k(Υ ∂_k ū)(x) = φ'(0) ψ'(0) + φ(0) ψ''(0)`. This file proves
(`abs_discrete_div_sub_le`)

`|φ(1)(ψ(2) - ψ(1)) - φ(0)(ψ(1) - ψ(0)) - (φ'(0) ψ'(0) + φ(0) ψ''(0))|
  ≤ 2 (A₂ B₁ + 2 A₁ B₂ + A₀ B₃)`

when `|φ^{(i)}| ≤ A_i` and `|ψ^{(j)}| ≤ B_j` on `[0, 2]`, by the mean value inequality, and the
resulting weak norm bound of the term (`weakNormLe_term_a`, with (3.27)). The bound involves the
derivatives of `Υ` and `ū` separately (in the source: `‖∇²(Υ∇ū)‖_{L^∞}`); both are bounded by the
interior estimates of `ū` and (3.15) on the support of `Υ`.
-/

open Set

namespace Rigidity.Green

/-- `|f(1) - f(0) - f'(0)| ≤ M` when `|f''| ≤ M` on `[0, 1]`. -/
theorem abs_sub_sub_deriv_le {f f' f'' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' s) s)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, |f'' s| ≤ M) : |f 1 - f 0 - f' 0| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have h1 : ∀ s ∈ Icc (0 : ℝ) 1, |f' s - f' 0| ≤ M := by
    intro s hs
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f') (f' := f'') (C := M)
      (fun x hx => (hf' x ⟨hx.1, hx.2.trans hs.2⟩).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hM x ⟨hx.1, hx.2.le.trans hs.2⟩) s
      ⟨hs.1, le_rfl⟩
    rw [Real.norm_eq_abs, sub_zero] at this
    exact this.trans (by nlinarith [hs.1, hs.2])
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => f s - f' 0 * s)
    (f' := fun s => f' s - f' 0) (C := M) (a := 0) (b := 1)
    (fun x hx => (((hf x hx).sub ((hasDerivAt_id x).const_mul (f' 0))).congr_deriv
      (by simp)).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact h1 x ⟨hx.1, hx.2.le⟩) 1 ⟨zero_le_one, le_rfl⟩
  rw [Real.norm_eq_abs] at this
  have e : f 1 - f' 0 * 1 - (f 0 - f' 0 * 0) = f 1 - f 0 - f' 0 := by ring
  rw [e] at this
  linarith

/-- The mean value inequality on a unit interval inside `[0, 2]`. -/
theorem abs_sub_shift_le {f f' : ℝ → ℝ} {B : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 2, HasDerivAt f (f' s) s) (hB : ∀ s ∈ Icc (0 : ℝ) 2, |f' s| ≤ B)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : |f (s + 1) - f s| ≤ B := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := f') (C := B) (a := s)
    (b := s + 1)
    (fun x hx => (hf x ⟨hs.1.trans hx.1, hx.2.trans (by linarith [hs.2])⟩).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact hB x ⟨hs.1.trans hx.1, hx.2.le.trans (by linarith [hs.2])⟩) (s + 1)
    ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs] at this
  linarith

/-- **The discrete divergence along a line** (the pointwise estimate behind (3.28)):
`|φ(1)(ψ(2) - ψ(1)) - φ(0)(ψ(1) - ψ(0)) - (φ'(0) ψ'(0) + φ(0) ψ''(0))|
  ≤ 2 (A₂ B₁ + 2 A₁ B₂ + A₀ B₃)`. -/
theorem abs_discrete_div_sub_le {φ φ1 φ2 ψ ψ1 ψ2 ψ3 : ℝ → ℝ} {A0 A1 A2 B1 B2 B3 : ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 2, HasDerivAt φ (φ1 s) s)
    (hφ1 : ∀ s ∈ Icc (0 : ℝ) 2, HasDerivAt φ1 (φ2 s) s)
    (hψ : ∀ s ∈ Icc (0 : ℝ) 2, HasDerivAt ψ (ψ1 s) s)
    (hψ1 : ∀ s ∈ Icc (0 : ℝ) 2, HasDerivAt ψ1 (ψ2 s) s)
    (hψ2 : ∀ s ∈ Icc (0 : ℝ) 2, HasDerivAt ψ2 (ψ3 s) s)
    (hA0 : ∀ s ∈ Icc (0 : ℝ) 2, |φ s| ≤ A0) (hA1 : ∀ s ∈ Icc (0 : ℝ) 2, |φ1 s| ≤ A1)
    (hA2 : ∀ s ∈ Icc (0 : ℝ) 2, |φ2 s| ≤ A2) (hB1 : ∀ s ∈ Icc (0 : ℝ) 2, |ψ1 s| ≤ B1)
    (hB2 : ∀ s ∈ Icc (0 : ℝ) 2, |ψ2 s| ≤ B2) (hB3 : ∀ s ∈ Icc (0 : ℝ) 2, |ψ3 s| ≤ B3) :
    |φ 1 * (ψ 2 - ψ 1) - φ 0 * (ψ 1 - ψ 0) - (φ1 0 * ψ1 0 + φ 0 * ψ2 0)| ≤
      2 * (A2 * B1 + 2 * A1 * B2 + A0 * B3) := by
  have h02 : (0 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hA0' : 0 ≤ A0 := (abs_nonneg _).trans (hA0 0 h02)
  have hA1' : 0 ≤ A1 := (abs_nonneg _).trans (hA1 0 h02)
  have hA2' : 0 ≤ A2 := (abs_nonneg _).trans (hA2 0 h02)
  have hB1' : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0 h02)
  have hB2' : 0 ≤ B2 := (abs_nonneg _).trans (hB2 0 h02)
  have hB3' : 0 ≤ B3 := (abs_nonneg _).trans (hB3 0 h02)
  have hsub : ∀ s ∈ Icc (0 : ℝ) 1, s ∈ Icc (0 : ℝ) 2 ∧ s + 1 ∈ Icc (0 : ℝ) 2 :=
    fun s hs => ⟨⟨hs.1, by linarith [hs.2]⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  set h : ℝ → ℝ := fun s => φ s * (ψ (s + 1) - ψ s) with hh
  set h' : ℝ → ℝ := fun s => φ1 s * (ψ (s + 1) - ψ s) + φ s * (ψ1 (s + 1) - ψ1 s) with hh'
  set h'' : ℝ → ℝ := fun s => φ2 s * (ψ (s + 1) - ψ s) + 2 * φ1 s * (ψ1 (s + 1) - ψ1 s) +
    φ s * (ψ2 (s + 1) - ψ2 s) with hh''
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt h (h' s) s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hsub s hs
    exact ((hφ s h1).mul (((hψ (s + 1) h2).comp_add_const s 1).sub (hψ s h1))).congr_deriv
      (by simp only [hh', Pi.sub_apply])
  have hd' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt h' (h'' s) s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hsub s hs
    exact (((hφ1 s h1).mul (((hψ (s + 1) h2).comp_add_const s 1).sub (hψ s h1))).add
      ((hφ s h1).mul (((hψ1 (s + 1) h2).comp_add_const s 1).sub (hψ1 s h1)))).congr_deriv
      (by simp only [hh'', Pi.sub_apply]; ring_nf)
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1, |h'' s| ≤ A2 * B1 + 2 * A1 * B2 + A0 * B3 := by
    intro s hs
    obtain ⟨h1, _⟩ := hsub s hs
    have e1 := abs_sub_shift_le hψ hB1 hs
    have e2 := abs_sub_shift_le hψ1 hB2 hs
    have e3 := abs_sub_shift_le hψ2 hB3 hs
    calc |h'' s| ≤ |φ2 s * (ψ (s + 1) - ψ s)| + |2 * φ1 s * (ψ1 (s + 1) - ψ1 s)| +
          |φ s * (ψ2 (s + 1) - ψ2 s)| := abs_add_three _ _ _
      _ = |φ2 s| * |ψ (s + 1) - ψ s| + 2 * (|φ1 s| * |ψ1 (s + 1) - ψ1 s|) +
          |φ s| * |ψ2 (s + 1) - ψ2 s| := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
          ring
      _ ≤ A2 * B1 + 2 * (A1 * B2) + A0 * B3 := by
          gcongr
          · exact hA2 s h1
          · exact hA1 s h1
          · exact hA0 s h1
      _ = A2 * B1 + 2 * A1 * B2 + A0 * B3 := by ring
  have hE1 := abs_sub_sub_deriv_le hd hd' hbd
  have hψa := abs_sub_sub_deriv_le (fun s hs => hψ s (hsub s hs).1)
    (fun s hs => hψ1 s (hsub s hs).1) (fun s hs => hB2 s (hsub s hs).1)
  have hψb := abs_sub_sub_deriv_le (fun s hs => hψ1 s (hsub s hs).1)
    (fun s hs => hψ2 s (hsub s hs).1) (fun s hs => hB3 s (hsub s hs).1)
  have hE2 : |h' 0 - (φ1 0 * ψ1 0 + φ 0 * ψ2 0)| ≤ A1 * B2 + A0 * B3 := by
    have e : h' 0 - (φ1 0 * ψ1 0 + φ 0 * ψ2 0) =
        φ1 0 * (ψ 1 - ψ 0 - ψ1 0) + φ 0 * (ψ1 1 - ψ1 0 - ψ2 0) := by
      simp only [hh', zero_add]
      ring
    rw [e]
    calc |φ1 0 * (ψ 1 - ψ 0 - ψ1 0) + φ 0 * (ψ1 1 - ψ1 0 - ψ2 0)|
        ≤ |φ1 0| * |ψ 1 - ψ 0 - ψ1 0| + |φ 0| * |ψ1 1 - ψ1 0 - ψ2 0| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ A1 * B2 + A0 * B3 := by
          gcongr
          · exact hA1 0 h02
          · exact hA0 0 h02
  have e : φ 1 * (ψ 2 - ψ 1) - φ 0 * (ψ 1 - ψ 0) - (φ1 0 * ψ1 0 + φ 0 * ψ2 0) =
      (h 1 - h 0 - h' 0) + (h' 0 - (φ1 0 * ψ1 0 + φ 0 * ψ2 0)) := by
    simp only [hh, zero_add, show (1 : ℝ) + 1 = 2 by norm_num]
    ring
  rw [e]
  calc |(h 1 - h 0 - h' 0) + (h' 0 - (φ1 0 * ψ1 0 + φ 0 * ψ2 0))|
      ≤ |h 1 - h 0 - h' 0| + |h' 0 - (φ1 0 * ψ1 0 + φ 0 * ψ2 0)| := abs_add_le _ _
    _ ≤ (A2 * B1 + 2 * A1 * B2 + A0 * B3) + (A1 * B2 + A0 * B3) := add_le_add hE1 hE2
    _ ≤ 2 * (A2 * B1 + 2 * A1 * B2 + A0 * B3) := by
        nlinarith [mul_nonneg hA2' hB1', mul_nonneg hA1' hB2', mul_nonneg hA0' hB3']

/-- **The term (3.25)-a** (with (3.27)): if `|L_in - Σ_k D_k F_k| ≤ ε` on `V`, the term
`(σ/2)(L_in - Σ_k D_k F_k)` has `H̲^{-1}(V)` norm at most `|σ/2| |V|^{1/2} ε`. -/
theorem weakNormLe_term_a (ω : LatticeProb.Percolation.Configuration 2)
    (V : Finset (LatticeProb.Percolation.Vertex 2)) (σ : ℝ)
    {Lin : LatticeProb.Percolation.Vertex 2 → ℝ}
    {F : Fin 2 → LatticeProb.Percolation.Vertex 2 → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x ∈ V, |Lin x - ∑ k : Fin 2, fwdDiff k (F k) x| ≤ ε) :
    WeakNormLe ω V (fun x => σ / 2 * (Lin x - ∑ k : Fin 2, fwdDiff k (F k) x))
      (|σ / 2| * (Real.sqrt V.card * ε)) :=
  (weakNormLe_of_abs_le ω V hε h).const_mul (σ / 2)

end Rigidity.Green
