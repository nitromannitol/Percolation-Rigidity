import Rigidity.Proofs.Green.DarioGuGaussianLatticeDiff

/-!
# Third differences of the planar Gaussian on the lattice

Step 3 of the proof of Proposition 4.3 of Dario–Gu (the quantity `Ξ₂` of (4.31), lines 2340-2346
of the source) uses the bound `|D³ p̄(t, x)| ≤ C t^{-5/2} exp(-|x|²/(Ct))`. On the lattice:

* `exists_thirdDiff_eq`: `D²g(n + 1) - D²g(n) = g'''(ξ)` with `ξ ∈ (n, n + 3)`;
* `abs_secondDiff_sub_le`: `|D²g(n + 1) - D²g(n)| ≤ 40 c^{-3/2} e^{9/(8c)} g_{16c}(n)`;
* `abs_fwdDiff_fwdDiff_fwdDiff_latticeGaussian_le`:
  `|D_j D_i D_k p̄(r, · - y)(x)| ≤ K r^{-5/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- `g'(n + 2) - 2 g'(n + 1) + g'(n) = g'''(ξ)` for some `ξ ∈ (n, n + 2)`. -/
theorem exists_secondDiff'_eq {c : ℝ} (hc : c ≠ 0) (n : ℝ) :
    ∃ ξ ∈ Set.Ioo n (n + 2),
      gauss1' c (n + 2) - 2 * gauss1' c (n + 1) + gauss1' c n = gauss1''' c ξ := by
  have hd : ∀ u, HasDerivAt (fun u => gauss1' c (u + 1) - gauss1' c u)
      (gauss1'' c (u + 1) - gauss1'' c u) u := fun u =>
    ((hasDerivAt_gauss1' hc (u + 1)).comp_add_const u 1).sub (hasDerivAt_gauss1' hc u)
  obtain ⟨η, hη, h⟩ := exists_hasDerivAt_eq_slope (fun u => gauss1' c (u + 1) - gauss1' c u)
    (fun u => gauss1'' c (u + 1) - gauss1'' c u) (by linarith : n < n + 1)
    (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => hd u)
  obtain ⟨ξ, hξ, h2⟩ := exists_sub_eq_gauss1''' hc (show η < η + 1 by linarith)
  refine ⟨ξ, ⟨by linarith [hη.1, hξ.1], by linarith [hη.2, hξ.2]⟩, ?_⟩
  rw [add_sub_cancel_left, one_mul] at h2
  rw [← h2, h, add_sub_cancel_left, div_one, show n + 1 + 1 = n + 2 by ring]
  ring

/-- `D²g(n + 1) - D²g(n) = g'''(ξ)` for some `ξ ∈ (n, n + 3)`. -/
theorem exists_thirdDiff_eq {c : ℝ} (hc : c ≠ 0) (n : ℝ) :
    ∃ ξ ∈ Set.Ioo n (n + 3), secondDiff c (n + 1) - secondDiff c n = gauss1''' c ξ := by
  have hd : ∀ u, HasDerivAt (fun u => secondDiff c u)
      (gauss1' c (u + 2) - 2 * gauss1' c (u + 1) + gauss1' c u) u := by
    intro u
    have h1 := (hasDerivAt_gauss1 c (u + 2)).comp_add_const u 2
    have h2 := ((hasDerivAt_gauss1 c (u + 1)).comp_add_const u 1).const_mul 2
    have h3 := hasDerivAt_gauss1 c u
    exact ((h1.sub h2).add h3).congr_deriv rfl
  obtain ⟨η, hη, h⟩ := exists_hasDerivAt_eq_slope (fun u => secondDiff c u)
    (fun u => gauss1' c (u + 2) - 2 * gauss1' c (u + 1) + gauss1' c u)
    (by linarith : n < n + 1)
    (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => hd u)
  obtain ⟨ξ, hξ, h2⟩ := exists_secondDiff'_eq hc η
  refine ⟨ξ, ⟨by linarith [hη.1, hξ.1], by linarith [hη.2, hξ.2]⟩, ?_⟩
  rw [← h2]
  rw [h, add_sub_cancel_left, div_one]

/-- The shift of the Gaussian decay by at most `3`: `g_{8c}(ζ) ≤ e^{9/(8c)} g_{16c}(n)`. -/
theorem gauss1_shift_le_three {c : ℝ} (hc : 0 < c) {n ζ : ℝ} (h : |ζ - n| ≤ 3) :
    gauss1 (8 * c) ζ ≤ Real.exp (9 / (8 * c)) * gauss1 (16 * c) n := by
  unfold gauss1
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (ζ - n) ^ 2 ≤ 9 := by
    have := abs_le.1 h
    nlinarith
  have h2 : n ^ 2 ≤ 2 * ζ ^ 2 + 18 := by nlinarith [sq_nonneg (ζ + (ζ - n))]
  have h3 : n ^ 2 / (16 * c) ≤ (2 * ζ ^ 2 + 18) / (16 * c) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have e : (2 * ζ ^ 2 + 18) / (16 * c) = ζ ^ 2 / (8 * c) + 9 / (8 * c) := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  linarith

/-- `|D²g(n + 1) - D²g(n)| ≤ 40 c^{-3/2} e^{9/(8c)} g_{16c}(n)`. -/
theorem abs_secondDiff_sub_le {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |secondDiff c (n + 1) - secondDiff c n| ≤
      40 / (c * Real.sqrt c) * (Real.exp (9 / (8 * c)) * gauss1 (16 * c) n) := by
  obtain ⟨ξ, hξ, h⟩ := exists_thirdDiff_eq hc.ne' n
  rw [h]
  refine (abs_gauss1'''_le hc ξ).trans ?_
  have hs := gauss1_shift_le_three hc (show |ξ - n| ≤ 3 by
    rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- The bound of the products of factors of the third differences. -/
theorem abs_thirdFactor_le {c : ℝ} (hc : 0 < c) (i k : Fin 2) (a b : ℝ) :
    |(gaussDiffFactor c i k 0 (a + 1) - gaussDiffFactor c i k 0 a) * gaussDiffFactor c i k 1 b| ≤
        40 / (c * Real.sqrt c) * Real.exp (9 / (8 * c)) ^ 2 *
          (gauss1 (16 * c) a * gauss1 (16 * c) b) ∧
      |gaussDiffFactor c i k 0 a * (gaussDiffFactor c i k 1 (b + 1) - gaussDiffFactor c i k 1 b)| ≤
        40 / (c * Real.sqrt c) * Real.exp (9 / (8 * c)) ^ 2 *
          (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
  set E := Real.exp (9 / (8 * c)) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hEh : Real.exp (1 / (2 * c)) ≤ E := Real.exp_le_exp.2 (by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hcs : 0 < c * Real.sqrt c := by positivity
  -- one-dimensional bounds, all with the factor `E`
  have b0 : ∀ u, |gauss1 c u| ≤ 1 * (E * gauss1 (16 * c) u) := fun u => by
    have := abs_gauss1_le_sixteen hc u
    have := gauss1_pos (16 * c) u
    nlinarith
  have b1 : ∀ u, |gauss1 c (u + 1) - gauss1 c u| ≤ 2 / Real.sqrt c * (E * gauss1 (16 * c) u) :=
    fun u => (abs_gauss1_sub_le hc u).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hEh (gauss1_pos _ _).le) (by positivity))
  have b2 : ∀ u, |secondDiff c u| ≤ 8 / c * (E * gauss1 (16 * c) u) :=
    fun u => (abs_secondDiff_le hc u).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hEh (gauss1_pos _ _).le) (by positivity))
  have b3 : ∀ u, |secondDiff c (u + 1) - secondDiff c u| ≤
      40 / (c * Real.sqrt c) * (E * gauss1 (16 * c) u) := fun u => abs_secondDiff_sub_le hc u
  have b2' : ∀ u, |(gauss1 c (u + 1 + 1) - gauss1 c (u + 1)) - (gauss1 c (u + 1) - gauss1 c u)| ≤
      8 / c * (E * gauss1 (16 * c) u) := fun u => by
    have e : (gauss1 c (u + 1 + 1) - gauss1 c (u + 1)) - (gauss1 c (u + 1) - gauss1 c u) =
        secondDiff c u := by
      rw [secondDiff, show u + 1 + 1 = u + 2 by ring]
      ring
    rw [e]
    exact b2 u
  -- the generic product bound
  have prod : ∀ (p q x z : ℝ),
      |x| ≤ p * (E * gauss1 (16 * c) a) → |z| ≤ q * (E * gauss1 (16 * c) b) → 0 ≤ p → 0 ≤ q →
      p * q ≤ 40 / (c * Real.sqrt c) → |x * z| ≤
        40 / (c * Real.sqrt c) * E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
    intro p q x z hx hz hp hq hpq
    have ga := gauss1_pos (16 * c) a
    have gb := gauss1_pos (16 * c) b
    rw [abs_mul]
    calc |x| * |z| ≤ (p * (E * gauss1 (16 * c) a)) * (q * (E * gauss1 (16 * c) b)) :=
          mul_le_mul hx hz (abs_nonneg _) (by positivity)
      _ = (p * q) * (E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b)) := by ring
      _ ≤ 40 / (c * Real.sqrt c) * (E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b)) :=
          mul_le_mul_of_nonneg_right hpq (by positivity)
      _ = 40 / (c * Real.sqrt c) * E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by ring
  have k21 : 8 / c * (2 / Real.sqrt c) ≤ 40 / (c * Real.sqrt c) := by
    rw [div_mul_div_comm]
    exact div_le_div_of_nonneg_right (by norm_num) hcs.le
  have k12 : 2 / Real.sqrt c * (8 / c) ≤ 40 / (c * Real.sqrt c) := by
    rw [mul_comm]
    exact k21
  have k30 : 40 / (c * Real.sqrt c) * 1 ≤ 40 / (c * Real.sqrt c) := by rw [mul_one]
  have k03 : 1 * (40 / (c * Real.sqrt c)) ≤ 40 / (c * Real.sqrt c) := by rw [one_mul]
  revert i k
  simp only [Fin.forall_fin_two]
  simp only [gaussDiffFactor, Fin.isValue, if_true,
    show ((0 : Fin 2) = 1) = False from by decide,
    show ((1 : Fin 2) = 0) = False from by decide, if_false]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact prod _ _ _ _ (b3 a) (b0 b) (by positivity) zero_le_one k30
  · exact prod _ _ _ _ (b2 a) (b1 b) (by positivity) (by positivity) k21
  · exact prod _ _ _ _ (b2' a) (b1 b) (by positivity) (by positivity) k21
  · exact prod _ _ _ _ (b1 a) (b2' b) (by positivity) (by positivity) k12
  · exact prod _ _ _ _ (b2' a) (b1 b) (by positivity) (by positivity) k21
  · exact prod _ _ _ _ (b1 a) (b2' b) (by positivity) (by positivity) k12
  · exact prod _ _ _ _ (b1 a) (b2 b) (by positivity) (by positivity) k12
  · exact prod _ _ _ _ (b0 a) (b3 b) zero_le_one (by positivity) k03

/-- **The third differences of the planar Gaussian**:
`|D_j D_i D_k p̄(r, · - y)(x)| ≤ K r^{-5/2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_fwdDiff_fwdDiff_fwdDiff_latticeGaussian_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ) (x y : Vertex 2) (i k j : Fin 2), 1 ≤ r →
      |fwdDiff j (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y)) x| ≤
        K / (r ^ 2 * Real.sqrt r) * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) := by
  refine ⟨(2 * Real.pi * σ)⁻¹ * (40 / (2 * σ * Real.sqrt (2 * σ))) *
    Real.exp (9 / (8 * (2 * σ))) ^ 2, by positivity, fun r x y i k j hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  have hN : 0 ≤ (2 * Real.pi * σ * r)⁻¹ := by positivity
  have hb := abs_thirdFactor_le hc i k ((x 0 : ℝ) - y 0) ((x 1 : ℝ) - y 1)
  have key : |fwdDiff j (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y)) x| ≤
      (2 * Real.pi * σ * r)⁻¹ * (40 / (2 * σ * r * Real.sqrt (2 * σ * r)) *
        Real.exp (9 / (8 * (2 * σ * r))) ^ 2 *
        (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
          gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1))) := by
    revert j
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have e : fwdDiff 0 (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y)) x =
          (2 * Real.pi * σ * r)⁻¹ *
            ((gaussDiffFactor (2 * σ * r) i k 0 ((x 0 : ℝ) - y 0 + 1) -
                gaussDiffFactor (2 * σ * r) i k 0 ((x 0 : ℝ) - y 0)) *
              gaussDiffFactor (2 * σ * r) i k 1 ((x 1 : ℝ) - y 1)) := by
        rw [show fwdDiff 0 (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y)) x =
            fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) (x + unit 0) -
              fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x from rfl,
          fwdDiff_fwdDiff_latticeGaussian_eq, fwdDiff_fwdDiff_latticeGaussian_eq,
          cast_add_unit_sub, cast_add_unit_sub]
        simp only [Fin.isValue, if_true, show ((0 : Fin 2) = 1) = False from by decide,
          if_false, add_zero]
        ring
      rw [e, abs_mul, abs_of_nonneg hN]
      exact mul_le_mul_of_nonneg_left hb.1 hN
    · have e : fwdDiff 1 (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y)) x =
          (2 * Real.pi * σ * r)⁻¹ *
            (gaussDiffFactor (2 * σ * r) i k 0 ((x 0 : ℝ) - y 0) *
              (gaussDiffFactor (2 * σ * r) i k 1 ((x 1 : ℝ) - y 1 + 1) -
                gaussDiffFactor (2 * σ * r) i k 1 ((x 1 : ℝ) - y 1))) := by
        rw [show fwdDiff 1 (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y)) x =
            fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) (x + unit 1) -
              fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x from rfl,
          fwdDiff_fwdDiff_latticeGaussian_eq, fwdDiff_fwdDiff_latticeGaussian_eq,
          cast_add_unit_sub, cast_add_unit_sub]
        simp only [Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False from by decide,
          if_false, add_zero]
        ring
      rw [e, abs_mul, abs_of_nonneg hN]
      exact mul_le_mul_of_nonneg_left hb.2 hN
  rw [← gauss16_prod_eq hσ hr0 x y]
  refine key.trans ?_
  have hE : Real.exp (9 / (8 * (2 * σ * r))) ≤ Real.exp (9 / (8 * (2 * σ))) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith))
  have hsc : Real.sqrt (2 * σ * r) = Real.sqrt (2 * σ) * Real.sqrt r :=
    Real.sqrt_mul (by positivity) r
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs2 : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.2 (by positivity)
  have hG : 0 ≤ gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
      gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1) :=
    (mul_pos (gauss1_pos _ _) (gauss1_pos _ _)).le
  calc (2 * Real.pi * σ * r)⁻¹ * (40 / (2 * σ * r * Real.sqrt (2 * σ * r)) *
        Real.exp (9 / (8 * (2 * σ * r))) ^ 2 *
        (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
          gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1)))
      ≤ (2 * Real.pi * σ * r)⁻¹ * (40 / (2 * σ * r * Real.sqrt (2 * σ * r)) *
          Real.exp (9 / (8 * (2 * σ))) ^ 2 *
          (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
            gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1))) := by
        gcongr
    _ = (2 * Real.pi * σ)⁻¹ * (40 / (2 * σ * Real.sqrt (2 * σ))) *
          Real.exp (9 / (8 * (2 * σ))) ^ 2 / (r ^ 2 * Real.sqrt r) *
          (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
            gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1)) := by
        rw [hsc]
        field_simp

end Rigidity.Green
