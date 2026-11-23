import Rigidity.Proofs.Green.DarioGuGaussianLattice

/-!
# Second differences and time derivative differences of the planar Gaussian on the lattice

Step 4 of the proof of Proposition 4.3 of Dario–Gu (lines 2416-2446 of the source) bounds the
terms `f` and `F` of (4.26) by the derivative bounds of the heat kernel `p̄`. On the lattice, with
`P = p̄(r, · - y)`, `r ≥ 1` and `Φ(x) = exp(-|x - y|²/(32σr))`:

* `abs_fwdDiff_fwdDiff_latticeGaussian_le`: `|D_i D_k P(x)| ≤ K r^{-2} Φ(x)`;
* `abs_fwdDiff_latticeGaussianTimeDeriv_le`: `|D_k ∂_r P(x)| ≤ K r^{-5/2} Φ(x)`.

Both follow from the product structure `P = (2πσr)^{-1} g(u₀) g(u₁)` (`latticeGaussian_eq_prod`)
and the one-dimensional bounds of the first and second differences of `g = gauss1 (2σr)`
(`abs_gauss1_sub_le`, `abs_secondDiff_le`, `abs_gauss1''_sub_le`).
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- `|g(n + 1) - g(n)| ≤ 2 c^{-1/2} e^{1/(2c)} g_{16c}(n)`. -/
theorem abs_gauss1_sub_le {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |gauss1 c (n + 1) - gauss1 c n| ≤
      2 / Real.sqrt c * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eq_gauss1' c n
  rw [h]
  refine (abs_gauss1'_le hc ξ).trans ?_
  have hs := gauss1_shift_le hc (show |ξ - n| ≤ 2 by
    rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- `|g(n + 2) - 2 g(n + 1) + g(n)| ≤ 8 c^{-1} e^{1/(2c)} g_{16c}(n)`. -/
theorem abs_secondDiff_le {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |secondDiff c n| ≤ 8 / c * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by
  obtain ⟨ξ, hξ, h⟩ := exists_secondDiff_eq hc.ne' n
  rw [secondDiff, h]
  refine (abs_gauss1''_le hc ξ).trans ?_
  have hs := gauss1_shift_le hc (show |ξ - n| ≤ 2 by
    rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2])
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- `|g''(n + 1) - g''(n)| ≤ 40 c^{-3/2} e^{1/(2c)} g_{16c}(n)`. -/
theorem abs_gauss1''_sub_le {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |gauss1'' c (n + 1) - gauss1'' c n| ≤
      40 / (c * Real.sqrt c) * (Real.exp (1 / (2 * c)) * gauss1 (16 * c) n) := by
  obtain ⟨ζ, hζ, h⟩ := exists_sub_eq_gauss1''' hc.ne' (show n < n + 1 by linarith)
  rw [h, add_sub_cancel_left, one_mul]
  refine (abs_gauss1'''_le hc ζ).trans ?_
  have hs := gauss1_shift_le hc (show |ζ - n| ≤ 2 by
    rw [abs_le]; constructor <;> linarith [hζ.1, hζ.2])
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- `|g''(n)| ≤ 8 c^{-1} g_{16c}(n)`. -/
theorem abs_gauss1''_le_sixteen {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |gauss1'' c n| ≤ 8 / c * gauss1 (16 * c) n :=
  (abs_gauss1''_le hc n).trans (mul_le_mul_of_nonneg_left
    (gauss1_mono (by positivity) (by linarith) n) (by positivity))

/-- `|g(n)| ≤ g_{16c}(n)`. -/
theorem abs_gauss1_le_sixteen {c : ℝ} (hc : 0 < c) (n : ℝ) :
    |gauss1 c n| ≤ gauss1 (16 * c) n := by
  rw [abs_of_pos (gauss1_pos c n)]
  exact gauss1_mono hc (by linarith) n

/-- `g_{32σr}(u₀) g_{32σr}(u₁) = exp(-|x - y|²/(32σr))`. -/
theorem gauss16_prod_eq {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (x y : Vertex 2) :
    gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) * gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1) =
      Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hr0 : r ≠ 0 := hr.ne'
  unfold gauss1
  rw [← Real.exp_add, latticeDist_sq]
  congr 1
  field_simp
  ring

/-- The factor of `D_i D_k p̄` in the coordinate `m`: the second difference of `g` if
`i = k = m`, the first difference if exactly one of `i`, `k` is `m`, and `g` otherwise. -/
noncomputable def gaussDiffFactor (c : ℝ) (i k m : Fin 2) (u : ℝ) : ℝ :=
  if i = m then (if k = m then secondDiff c u else gauss1 c (u + 1) - gauss1 c u)
  else (if k = m then gauss1 c (u + 1) - gauss1 c u else gauss1 c u)

/-- **The second differences of the planar Gaussian** in product form. -/
theorem fwdDiff_fwdDiff_latticeGaussian_eq (σ r : ℝ) (x y : Vertex 2) (i k : Fin 2) :
    fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x = (2 * Real.pi * σ * r)⁻¹ *
      (gaussDiffFactor (2 * σ * r) i k 0 ((x 0 : ℝ) - y 0) *
        gaussDiffFactor (2 * σ * r) i k 1 ((x 1 : ℝ) - y 1)) := by
  revert i k
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
  · simp only [fwdDiff, latticeGaussian_eq_prod, cast_add_unit_sub, gaussDiffFactor, secondDiff]
    simp only [Fin.isValue, if_true, show ((0 : Fin 2) = 1) = False from by decide,
      show ((1 : Fin 2) = 0) = False from by decide, if_false, add_zero]
    try simp only [add_assoc, one_add_one_eq_two]
    ring

/-- The bound of the product of the two factors of `D_i D_k p̄`. -/
theorem abs_gaussDiffFactor_mul_le {c : ℝ} (hc : 0 < c) (i k : Fin 2) (a b : ℝ) :
    |gaussDiffFactor c i k 0 a * gaussDiffFactor c i k 1 b| ≤
      8 / c * Real.exp (1 / (2 * c)) ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
  set E := Real.exp (1 / (2 * c)) with hEdef
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hEE : E ≤ E ^ 2 := by nlinarith
  have ga := gauss1_pos (16 * c) a
  have gb := gauss1_pos (16 * c) b
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq : 2 / Real.sqrt c * (2 / Real.sqrt c) = 4 / c := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hc.le]
    ring
  -- the mixed case
  have hmix : |(gauss1 c (a + 1) - gauss1 c a) * (gauss1 c (b + 1) - gauss1 c b)| ≤
      8 / c * E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
    rw [abs_mul]
    have h1 := abs_gauss1_sub_le hc a
    have h2 := abs_gauss1_sub_le hc b
    calc |gauss1 c (a + 1) - gauss1 c a| * |gauss1 c (b + 1) - gauss1 c b|
        ≤ (2 / Real.sqrt c * (E * gauss1 (16 * c) a)) *
            (2 / Real.sqrt c * (E * gauss1 (16 * c) b)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 4 / c * E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
          rw [← hsq]
          ring
      _ ≤ 8 / c * E ^ 2 * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
          gcongr
          norm_num
  -- the pure cases
  have hpure : ∀ u v : ℝ, |secondDiff c u * gauss1 c v| ≤
      8 / c * E ^ 2 * (gauss1 (16 * c) u * gauss1 (16 * c) v) := by
    intro u v
    rw [abs_mul]
    have h1 := abs_secondDiff_le hc u
    have h2 := abs_gauss1_le_sixteen hc v
    have gu := gauss1_pos (16 * c) u
    have gv := gauss1_pos (16 * c) v
    calc |secondDiff c u| * |gauss1 c v|
        ≤ (8 / c * (E * gauss1 (16 * c) u)) * gauss1 (16 * c) v :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 8 / c * (gauss1 (16 * c) u * gauss1 (16 * c) v) * E := by ring
      _ ≤ 8 / c * (gauss1 (16 * c) u * gauss1 (16 * c) v) * E ^ 2 :=
          mul_le_mul_of_nonneg_left hEE (by positivity)
      _ = 8 / c * E ^ 2 * (gauss1 (16 * c) u * gauss1 (16 * c) v) := by ring
  revert i k
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [gaussDiffFactor, Fin.isValue, if_true,
      show ((0 : Fin 2) = 1) = False from by decide, if_false]
    exact hpure a b
  · simp only [gaussDiffFactor, Fin.isValue, if_true,
      show ((0 : Fin 2) = 1) = False from by decide,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    exact hmix
  · simp only [gaussDiffFactor, Fin.isValue, if_true,
      show ((0 : Fin 2) = 1) = False from by decide,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    exact hmix
  · simp only [gaussDiffFactor, Fin.isValue, if_true,
      show ((1 : Fin 2) = 0) = False from by decide, if_false]
    rw [mul_comm (gauss1 c a), mul_comm (gauss1 (16 * c) a)]
    exact hpure b a

/-- `exp(1/(2·2σr)) ≤ exp(1/(4σ))` for `r ≥ 1`. -/
theorem exp_inv_two_mul_le {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r) :
    Real.exp (1 / (2 * (2 * σ * r))) ≤ Real.exp (1 / (4 * σ)) := by
  rw [Real.exp_le_exp, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The second differences of the planar Gaussian** (Step 4 of Proposition 4.3 of Dario–Gu):
`|D_i D_k p̄(r, · - y)(x)| ≤ K r^{-2} exp(-|x - y|²/(32σr))` for `r ≥ 1`. -/
theorem abs_fwdDiff_fwdDiff_latticeGaussian_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ) (x y : Vertex 2) (i k : Fin 2), 1 ≤ r →
      |fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x| ≤
        K / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) := by
  refine ⟨(2 * Real.pi * σ)⁻¹ * (4 / σ) * Real.exp (1 / (4 * σ)) ^ 2, by positivity,
    fun r x y i k hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  have hE := exp_inv_two_mul_le hσ hr
  have hN : 0 ≤ (2 * Real.pi * σ * r)⁻¹ := by positivity
  rw [fwdDiff_fwdDiff_latticeGaussian_eq, ← gauss16_prod_eq hσ hr0 x y, abs_mul,
    abs_of_nonneg hN]
  have hf := abs_gaussDiffFactor_mul_le hc i k ((x 0 : ℝ) - y 0) ((x 1 : ℝ) - y 1)
  have hG : 0 ≤ gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
      gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1) :=
    (mul_pos (gauss1_pos _ _) (gauss1_pos _ _)).le
  calc (2 * Real.pi * σ * r)⁻¹ * |gaussDiffFactor (2 * σ * r) i k 0 ((x 0 : ℝ) - y 0) *
        gaussDiffFactor (2 * σ * r) i k 1 ((x 1 : ℝ) - y 1)|
      ≤ (2 * Real.pi * σ * r)⁻¹ * (8 / (2 * σ * r) * Real.exp (1 / (2 * (2 * σ * r))) ^ 2 *
          (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
            gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1))) :=
        mul_le_mul_of_nonneg_left hf hN
    _ ≤ (2 * Real.pi * σ * r)⁻¹ * (8 / (2 * σ * r) * Real.exp (1 / (4 * σ)) ^ 2 *
          (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
            gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1))) := by
        gcongr
    _ = (2 * Real.pi * σ)⁻¹ * (4 / σ) * Real.exp (1 / (4 * σ)) ^ 2 / r ^ 2 *
          (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
            gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1)) := by
        field_simp
        ring

/-- `D_0 ∂_r p̄` in product form. -/
theorem fwdDiff_zero_latticeGaussianTimeDeriv_eq {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (x y : Vertex 2) :
    fwdDiff 0 (fun z => latticeGaussianTimeDeriv σ r z y) x = σ / 2 * (2 * Real.pi * σ * r)⁻¹ *
      ((gauss1'' (2 * σ * r) ((x 0 : ℝ) - y 0 + 1) - gauss1'' (2 * σ * r) ((x 0 : ℝ) - y 0)) *
          gauss1 (2 * σ * r) ((x 1 : ℝ) - y 1) +
        (gauss1 (2 * σ * r) ((x 0 : ℝ) - y 0 + 1) - gauss1 (2 * σ * r) ((x 0 : ℝ) - y 0)) *
          gauss1'' (2 * σ * r) ((x 1 : ℝ) - y 1)) := by
  simp only [fwdDiff, latticeGaussianTimeDeriv_eq hσ hr, cast_add_unit_sub]
  simp only [Fin.isValue, if_true, show ((0 : Fin 2) = 1) = False from by decide, if_false,
    add_zero]
  ring

/-- `D_1 ∂_r p̄` in product form. -/
theorem fwdDiff_one_latticeGaussianTimeDeriv_eq {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (x y : Vertex 2) :
    fwdDiff 1 (fun z => latticeGaussianTimeDeriv σ r z y) x = σ / 2 * (2 * Real.pi * σ * r)⁻¹ *
      ((gauss1'' (2 * σ * r) ((x 1 : ℝ) - y 1 + 1) - gauss1'' (2 * σ * r) ((x 1 : ℝ) - y 1)) *
          gauss1 (2 * σ * r) ((x 0 : ℝ) - y 0) +
        (gauss1 (2 * σ * r) ((x 1 : ℝ) - y 1 + 1) - gauss1 (2 * σ * r) ((x 1 : ℝ) - y 1)) *
          gauss1'' (2 * σ * r) ((x 0 : ℝ) - y 0)) := by
  simp only [fwdDiff, latticeGaussianTimeDeriv_eq hσ hr, cast_add_unit_sub]
  simp only [Fin.isValue, if_true, show ((1 : Fin 2) = 0) = False from by decide, if_false,
    add_zero]
  ring

/-- The one-dimensional bound behind `D_k ∂_r p̄`. -/
theorem abs_timeDeriv_factor_le {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    |(gauss1'' c (a + 1) - gauss1'' c a) * gauss1 c b +
        (gauss1 c (a + 1) - gauss1 c a) * gauss1'' c b| ≤
      56 / (c * Real.sqrt c) * Real.exp (1 / (2 * c)) *
        (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
  set E := Real.exp (1 / (2 * c)) with hEdef
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have ga := gauss1_pos (16 * c) a
  have gb := gauss1_pos (16 * c) b
  have h1 := abs_gauss1''_sub_le hc a
  have h2 := abs_gauss1_le_sixteen hc b
  have h3 := abs_gauss1_sub_le hc a
  have h4 := abs_gauss1''_le_sixteen hc b
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have e : 2 / Real.sqrt c * (8 / c) = 16 / (c * Real.sqrt c) := by
    field_simp
    ring
  calc |gauss1'' c (a + 1) - gauss1'' c a| * |gauss1 c b| +
        |gauss1 c (a + 1) - gauss1 c a| * |gauss1'' c b|
      ≤ (40 / (c * Real.sqrt c) * (E * gauss1 (16 * c) a)) * gauss1 (16 * c) b +
          (2 / Real.sqrt c * (E * gauss1 (16 * c) a)) * (8 / c * gauss1 (16 * c) b) :=
        add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (by positivity))
          (mul_le_mul h3 h4 (abs_nonneg _) (by positivity))
    _ = (40 / (c * Real.sqrt c) + 2 / Real.sqrt c * (8 / c)) * E *
          (gauss1 (16 * c) a * gauss1 (16 * c) b) := by ring
    _ = 56 / (c * Real.sqrt c) * E * (gauss1 (16 * c) a * gauss1 (16 * c) b) := by
        rw [e]
        ring

/-- **The space differences of the time derivative of the planar Gaussian** (Step 4 of
Proposition 4.3 of Dario–Gu): `|D_k ∂_r p̄(r, · - y)(x)| ≤ K r^{-5/2} exp(-|x - y|²/(32σr))`
for `r ≥ 1`. -/
theorem abs_fwdDiff_latticeGaussianTimeDeriv_le {σ : ℝ} (hσ : 0 < σ) : ∃ K : ℝ, 0 < K ∧
    ∀ (r : ℝ) (x y : Vertex 2) (k : Fin 2), 1 ≤ r →
      |fwdDiff k (fun z => latticeGaussianTimeDeriv σ r z y) x| ≤
        K / (r ^ 2 * Real.sqrt r) * Real.exp (-(latticeDist x y ^ 2 / (32 * σ * r))) := by
  refine ⟨σ / 2 * (2 * Real.pi * σ)⁻¹ * (56 / (2 * σ * Real.sqrt (2 * σ))) *
    Real.exp (1 / (4 * σ)), by positivity, fun r x y k hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have hc : 0 < 2 * σ * r := by positivity
  have hE := exp_inv_two_mul_le hσ hr
  have hN : 0 ≤ σ / 2 * (2 * Real.pi * σ * r)⁻¹ := by positivity
  set G := gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0) *
    gauss1 (16 * (2 * σ * r)) ((x 1 : ℝ) - y 1) with hGdef
  have hG : 0 ≤ G := (mul_pos (gauss1_pos _ _) (gauss1_pos _ _)).le
  have key : ∀ k : Fin 2, |fwdDiff k (fun z => latticeGaussianTimeDeriv σ r z y) x| ≤
      σ / 2 * (2 * Real.pi * σ * r)⁻¹ * (56 / (2 * σ * r * Real.sqrt (2 * σ * r)) *
        Real.exp (1 / (2 * (2 * σ * r))) * G) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [fwdDiff_zero_latticeGaussianTimeDeriv_eq hσ hr0, abs_mul, abs_of_nonneg hN]
      exact mul_le_mul_of_nonneg_left (abs_timeDeriv_factor_le hc _ _) hN
    · rw [fwdDiff_one_latticeGaussianTimeDeriv_eq hσ hr0, abs_mul, abs_of_nonneg hN, hGdef,
        mul_comm (gauss1 (16 * (2 * σ * r)) ((x 0 : ℝ) - y 0))]
      exact mul_le_mul_of_nonneg_left (abs_timeDeriv_factor_le hc _ _) hN
  rw [← gauss16_prod_eq hσ hr0 x y, ← hGdef]
  refine (key k).trans ?_
  have hsc : Real.sqrt (2 * σ * r) = Real.sqrt (2 * σ) * Real.sqrt r :=
    Real.sqrt_mul (by positivity) r
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs2 : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.2 (by positivity)
  calc σ / 2 * (2 * Real.pi * σ * r)⁻¹ * (56 / (2 * σ * r * Real.sqrt (2 * σ * r)) *
        Real.exp (1 / (2 * (2 * σ * r))) * G)
      ≤ σ / 2 * (2 * Real.pi * σ * r)⁻¹ * (56 / (2 * σ * r * Real.sqrt (2 * σ * r)) *
          Real.exp (1 / (4 * σ)) * G) := by
        gcongr
    _ = σ / 2 * (2 * Real.pi * σ)⁻¹ * (56 / (2 * σ * Real.sqrt (2 * σ))) *
          Real.exp (1 / (4 * σ)) / (r ^ 2 * Real.sqrt r) * G := by
        rw [hsc]
        field_simp

end Rigidity.Green
