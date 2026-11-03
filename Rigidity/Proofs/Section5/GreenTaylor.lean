import Rigidity.Steps.Section5.TwoScaleExpansion
import Rigidity.Proofs.S2.ContinuumGreen

/-! # Proposition 5.8, step:5.8-taylor: the first-order expansion of `∇Ḡ` around the pole

Proof of `GreenTaylorStep` (eq. `gradient-green-taylor`, corrected draft L1703-1727, with the sign
of correction C18). In the plane `∇Ḡ(v) = -v / (2πκ |v|²)`, so with `w = x - z`,
`∂ᵢḠ(z - x) + ∂ᵢḠ(x) = (wᵢ / |w|² - xᵢ / |x|²) / (2πκ)`. The inversion identity
`|w / |w|² - x / |x|²| = |w - x| / (|w| |x|)` (`dist_div_norm_sq_smul`) and `|w|, |x| ≥ |x|₁ / 4`
when `4 |z|₁ ≤ |x|₁` give the bound `4 |z|₁ / (πκ |x|₁²)`. -/

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Section5 Rigidity.Steps.Section5
open scoped RealInnerProductSpace

namespace Rigidity.Proofs.Section5

/-- `∇Ḡ(v) · w = -v · w / (2πκ |v|²)` off the pole (`d = 2`). (This is
`Rigidity.Steps.Section5.fderiv_greenBar_two`; the module `FastDecayPotential` that holds it
cannot be imported together with `TwoScaleExpansion`, which both declare
`Rigidity.Steps.Section5.l1_nonneg`.) -/
private theorem fderiv_greenBar_two_apply (κ : {a : ℝ // 0 < a}) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : v ≠ 0) (w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (greenBar 2 le_rfl κ) v w = -⟪v, w⟫ / (2 * Real.pi * κ.val * ‖v‖ ^ 2) := by
  have hκ := κ.2
  have hF : ∀ u : EuclideanSpace ℝ (Fin 2), u ≠ 0 →
      greenBar 2 le_rfl κ u = (fun t => -Real.log t / (4 * Real.pi * κ.val)) (‖u‖ ^ 2) := by
    intro u hu
    simp only [greenBar, continuumGreen, dif_pos hu, Real.log_pow, ↓reduceIte]
    field_simp
    ring
  have hΦ : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => -Real.log t / (4 * Real.pi * κ.val))
      (-(1 / (4 * Real.pi * κ.val)) * t ^ (-(1 : ℝ))) t := by
    intro t ht
    rw [Real.rpow_neg_one]
    refine (((Real.hasDerivAt_log ht.ne').neg).div_const (4 * Real.pi * κ.val)).congr_deriv ?_
    ring
  have hn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  rw [(Rigidity.Proofs.S2.hasFDerivAt_of_radial hF hΦ hv).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    Real.rpow_neg_one]
  field_simp
  ring

/-- The coordinates of `toReal v` are those of `v`. -/
private theorem toReal_apply (v : Vertex 2) (k : Fin 2) : toReal v k = (v k : ℝ) := rfl

/-- The Euclidean norm of a lattice point is at most its `ℓ¹` norm. -/
private theorem norm_toReal_le_l1 (v : Vertex 2) : ‖toReal v‖ ≤ l1 v := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    toReal_apply, toReal_apply, Real.sqrt_le_left (l1_nonneg v)]
  simp only [l1, Fin.sum_univ_two, sq_abs]
  nlinarith [mul_nonneg (abs_nonneg (v 0 : ℝ)) (abs_nonneg (v 1 : ℝ)), sq_abs (v 0 : ℝ),
    sq_abs (v 1 : ℝ)]

/-- The `ℓ¹` norm of a lattice point of the plane is at most twice its Euclidean norm. -/
private theorem l1_le_two_mul_norm_toReal (v : Vertex 2) : l1 v ≤ 2 * ‖toReal v‖ := by
  have h : ∀ k, |(v k : ℝ)| ≤ ‖toReal v‖ := fun k => by
    have := PiLp.norm_apply_le (toReal v) k
    rwa [Real.norm_eq_abs, toReal_apply] at this
  simp only [l1, Fin.sum_univ_two]
  linarith [h 0, h 1]

/-- A nonzero lattice point has positive `ℓ¹` norm. -/
private theorem l1_pos_of_ne_zero {x : Vertex 2} (hx : x ≠ 0) : 0 < l1 x := by
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hk' : 0 < |(x k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have := Finset.single_le_sum (f := fun k => |(x k : ℝ)|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ k)
  unfold l1
  linarith

/-- The inversion identity, read on the `i`-th coordinate:
`|wᵢ / |w|² - xᵢ / |x|²| ≤ |w - x| / (|w| |x|)`. -/
private theorem abs_coord_inv_sub_le {w x : EuclideanSpace ℝ (Fin 2)} (hw : w ≠ 0) (hx : x ≠ 0)
    (i : Fin 2) : |w i / ‖w‖ ^ 2 - x i / ‖x‖ ^ 2| ≤ ‖w - x‖ / (‖w‖ * ‖x‖) := by
  have h := PiLp.norm_apply_le ((1 / ‖w‖) ^ 2 • w - (1 / ‖x‖) ^ 2 • x) i
  rw [← dist_eq_norm, dist_div_norm_sq_smul hw hx, dist_eq_norm, Real.norm_eq_abs] at h
  convert h using 2
  · simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · ring

/-- **step:5.8-taylor** (eq. `gradient-green-taylor`, with the oddness of `∇Ḡ` [C18]): for
`4 |z|₁ ≤ |x|₁`, `|∂ᵢḠ(z - x) + ∂ᵢḠ(x)| ≤ 4 |z|₁ / (πκ |x|₁²)`. -/
theorem greenTaylorStep : GreenTaylorStep := by
  intro κ
  have hκ := κ.2
  refine ⟨4 / (Real.pi * κ.val), by positivity, fun x z hx hzx i => ?_⟩
  have hx1 := l1_pos_of_ne_zero hx
  have hZ := norm_toReal_le_l1 z
  have hX := l1_le_two_mul_norm_toReal x
  have hXpos : 0 < ‖toReal x‖ := by linarith
  have hW : l1 x ≤ 4 * ‖toReal x - toReal z‖ := by
    have := norm_sub_norm_le (toReal x) (toReal z)
    linarith
  have hWpos : 0 < ‖toReal x - toReal z‖ := by linarith
  have hXne : toReal x ≠ 0 := norm_pos_iff.mp hXpos
  have hWne : toReal x - toReal z ≠ 0 := norm_pos_iff.mp hWpos
  have hZXne : toReal z - toReal x ≠ 0 := by
    rw [← neg_sub]
    exact neg_ne_zero.mpr hWne
  have hD : 0 < 2 * Real.pi * κ.val := by positivity
  have hS : fderiv ℝ (greenBar 2 le_rfl κ) (toReal z - toReal x) (EuclideanSpace.single i 1) +
      fderiv ℝ (greenBar 2 le_rfl κ) (toReal x) (EuclideanSpace.single i 1) =
      ((toReal x - toReal z) i / ‖toReal x - toReal z‖ ^ 2 - toReal x i / ‖toReal x‖ ^ 2) /
        (2 * Real.pi * κ.val) := by
    rw [fderiv_greenBar_two_apply κ hZXne, fderiv_greenBar_two_apply κ hXne,
      EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right,
      norm_sub_rev (toReal z) (toReal x)]
    simp only [PiLp.sub_apply, one_mul, starRingEnd_apply, star_trivial]
    field_simp
    ring
  have hinv := abs_coord_inv_sub_le hWne hXne i
  rw [show toReal x - toReal z - toReal x = -toReal z by abel, norm_neg] at hinv
  have hfinal : ‖toReal z‖ / (‖toReal x - toReal z‖ * ‖toReal x‖) ≤ 8 * l1 z / l1 x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖toReal z‖ * l1 x ^ 2 = ‖toReal z‖ * (l1 x * l1 x) := by ring
      _ ≤ l1 z * ((4 * ‖toReal x - toReal z‖) * (2 * ‖toReal x‖)) :=
          mul_le_mul hZ (mul_le_mul hW hX hx1.le (by positivity)) (by positivity)
            (l1_nonneg z)
      _ = 8 * l1 z * (‖toReal x - toReal z‖ * ‖toReal x‖) := by ring
  rw [hS, abs_div, abs_of_pos hD]
  calc _ ≤ (8 * l1 z / l1 x ^ 2) / (2 * Real.pi * κ.val) :=
        div_le_div_of_nonneg_right (hinv.trans hfinal) hD.le
    _ = 4 / (Real.pi * κ.val) * l1 z / l1 x ^ 2 := by
        field_simp
        ring

end Rigidity.Proofs.Section5
