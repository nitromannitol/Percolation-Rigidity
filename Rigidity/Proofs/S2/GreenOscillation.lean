import Rigidity.Steps.S2.GreenGradientHomogenization

/-!
# Proposition 2.6, step:2.6-expansion: the size of `u` on `B_R(x)`

`GreenOscillationStep` (proof step `step:2.6-expansion`): under the
homogenization of the Green function (H1) at the scale `X ≤ |x - y| / 2`, for `z` in the cluster
with `|z - x| < |x - y| / 2`, `|G(z, y) - K - Ḡ(x - y)| ≤ A₂ |x - y|^{2-d}`. This replaces eq.
(decay-estimate) of the paper, which fails in `d = 2`.

The proof splits `G(z, y) - K - Ḡ(x - y)` into the homogenization error
`G(z, y) - Ḡ(z - y) - K`, bounded by (H1) since `|z - y| > |x - y| / 2 ≥ X`, and the oscillation
`Ḡ(z - y) - Ḡ(x - y)` of the homogenized Green function on the ball `B_{|w|/2}(w)`, `w = x - y`,
bounded from the explicit formula of `Ḡ` (`abs_greenBar_sub_le`): `|log |v| - log |w|| ≤ 1` in
`d = 2` and `|v|^{2-d} ≤ 2^{d-2} |w|^{2-d}` in `d ≥ 3`.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

variable {d : ℕ}

/-- The lattice point as a vector of `ℝ^d` is its Euclidean embedding. -/
theorem toReal_eq_latticeEuclideanEmbedding (x : Vertex d) :
    toReal x = latticeEuclideanEmbedding x := rfl

/-- Distinct vertices are at Euclidean distance at least one. -/
theorem one_le_dist_latticeEuclideanEmbedding {x y : Vertex d} (h : x ≠ y) :
    1 ≤ dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp h
  have h1 : (1 : ℝ) ≤ |(x i : ℝ) - (y i : ℝ)| := by
    have : (1 : ℤ) ≤ |x i - y i| := Int.one_le_abs (sub_ne_zero.mpr hi)
    exact_mod_cast this
  have hi' := PiLp.norm_apply_le
    (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y) i
  change |(x i : ℝ) - (y i : ℝ)| ≤
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ at hi'
  rw [dist_eq_norm]
  exact h1.trans hi'

/-- For `t ≥ 0` and `d ≥ 2`, `t^{2-d} = (t^{d-2})⁻¹`. -/
theorem rpow_two_sub_eq_inv_pow (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    t ^ (2 - (d : ℝ)) = (t ^ (d - 2))⁻¹ := by
  rw [show (2 : ℝ) - d = -((d - 2 : ℕ) : ℝ) by push_cast [Nat.cast_sub hd]; ring,
    Real.rpow_neg ht, Real.rpow_natCast]

/-- The constant `Γ(d/2 - 1) / (4 π^{d/2} κ)` of the homogenized Green function in `d ≥ 3`. -/
noncomputable def greenBarConst (d : ℕ) (κ : {a : ℝ // 0 < a}) : ℝ :=
  Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.rpow Real.pi ((d : ℝ) / 2) * κ.val)

/-- The oscillation of `Ḡ` on `B_{|w|/2}(w)`: `|Ḡ(v) - Ḡ(w)| ≤ A |w|^{2-d}` for `|v - w| ≤ |w|/2`,
from the explicit formula of `Ḡ`. -/
theorem abs_greenBar_sub_le (hd : 2 ≤ d) (κ : {a : ℝ // 0 < a})
    {v w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (hvw : ‖v - w‖ ≤ ‖w‖ / 2) :
    |greenBar d hd κ v - greenBar d hd κ w| ≤
      (1 / (2 * Real.pi * κ.val) + |greenBarConst d κ| * (2 ^ (d - 2) + 1)) *
        (‖w‖ ^ (d - 2))⁻¹ := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hvlow : ‖w‖ / 2 ≤ ‖v‖ := by
    have := norm_sub_norm_le w v
    rw [norm_sub_rev] at this
    linarith
  have hvup : ‖v‖ ≤ 3 * ‖w‖ / 2 := by
    have := norm_sub_norm_le v w
    linarith
  have hv0' : 0 < ‖v‖ := by linarith
  have hv : v ≠ 0 := norm_pos_iff.mp hv0'
  have hκ : 0 < 2 * Real.pi * κ.val := by have := κ.property; positivity
  have hA1 : 0 ≤ 1 / (2 * Real.pi * κ.val) := by positivity
  have hA2 : 0 ≤ |greenBarConst d κ| * (2 ^ (d - 2) + 1) := by positivity
  have hwinv : 0 < (‖w‖ ^ (d - 2))⁻¹ := by positivity
  simp only [greenBar, dif_pos hv, dif_pos hw, continuumGreen]
  by_cases h2 : d = 2
  · subst h2
    simp only [if_true, Nat.sub_self, pow_zero, inv_one, mul_one]
    have hlog : |Real.log ‖w‖ - Real.log ‖v‖| ≤ 1 := by
      have e1 : Real.log ‖v‖ - Real.log ‖w‖ ≤ 1 := by
        rw [← Real.log_div hv0'.ne' hw0.ne']
        have := Real.log_le_sub_one_of_pos (div_pos hv0' hw0)
        have : ‖v‖ / ‖w‖ ≤ 3 / 2 := by rw [div_le_iff₀ hw0]; linarith
        linarith
      have e2 : Real.log ‖w‖ - Real.log ‖v‖ ≤ 1 := by
        rw [← Real.log_div hw0.ne' hv0'.ne']
        have := Real.log_le_sub_one_of_pos (div_pos hw0 hv0')
        have : ‖w‖ / ‖v‖ ≤ 2 := by rw [div_le_iff₀ hv0']; linarith
        linarith
      exact abs_le.mpr ⟨by linarith, e2⟩
    calc |-Real.log ‖v‖ / (2 * Real.pi * κ.val) - -Real.log ‖w‖ / (2 * Real.pi * κ.val)|
        = |Real.log ‖w‖ - Real.log ‖v‖| / (2 * Real.pi * κ.val) := by
          rw [← sub_div, abs_div, abs_of_pos hκ]; congr 2; ring
      _ ≤ 1 / (2 * Real.pi * κ.val) := by gcongr
      _ ≤ _ := le_add_of_nonneg_right hA2
  · simp only [if_neg h2]
    rw [← greenBarConst, Real.rpow_eq_pow, Real.rpow_eq_pow, rpow_two_sub_eq_inv_pow hd hv0'.le,
      rpow_two_sub_eq_inv_pow hd hw0.le]
    have hvinv : (‖v‖ ^ (d - 2))⁻¹ ≤ 2 ^ (d - 2) * (‖w‖ ^ (d - 2))⁻¹ := by
      have : (‖w‖ / 2) ^ (d - 2) ≤ ‖v‖ ^ (d - 2) := pow_le_pow_left₀ (by positivity) hvlow _
      calc (‖v‖ ^ (d - 2))⁻¹ ≤ ((‖w‖ / 2) ^ (d - 2))⁻¹ := inv_anti₀ (by positivity) this
        _ = 2 ^ (d - 2) * (‖w‖ ^ (d - 2))⁻¹ := by rw [div_pow, inv_div, div_eq_mul_inv]
    calc |greenBarConst d κ * (‖v‖ ^ (d - 2))⁻¹ - greenBarConst d κ * (‖w‖ ^ (d - 2))⁻¹|
        = |greenBarConst d κ| * |(‖v‖ ^ (d - 2))⁻¹ - (‖w‖ ^ (d - 2))⁻¹| := by
          rw [← mul_sub, abs_mul]
      _ ≤ |greenBarConst d κ| * ((2 ^ (d - 2) + 1) * (‖w‖ ^ (d - 2))⁻¹) := by
          gcongr
          rw [abs_sub_le_iff]
          constructor <;> nlinarith [inv_pos.mpr (pow_pos hv0' (d - 2))]
      _ ≤ _ := by
          rw [← mul_assoc, add_mul _ _ (‖w‖ ^ (d - 2))⁻¹]
          exact le_add_of_nonneg_left (by positivity)

/-- step:2.6-expansion, size of `u`: `GreenOscillationStep`. -/
theorem greenOscillationStep (hd : 2 ≤ d) : GreenOscillationStep d hd := by
  intro κ δ Ch hδ hδ1 hCh
  refine ⟨2 ^ (d - 1) * Ch +
    (1 / (2 * Real.pi * κ.val) + |greenBarConst d κ| * (2 ^ (d - 2) + 1)),
    by have := κ.property; positivity, ?_⟩
  intro ω C y g K x X hclose hX z hz
  set D := dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) with hD
  have hxy : x.val ≠ y.val := by
    intro h
    rw [hD, h, dist_self] at hz
    linarith [dist_nonneg (x := latticeEuclideanEmbedding z.val)
      (y := latticeEuclideanEmbedding y.val)]
  have hD1 : 1 ≤ D := one_le_dist_latticeEuclideanEmbedding hxy
  set w := latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val with hw
  set v := latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding y.val with hv
  have hwD : ‖w‖ = D := (dist_eq_norm _ _).symm
  have hvw : ‖v - w‖ < D / 2 := by
    have : v - w = latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding x.val := by
      rw [hv, hw]; abel
    rw [this, ← dist_eq_norm]
    exact hz
  have hvD : D / 2 < ‖v‖ := by
    have := norm_sub_norm_le w v
    have := norm_sub_rev w v
    linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
  -- the homogenization error at `z`
  have h1 := hclose z ⟨v, hv0⟩ rfl (by simp only; linarith)
  have hDpow : 0 < D ^ (d - 2) := by positivity
  have h1' : Ch / (Real.rpow ‖v‖ (1 - δ / 4) * ‖v‖ ^ (d - 2)) ≤
      2 ^ (d - 1) * Ch * (D ^ (d - 2))⁻¹ := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.rpow ‖v‖ (1 - δ / 4) := by
      calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 2) ^ (1 - δ / 4) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        _ ≤ ‖v‖ ^ (1 - δ / 4) := Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
    have hpow : (D / 2) ^ (d - 2) ≤ ‖v‖ ^ (d - 2) := pow_le_pow_left₀ (by positivity) hvD.le _
    have hden : (1 / 2) * (D / 2) ^ (d - 2) ≤ Real.rpow ‖v‖ (1 - δ / 4) * ‖v‖ ^ (d - 2) :=
      mul_le_mul hhalf hpow (by positivity) (by linarith)
    calc Ch / (Real.rpow ‖v‖ (1 - δ / 4) * ‖v‖ ^ (d - 2))
        ≤ Ch / ((1 / 2) * (D / 2) ^ (d - 2)) := div_le_div_of_nonneg_left hCh.le
          (by positivity) hden
      _ = 2 ^ (d - 1) * Ch * (D ^ (d - 2))⁻¹ := by
          rw [div_pow]
          have : d - 1 = (d - 2) + 1 := by omega
          rw [this, pow_succ]
          field_simp
  -- the oscillation of `Ḡ`
  have h2 := abs_greenBar_sub_le hd κ hw0 (v := v) (by rw [hwD]; exact hvw.le)
  rw [hwD] at h2
  have hgv : greenBar d hd κ v = continuumGreen d hd κ ⟨v, hv0⟩ := dif_pos hv0
  rw [show toReal x.val - toReal y.val = w from rfl,
    rpow_two_sub_eq_inv_pow hd (by positivity : (0 : ℝ) ≤ D)]
  calc |g z - K - greenBar d hd κ w|
      = |(g z - continuumGreen d hd κ ⟨v, hv0⟩ - K) + (greenBar d hd κ v - greenBar d hd κ w)| := by
        rw [hgv]; ring_nf
    _ ≤ |g z - continuumGreen d hd κ ⟨v, hv0⟩ - K| + |greenBar d hd κ v - greenBar d hd κ w| :=
        abs_add_le _ _
    _ ≤ 2 ^ (d - 1) * Ch * (D ^ (d - 2))⁻¹ +
        (1 / (2 * Real.pi * κ.val) + |greenBarConst d κ| * (2 ^ (d - 2) + 1)) *
          (D ^ (d - 2))⁻¹ := add_le_add (h1.trans h1') h2
    _ = _ := by ring

end Rigidity.Proofs.S2
