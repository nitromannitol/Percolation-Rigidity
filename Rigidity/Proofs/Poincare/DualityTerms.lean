import Rigidity.Proofs.Poincare.DualityLowFreq
import Rigidity.Proofs.Poincare.DualTestFunction

/-!
# The two terms of the duality identity, with the weights of (2.26)

For `R = 2ρ + 1` and `g` supported in the box `B = [-ρ, ρ]²`, with
`RHS = Σ_x R^{-2} e^{-|x|/(2R)} Sq(x)^{q/2}` the right-hand side of Dario's (2.26):

* `ofReal_abs_termI_le`: the bilinear term is at most
  `2√2 · 8e C q R^{2/q} ‖g‖_{ℓ^p} RHS^{1/q}`, by Hölder's inequality in `x` with the weight of
  (2.26) (`tsum_mul_le_weighted`) and the weighted Littlewood-Paley bound for the dual exponent
  `p = q/(q-1)` with the weight `cosh(x₀/2R) cosh(x₁/2R) ≥ e^{|x|/(2R)}/4`;
* `ofReal_abs_termII_le`: the low-frequency term is at most `4 √K Σ_B |g| RHS^{1/q}`.
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.Green MeasureTheory

namespace Rigidity.Poincare

variable {u : Vertex 2 → ℝ}

/-- **Hölder's inequality with a weight** on `ℤ²`. -/
theorem tsum_mul_le_weighted {p q : ℝ} (hpq : p.HolderConjugate q) (X Y w : Vertex 2 → ENNReal)
    (hw0 : ∀ x, w x ≠ 0) (hwt : ∀ x, w x ≠ ⊤) :
    ∑' x, X x * Y x ≤ (∑' x, X x ^ p * w x ^ (-(p / q))) ^ (1 / p) *
      (∑' x, Y x ^ q * w x) ^ (1 / q) := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set f : Vertex 2 → ENNReal := fun x => X x * w x ^ (-(1 / q)) with hfdef
  set g : Vertex 2 → ENNReal := fun x => Y x * w x ^ (1 / q) with hgdef
  have hfg : ∀ x, X x * Y x = f x * g x := by
    intro x
    have h1 : w x ^ (-(1 / q)) * w x ^ (1 / q) = 1 := by
      rw [← ENNReal.rpow_add _ _ (hw0 x) (hwt x), neg_add_cancel, ENNReal.rpow_zero]
    calc X x * Y x = X x * Y x * (w x ^ (-(1 / q)) * w x ^ (1 / q)) := by rw [h1, mul_one]
      _ = f x * g x := by simp only [hfdef, hgdef]; ring
  have hf : ∀ x, f x ^ p = X x ^ p * w x ^ (-(p / q)) := by
    intro x
    simp only [hfdef]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
      show -(1 / q) * p = -(p / q) by ring]
  have hg : ∀ x, g x ^ q = Y x ^ q * w x := by
    intro x
    simp only [hgdef]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count (α := Vertex 2)) hpq (f := f)
    (g := g) (Measurable.of_discrete).aemeasurable (Measurable.of_discrete).aemeasurable
  simp only [lintegral_count, Pi.mul_apply] at h
  simp only [hfg]
  refine h.trans (le_of_eq ?_)
  simp only [hf, hg]

theorem cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 : Real.exp (-|t|) ≤ Real.exp |t| := Real.exp_le_exp.2 (by linarith [abs_nonneg t])
  linarith

theorem coshW_le_exp_of_mem {ρ : ℕ} {y : Vertex 2} (hy : y ∈ supBox 0 ρ) :
    coshW (1 / (2 * (2 * ρ + 1))) y ≤ Real.exp 1 := by
  have hR : (0 : ℝ) < 2 * (2 * ρ + 1) := by positivity
  rw [mem_supBox] at hy
  have h0 := hy 0
  have h1 := hy 1
  simp only [Pi.zero_apply, sub_zero] at h0 h1
  have h0' : |((y 0 : ℤ) : ℝ)| ≤ ρ := by exact_mod_cast h0
  have h1' : |((y 1 : ℤ) : ℝ)| ≤ ρ := by exact_mod_cast h1
  rw [coshW]
  refine (mul_le_mul (cosh_le_exp_abs _) (cosh_le_exp_abs _) (Real.cosh_pos _).le
    (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * (2 * ρ + 1)))]
  rw [← mul_add, div_mul_eq_mul_div, one_mul, div_le_one hR]
  linarith

theorem abs_coord_le_of_mem {ρ : ℕ} {y : Vertex 2} (hy : y ∈ supBox 0 ρ) :
    |((y 0 : ℤ) : ℝ)| + |((y 1 : ℤ) : ℝ)| ≤ 2 * ρ + 1 := by
  rw [mem_supBox] at hy
  have h0 := hy 0
  have h1 := hy 1
  simp only [Pi.zero_apply, sub_zero] at h0 h1
  have h0' : |((y 0 : ℤ) : ℝ)| ≤ ρ := by exact_mod_cast h0
  have h1' : |((y 1 : ℤ) : ℝ)| ≤ ρ := by exact_mod_cast h1
  linarith

/-- The weight of (2.26) against the weight of the Littlewood-Paley bound:
`(R^{-2} e^{-|x|/(2R)})^{-(p-1)} ≤ 4 (R²)^{p-1} cosh(x₀/2R) cosh(x₁/2R)` for `p ≤ 2`. -/
theorem dwt_rpow_neg_le {R e : ℝ} (hR : 0 < R) (he1 : e ≤ 1) (x : Vertex 2) :
    dwt R x ^ (-e) ≤ ENNReal.ofReal (4 * (R ^ 2) ^ e * coshW (1 / (2 * R)) x) := by
  rw [dwt, ENNReal.ofReal_rpow_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  set t := ‖latticeEuclideanEmbedding x‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have e1 : (Real.exp (-t / (2 * R)) / R ^ 2) ^ (-e) =
      (R ^ 2) ^ e * Real.exp (t / (2 * R) * e) := by
    rw [Real.div_rpow (Real.exp_pos _).le (by positivity), Real.rpow_neg (Real.exp_pos _).le,
      Real.rpow_neg (by positivity), ← Real.exp_mul, ← Real.exp_neg]
    field_simp
  rw [e1]
  have h1 : Real.exp (t / (2 * R) * e) ≤ Real.exp (t / (2 * R)) :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right (by positivity) he1)
  have h2 : Real.exp (t / (2 * R)) ≤ 4 * coshW (1 / (2 * R)) x := by
    refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_four_mul_coshW _ x)
    have hn := norm_euclid_le_abs_add_abs x
    rw [← mul_add, div_eq_mul_one_div t, mul_comm t]
    exact mul_le_mul_of_nonneg_left hn (by positivity)
  have hRe : 0 ≤ (R ^ 2) ^ e := Real.rpow_nonneg (by positivity) _
  calc (R ^ 2) ^ e * Real.exp (t / (2 * R) * e) ≤ (R ^ 2) ^ e * (4 * coshW (1 / (2 * R)) x) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hRe
    _ = 4 * (R ^ 2) ^ e * coshW (1 / (2 * R)) x := by ring

theorem holderConjugate_conj {q : ℝ} (hq : 1 < q) : (q / (q - 1)).HolderConjugate q :=
  ((Real.holderConjugate_iff_eq_conjExponent hq).2 rfl).symm

/-- **The bilinear term** with the weights of (2.26). -/
theorem ofReal_abs_termI_le {Cs : ℝ} (hCs : 1 ≤ Cs)
    (hStein : ∀ p a T : ℝ, 1 < p → p ≤ 2 → 0 ≤ a → a ≤ 1 / 6 → a * max (Real.sqrt T) 1 ≤ 1 →
      0 ≤ T → ∀ (S : Finset (Vertex 2)) (g : Vertex 2 → ℝ), (∀ y ∉ S, g y = 0) →
        ∑' x, ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2)) ≤
          ENNReal.ofReal (2 * (Cs * (p / (p - 1))) ^ p * ∑ y ∈ S, coshW a y * |g y| ^ p))
    (hu : HeatSummable u) {ρ : ℕ} (hρ : 1 ≤ ρ) {q : ℝ} (hq : 2 ≤ q) {g : Vertex 2 → ℝ}
    (hgS : ∀ y ∉ supBox 0 ρ, g y = 0) :
    ENNReal.ofReal |∫ t in (0 : ℝ)..(2 * (4 * (2 * ρ + 1 : ℝ) ^ 2)), ∑ i : Fin 2, ∑' y,
        (g (y + unit i) - g y) * heatGrad u i t y| ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * (8 * Real.exp 1) * Cs * q * (2 * ρ + 1 : ℝ) ^ (2 / q) *
        (∑ y ∈ supBox 0 ρ, |g y| ^ (q / (q - 1))) ^ (1 / (q / (q - 1)))) *
      (∑' x, dwt (2 * ρ + 1) x * sqInt u (2 * (2 * ρ + 1)) x ^ (q / 2)) ^ (1 / q) := by
  set R : ℝ := 2 * ρ + 1 with hRdef
  have hR3 : 3 ≤ R := by
    have : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
    linarith
  have hR0 : 0 < R := by linarith
  have hq1 : 1 < q := by linarith
  have hq0 : 0 < q := by linarith
  set p := q / (q - 1) with hpdef
  have hpq := holderConjugate_conj hq1
  rw [← hpdef] at hpq
  have hq10 : 0 < q - 1 := by linarith
  have hp1 : 1 < p := by rw [hpdef, lt_div_iff₀ hq10]; linarith
  have hp2 : p ≤ 2 := by rw [hpdef, div_le_iff₀ hq10]; linarith
  have hp0 : 0 < p := by linarith
  have hpp : p / (p - 1) = q := by
    rw [hpdef]
    field_simp
    ring
  have hpe : p / q = p - 1 := by
    rw [hpdef]
    field_simp
    ring
  set S := supBox 0 ρ with hS
  set a : ℝ := 1 / (2 * R) with ha
  set T : ℝ := 4 * R ^ 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hsqT : Real.sqrt T = 2 * R := by
    rw [hT, show 4 * R ^ 2 = (2 * R) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  set G : ℝ := ∑ y ∈ S, |g y| ^ p with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun y _ => Real.rpow_nonneg (abs_nonneg _) _
  set RHS := ∑' x, dwt R x * sqInt u (2 * R) x ^ (q / 2) with hRHS
  have h1 := ofReal_abs_integral_le hu hgS hT0
  rw [hsqT] at h1
  set X : Vertex 2 → ENNReal := fun x => ENNReal.ofReal (gam S g T x) ^ (1 / 2 : ℝ) with hX
  set Y : Vertex 2 → ENNReal := fun x => (2 * sqInt u (2 * R) x) ^ (1 / 2 : ℝ) with hY
  have hw0 : ∀ x, dwt R x ≠ 0 := fun x => by
    rw [dwt, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hwt : ∀ x, dwt R x ≠ ⊤ := fun x => ENNReal.ofReal_ne_top
  have hH := tsum_mul_le_weighted hpq X Y (dwt R) hw0 hwt
  -- the first factor
  have hA : ∑' x, X x ^ p * dwt R x ^ (-(p / q)) ≤
      ENNReal.ofReal (8 * Real.exp 1 * (R ^ 2) ^ (p - 1) * (Cs * q) ^ p * G) := by
    have hpt : ∀ x, X x ^ p * dwt R x ^ (-(p / q)) ≤ ENNReal.ofReal (4 * (R ^ 2) ^ (p - 1)) *
        ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2)) := by
      intro x
      have hX' : X x ^ p = ENNReal.ofReal (gam S g T x ^ (p / 2)) := by
        rw [hX, ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg (gam_nonneg hT0 x)
          (by positivity)]
        congr 2
        ring
      rw [hX', hpe, ← ENNReal.ofReal_mul (by positivity)]
      refine (mul_le_mul_of_nonneg_left (dwt_rpow_neg_le hR0 (by linarith) x)
        (by positivity)).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (gam_nonneg hT0 x) _)]
      congr 1
      ring
    have hSt := hStein p a T hp1 hp2 (by positivity)
      (by rw [ha, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
      (le_of_eq (by rw [hsqT, max_eq_left (by linarith), ha, one_div_mul_cancel (by positivity)]))
      hT0 S g hgS
    rw [hpp] at hSt
    have hcosh : ∑ y ∈ S, coshW a y * |g y| ^ p ≤ Real.exp 1 * G := by
      rw [hG, Finset.mul_sum]
      refine Finset.sum_le_sum fun y hy => ?_
      exact mul_le_mul_of_nonneg_right (coshW_le_exp_of_mem hy) (Real.rpow_nonneg (abs_nonneg _) _)
    calc ∑' x, X x ^ p * dwt R x ^ (-(p / q))
        ≤ ∑' x, ENNReal.ofReal (4 * (R ^ 2) ^ (p - 1)) *
            ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2)) := ENNReal.tsum_le_tsum hpt
      _ = ENNReal.ofReal (4 * (R ^ 2) ^ (p - 1)) *
            ∑' x, ENNReal.ofReal (coshW a x * gam S g T x ^ (p / 2)) := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (4 * (R ^ 2) ^ (p - 1)) *
            ENNReal.ofReal (2 * (Cs * q) ^ p * ∑ y ∈ S, coshW a y * |g y| ^ p) := by gcongr
      _ ≤ ENNReal.ofReal (4 * (R ^ 2) ^ (p - 1)) *
            ENNReal.ofReal (2 * (Cs * q) ^ p * (Real.exp 1 * G)) := by
          gcongr
      _ = ENNReal.ofReal (8 * Real.exp 1 * (R ^ 2) ^ (p - 1) * (Cs * q) ^ p * G) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- the second factor
  have hB : ∑' x, Y x ^ q * dwt R x = ENNReal.ofReal (2 ^ (q / 2)) * RHS := by
    rw [hRHS, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [hY, ← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      show (1 / 2 : ℝ) * q = q / 2 by ring, ← ENNReal.ofReal_ofNat 2,
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by positivity)]
    ring
  -- assembly
  have hfin : ENNReal.ofReal (8 * Real.exp 1 * (R ^ 2) ^ (p - 1) * (Cs * q) ^ p * G) ^ (1 / p)
      ≤ ENNReal.ofReal (8 * Real.exp 1 * R ^ (2 / q) * (Cs * q) * G ^ (1 / p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hCq : 0 ≤ Cs * q := by positivity
    rw [Real.mul_rpow (by positivity) hG0, Real.mul_rpow (by positivity) (Real.rpow_nonneg hCq _),
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul hCq, mul_one_div_cancel hp0.ne', Real.rpow_one,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ R ^ 2)]
    have hR2 : (R ^ 2) ^ ((p - 1) * (1 / p)) = R ^ (2 / q) := by
      rw [show (R ^ 2 : ℝ) = R ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hR0.le]
      congr 1
      rw [hpdef]
      field_simp
      ring
    rw [hR2]
    have h8 : (8 * Real.exp 1) ^ (1 / p) ≤ 8 * Real.exp 1 :=
      Real.rpow_le_self_of_one_le (by nlinarith [Real.add_one_le_exp 1])
        (by rw [div_le_one hp0]; linarith)
    have hrest : 0 ≤ R ^ (2 / q) * (Cs * q) * G ^ (1 / p) := by positivity
    calc (8 * Real.exp 1) ^ (1 / p) * R ^ (2 / q) * (Cs * q) * G ^ (1 / p)
        = (8 * Real.exp 1) ^ (1 / p) * (R ^ (2 / q) * (Cs * q) * G ^ (1 / p)) := by ring
      _ ≤ (8 * Real.exp 1) * (R ^ (2 / q) * (Cs * q) * G ^ (1 / p)) :=
          mul_le_mul_of_nonneg_right h8 hrest
      _ = 8 * Real.exp 1 * R ^ (2 / q) * (Cs * q) * G ^ (1 / p) := by ring
  have hsq2 : (ENNReal.ofReal (2 ^ (q / 2)) * RHS) ^ (1 / q) =
      ENNReal.ofReal (Real.sqrt 2) * RHS ^ (1 / q) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul (by norm_num),
      show q / 2 * (1 / q) = 1 / 2 by field_simp, Real.sqrt_eq_rpow]
  calc ENNReal.ofReal |∫ t in (0 : ℝ)..(2 * T), ∑ i : Fin 2, ∑' y,
          (g (y + unit i) - g y) * heatGrad u i t y|
      ≤ 2 * ∑' x, X x * Y x := h1
    _ ≤ 2 * ((∑' x, X x ^ p * dwt R x ^ (-(p / q))) ^ (1 / p) *
          (∑' x, Y x ^ q * dwt R x) ^ (1 / q)) := by gcongr
    _ ≤ 2 * (ENNReal.ofReal (8 * Real.exp 1 * R ^ (2 / q) * (Cs * q) * G ^ (1 / p)) *
          (ENNReal.ofReal (Real.sqrt 2) * RHS ^ (1 / q))) := by
        rw [hB, hsq2]
        gcongr
        exact (ENNReal.rpow_le_rpow hA (by positivity)).trans hfin
    _ = ENNReal.ofReal (2 * Real.sqrt 2 * (8 * Real.exp 1) * Cs * q * R ^ (2 / q) *
          G ^ (1 / p)) * RHS ^ (1 / q) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

end Rigidity.Poincare
