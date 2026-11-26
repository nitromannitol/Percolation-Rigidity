import Rigidity.Proofs.Corrector.PeriodicHeatDecay
import Rigidity.Proofs.Poincare.GeneralLatticeHeatKernel

/-!
# Heat decay of periodic functions of mean zero on `ℤᵈ`

Dario, Lemma 3.2, Step 3, in every dimension: for a function `f` on `ℤᵈ` which is `L`-periodic
with mean zero over a period, `Φ_t * f` decays like `exp(-16 t / L²)`. As in the source, by the
discrete Fourier transform: the characters `ψ_a(y) = exp(2πi Σ_i a_i y_i / L)` are eigenfunctions
of the heat kernel of `ℤᵈ`, `Φ_t * ψ_a = exp(-t λ_a) ψ_a` with
`λ_a = Σ_i 2(1 - cos(2πa_i/L)) ≥ 16/L²` for `a ≠ 0`, and the indicator of a residue class modulo
`L` is the average of the characters against it.

* `hasSum_zdHeat_mul_zdChar`: `Σ_y Φ(t, x, y) ψ(y) = e^{-t λ} ψ(x)` with
  `λ = Σ_i 2(1 - cos θ_i)`;
* `indicator_eq_sum_zdChar`: the indicator of a residue class as an average of characters;
* `abs_tsum_zdHeat_mul_le`: `|Σ_y Φ(t, x, y) g(y mod L)| ≤ e^{-16 t/L²} Σ_w |g(w)|` for every
  `g : (ℤ/L)ᵈ → ℝ` of sum zero;
* `abs_tsum_zdHeat_mul_periodic_le`, `abs_tsum_zdHeat_mul_periodic_le_exp`: the same for
  `L`-periodic functions of sum zero over `{0, …, L-1}ᵈ`, and the form used by Dario, with
  `L = 3^k`, `t = r²` and `9^k ≤ r`: `|Φ_{r²} * f(x)| ≤ e^{-16 r} Σ_{period} |f|`.
-/

open scoped Classical
open Finset

namespace Rigidity.Corrector.GeneralDim

open LatticeProb LatticeProb.Percolation Rigidity.Green Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The neighbours of `x` in `ℤᵈ`, direction by direction, for complex functions. -/
theorem sum_neighborFinset_allOpen_complex (x : Vertex d) (u : Vertex d → ℂ) :
    ∑ z ∈ (openGraph (allOpen d)).neighborFinset x, u z =
      ∑ i : Fin d, (u (x + unit i) + u (x - unit i)) := by
  rw [Rigidity.Poincare.GeneralDim.neighborFinset_allOpen, nbrFinset, sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [sum_pair]
    intro h
    have := congrFun h i
    simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
    omega
  · intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- The character `ψ(y) = exp(i Σ_i θ_i y_i)` of `ℤᵈ`. -/
noncomputable def zdChar (θ : Fin d → ℝ) (y : Vertex d) : ℂ :=
  Complex.exp (((∑ i, θ i * y i : ℝ) : ℂ) * Complex.I)

theorem norm_zdChar (θ : Fin d → ℝ) (y : Vertex d) : ‖zdChar θ y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem sum_mul_add_smul_unit (θ : Fin d → ℝ) (y : Vertex d) (i : Fin d) (s : ℤ) :
    ∑ i', θ i' * (((y + s • unit i) i' : ℤ) : ℝ) = ∑ i', θ i' * (y i' : ℝ) + θ i * s := by
  have e : ∀ i', θ i' * (((y + s • unit i) i' : ℤ) : ℝ) =
      θ i' * (y i' : ℝ) + (if i' = i then θ i * s else 0) := by
    intro i'
    by_cases h : i' = i
    · subst h
      simp [unit, Pi.single_eq_same]
      ring
    · simp [unit, h]
  rw [Finset.sum_congr rfl fun i' _ => e i', Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem zdChar_add_unit (θ : Fin d → ℝ) (y : Vertex d) (i : Fin d) (s : ℤ) :
    zdChar θ (y + s • unit i) = zdChar θ y * Complex.exp (((θ i * s : ℝ) : ℂ) * Complex.I) := by
  rw [zdChar, zdChar, ← Complex.exp_add, sum_mul_add_smul_unit]
  congr 1
  push_cast
  ring

/-- The characters are eigenfunctions of the lazy kernel of `ℤᵈ`, with eigenvalue
`(Σ_i cos θ_i)/d`. -/
theorem zdChar_eigen [NeZero d] (θ : Fin d → ℝ) (x : Vertex d) :
    (1 - ((openGraph (allOpen d)).degree x : ℂ) / ((2 * d : ℕ) : ℂ)) * zdChar θ x +
      1 / ((2 * d : ℕ) : ℂ) * ∑ z ∈ (openGraph (allOpen d)).neighborFinset x, zdChar θ z =
      (((∑ i, Real.cos (θ i)) / d : ℝ) : ℂ) * zdChar θ x := by
  have hp : ∀ i : Fin d, zdChar θ (x + unit i) + zdChar θ (x - unit i) =
      zdChar θ x * (2 * (Real.cos (θ i) : ℂ)) := by
    intro i
    have h1 := zdChar_add_unit θ x i 1
    have h2 := zdChar_add_unit θ x i (-1)
    rw [one_smul] at h1
    rw [neg_smul, one_smul, ← sub_eq_add_neg] at h2
    rw [h1, h2, ← mul_add, Complex.ofReal_cos]
    congr 1
    rw [Complex.cos, Int.cast_one, mul_one, Int.cast_neg, Int.cast_one, mul_neg_one,
      Complex.ofReal_neg, neg_mul]
    ring
  have hsum : ∑ z ∈ (openGraph (allOpen d)).neighborFinset x, zdChar θ z =
      zdChar θ x * (2 * ∑ i, (Real.cos (θ i) : ℂ)) := by
    rw [sum_neighborFinset_allOpen_complex, Finset.sum_congr rfl fun i _ => hp i,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [Rigidity.Poincare.GeneralDim.degree_allOpen, hsum]
  push_cast
  field_simp
  ring

/-- `Σ_y Φ(t, x, y) ψ(y) = e^{-t λ} ψ(x)` with `λ = Σ_i 2(1 - cos θ_i)`. -/
theorem hasSum_zdHeat_mul_zdChar [NeZero d] (θ : Fin d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (x : Vertex d) :
    HasSum (fun y => (zdHeat d t x y : ℂ) * zdChar θ y)
      (((Real.exp (-(t * ∑ i, 2 * (1 - Real.cos (θ i))))) : ℝ) * zdChar θ x) := by
  have h := hasSum_vsrwHeat_mul_eigen (G := openGraph (allOpen d)) (D := 2 * d)
    two_mul_pos_of_neZero (openGraph_degree_le (allOpen d)) (fun y => (norm_zdChar θ y).le)
    (zdChar_eigen θ) ht x
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have eR : (2 * d : ℝ) * t * ((∑ i, Real.cos (θ i)) / d - 1) =
      -(t * ∑ i, 2 * (1 - Real.cos (θ i))) := by
    have : ∑ i : Fin d, 2 * (1 - Real.cos (θ i)) = 2 * d - 2 * ∑ i, Real.cos (θ i) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    rw [this]
    field_simp
    ring
  have e : ((2 * d : ℕ) : ℂ) * t * ((((∑ i, Real.cos (θ i)) / d : ℝ) : ℂ) - 1) =
      ((-(t * ∑ i, 2 * (1 - Real.cos (θ i))) : ℝ) : ℂ) := by
    rw [← eR]
    push_cast
    ring
  rw [e, ← Complex.ofReal_exp] at h
  exact h

/-- The angles `2π a_i / L` of the character `ψ_a`. -/
noncomputable def zdAngle (L : ℕ) (a : Fin d → ℕ) : Fin d → ℝ := fun i => charAngle L (a i)

/-- The exponent `λ_a = Σ_i 2(1 - cos(2πa_i/L))`. -/
noncomputable def zdEigen (L : ℕ) (a : Fin d → ℕ) : ℝ :=
  ∑ i, 2 * (1 - Real.cos (charAngle L (a i)))

/-- The phase `exp(-i Σ_i 2π a_i w_i / L)` of a residue class `w`. -/
noncomputable def zdPhase (L : ℕ) (a : Fin d → ℕ) (w : Fin d → ZMod L) : ℂ :=
  Complex.exp (((-(∑ i, charAngle L (a i) * ((w i).val : ℤ)) : ℝ) : ℂ) * Complex.I)

theorem norm_zdPhase (L : ℕ) (a : Fin d → ℕ) (w : Fin d → ZMod L) : ‖zdPhase L a w‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem zdPhase_zero (L : ℕ) (w : Fin d → ZMod L) : zdPhase L 0 w = 1 := by
  simp [zdPhase, charAngle]

/-- `λ_a ≥ 16/L²` for `a ≠ 0` with every `a_i < L`. -/
theorem zdEigen_ge {L : ℕ} {a : Fin d → ℕ} (haL : ∀ i, a i < L) (ha : a ≠ 0) :
    16 / (L : ℝ) ^ 2 ≤ zdEigen L a := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  have hpos : 0 < a i := Nat.pos_of_ne_zero hi
  have h8 := one_sub_cos_charAngle_ge hpos (haL i)
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ 2 * (1 - Real.cos (charAngle L (a j))) :=
    fun j _ => by linarith [Real.cos_le_one (charAngle L (a j))]
  have hle := Finset.single_le_sum hnn (Finset.mem_univ i)
  have e : (16 : ℝ) / L ^ 2 = 2 * (8 / L ^ 2) := by ring
  unfold zdEigen
  linarith

/-- **The indicator of a residue class is an average of characters**:
`1_{y ≡ w} = L^{-d} Σ_{a ∈ {0, …, L-1}ᵈ} ψ_a(y) exp(-i Σ_i 2π a_i w_i/L)`. -/
theorem indicator_eq_sum_zdChar {L : ℕ} [NeZero L] (y : Vertex d) (w : Fin d → ZMod L) :
    (if (fun i => (y i : ZMod L)) = w then (1 : ℂ) else 0) =
      ((L : ℂ) ^ d)⁻¹ * ∑ a ∈ Fintype.piFinset fun _ : Fin d => Finset.range L,
        zdChar (zdAngle L a) y * zdPhase L a w := by
  have hL : 0 < L := NeZero.pos L
  have hLc : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  have hfac : ∀ a : Fin d → ℕ, zdChar (zdAngle L a) y * zdPhase L a w =
      ∏ i, Complex.exp (2 * Real.pi * Complex.I * (((a i : ℕ) : ℂ) *
        ((y i - (w i).val : ℤ) : ℂ)) / L) := by
    intro a
    have hterm : ∀ i, Complex.exp (2 * Real.pi * Complex.I * (((a i : ℕ) : ℂ) *
        ((y i - (w i).val : ℤ) : ℂ)) / L) =
        Complex.exp (((charAngle L (a i) * ((y i - (w i).val : ℤ) : ℝ) : ℝ) : ℂ) *
          Complex.I) := fun i => (exp_charAngle L (a i) _).symm
    rw [Finset.prod_congr rfl fun i _ => hterm i, ← Complex.exp_sum, zdChar, zdPhase,
      ← Complex.exp_add]
    congr 1
    simp only [zdAngle]
    push_cast
    rw [← add_mul, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hps := Finset.prod_univ_sum (fun _ : Fin d => Finset.range L)
    (fun i (j : ℕ) => Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) *
      ((y i - (w i).val : ℤ) : ℂ)) / L))
  rw [Finset.sum_congr rfl fun a _ => hfac a, ← hps]
  simp_rw [sum_range_exp_mul_eq hL]
  have e : ∀ i, ((L : ℤ) ∣ y i - ((w i).val : ℤ)) ↔ (y i : ZMod L) = w i := by
    intro i
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, eq_comm, Int.cast_natCast, ZMod.natCast_zmod_val]
  by_cases h : ∀ i, (y i : ZMod L) = w i
  · rw [if_pos (funext h), Finset.prod_congr rfl fun i _ => if_pos ((e i).2 (h i)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_mul_cancel₀ (pow_ne_zero d hLc)]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg (fun h' => hi (congrFun h' i)),
      Finset.prod_eq_zero (Finset.mem_univ i) (if_neg fun h' => hi ((e i).1 h')), mul_zero]

/-- The heat kernel on the characters `ψ_a`. -/
theorem hasSum_zdHeat_mul_char [NeZero d] (L : ℕ) (a : Fin d → ℕ) {t : ℝ} (ht : 0 ≤ t)
    (x : Vertex d) :
    HasSum (fun y => (zdHeat d t x y : ℂ) * zdChar (zdAngle L a) y)
      ((Real.exp (-(t * zdEigen L a)) : ℝ) * zdChar (zdAngle L a) x) :=
  hasSum_zdHeat_mul_zdChar (zdAngle L a) ht x

/-- **Dario, Lemma 3.2, Step 3**: for `g : (ℤ/L)ᵈ → ℝ` of sum zero,
`|Σ_y Φ(t, x, y) g(y mod L)| ≤ e^{-16 t/L²} Σ_w |g(w)|`. -/
theorem abs_tsum_zdHeat_mul_le [NeZero d] {L : ℕ} [NeZero L] (g : (Fin d → ZMod L) → ℝ)
    (hg : ∑ w, g w = 0) {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    |∑' y, zdHeat d t x y * g (fun i => (y i : ZMod L))| ≤
      Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
  have hL : 0 < L := NeZero.pos L
  set A := Fintype.piFinset fun _ : Fin d => Finset.range L with hA
  set E : (Fin d → ℕ) → ℂ := fun a =>
    ((Real.exp (-(t * zdEigen L a)) : ℝ) : ℂ) * zdChar (zdAngle L a) x with hE
  have hp0 : ∀ y, 0 ≤ zdHeat d t x y := fun y => zdHeat_nonneg ht x y
  have hsum : HasSum (fun y => ((zdHeat d t x y * g (fun i => (y i : ZMod L)) : ℝ) : ℂ))
      (∑ w, (g w : ℂ) * (((L : ℂ) ^ d)⁻¹ * ∑ a ∈ A, zdPhase L a w * E a)) := by
    have hrep : ∀ y, ((zdHeat d t x y * g (fun i => (y i : ZMod L)) : ℝ) : ℂ) =
        ∑ w, (g w : ℂ) * (((L : ℂ) ^ d)⁻¹ * ∑ a ∈ A,
          zdPhase L a w * ((zdHeat d t x y : ℂ) * zdChar (zdAngle L a) y)) := by
      intro y
      have hfy : (g (fun i => (y i : ZMod L)) : ℂ) = ∑ w, (g w : ℂ) *
          (if (fun i => (y i : ZMod L)) = w then (1 : ℂ) else 0) := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Complex.ofReal_mul, hfy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [indicator_eq_sum_zdChar]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [funext hrep]
    exact hasSum_sum fun w _ => ((hasSum_sum fun a _ =>
      (hasSum_zdHeat_mul_char L a ht x).mul_left (zdPhase L a w)).mul_left
        (((L : ℂ) ^ d)⁻¹)).mul_left (g w : ℂ)
  have hpsum : Summable fun y => zdHeat d t x y := by
    refine (ENNReal.summable_toReal (by rw [tsum_ofReal_zdHeat ht x]; exact ENNReal.one_ne_top)).congr
      fun y => ENNReal.toReal_ofReal (hp0 y)
  have hfb : ∀ y : Vertex d, |g (fun i => (y i : ZMod L))| ≤ ∑ w, |g w| := fun y =>
    Finset.single_le_sum (f := fun w => |g w|) (fun w _ => abs_nonneg _) (Finset.mem_univ _)
  have hreal : Summable fun y => zdHeat d t x y * g (fun i => (y i : ZMod L)) := by
    refine (hpsum.mul_right (∑ w, |g w|)).of_norm_bounded fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 y)]
    exact mul_le_mul_of_nonneg_left (hfb y) (hp0 y)
  have heq := (Complex.hasSum_ofReal.2 hreal.hasSum).unique hsum
  rw [← Real.norm_eq_abs, ← Complex.norm_real, heq]
  have hregroup : ∑ w, (g w : ℂ) * (((L : ℂ) ^ d)⁻¹ * ∑ a ∈ A, zdPhase L a w * E a) =
      ((L : ℂ) ^ d)⁻¹ * ∑ a ∈ A, (∑ w, (g w : ℂ) * zdPhase L a w) * E a := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hregroup]
  have hterm : ∀ a ∈ A, ‖(∑ w, (g w : ℂ) * zdPhase L a w) * E a‖ ≤
      Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
    intro a ha
    rw [hA, Fintype.mem_piFinset] at ha
    by_cases h0 : a = 0
    · subst h0
      simp_rw [zdPhase_zero, mul_one]
      rw [← Complex.ofReal_sum, hg, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hlam : 16 / (L : ℝ) ^ 2 ≤ zdEigen L a :=
        zdEigen_ge (fun i => Finset.mem_range.1 (ha i)) h0
      have hc' : ‖∑ w, (g w : ℂ) * zdPhase L a w‖ ≤ ∑ w, |g w| := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
        rw [norm_mul, norm_zdPhase, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [hE]
      simp only
      rw [norm_mul, norm_mul, norm_zdChar, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      refine mul_le_mul (Real.exp_le_exp.2 ?_) hc' (norm_nonneg _) (Real.exp_pos _).le
      have e : 16 * t / (L : ℝ) ^ 2 = t * (16 / (L : ℝ) ^ 2) := by ring
      rw [e]
      exact neg_le_neg (mul_le_mul_of_nonneg_left hlam ht)
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hcard : (A.card : ℝ) = (L : ℝ) ^ d := by
    rw [hA, Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
      Fintype.card_fin]
    push_cast
    rfl
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((L : ℝ) ^ d)⁻¹ * ‖∑ a ∈ A, (∑ w, (g w : ℂ) * zdPhase L a w) * E a‖
      ≤ ((L : ℝ) ^ d)⁻¹ * ∑ _a ∈ A, Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
          (by positivity)
    _ = Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w, |g w| := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc, inv_mul_cancel₀ hLd.ne', one_mul]

/-- The representative `(w_i.val)_i ∈ {0, …, L-1}ᵈ` of a residue class modulo `L`. -/
def zdResidueRep {L : ℕ} (w : Fin d → ZMod L) : Vertex d := fun i => ((w i).val : ℤ)

/-- **Dario, Lemma 3.2, Step 3, for periodic functions**: if `f` is `L`-periodic in every
direction with sum zero over `{0, …, L-1}ᵈ`, then `|Φ_t * f(x)| ≤ e^{-16t/L²} Σ_{period} |f|`. -/
theorem abs_tsum_zdHeat_mul_periodic_le [NeZero d] {L : ℕ} [NeZero L] {f : Vertex d → ℝ}
    (hper : ∀ y z : Vertex d, (∀ i, (L : ℤ) ∣ y i - z i) → f y = f z)
    (h0 : ∑ w : Fin d → ZMod L, f (zdResidueRep w) = 0) {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    |∑' y, zdHeat d t x y * f y| ≤
      Real.exp (-(16 * t / (L : ℝ) ^ 2)) * ∑ w : Fin d → ZMod L, |f (zdResidueRep w)| := by
  have key : ∀ a : ℤ, (L : ℤ) ∣ a - (((a : ZMod L)).val : ℤ) := fun a => by
    rw [ZMod.val_intCast]
    exact ⟨a / L, by have := Int.mul_ediv_add_emod a L; linarith⟩
  have hf : ∀ y, f y = f (zdResidueRep fun i => (y i : ZMod L)) :=
    fun y => hper _ _ fun i => key (y i)
  have e : (fun y => zdHeat d t x y * f y) =
      fun y => zdHeat d t x y * f (zdResidueRep fun i => (y i : ZMod L)) :=
    funext fun y => by rw [← hf y]
  rw [e]
  exact abs_tsum_zdHeat_mul_le (fun w => f (zdResidueRep w)) h0 ht x

/-- **Dario, Lemma 3.2, Step 3, as used**: for `f` which is `3^k`-periodic with sum zero over a
period and `9^k ≤ r`, `|Φ_{r²} * f(x)| ≤ e^{-16 r} Σ_{period} |f|`. -/
theorem abs_tsum_zdHeat_mul_periodic_le_exp [NeZero d] {k : ℕ} {f : Vertex d → ℝ}
    (hper : ∀ y z : Vertex d, (∀ i, ((3 ^ k : ℕ) : ℤ) ∣ y i - z i) → f y = f z)
    (h0 : ∑ w : Fin d → ZMod (3 ^ k), f (zdResidueRep w) = 0) {r : ℝ} (hr : 0 < r)
    (hkr : (9 : ℝ) ^ k ≤ r) (x : Vertex d) :
    |∑' y, zdHeat d (r ^ 2) x y * f y| ≤
      Real.exp (-(16 * r)) * ∑ w : Fin d → ZMod (3 ^ k), |f (zdResidueRep w)| := by
  haveI : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have h := abs_tsum_zdHeat_mul_periodic_le hper h0 (sq_nonneg r) x
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (Finset.sum_nonneg fun w _ => abs_nonneg _))
  have hL : (((3 ^ k : ℕ) : ℝ)) ^ 2 = (9 : ℝ) ^ k := by
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hL, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  nlinarith

end Rigidity.Corrector.GeneralDim
