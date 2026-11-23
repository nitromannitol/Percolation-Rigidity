import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The heat kernel of the variable speed random walk on a graph of bounded degree

For a locally finite graph `G` with degrees at most `D > 0`, the variable speed random walk has
the generator `Δ u(x) = Σ_{z ∼ x} (u(z) - u(x))` (Dario–Gu, (1.1), with unit conductances). With
the lazy kernel `Q(x, z) = 1/D` for `z ∼ x` and `Q(x, x) = 1 - deg x / D` one has `Δ = D (Q - I)`,
so that the heat kernel is the Poisson average
`p_t(x, y) = Σ_n e^{-Dt} (Dt)^n / n! · Q^n(x, y)`.

This file proves the defining properties of the heat kernel of Dario–Gu, (1.2): `p_0(x, y) = δ_{xy}`
and `∂_t p_t(x, y) = Δ_x p_t(x, y)` for every `t`, together with `0 ≤ p_t(x, y) ≤ 1` for `t ≥ 0`.
-/

open scoped Classical
open Finset Filter

namespace Rigidity.Green

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ)

/-- The powers `Q^n(x, y)` of the lazy kernel `Q(x, z) = 1/D` for `z ∼ x`,
`Q(x, x) = 1 - deg x / D`, acting on the first variable. -/
noncomputable def lazyPow : ℕ → V → V → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | n + 1 => fun x y => (1 - (G.degree x : ℝ) / D) * lazyPow n x y +
      (1 / (D : ℝ)) * ∑ z ∈ G.neighborFinset x, lazyPow n z y

theorem lazyPow_zero (x y : V) : lazyPow G D 0 x y = if x = y then 1 else 0 := rfl

theorem lazyPow_succ (n : ℕ) (x y : V) :
    lazyPow G D (n + 1) x y = (1 - (G.degree x : ℝ) / D) * lazyPow G D n x y +
      (1 / (D : ℝ)) * ∑ z ∈ G.neighborFinset x, lazyPow G D n z y := rfl

/-- The Poisson weight `e^{-Dt} (Dt)^n / n!`. -/
noncomputable def poissonWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-D * t) * (D * t) ^ n / n.factorial

/-- The shifted Poisson weight: `0` at `n = 0` and `e^{-Dt} (Dt)^{n-1} / (n-1)!` otherwise. -/
noncomputable def poissonWeightPrev (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => poissonWeight D t n

/-- The heat kernel `p_t(x, y) = Σ_n e^{-Dt} (Dt)^n / n! · Q^n(x, y)` of the variable speed random
walk. -/
noncomputable def vsrwHeat (t : ℝ) (x y : V) : ℝ :=
  ∑' n, poissonWeight D t n * lazyPow G D n x y

variable {G D}

/-- `0 ≤ Q^n(x, y) ≤ 1`. -/
theorem lazyPow_mem_Icc (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) :
    ∀ n x y, 0 ≤ lazyPow G D n x y ∧ lazyPow G D n x y ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro x y
    rw [lazyPow_zero]
    split_ifs <;> norm_num
  | succ n ih =>
    intro x y
    rw [lazyPow_succ]
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hdx : (G.degree x : ℝ) ≤ D := by exact_mod_cast hdeg x
    have ha : 0 ≤ 1 - (G.degree x : ℝ) / D := by
      rw [sub_nonneg, div_le_one hDr]
      exact hdx
    have hsum0 : 0 ≤ ∑ z ∈ G.neighborFinset x, lazyPow G D n z y :=
      sum_nonneg fun z _ => (ih z y).1
    have hsum1 : ∑ z ∈ G.neighborFinset x, lazyPow G D n z y ≤ G.degree x := by
      calc ∑ z ∈ G.neighborFinset x, lazyPow G D n z y
          ≤ ∑ _z ∈ G.neighborFinset x, (1 : ℝ) := sum_le_sum fun z _ => (ih z y).2
        _ = G.degree x := by rw [sum_const, G.card_neighborFinset_eq_degree]; simp
    have hb : (0 : ℝ) ≤ 1 / D := by positivity
    constructor
    · exact add_nonneg (mul_nonneg ha (ih x y).1) (mul_nonneg hb hsum0)
    · calc (1 - (G.degree x : ℝ) / D) * lazyPow G D n x y +
            1 / D * ∑ z ∈ G.neighborFinset x, lazyPow G D n z y
          ≤ (1 - (G.degree x : ℝ) / D) * 1 + 1 / D * G.degree x :=
            add_le_add (mul_le_mul_of_nonneg_left (ih x y).2 ha)
              (mul_le_mul_of_nonneg_left hsum1 hb)
        _ = 1 := by field_simp; ring

theorem poissonWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ poissonWeight D t n := by
  unfold poissonWeight
  positivity

theorem abs_poissonWeight_le (t : ℝ) (n : ℕ) :
    |poissonWeight D t n| ≤ Real.exp (-D * t) * (|(D : ℝ) * t| ^ n / n.factorial) := by
  unfold poissonWeight
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), Nat.abs_cast, mul_div_assoc]

/-- The Poisson weights sum to one. -/
theorem hasSum_poissonWeight (t : ℝ) : HasSum (poissonWeight D t) 1 := by
  have h := NormedSpace.expSeries_div_hasSum_exp ((D : ℝ) * t)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-D * t))
  have he : Real.exp (-D * t) * Real.exp (D * t) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  rw [he] at h2
  have hf : poissonWeight D t = fun i => Real.exp (-D * t) * (((D : ℝ) * t) ^ i / i.factorial) := by
    funext n
    unfold poissonWeight
    ring
  rw [hf]
  exact h2

theorem summable_poissonWeight_mul {t : ℝ} {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) :
    Summable fun n => poissonWeight D t n * c n := by
  refine Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial |(D : ℝ) * t|).mul_left (Real.exp (-D * t))) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |poissonWeight D t n| * |c n| ≤ |poissonWeight D t n| * 1 :=
        mul_le_mul_of_nonneg_left (hc n) (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact abs_poissonWeight_le t n

theorem abs_lazyPow_le (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (n : ℕ) (x y : V) :
    |lazyPow G D n x y| ≤ 1 := by
  obtain ⟨h0, h1⟩ := lazyPow_mem_Icc hD hdeg n x y
  rw [abs_of_nonneg h0]
  exact h1

theorem summable_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (t : ℝ) (x y : V) :
    Summable fun n => poissonWeight D t n * lazyPow G D n x y :=
  summable_poissonWeight_mul fun n => abs_lazyPow_le hD hdeg n x y

/-- `p_0(x, y) = δ_{xy}`. -/
theorem vsrwHeat_zero (x y : V) : vsrwHeat G D 0 x y = if x = y then 1 else 0 := by
  rw [vsrwHeat, tsum_eq_single 0]
  · simp [poissonWeight, lazyPow_zero]
  · intro n hn
    simp [poissonWeight, zero_pow hn]

/-- `0 ≤ p_t(x, y)` for `t ≥ 0`. -/
theorem vsrwHeat_nonneg (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x y : V) : 0 ≤ vsrwHeat G D t x y :=
  tsum_nonneg fun n => mul_nonneg (poissonWeight_nonneg ht n) (lazyPow_mem_Icc hD hdeg n x y).1

/-- `p_t(x, y) ≤ 1` for `t ≥ 0`. -/
theorem vsrwHeat_le_one (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) {t : ℝ} (ht : 0 ≤ t)
    (x y : V) : vsrwHeat G D t x y ≤ 1 := by
  rw [vsrwHeat, ← (hasSum_poissonWeight (D := D) t).tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_vsrwHeat hD hdeg t x y)
    (hasSum_poissonWeight t).summable
  calc poissonWeight D t n * lazyPow G D n x y ≤ poissonWeight D t n * 1 :=
        mul_le_mul_of_nonneg_left (lazyPow_mem_Icc hD hdeg n x y).2 (poissonWeight_nonneg ht n)
    _ = poissonWeight D t n := mul_one _

/-- `∂_t e^{-Dt} (Dt)^n / n! = D (e^{-Dt} (Dt)^{n-1} / (n-1)! - e^{-Dt} (Dt)^n / n!)`. -/
theorem hasDerivAt_poissonWeight (t : ℝ) (n : ℕ) :
    HasDerivAt (fun t => poissonWeight D t n)
      (D * poissonWeightPrev D t n - D * poissonWeight D t n) t := by
  have h0 : HasDerivAt (fun x : ℝ => -(D : ℝ) * x) (-(D : ℝ) * 1) t :=
    (hasDerivAt_id' t).const_mul (-(D : ℝ))
  have h1 : HasDerivAt (fun x => Real.exp (-(D : ℝ) * x)) (Real.exp (-(D : ℝ) * t) * (-(D : ℝ) * 1))
      t := HasDerivAt.exp h0
  have hc : HasDerivAt (fun x : ℝ => (D : ℝ) * x) ((D : ℝ) * 1) t :=
    (hasDerivAt_id' t).const_mul (D : ℝ)
  have h2 : HasDerivAt (fun x => ((D : ℝ) * x) ^ n)
      ((n : ℝ) * ((D : ℝ) * t) ^ (n - 1) * ((D : ℝ) * 1)) t := HasDerivAt.pow hc n
  have h3 : HasDerivAt (fun x => Real.exp (-(D : ℝ) * x) * ((D : ℝ) * x) ^ n / (n.factorial : ℝ))
      ((Real.exp (-(D : ℝ) * t) * (-(D : ℝ) * 1) * ((D : ℝ) * t) ^ n +
        Real.exp (-(D : ℝ) * t) * ((n : ℝ) * ((D : ℝ) * t) ^ (n - 1) * ((D : ℝ) * 1))) /
          (n.factorial : ℝ)) t :=
    HasDerivAt.div_const (HasDerivAt.mul h1 h2) _
  refine (h3 : HasDerivAt (fun t => poissonWeight D t n) _ t).congr_deriv ?_
  cases n with
  | zero =>
    simp only [poissonWeight, poissonWeightPrev, pow_zero, Nat.factorial_zero, Nat.cast_one,
      Nat.cast_zero, zero_mul, mul_zero, add_zero, div_one, mul_one]
    ring
  | succ n =>
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    simp only [poissonWeight, poissonWeightPrev, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `|e^{-Ds} (Ds)^n / n!| ≤ e^{DR} (DR)^n / n!` for `|s| < R`. -/
theorem abs_poissonWeight_le_of_abs_lt {s R : ℝ} (hs : |s| < R) (n : ℕ) :
    |poissonWeight D s n| ≤ Real.exp (D * R) * ((D * R) ^ n / n.factorial) := by
  refine (abs_poissonWeight_le s n).trans ?_
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have h1 : Real.exp (-D * s) ≤ Real.exp (D * R) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le s) hD0, mul_le_mul_of_nonneg_left hs.le hD0]
  have h2 : |(D : ℝ) * s| ^ n ≤ ((D : ℝ) * R) ^ n := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hs.le hD0) n
  gcongr

/-- The shifted bound: `0` at `n = 0`, `e^{DR} (DR)^{n-1} / (n-1)!` otherwise. -/
noncomputable def poissonBoundPrev (D : ℕ) (R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => Real.exp (D * R) * ((D * R) ^ n / n.factorial)

theorem summable_poissonBoundPrev (R : ℝ) : Summable (poissonBoundPrev D R) := by
  rw [← summable_nat_add_iff 1]
  exact (Real.summable_pow_div_factorial ((D : ℝ) * R)).mul_left _

theorem abs_poissonWeightPrev_le {s R : ℝ} (hs : |s| < R) (n : ℕ) :
    |poissonWeightPrev D s n| ≤ poissonBoundPrev D R n := by
  cases n with
  | zero => simp [poissonWeightPrev, poissonBoundPrev]
  | succ n => exact abs_poissonWeight_le_of_abs_lt hs n

/-- **The heat equation** `∂_t p_t(x, y) = Δ_x p_t(x, y) = Σ_{z ∼ x} (p_t(z, y) - p_t(x, y))`. -/
theorem hasDerivAt_vsrwHeat (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D) (t : ℝ) (x y : V) :
    HasDerivAt (fun t => vsrwHeat G D t x y)
      (∑ z ∈ G.neighborFinset x, (vsrwHeat G D t z y - vsrwHeat G D t x y)) t := by
  set R := |t| + 1 with hR
  have htR : t ∈ Set.Ioo (-R) R := by
    rw [Set.mem_Ioo]
    constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
  set u : ℕ → ℝ := fun n => D * (poissonBoundPrev D R n +
    Real.exp (D * R) * ((D * R) ^ n / n.factorial)) with hu
  have hus : Summable u :=
    ((summable_poissonBoundPrev R).add
      ((Real.summable_pow_div_factorial ((D : ℝ) * R)).mul_left _)).mul_left _
  have hc := fun n => abs_lazyPow_le hD hdeg n x y
  have key := hasDerivAt_tsum_of_isPreconnected (u := u) hus isOpen_Ioo isPreconnected_Ioo
    (g := fun n s => poissonWeight D s n * lazyPow G D n x y)
    (g' := fun n s => (D * poissonWeightPrev D s n - D * poissonWeight D s n) * lazyPow G D n x y)
    (fun n s _ => (hasDerivAt_poissonWeight s n).mul_const _)
    (fun n s hs => by
      have hs' : |s| < R := abs_lt.2 ⟨(Set.mem_Ioo.1 hs).1, (Set.mem_Ioo.1 hs).2⟩
      rw [Real.norm_eq_abs, abs_mul]
      have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
      calc |(D : ℝ) * poissonWeightPrev D s n - D * poissonWeight D s n| * |lazyPow G D n x y|
          ≤ |(D : ℝ) * poissonWeightPrev D s n - D * poissonWeight D s n| * 1 :=
            mul_le_mul_of_nonneg_left (hc n) (abs_nonneg _)
        _ ≤ D * (|poissonWeightPrev D s n| + |poissonWeight D s n|) := by
            rw [mul_one, ← mul_sub, abs_mul, abs_of_nonneg hD0]
            exact mul_le_mul_of_nonneg_left (abs_sub _ _) hD0
        _ ≤ u n := mul_le_mul_of_nonneg_left (add_le_add (abs_poissonWeightPrev_le hs' n)
              (abs_poissonWeight_le_of_abs_lt hs' n)) hD0)
    htR (summable_vsrwHeat hD hdeg t x y) htR
  refine key.congr_deriv ?_
  -- identification of the derivative
  have hsP : ∀ z, Summable fun n => poissonWeight D t n * lazyPow G D n z y :=
    fun z => summable_vsrwHeat hD hdeg t z y
  have hsPrev : Summable fun n => poissonWeightPrev D t n * lazyPow G D n x y := by
    rw [← summable_nat_add_iff 1]
    exact summable_poissonWeight_mul fun n => abs_lazyPow_le hD hdeg (n + 1) x y
  have hshift : ∑' n, poissonWeightPrev D t n * lazyPow G D n x y =
      ∑' n, poissonWeight D t n * lazyPow G D (n + 1) x y := by
    rw [hsPrev.tsum_eq_zero_add]
    simp [poissonWeightPrev]
  have hA : Summable fun n =>
      poissonWeight D t n * ((1 - (G.degree x : ℝ) / D) * lazyPow G D n x y) :=
    ((hsP x).mul_left (1 - (G.degree x : ℝ) / D)).congr fun n => by ring
  have hB : Summable fun n =>
      poissonWeight D t n * (1 / (D : ℝ) * ∑ z ∈ G.neighborFinset x, lazyPow G D n z y) :=
    (summable_sum fun z _ => (hsP z).mul_left (1 / (D : ℝ))).congr fun n => by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
  have hsucc : ∑' n, poissonWeight D t n * lazyPow G D (n + 1) x y =
      (1 - (G.degree x : ℝ) / D) * vsrwHeat G D t x y +
        1 / D * ∑ z ∈ G.neighborFinset x, vsrwHeat G D t z y := by
    simp only [lazyPow_succ, mul_add]
    rw [Summable.tsum_add hA hB]
    congr 1
    · rw [vsrwHeat, ← tsum_mul_left]
      exact tsum_congr fun n => by ring
    · simp only [vsrwHeat]
      rw [← Summable.tsum_finsetSum fun z _ => hsP z, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
  have hsplit : ∑' n, (D * poissonWeightPrev D t n - D * poissonWeight D t n) *
      lazyPow G D n x y = D * ∑' n, poissonWeightPrev D t n * lazyPow G D n x y -
        D * vsrwHeat G D t x y := by
    rw [vsrwHeat, ← tsum_mul_left, ← tsum_mul_left,
      ← Summable.tsum_sub (hsPrev.mul_left _) ((hsP x).mul_left _)]
    exact tsum_congr fun n => by ring
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD' : (D : ℝ) ≠ 0 := hDr.ne'
  rw [hsplit, hshift, hsucc, Finset.sum_sub_distrib, Finset.sum_const,
    G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  field_simp
  ring

end Rigidity.Green
