import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul

/-!
# Quadratic functions of the slope and the deterministic part of Lemma 5.3, in every dimension

A function `g` of the slope `x ∈ ℝᵈ` is quadratic (`IsSlopeQuadratic`) when it equals its
polarization, `g(x) = (1/2) ∑_{i,j} xᵢ xⱼ (g(eᵢ + eⱼ) - g(eᵢ) - g(eⱼ))`. Its gradient is
`∇g(x)ᵢ = ∑ⱼ (g(eᵢ + eⱼ) - g(eᵢ) - g(eⱼ)) xⱼ` (`slopeGrad`), with `x · ∇g(x) = 2 g(x)` and
`g(x - t r) = g(x) - t r · ∇g(x) + t² g(r)`.

Lemma 5.3 of Armstrong and Dario is deterministic once its random errors are named: for a
quadratic `g` (here `-μ(□, ·)`) and a function `h` (here `ν(□, ·)`) with

* the comparison `q · p ≤ g(q) + h(p) + Y |p|₁ |q|₁` (Corollary 4.6, display (4.29)),
* the upper bound `g(r) ≤ Λ |r|²` (Lemma 4.4), and
* `h(B q) + g(q) - q · B q ≤ ρ |q|²` (the definition of `ω` with `B = ā⁻¹`),

one has `|g(q) - (1/2) q · B q| ≤ (d/2) (2 d Y S + √(4 d Λ (ρ + Y S))) |q|²`, where `S` bounds the
`ℓ¹` operator norm of `B` (`abs_slopeQuadratic_sub_half_le`). The proof is that of the
two-dimensional version `Rigidity.Proofs.Cluster.abs_quadratic_sub_half_le`: the function
`x ↦ h(p) + g(x) - x · p`, `p = B q`, is quadratic, is bounded below by the comparison and is at
most `ρ |q|²` at `x = q`; a gradient step of length `1/(2Λ)` from `q` shows that `r = ∇g(q) - p`
is small, and `g(q) - (1/2) q · p = (1/2) q · r`. The gradient step replaces the minimizer `q₀` of
Armstrong and Dario, which needs the lower bound `k(□)` of display (5.7).
-/

open scoped Matrix

namespace Rigidity.Percolation

variable {d : ℕ}

/-- The polarization coefficient `g(eᵢ + eⱼ) - g(eᵢ) - g(eⱼ)` of a function of the slope. -/
noncomputable def slopePolar (g : (Fin d → ℝ) → ℝ) (i j : Fin d) : ℝ :=
  g (Pi.single i 1 + Pi.single j 1) - g (Pi.single i 1) - g (Pi.single j 1)

/-- **A quadratic function of the slope**: `g` equals its polarization,
`g(x) = (1/2) ∑_{i,j} xᵢ xⱼ (g(eᵢ + eⱼ) - g(eᵢ) - g(eⱼ))`. -/
def IsSlopeQuadratic (g : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x, g x = 1 / 2 * ∑ i, ∑ j, x i * x j * slopePolar g i j

theorem slopePolar_comm (g : (Fin d → ℝ) → ℝ) (i j : Fin d) :
    slopePolar g i j = slopePolar g j i := by
  simp only [slopePolar, add_comm (Pi.single i 1 : Fin d → ℝ)]
  ring

/-- The gradient `∇g(x)` of a quadratic function of the slope, in coordinates. -/
noncomputable def slopeGrad (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ j, slopePolar g i j * x j

theorem sum_mul_slopeGrad (g : (Fin d → ℝ) → ℝ) (x r : Fin d → ℝ) :
    ∑ i, r i * slopeGrad g x i = ∑ i, ∑ j, r i * x j * slopePolar g i j := by
  simp only [slopeGrad, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `x · ∇g(x) = 2 g(x)`. -/
theorem IsSlopeQuadratic.sum_mul_slopeGrad_self {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (x : Fin d → ℝ) : ∑ i, x i * slopeGrad g x i = 2 * g x := by
  rw [sum_mul_slopeGrad, hg x]
  ring

/-- `g(x - t r) = g(x) - t r · ∇g(x) + t² g(r)`. -/
theorem IsSlopeQuadratic.sub_smul {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (x r : Fin d → ℝ) (t : ℝ) :
    g (x - t • r) = g x - t * ∑ i, r i * slopeGrad g x i + t ^ 2 * g r := by
  have hsym : ∑ i, ∑ j, x i * r j * slopePolar g i j =
      ∑ i, ∑ j, r i * x j * slopePolar g i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [slopePolar_comm]
      ring
  have hterm : ∀ i j, (x - t • r) i * (x - t • r) j * slopePolar g i j =
      x i * x j * slopePolar g i j - t * (x i * r j * slopePolar g i j) -
        t * (r i * x j * slopePolar g i j) + t ^ 2 * (r i * r j * slopePolar g i j) := by
    intro i j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hexp : ∑ i, ∑ j, (x - t • r) i * (x - t • r) j * slopePolar g i j =
      ∑ i, ∑ j, x i * x j * slopePolar g i j - t * ∑ i, ∑ j, x i * r j * slopePolar g i j -
        t * ∑ i, ∑ j, r i * x j * slopePolar g i j +
          t ^ 2 * ∑ i, ∑ j, r i * r j * slopePolar g i j := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hg (x - t • r), hexp, hsym, sum_mul_slopeGrad, hg x, hg r]
  ring

theorem IsSlopeQuadratic.apply_zero {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g) : g 0 = 0 := by
  rw [hg 0]
  simp

/-- The matrix `(1/2) (g(eᵢ + eⱼ) - g(eᵢ) - g(eⱼ))` of a quadratic function of the slope. -/
noncomputable def slopeMatrix (g : (Fin d → ℝ) → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => slopePolar g i j / 2

/-- A quadratic function is `x ↦ x · M x` with `M` its matrix. -/
theorem IsSlopeQuadratic.eq_dotProduct {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (x : Fin d → ℝ) : g x = ∑ i, x i * (slopeMatrix g *ᵥ x) i := by
  rw [hg x]
  simp only [Matrix.mulVec, dotProduct, slopeMatrix, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **`x ↦ x · A x` is quadratic** for every matrix `A`. -/
theorem isSlopeQuadratic_of_eq_dotProduct {g : (Fin d → ℝ) → ℝ} (A : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ x, g x = ∑ i, x i * (A *ᵥ x) i) : IsSlopeQuadratic g := by
  have hq : ∀ u v : Fin d → ℝ, ∑ k, (u + v) k * (A *ᵥ (u + v)) k =
      ∑ k, u k * (A *ᵥ u) k + ∑ k, v k * (A *ᵥ v) k +
        (∑ k, u k * (A *ᵥ v) k + ∑ k, v k * (A *ᵥ u) k) := by
    intro u v
    simp only [Matrix.mulVec_add, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hs : ∀ a b : Fin d, ∑ k, (Pi.single a 1 : Fin d → ℝ) k * (A *ᵥ Pi.single b 1) k =
      A a b := by
    intro a b
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hP : ∀ i j, slopePolar g i j = A i j + A j i := by
    intro i j
    simp only [slopePolar, h]
    rw [hq, hs, hs, hs, hs]
    ring
  intro x
  have e1 : ∑ i, x i * (A *ᵥ x) i = ∑ i, ∑ j, x i * x j * A i j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, ∑ j, x i * x j * A j i = ∑ i, ∑ j, x i * x j * A i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i, ∑ j, x i * x j * slopePolar g i j =
      ∑ i, ∑ j, x i * x j * A i j + ∑ i, ∑ j, x i * x j * A j i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [hP]
        ring
  rw [h x, e1, e3, e2]
  ring

theorem isSlopeQuadratic_dotProduct_mulVec (A : Matrix (Fin d) (Fin d) ℝ) :
    IsSlopeQuadratic fun x => ∑ i, x i * (A *ᵥ x) i :=
  isSlopeQuadratic_of_eq_dotProduct A fun _ => rfl

theorem isSlopeQuadratic_zero : IsSlopeQuadratic fun _ : Fin d → ℝ => (0 : ℝ) :=
  isSlopeQuadratic_of_eq_dotProduct 0 fun x => by simp

theorem IsSlopeQuadratic.add {f g : (Fin d → ℝ) → ℝ} (hf : IsSlopeQuadratic f)
    (hg : IsSlopeQuadratic g) : IsSlopeQuadratic fun x => f x + g x :=
  isSlopeQuadratic_of_eq_dotProduct (slopeMatrix f + slopeMatrix g) fun x => by
    rw [hf.eq_dotProduct x, hg.eq_dotProduct x]
    simp only [Matrix.add_mulVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem IsSlopeQuadratic.neg {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g) :
    IsSlopeQuadratic fun x => -g x :=
  isSlopeQuadratic_of_eq_dotProduct (-slopeMatrix g) fun x => by
    rw [hg.eq_dotProduct x]
    simp only [Matrix.neg_mulVec, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem IsSlopeQuadratic.sub {f g : (Fin d → ℝ) → ℝ} (hf : IsSlopeQuadratic f)
    (hg : IsSlopeQuadratic g) : IsSlopeQuadratic fun x => f x - g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- Quadratic functions are stable under composition with matrices. -/
theorem IsSlopeQuadratic.comp_mulVec {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (B : Matrix (Fin d) (Fin d) ℝ) : IsSlopeQuadratic fun x => g (B *ᵥ x) :=
  isSlopeQuadratic_of_eq_dotProduct (Bᵀ * slopeMatrix g * B) fun x => by
    rw [hg.eq_dotProduct (B *ᵥ x)]
    change (B *ᵥ x) ⬝ᵥ (slopeMatrix g *ᵥ (B *ᵥ x)) = x ⬝ᵥ ((Bᵀ * slopeMatrix g * B) *ᵥ x)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Bᵀ,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]

/-- **A quadratic function is bounded by its matrix**: `|g(x)| ≤ (∑_{i,j} |Mᵢⱼ|) |x|²`. -/
theorem IsSlopeQuadratic.abs_le {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (x : Fin d → ℝ) : |g x| ≤ (∑ i, ∑ j, |slopeMatrix g i j|) * ∑ i, x i ^ 2 := by
  rw [hg.eq_dotProduct x]
  have e1 : ∑ i, x i * (slopeMatrix g *ᵥ x) i = ∑ i, ∑ j, x i * (slopeMatrix g i j * x j) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  have e2 : (∑ i, ∑ j, |slopeMatrix g i j|) * ∑ i, x i ^ 2 =
      ∑ i, ∑ j, |slopeMatrix g i j| * ∑ k, x k ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  rw [e1, e2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  have hi : x i ^ 2 ≤ ∑ k, x k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i)
  have hj : x j ^ 2 ≤ ∑ k, x k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
  have hij : |x i| * |x j| ≤ ∑ k, x k ^ 2 := by
    nlinarith [sq_abs (x i), sq_abs (x j), sq_nonneg (|x i| - |x j|)]
  rw [abs_mul, abs_mul]
  calc |x i| * (|slopeMatrix g i j| * |x j|) = |slopeMatrix g i j| * (|x i| * |x j|) := by ring
    _ ≤ |slopeMatrix g i j| * ∑ k, x k ^ 2 := mul_le_mul_of_nonneg_left hij (abs_nonneg _)

/-- `|B v|₁ ≤ (∑_{i,j} |Bᵢⱼ|) |v|₁`. -/
theorem sum_abs_mulVec_le (B : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    ∑ i, |(B *ᵥ v) i| ≤ (∑ i, ∑ j, |B i j|) * ∑ i, |v i| := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun k _ => abs_nonneg (v k)) (Finset.mem_univ j)) (abs_nonneg _)

theorem IsSlopeQuadratic.const_mul {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g) (c : ℝ) :
    IsSlopeQuadratic fun x => c * g x :=
  isSlopeQuadratic_of_eq_dotProduct (c • slopeMatrix g) fun x => by
    rw [hg.eq_dotProduct x, Matrix.smul_mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

theorem isSlopeQuadratic_sum_sq : IsSlopeQuadratic fun x : Fin d → ℝ => ∑ i, x i ^ 2 :=
  isSlopeQuadratic_of_eq_dotProduct 1 fun x => by
    rw [Matrix.one_mulVec]
    exact Finset.sum_congr rfl fun i _ => sq (x i)

/-- `g(c r) = c² g(r)`. -/
theorem IsSlopeQuadratic.smul {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g) (c : ℝ)
    (r : Fin d → ℝ) : g (c • r) = c ^ 2 * g r := by
  have h := hg.sub_smul 0 r (-c)
  have e : (0 : Fin d → ℝ) - (-c) • r = c • r := by
    rw [neg_smul, sub_neg_eq_add, zero_add]
  have hgrad : ∀ i, slopeGrad g 0 i = 0 := fun i => by simp [slopeGrad]
  rw [e] at h
  rw [h, hg.apply_zero]
  simp only [hgrad, mul_zero, Finset.sum_const_zero]
  ring

/-- For a nonnegative quadratic function, `g(a + b) ≤ (1 + t) g(a) + (1 + 1/t) g(b)`, `t > 0`. -/
theorem IsSlopeQuadratic.add_le_of_nonneg {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (h0 : ∀ x, 0 ≤ g x) (a b : Fin d → ℝ) {t : ℝ} (ht : 0 < t) :
    g (a + b) ≤ (1 + t) * g a + (1 + 1 / t) * g b := by
  have h1 := hg.sub_smul b a t
  have h2 := hg.sub_smul b a (-1)
  have e : b - (-1 : ℝ) • a = a + b := by
    rw [neg_smul, one_smul, sub_neg_eq_add, add_comm]
  rw [e] at h2
  have hnn := h0 (b - t • a)
  set X := ∑ i, a i * slopeGrad g b i with hX
  have hX1 : t * X ≤ g b + t * (t * g a) := by nlinarith
  have hX2 : X ≤ 1 / t * g b + t * g a := by
    have : X ≤ (g b + t * (t * g a)) / t := by
      rw [le_div_iff₀ ht]
      linarith
    refine this.trans (le_of_eq ?_)
    field_simp
  rw [h2]
  nlinarith

/-- For a nonnegative quadratic function, `g(∑_{i ∈ s} vᵢ) ≤ |s| ∑_{i ∈ s} g(vᵢ)`. -/
theorem IsSlopeQuadratic.sum_le_of_nonneg {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (h0 : ∀ x, 0 ≤ g x) {ι : Type*} (s : Finset ι) (v : ι → Fin d → ℝ) :
    g (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, g (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hg.apply_zero]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj]
    rcases Nat.eq_zero_or_pos s.card with hk | hk
    · have hs : s = ∅ := Finset.card_eq_zero.1 hk
      subst hs
      simp
    · have hk' : (0 : ℝ) < s.card := by exact_mod_cast hk
      have h := hg.add_le_of_nonneg h0 (v j) (∑ i ∈ s, v i) hk'
      have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ 1 + 1 / (s.card : ℝ))
      have e : (1 + 1 / (s.card : ℝ)) * ((s.card : ℝ) * ∑ i ∈ s, g (v i)) =
          ((s.card : ℝ) + 1) * ∑ i ∈ s, g (v i) := by
        field_simp
      push_cast
      nlinarith [h0 (v j)]

/-- **A nonnegative quadratic function is controlled by its values at the unit vectors**:
`g(q) ≤ d |q|² ∑ᵢ g(eᵢ)`. -/
theorem IsSlopeQuadratic.le_of_nonneg {g : (Fin d → ℝ) → ℝ} (hg : IsSlopeQuadratic g)
    (h0 : ∀ x, 0 ≤ g x) (q : Fin d → ℝ) :
    g q ≤ d * (∑ i, q i ^ 2) * ∑ i, g (Pi.single i 1) := by
  have hq : q = ∑ i, q i • (Pi.single i 1 : Fin d → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h := hg.sum_le_of_nonneg h0 Finset.univ (fun i => q i • (Pi.single i 1 : Fin d → ℝ))
  beta_reduce at h
  rw [← hq, Finset.card_univ, Fintype.card_fin] at h
  refine h.trans ?_
  simp only [hg.smul]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (h0 _)
  exact Finset.single_le_sum (fun j _ => sq_nonneg (q j)) (Finset.mem_univ i)

/-- `|x|² ≤ |x|₁²`. -/
theorem sum_sq_le_sq_sum_abs_vec (x : Fin d → ℝ) : ∑ i, x i ^ 2 ≤ (∑ i, |x i|) ^ 2 := by
  have e : (∑ i, |x i|) ^ 2 = ∑ i, |x i| * ∑ j, |x j| := by rw [sq, Finset.sum_mul]
  rw [e]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)) (abs_nonneg _)

/-- `|x|₁² ≤ d |x|²`. -/
theorem sq_sum_abs_le_card_mul (x : Fin d → ℝ) : (∑ i, |x i|) ^ 2 ≤ d * ∑ i, x i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
  simpa only [Finset.card_univ, Fintype.card_fin, sq_abs] using h

/-- `|x · y| ≤ |x|₁ |y|₁`. -/
theorem abs_sum_mul_le_sum_abs_mul (x y : Fin d → ℝ) :
    |∑ i, x i * y i| ≤ (∑ i, |x i|) * ∑ i, |y i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)) (abs_nonneg _)

/-- `x ≤ (β + √α) Q` when `x² ≤ α Q² + β Q x` with `x, Q, α, β ≥ 0`. -/
theorem le_add_sqrt_mul_of_sq_le {x Q α β : ℝ} (hQ : 0 ≤ Q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h : x ^ 2 ≤ α * Q ^ 2 + β * Q * x) : x ≤ (β + √α) * Q := by
  by_contra hlt
  have hlt := not_le.1 hlt
  have hs := Real.sq_sqrt hα
  have hs0 := Real.sqrt_nonneg α
  have h1 : √α * Q ≤ x := by nlinarith [mul_nonneg hβ hQ]
  have h2 : α * Q ^ 2 ≤ √α * Q * x := by
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hQ)
    nlinarith
  have h3 : (β + √α) * Q * x < x * x := mul_lt_mul_of_pos_right hlt
    (lt_of_le_of_lt (mul_nonneg (add_nonneg hβ hs0) hQ) hlt)
  nlinarith

/-- **The deterministic content of Lemma 5.3 of Armstrong and Dario** (every dimension). -/
theorem abs_slopeQuadratic_sub_half_le (hd : 0 < d) {g h : (Fin d → ℝ) → ℝ}
    (hg : IsSlopeQuadratic g) (B : Matrix (Fin d) (Fin d) ℝ) {S Y Λ ρ : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ v : Fin d → ℝ, ∑ i, |(B *ᵥ v) i| ≤ S * ∑ i, |v i|)
    (hY : 0 ≤ Y) (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (hcomp : ∀ p q : Fin d → ℝ,
      ∑ i, q i * p i ≤ g q + h p + Y * ((∑ i, |p i|) * ∑ i, |q i|))
    (hup : ∀ r : Fin d → ℝ, g r ≤ Λ * ∑ i, r i ^ 2)
    (hω : ∀ q : Fin d → ℝ, h (B *ᵥ q) + g q - ∑ i, q i * (B *ᵥ q) i ≤ ρ * ∑ i, q i ^ 2)
    (q : Fin d → ℝ) :
    |g q - 1 / 2 * ∑ i, q i * (B *ᵥ q) i| ≤
      d / 2 * (2 * d * Y * S + √(4 * d * Λ * (ρ + Y * S))) * ∑ i, q i ^ 2 := by
  set p := B *ᵥ q with hp
  set r : Fin d → ℝ := slopeGrad g q - p with hr
  set t : ℝ := 1 / (2 * Λ) with ht
  have ht0 : 0 < t := by positivity
  set Q := ∑ i, |q i| with hQ
  set P := ∑ i, |p i| with hP
  set R := ∑ i, |r i| with hR
  set N := ∑ i, r i ^ 2 with hN
  set Nq := ∑ i, q i ^ 2 with hNq
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hPQ : P ≤ S * Q := hS q
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 hd
  -- the gradient step
  have hstep := hg.sub_smul q r t
  have hdot : ∑ i, (q - t • r) i * p i = ∑ i, q i * p i - t * ∑ i, r i * p i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hrr : ∑ i, r i * slopeGrad g q i - ∑ i, r i * p i = N := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [hr, Pi.sub_apply]
      ring
  have hc := hcomp p (q - t • r)
  rw [hdot, hstep] at hc
  have hgr := hup r
  have hωq := hω q
  rw [← hp] at hωq
  have hqr : ∑ i, |(q - t • r) i| ≤ Q + t * R := by
    rw [hQ, hR, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc |q i - t * r i| ≤ |q i| + |t * r i| := abs_sub _ _
      _ = |q i| + t * |r i| := by rw [abs_mul, abs_of_pos ht0]
  have htΛ : t * Λ = 1 / 2 := by
    rw [ht]
    field_simp
  have hYP : 0 ≤ Y * P := mul_nonneg hY hP0
  have key : t / 2 * N ≤ ρ * Nq + Y * P * (Q + t * R) := by
    have a := mul_le_mul_of_nonneg_left hqr hYP
    have b := mul_le_mul_of_nonneg_left hgr (sq_nonneg t)
    have e : t * N - t ^ 2 * (Λ * N) = t / 2 * N := by
      have : t ^ 2 * (Λ * N) = t * (t * Λ) * N := by ring
      rw [this, htΛ]
      ring
    have e2 : t * ∑ i, r i * slopeGrad g q i - t * ∑ i, r i * p i = t * N := by
      rw [← mul_sub, hrr]
    nlinarith
  have hNqQ : Nq ≤ Q ^ 2 := sum_sq_le_sq_sum_abs_vec q
  have hRN : R ^ 2 ≤ d * N := sq_sum_abs_le_card_mul r
  have hmain : R ^ 2 ≤ 4 * d * Λ * (ρ + Y * S) * Q ^ 2 + 2 * d * Y * S * Q * R := by
    have k1 : t / 2 * N ≤ ρ * Q ^ 2 + Y * S * Q * (Q + t * R) := by
      have a : ρ * Nq ≤ ρ * Q ^ 2 := mul_le_mul_of_nonneg_left hNqQ hρ
      have b : Y * P * (Q + t * R) ≤ Y * (S * Q) * (Q + t * R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQ hY) (by positivity)
      nlinarith
    have k2 := mul_le_mul_of_nonneg_left k1 (by positivity : (0 : ℝ) ≤ 4 * d * Λ)
    have e1 : 4 * d * Λ * (t / 2 * N) = d * N := by
      have : 4 * d * Λ * (t / 2 * N) = 2 * d * (t * Λ) * N := by ring
      rw [this, htΛ]
      ring
    have e2 : 4 * d * Λ * (ρ * Q ^ 2 + Y * S * Q * (Q + t * R)) =
        4 * d * Λ * (ρ + Y * S) * Q ^ 2 + 2 * d * Y * S * Q * R := by
      have : 4 * d * Λ * (ρ * Q ^ 2 + Y * S * Q * (Q + t * R)) =
          4 * d * Λ * (ρ + Y * S) * Q ^ 2 + 4 * d * Y * S * Q * R * (t * Λ) := by ring
      rw [this, htΛ]
      ring
    rw [e1, e2] at k2
    linarith
  have hRle : R ≤ (2 * d * Y * S + √(4 * d * Λ * (ρ + Y * S))) * Q :=
    le_add_sqrt_mul_of_sq_le hQ0 (by positivity) (by positivity) hmain
  -- `g(q) - (1/2) q · p = (1/2) q · r`
  have hid : g q - 1 / 2 * ∑ i, q i * p i = 1 / 2 * ∑ i, q i * r i := by
    have h2 := hg.sum_mul_slopeGrad_self q
    have e : ∑ i, q i * r i = ∑ i, q i * slopeGrad g q i - ∑ i, q i * p i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [hr, Pi.sub_apply]
        ring
    rw [e, h2]
    ring
  rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  set K := 2 * d * Y * S + √(4 * d * Λ * (ρ + Y * S)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hqr' : |∑ i, q i * r i| ≤ Q * (K * Q) :=
    (abs_sum_mul_le_sum_abs_mul q r).trans (mul_le_mul_of_nonneg_left hRle hQ0)
  have hQ2 : Q ^ 2 ≤ d * Nq := sq_sum_abs_le_card_mul q
  calc 1 / 2 * |∑ i, q i * r i| ≤ 1 / 2 * (Q * (K * Q)) := by linarith
    _ = 1 / 2 * K * Q ^ 2 := by ring
    _ ≤ 1 / 2 * K * (d * Nq) := mul_le_mul_of_nonneg_left hQ2 (by positivity)
    _ = d / 2 * K * Nq := by ring

end Rigidity.Percolation
