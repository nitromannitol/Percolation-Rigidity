import Rigidity.Proofs.Regularity.ClusterBallGeometry

/-!
# Quadratic functions on cluster balls

For the case `k = 1` of Armstrong–Dario, Lemma 7.2 (arXiv:1609.09431v2), the iteration runs one
degree higher, with the quadratic polynomials `Ā_2`. This file provides the quadratic forms
`quadForm M v = ∑ᵢ ∑ⱼ Mᵢⱼ vᵢ vⱼ` on `ℝ^d` with their polarization `quadPolar`, the bounds by the
largest entry of the symmetric part of `M`, the second difference
`q(y + h) + q(y - h) - 2 q(y) = 2 q(h)`, and a vector `e` with `‖e‖² ≤ 2` on which `|q(e)|` is at
least any entry of the symmetric part (`exists_le_abs_quadForm`).
-/

namespace Rigidity.Proofs.Regularity

open LatticeProb LatticeProb.Percolation Rigidity.External

variable {d : ℕ}

/-- The quadratic form `v ↦ ∑ᵢ ∑ⱼ Mᵢⱼ vᵢ vⱼ`. -/
def quadForm (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, M i j * v i * v j

/-- The polarization `(u, v) ↦ ∑ᵢ ∑ⱼ Mᵢⱼ (uᵢ vⱼ + vᵢ uⱼ)` of `quadForm M`. -/
def quadPolar (M : Matrix (Fin d) (Fin d) ℝ) (u v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, M i j * (u i * v j + v i * u j)

/-- The symmetric part `(Mᵢⱼ + Mⱼᵢ) / 2`. -/
noncomputable def symEntry (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) : ℝ := (M i j + M j i) / 2

theorem quadForm_add (M : Matrix (Fin d) (Fin d) ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    quadForm M (u + v) = quadForm M u + quadForm M v + quadPolar M u v := by
  simp only [quadForm, quadPolar, PiLp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quadForm_smul (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quadForm M (t • v) = t ^ 2 * quadForm M v := by
  simp only [quadForm, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quadForm_neg (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quadForm M (-v) = quadForm M v := by
  have := quadForm_smul M (-1) v
  rwa [neg_one_smul, neg_one_sq, one_mul] at this

theorem quadPolar_neg_right (M : Matrix (Fin d) (Fin d) ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    quadPolar M u (-v) = -quadPolar M u v := by
  simp only [quadPolar, PiLp.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Second difference** of a quadratic form. -/
theorem quadForm_add_add_sub (M : Matrix (Fin d) (Fin d) ℝ) (y h : EuclideanSpace ℝ (Fin d)) :
    quadForm M (y + h) + quadForm M (y - h) - 2 * quadForm M y = 2 * quadForm M h := by
  have h1 := quadForm_add M y h
  have h2 := quadForm_add M y (-h)
  rw [quadForm_neg, quadPolar_neg_right] at h2
  rw [show y - h = y + -h from sub_eq_add_neg y h, h1, h2]
  ring

theorem quadForm_eq_symEntry (M : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    quadForm M v = ∑ i, ∑ j, symEntry M i j * v i * v j := by
  have h : ∑ i, ∑ j, M j i * v i * v j = ∑ i, ∑ j, M i j * v i * v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e : ∑ i, ∑ j, symEntry M i j * v i * v j =
      (∑ i, ∑ j, M i j * v i * v j + ∑ i, ∑ j, M j i * v i * v j) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [symEntry]
    ring
  rw [e, h, quadForm]
  ring

theorem quadPolar_eq_symEntry (M : Matrix (Fin d) (Fin d) ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    quadPolar M u v = ∑ i, ∑ j, 2 * symEntry M i j * u i * v j := by
  have h : ∑ i, ∑ j, M i j * (v i * u j) = ∑ i, ∑ j, M j i * u i * v j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e : quadPolar M u v = ∑ i, ∑ j, M i j * u i * v j + ∑ i, ∑ j, M i j * (v i * u j) := by
    simp only [quadPolar, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [symEntry]
  ring

theorem sum_abs_le_sqrt_mul_norm (v : EuclideanSpace ℝ (Fin d)) :
    ∑ i, |v i| ≤ Real.sqrt d * ‖v‖ := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |v i|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
  have hn : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [← hn] at h
  have h0 : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc ∑ i, |v i| = Real.sqrt ((∑ i, |v i|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (d * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt d * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Bound of the polarization by the largest entry of the symmetric part. -/
theorem abs_quadPolar_le (M : Matrix (Fin d) (Fin d) ℝ) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ i j, |symEntry M i j| ≤ m) (u v : EuclideanSpace ℝ (Fin d)) :
    |quadPolar M u v| ≤ 2 * d * m * ‖u‖ * ‖v‖ := by
  rw [quadPolar_eq_symEntry]
  have hu := sum_abs_le_sqrt_mul_norm u
  have hv := sum_abs_le_sqrt_mul_norm v
  have hsd := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) d)
  calc |∑ i, ∑ j, 2 * symEntry M i j * u i * v j|
      ≤ ∑ i, ∑ j, |2 * symEntry M i j * u i * v j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, 2 * m * (|u i| * |v j|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul, abs_mul, abs_two]
        have := hm i j
        have h1 : 0 ≤ |u i| * |v j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        nlinarith
    _ = 2 * m * ((∑ i, |u i|) * (∑ j, |v j|)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 2 * m * ((Real.sqrt d * ‖u‖) * (Real.sqrt d * ‖v‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hu hv (Finset.sum_nonneg fun j _ => abs_nonneg _) (by positivity)
    _ = 2 * d * m * ‖u‖ * ‖v‖ := by
        have : Real.sqrt d * ‖u‖ * (Real.sqrt d * ‖v‖) = (Real.sqrt d * Real.sqrt d) * ‖u‖ * ‖v‖ :=
          by ring
        rw [this, hsd]; ring

/-- Bound of the quadratic form by the largest entry of the symmetric part. -/
theorem abs_quadForm_le (M : Matrix (Fin d) (Fin d) ℝ) {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ i j, |symEntry M i j| ≤ m) (v : EuclideanSpace ℝ (Fin d)) :
    |quadForm M v| ≤ d * m * ‖v‖ ^ 2 := by
  have h2 : quadForm M v = quadPolar M v v / 2 := by
    rw [quadForm, quadPolar, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h2, abs_div, abs_two]
  have := abs_quadPolar_le M hm0 hm v v
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem quadForm_single (M : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    quadForm M (EuclideanSpace.single i 1) = M i i := by
  simp [quadForm]

theorem quadPolar_single (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    quadPolar M (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 2 * symEntry M i j := by
  rw [quadPolar_eq_symEntry]
  simp

/-- A vector `e` with `‖e‖ ≤ 2` and `|q(e)| ≥ |(Mᵢⱼ + Mⱼᵢ)/2|`. -/
theorem exists_le_abs_quadForm (M : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ ≤ 2 ∧ |symEntry M i j| ≤ |quadForm M e| := by
  have hn : ∀ k : Fin d, ‖(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 :=
    fun k => by simp
  rcases eq_or_ne i j with hij | hij
  · subst hij
    refine ⟨EuclideanSpace.single i 1, by rw [hn]; norm_num, ?_⟩
    rw [quadForm_single, symEntry]
    exact le_of_eq (by ring_nf)
  set a : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  set b : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single j 1
  have h1 := quadForm_add M a b
  have h2 := quadForm_add M a (-b)
  rw [quadForm_neg, quadPolar_neg_right] at h2
  have hP := quadPolar_single M i j
  have hdiff : quadForm M (a + b) - quadForm M (a + -b) = 4 * symEntry M i j := by
    rw [h1, h2, hP]; ring
  have hna : ‖a + b‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hn, hn]; norm_num)
  have hnb : ‖a + -b‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_neg, hn, hn]; norm_num)
  by_contra hcon
  push Not at hcon
  have c1 := (hcon (a + b) hna)
  have c2 := (hcon (a + -b) hnb)
  have habs : |4 * symEntry M i j| ≤ |quadForm M (a + b)| + |quadForm M (a + -b)| := by
    rw [← hdiff]; exact abs_sub _ _
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at habs
  have := abs_nonneg (symEntry M i j)
  linarith

end Rigidity.Proofs.Regularity
