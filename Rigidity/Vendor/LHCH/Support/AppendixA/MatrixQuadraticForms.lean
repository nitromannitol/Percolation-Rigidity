/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/MatrixQuadraticForms.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Quadratic forms and operator norms of real symmetric matrices

Facts about the quadratic form `p ⬝ᵥ (A *ᵥ p)` of a real `d × d` matrix `A` and its `L²` operator
norm: the bound `|p · A p| ≤ ‖A‖ |p|²`, the converse for symmetric matrices (the operator norm is
the supremum of the form on the unit sphere), the norm of the difference of two ordered forms, and
the fact that a symmetric matrix whose form is invariant under the coordinate permutations and
sign changes is scalar. Nothing about conductances or cubes is used here (Appendix A,
`s:homogenization`).
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace LatticeHC

variable {d : ℕ}

/-! ## Operator norm and quadratic forms -/

/-- The squared Euclidean norm of a vector is its dot product with itself. -/
theorem norm_toLp_sq (p : Fin d → ℝ) :
    ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖ ^ 2 = p ⬝ᵥ p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

/-- `|p · A p| ≤ ‖A‖ |p|²` for the `L²` operator norm. -/
theorem abs_dotProduct_mulVec_le_opNorm (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    |p ⬝ᵥ (A *ᵥ p)| ≤ ‖A‖ * (p ⬝ᵥ p) := by
  have h1 := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 p)
  have h2 : p ⬝ᵥ (A *ᵥ p) = inner ℝ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (A *ᵥ p)) := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [h2]
  calc |inner ℝ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))
        ((EuclideanSpace.equiv (Fin d) ℝ).symm (A *ᵥ p))|
      ≤ ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖ *
        ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A *ᵥ p)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖ *
        (‖A‖ * ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖A‖ * (p ⬝ᵥ p) := by rw [← norm_toLp_sq]; ring

/-- **Operator norm of a symmetric matrix from its quadratic form.** If `Y` is symmetric and
`|p · Y p| ≤ C |p|²` for all `p`, then `‖Y‖ ≤ C` (polarization: `4 p · Y y = (p + y) · Y (p + y) -
(p - y) · Y (p - y)` with `y = t Y p`). -/
theorem opNorm_le_of_abs_dotProduct_le {Y : Matrix (Fin d) (Fin d) ℝ} (hY : Y.IsSymm) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ p : Fin d → ℝ, |p ⬝ᵥ (Y *ᵥ p)| ≤ C * (p ⬝ᵥ p)) : ‖Y‖ ≤ C := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  set p : Fin d → ℝ := x.ofLp with hp
  set w : Fin d → ℝ := Y *ᵥ p with hw
  have hT : ((toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) Y) x =
      WithLp.toLp 2 w := rfl
  rw [hT]
  have hx : ‖x‖ = ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖ := by simp [hp]
  rw [hx]
  have hsymm : ∀ u v : Fin d → ℝ, u ⬝ᵥ (Y *ᵥ v) = v ⬝ᵥ (Y *ᵥ u) := by
    intro u v
    have : u ⬝ᵥ (Y *ᵥ v) = (Y *ᵥ u) ⬝ᵥ v := by
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hY.eq]
    rw [this, dotProduct_comm]
  have hb : p ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ w := by
    rw [hsymm p w]
  have hdot : ∀ t : ℝ, (p + t • w) ⬝ᵥ (Y *ᵥ (p + t • w)) =
      p ⬝ᵥ (Y *ᵥ p) + 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (Y *ᵥ w)) := by
    intro t
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hsymm w p, hb]
    ring
  have hdot' : ∀ t : ℝ, (p - t • w) ⬝ᵥ (Y *ᵥ (p - t • w)) =
      p ⬝ᵥ (Y *ᵥ p) - 2 * t * (w ⬝ᵥ w) + t ^ 2 * (w ⬝ᵥ (Y *ᵥ w)) := by
    intro t
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hsymm w p, hb]
    ring
  have hnorm : ∀ t : ℝ, (p + t • w) ⬝ᵥ (p + t • w) + (p - t • w) ⬝ᵥ (p - t • w) =
      2 * (p ⬝ᵥ p) + 2 * t ^ 2 * (w ⬝ᵥ w) := by
    intro t
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm w p]
    ring
  have hs2 : ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖ ^ 2 = p ⬝ᵥ p := norm_toLp_sq p
  have hr2 : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))‖ ^ 2 = w ⬝ᵥ w := norm_toLp_sq w
  set s := ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin d))‖ with hs
  set r := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin d))‖ with hr
  have hs0 : 0 ≤ s := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have key : ∀ t : ℝ, 2 * t * r ^ 2 ≤ C * (s ^ 2 + t ^ 2 * r ^ 2) := by
    intro t
    have h1 := (le_abs_self _).trans (h (p + t • w))
    have h2 := (neg_le_abs _).trans (h (p - t • w))
    rw [hdot] at h1
    rw [hdot'] at h2
    have h3 := hnorm t
    rw [hs2, hr2]
    nlinarith
  by_cases hr00 : r = 0
  · rw [hr00]; exact mul_nonneg hC hs0
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr00)
    have hspos : 0 < s := by
      rcases hs0.lt_or_eq with h' | h'
      · exact h'
      · exfalso
        have hp0 : p ⬝ᵥ p = 0 := by rw [← hs2, ← h']; ring
        have hpz : p = 0 := dotProduct_self_eq_zero.1 hp0
        have hw0 : w = 0 := by rw [hw, hpz, Matrix.mulVec_zero]
        apply hr00
        rw [hr, hw0]
        simp
    have := key (s / r)
    have hrr : (s / r) * r = s := div_mul_cancel₀ s hr00
    have h5 : 2 * (s / r) * r ^ 2 = 2 * s * r := by field_simp
    have h6 : (s / r) ^ 2 * r ^ 2 = s ^ 2 := by rw [← mul_pow, hrr]
    rw [h5, h6] at this
    nlinarith

/-- **Norm of a difference of ordered forms.** If `X, X'` are symmetric, `X'` has a nonnegative
form and `Γ⁻¹ X' ⪯ X ⪯ Γ X'` for `Γ ≥ 1`, then `‖X - X'‖ ≤ (Γ - 1) ‖X'‖`. -/
theorem opNorm_sub_le_of_ratio_forms {X X' : Matrix (Fin d) (Fin d) ℝ} (hX : X.IsSymm)
    (hX' : X'.IsSymm) {Γ : ℝ} (hΓ : 1 ≤ Γ) (hpos : ∀ p : Fin d → ℝ, 0 ≤ p ⬝ᵥ (X' *ᵥ p))
    (hlo : ∀ p : Fin d → ℝ, Γ⁻¹ * (p ⬝ᵥ (X' *ᵥ p)) ≤ p ⬝ᵥ (X *ᵥ p))
    (hhi : ∀ p : Fin d → ℝ, p ⬝ᵥ (X *ᵥ p) ≤ Γ * (p ⬝ᵥ (X' *ᵥ p))) :
    ‖X - X'‖ ≤ (Γ - 1) * ‖X'‖ := by
  have hΓ0 : 0 < Γ := by linarith
  have hC : 0 ≤ (Γ - 1) * ‖X'‖ := mul_nonneg (by linarith) (norm_nonneg _)
  refine opNorm_le_of_abs_dotProduct_le (hX.sub hX') hC fun p => ?_
  have hq := hpos p
  have hb : p ⬝ᵥ (X' *ᵥ p) ≤ ‖X'‖ * (p ⬝ᵥ p) :=
    (le_abs_self _).trans (abs_dotProduct_mulVec_le_opNorm X' p)
  have hΓinv : 1 - Γ⁻¹ ≤ Γ - 1 := by
    have h1 : Γ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΓ
    have h2 : 0 < Γ⁻¹ := inv_pos.2 hΓ0
    have h3 : Γ * Γ⁻¹ = 1 := mul_inv_cancel₀ hΓ0.ne'
    nlinarith
  have hy : p ⬝ᵥ ((X - X') *ᵥ p) = p ⬝ᵥ (X *ᵥ p) - p ⬝ᵥ (X' *ᵥ p) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [hy, abs_le]
  have h1 := hlo p
  have h2 := hhi p
  have h3 : (Γ - 1) * (p ⬝ᵥ (X' *ᵥ p)) ≤ (Γ - 1) * (‖X'‖ * (p ⬝ᵥ p)) :=
    mul_le_mul_of_nonneg_left hb (by linarith)
  constructor
  · nlinarith
  · nlinarith

/-! ## Linear algebra -/

/-- **A symmetric matrix whose quadratic form is invariant under the coordinate permutations
and the sign changes is scalar.** Proof: the off-diagonal entries from `p = e_k + e_j` and the
reflection in `k`, the diagonal ones from the transposition `(i j)`. -/
theorem eq_smul_one_of_signed_perm_invariant {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsSymm)
    (hperm : ∀ (σ : Equiv.Perm (Fin d)) (p : Fin d → ℝ),
      (fun i => p (σ.symm i)) ⬝ᵥ (S *ᵥ fun i => p (σ.symm i)) = p ⬝ᵥ (S *ᵥ p))
    (hrefl : ∀ (k : Fin d) (p : Fin d → ℝ),
      (fun i => if i = k then -p i else p i) ⬝ᵥ (S *ᵥ fun i => if i = k then -p i else p i) =
        p ⬝ᵥ (S *ᵥ p)) :
    ∃ s : ℝ, S = s • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  classical
  have hsymm : ∀ i j, S j i = S i j := fun i j => by
    simpa using congrFun (congrFun hS i) j
  -- the quadratic form on basis vectors
  have hdiag : ∀ i, (Pi.single i 1 : Fin d → ℝ) ⬝ᵥ (S *ᵥ Pi.single i 1) = S i i := fun i => by
    simp
  have hoff : ∀ i j, (Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) ⬝ᵥ
      (S *ᵥ (Pi.single i 1 + Pi.single j 1)) = S i i + S j j + 2 * S i j := fun i j => by
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single_one,
      single_dotProduct, one_mul]
    simp [hsymm i j]
    ring
  have hoff' : ∀ i j, (-Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) ⬝ᵥ
      (S *ᵥ (-Pi.single i 1 + Pi.single j 1)) = S i i + S j j - 2 * S i j := fun i j => by
    simp only [Matrix.mulVec_add, Matrix.mulVec_neg, dotProduct_add, add_dotProduct,
      dotProduct_neg, neg_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul]
    simp [hsymm i j]
    ring
  have hzero : ∀ i j, i ≠ j → S i j = 0 := fun i j hij => by
    have h := hrefl i (Pi.single i 1 + Pi.single j 1)
    have e : (fun l => if l = i then -(Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) l
        else (Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) l) = -Pi.single i 1 + Pi.single j 1 := by
      funext l
      by_cases hl : l = i
      · subst hl; simp [hij]
      · simp [hl]
    rw [e, hoff', hoff] at h
    linarith
  have heq : ∀ i j, S i i = S j j := fun i j => by
    have h := hperm (Equiv.swap i j) (Pi.single i 1)
    have e : (fun l => (Pi.single i 1 : Fin d → ℝ) ((Equiv.swap i j).symm l)) = Pi.single j 1 := by
      funext l
      have : (Equiv.swap i j l = i) ↔ (l = j) := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      simp only [Pi.single_apply, Equiv.symm_swap, this]
    rw [e, hdiag, hdiag] at h
    exact h.symm
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, Subsingleton.elim _ _⟩
  · refine ⟨S ⟨0, hd⟩ ⟨0, hd⟩, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [heq i ⟨0, hd⟩]
    · simp [hzero i j hij, Matrix.one_apply_ne hij]

end LatticeHC
