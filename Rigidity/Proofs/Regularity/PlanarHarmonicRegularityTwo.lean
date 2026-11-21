import Rigidity.Proofs.Regularity.PlanarHarmonicRegularity
import Rigidity.Proofs.Regularity.ContinuumBallExcessTwo
import Rigidity.Proofs.Regularity.LatticeHarmonicExcessTwo

/-!
# Excess decay of order two of harmonic functions in the plane

The harmonic quadratic polynomials of the plane are the functions
`x ↦ a + Re(q₁ ζ) + Re(q₂ ζ²)`, `ζ = planarEquiv.symm x` (`planarHarmonicQuadratic`); they are
quadratic functions of `x` (`planarHarmonicQuadratic_le_continuumQuadratic`, with
`Re(q ζ²) = q_M(x)` for `M = planarQuadMatrix q`) and contain the affine functions. For `v`
harmonic on `B_r(z)` and `w` a harmonic quadratic polynomial, the second-order Taylor expansion of
the planar harmonic function `(v - w) ∘ planarEquiv` gives a harmonic quadratic polynomial within
`C (s/r)³ ‖v - w‖_{L̲²(B_r)}` of `v` on `B_s`, `s < r / 8`: the excess decay of order two
(`harmonicRegularity_two_planarHarmonicClass`). With the excess decay of order one this gives
Lemma 7.2 of Armstrong and Dario for `k = 1` in the plane with only the harmonic approximation
hypothesis (`armstrongDario_lemma_7_2_one_planar`).
-/

open MeasureTheory Metric Complex

namespace Rigidity.Proofs.Regularity

theorem planarEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    planarEquiv.symm x = (x 0 : ℂ) + (x 1 : ℂ) * I :=
  Complex.orthonormalBasisOneI_repr_symm_apply x

theorem re_mul_planarEquiv_symm (q : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    (q * planarEquiv.symm x).re = inner ℝ (planarEquiv (starRingEnd ℂ q)) x := by
  conv_rhs => rw [← planarEquiv.apply_symm_apply x]
  rw [planarEquiv.inner_map_map, Complex.inner, Complex.conj_conj, mul_comm]

/-- The matrix of the quadratic form `x ↦ Re(q ζ²)`. -/
def planarQuadMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![q.re, -q.im; -q.im, -q.re]

theorem re_mul_sq_planarEquiv_symm (q : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    (q * planarEquiv.symm x ^ 2).re = quadForm (planarQuadMatrix q) x := by
  rw [planarEquiv_symm_apply]
  simp [quadForm, Fin.sum_univ_two, planarQuadMatrix, sq, Complex.mul_re, Complex.mul_im]
  ring

/-- The harmonic quadratic polynomials of the plane, `Ā_2`. -/
def planarHarmonicQuadratic : AddSubgroup (locallySqIntegrable 2) where
  carrier := {f | ∃ (a : ℝ) (q₁ q₂ : ℂ), ∀ x, (f : EuclideanSpace ℝ (Fin 2) → ℝ) x =
    a + (q₁ * planarEquiv.symm x).re + (q₂ * planarEquiv.symm x ^ 2).re}
  add_mem' := by
    rintro f g ⟨a, q₁, q₂, hf⟩ ⟨b, r₁, r₂, hg⟩
    refine ⟨a + b, q₁ + r₁, q₂ + r₂, fun x => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, hf, hg, add_mul, add_re]
    ring
  zero_mem' := ⟨0, 0, 0, fun _ => by simp⟩
  neg_mem' := by
    rintro f ⟨a, q₁, q₂, hf⟩
    refine ⟨-a, -q₁, -q₂, fun x => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, hf, neg_mul, neg_re]
    ring

theorem planarHarmonicQuadratic_le_continuumQuadratic :
    planarHarmonicQuadratic ≤ continuumQuadratic 2 := by
  rintro f ⟨a, q₁, q₂, hf⟩
  exact ⟨a, planarEquiv (starRingEnd ℂ q₁), planarQuadMatrix q₂, fun x => by
    rw [hf, re_mul_planarEquiv_symm, re_mul_sq_planarEquiv_symm]⟩

theorem continuumAffine_le_planarHarmonicQuadratic :
    continuumAffine 2 ≤ planarHarmonicQuadratic := by
  rintro f ⟨a, p, hf⟩
  refine ⟨a, starRingEnd ℂ (planarEquiv.symm p), 0, fun x => ?_⟩
  rw [hf, re_mul_planarEquiv_symm, Complex.conj_conj, LinearIsometryEquiv.apply_symm_apply]
  simp

theorem harmonicOnNhd_planarHarmonicQuadratic {f : locallySqIntegrable 2}
    (hf : f ∈ planarHarmonicQuadratic) (s : Set ℂ) :
    InnerProductSpace.HarmonicOnNhd
      (fun ζ : ℂ => (f : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) s := by
  obtain ⟨a, q₁, q₂, hf⟩ := hf
  have e : (fun ζ : ℂ => (f : EuclideanSpace ℝ (Fin 2) → ℝ) (planarEquiv ζ)) =
      fun ζ => ((a : ℂ) + q₁ * ζ + q₂ * ζ ^ 2).re := by
    funext ζ
    rw [hf, LinearIsometryEquiv.symm_apply_apply]
    simp [add_re]
  rw [e]
  intro ζ _
  exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add
    (analyticAt_const.mul (analyticAt_id.pow 2))).harmonicAt_re

end Rigidity.Proofs.Regularity
