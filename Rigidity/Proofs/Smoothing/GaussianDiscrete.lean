import Rigidity.Proofs.Smoothing.GaussianZLattice
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Gaussian shifts on discrete submodules

The Gaussian shift inequality extends to integer lattices of arbitrary rank by passing to their
real span and projecting the shift orthogonally onto that span. This is the general-rank form of
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

open Module

namespace Rigidity.Smoothing

/-- A Gaussian on a discrete integer submodule has maximal mass at the origin. -/
theorem gaussian_shift_le_of_discrete {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) (x : E) :
    Summable (fun z : L => Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ∧
    Summable (fun z : L => Real.exp (-a * ‖(z : E)‖ ^ 2)) ∧
    (∑' z : L, Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ≤
      ∑' z : L, Real.exp (-a * ‖(z : E)‖ ^ 2) := by
  let V := Submodule.span ℝ (L : Set E)
  let K : Submodule ℤ V := ZLattice.comap ℝ L V.subtype
  letI : DiscreteTopology K := ZLattice.comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
  let e : K ≃ₗ[ℤ] L :=
    Submodule.comapSubtypeEquivOfLe (p := L) (q := V.restrictScalars ℤ) Submodule.subset_span
  letI : IsZLattice ℝ K :=
    ⟨Submodule.map_injective_of_injective V.subtype_injective (by simp [V, K])⟩
  let xp : V := V.orthogonalProjectionOnto x
  have hk := gaussian_shift_le_of_isZLattice K ha xp
  have hpoint (z : K) : Real.exp (-a * ‖(e z : E) + x‖ ^ 2) ≤
      Real.exp (-a * ‖(z : V) + xp‖ ^ 2) := by
    have hp : V.orthogonalProjectionOnto ((e z : E) + x) = (z : V) + xp := by
      rw [map_add]
      congr 1
      exact V.orthogonalProjectionOnto_mem_subspace_eq_self (z : V)
    have hn := V.norm_orthogonalProjectionOnto_apply_le ((e z : E) + x)
    rw [hp] at hn
    have hs : ‖(z : V) + xp‖ ^ 2 ≤ ‖(e z : E) + x‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hs)]
  have hshift := summable_gaussian_add L ha x
  have hunshift := summable_gaussian L ha
  have hcomp := hshift.comp_injective e.injective
  refine ⟨hshift, hunshift, ?_⟩
  calc
    (∑' z : L, Real.exp (-a * ‖(z : E) + x‖ ^ 2)) =
        ∑' z : K, Real.exp (-a * ‖(e z : E) + x‖ ^ 2) :=
      (e.toEquiv.tsum_eq _).symm
    _ ≤ ∑' z : K, Real.exp (-a * ‖(z : V) + xp‖ ^ 2) :=
      hcomp.tsum_le_tsum hpoint hk.1
    _ ≤ ∑' z : K, Real.exp (-a * ‖(z : V)‖ ^ 2) := hk.2.2
    _ = ∑' z : K, Real.exp (-a * ‖(e z : E)‖ ^ 2) := by
      apply tsum_congr
      intro z
      rfl
    _ = ∑' z : L, Real.exp (-a * ‖(z : E)‖ ^ 2) :=
      e.toEquiv.tsum_eq (fun z : L => Real.exp (-a * ‖(z : E)‖ ^ 2))

end Rigidity.Smoothing
