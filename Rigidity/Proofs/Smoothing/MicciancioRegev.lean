import Rigidity.Proofs.Smoothing.DualMassBound
import Rigidity.Proofs.Smoothing.DualLatticeCharacterization
import Rigidity.Proofs.Smoothing.DualCoordinates
import Rigidity.Proofs.Smoothing.ZeroRank

/-!
# The lattice smoothing parameter

Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*,
SIAM J. Comput. 37 (2007), no. 1, 267–302, doi:10.1137/S0097539705447360, Lemma 3.3,
bounds the Gaussian mass of the nonzero dual lattice
at the smoothing scale. The lattice is taken in the real span of its independent generators.
-/

open Module

namespace Rigidity.Smoothing

/-- The smoothing parameter bound of Micciancio and Regev, Lemma 3.3. -/
theorem micciancio_regev_smoothing : Rigidity.External.MicciancioRegevSmoothing := by
  classical
  intro N k b hb r hbr ε hε s hs
  by_cases hk : k = 0
  · subst k
    exact Rigidity.External.smoothing_fin_zero N b ε s hε
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let i : Fin k := ⟨0, hkpos⟩
    have hr : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr (hb.ne_zero i)) (hbr i)
    let V := Submodule.span ℝ (Set.range b)
    letI : DecidableEq V := Classical.decEq V
    let bV : Basis (Fin k) ℝ V := Basis.span hb
    let L : Submodule ℤ V := Submodule.span ℤ (Set.range (frequencyBasis bV))
    have hbrV : ∀ j, ‖bV j‖ ≤ r := by
      intro j
      rw [Submodule.coe_norm]
      have h : ((bV j : V) : EuclideanSpace ℝ (Fin N)) = b j := Basis.coe_span_apply hb j
      rw [h]
      exact hbr j
    have hmem (y : V) : y ∈ L ↔ (y : EuclideanSpace ℝ (Fin N)) ∈ Rigidity.External.dualLattice b := by
      change y ∈ Submodule.span ℤ (Set.range (frequencyBasis bV)) ↔ _
      rw [mem_span_frequencyBasis_iff]
      change (∀ j, ∃ z : ℤ, inner ℝ y (bV j) = z) ↔
        (y : EuclideanSpace ℝ (Fin N)) ∈ V ∧ ∀ j, ∃ z : ℤ, inner ℝ (y : EuclideanSpace ℝ (Fin N)) (b j) = z
      have hcoord (j : Fin k) : ((bV j : V) : EuclideanSpace ℝ (Fin N)) = b j :=
        Basis.coe_span_apply hb j
      constructor
      · intro h
        refine ⟨y.2, ?_⟩
        intro j
        obtain ⟨z, hz⟩ := h j
        exact ⟨z, by simpa only [Submodule.coe_inner, hcoord] using hz⟩
      · rintro ⟨_, h⟩ j
        obtain ⟨z, hz⟩ := h j
        exact ⟨z, by simpa only [Submodule.coe_inner, hcoord] using hz⟩
    have hmass := gaussian_dual_fin_mass_le k hkpos bV r hr hbrV ε hε s hs
    let e : {y : L // y ≠ 0} ≃
        {y : EuclideanSpace ℝ (Fin N) // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0} := {
      toFun := fun y => ⟨((y.1 : V) : EuclideanSpace ℝ (Fin N)),
        ⟨(hmem y.1).mp y.1.2, by
          intro h
          apply y.2
          apply Subtype.ext
          apply Subtype.ext
          exact h⟩⟩
      invFun := fun y => ⟨⟨⟨y.1, y.2.1.1⟩, (hmem (⟨y.1, y.2.1.1⟩ : V)).mpr y.2.1⟩, by
        intro h
        apply y.2.2
        exact congrArg (fun z : L => ((z : V) : EuclideanSpace ℝ (Fin N))) h⟩
      left_inv := fun y => by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := fun y => by
        apply Subtype.ext
        rfl }
    have heval (y : {y : L // y ≠ 0}) :
        ((e y : {y : EuclideanSpace ℝ (Fin N) // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0}) :
          EuclideanSpace ℝ (Fin N)) = (((y.1 : L) : V) : EuclideanSpace ℝ (Fin N)) := rfl
    let f : L → ℝ := fun y => Real.exp (-(Real.pi * s ^ 2) * ‖(y : V)‖ ^ 2)
    have hsub : (∑' y : {y : L // y ≠ 0}, f y.1) ≤ ε := by
      have heq : (∑' y : {y : L // y ≠ 0}, f y.1) =
          ∑' y : L, if y = 0 then 0 else f y := by
        calc
          (∑' y : {y : L // y ≠ 0}, f y.1) =
              ∑' y : L, ({y : L | y ≠ 0}).indicator f y := tsum_subtype _ _
          _ = ∑' y : L, if y = 0 then 0 else f y := by
            apply tsum_congr
            intro y
            by_cases hy : y = 0 <;> simp [hy, Set.indicator]
      rw [heq]
      simpa only [f] using hmass.2
    refine ⟨summable_dualLattice_of_scale_bound N k b hb r hbr ε hε s hs, ?_⟩
    calc
      (∑' y : {y // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0},
          Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2))) =
          ∑' y : {y : L // y ≠ 0}, f y.1 := by
        simpa only [f, heval, Submodule.coe_norm, neg_mul] using
          (e.tsum_eq (fun y : {y // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0} =>
            Real.exp (-(Real.pi * s ^ 2 * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2)))).symm
      _ ≤ ε := hsub

end Rigidity.Smoothing
