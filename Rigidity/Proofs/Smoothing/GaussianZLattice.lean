import Rigidity.Proofs.Smoothing.GaussianShiftInequality

/-!
# Gaussian shifts on integer lattices

The Gaussian shift inequality holds for any full-rank integer lattice, independently of a chosen
basis. This is Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian
measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

open Module

namespace Rigidity.Smoothing

/-- A translated Gaussian on an integer lattice has no more mass than the unshifted Gaussian. -/
theorem gaussian_shift_le_of_isZLattice {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {a : ℝ} (ha : 0 < a) (x : E) :
    Summable (fun z : L => Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ∧
    Summable (fun z : L => Real.exp (-a * ‖(z : E)‖ ^ 2)) ∧
    (∑' z : L, Real.exp (-a * ‖(z : E) + x‖ ^ 2)) ≤
      ∑' z : L, Real.exp (-a * ‖(z : E)‖ ^ 2) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  letI : Fintype (Module.Free.ChooseBasisIndex ℤ L) := Fintype.ofFinite _
  have hb : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) = L :=
    b.ofZLatticeBasis_span ℝ
  rw [← hb]
  exact gaussian_shift_le (b.ofZLatticeBasis ℝ) ha x

end Rigidity.Smoothing
