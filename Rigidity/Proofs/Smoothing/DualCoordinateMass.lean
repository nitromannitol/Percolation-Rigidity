import Rigidity.Proofs.Smoothing.PairingSliceMass
import Rigidity.Proofs.Smoothing.IntegerCoordinates

/-!
# Coordinate mass bounds on a dual lattice

The dual basis identifies pairings with a real basis as integer coordinates. The nonzero slices of
each coordinate satisfy the Gaussian mass estimate used in Micciancio and Regev, *Worst-case to
average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

open Module

namespace Rigidity.Smoothing

/-- Integer coordinates of a vector in the integer span of the dual basis. -/
noncomputable def dualCoordinate {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (i : d)
    (y : Submodule.span ℤ (Set.range (frequencyBasis b))) : ℤ :=
  (integerCoordinates (frequencyBasis b)).symm y i

/-- The integer coordinate equals the pairing with the corresponding primal basis vector. -/
theorem inner_eq_dualCoordinate {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] (b : Basis d ℝ E) (i : d)
    (y : Submodule.span ℤ (Set.range (frequencyBasis b))) :
    inner ℝ (y : E) (b i) = (dualCoordinate b i y : ℝ) := by
  let n := (integerCoordinates (frequencyBasis b)).symm y
  have hy : (y : E) = (frequencyBasis b).equivFun.symm (fun j => (n j : ℝ)) := by
    simpa only [n, Equiv.apply_symm_apply] using coe_integerCoordinates (frequencyBasis b) n
  rw [hy]
  change inner ℝ (dualFrequency b n) (b i) = (n i : ℝ)
  exact inner_dualFrequency_basis b n i

/-- A dual lattice vector with one in a selected coordinate and zero in the others. -/
noncomputable def dualCoordinateUnit {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] [DecidableEq d] (b : Basis d ℝ E) (i : d) :
    Submodule.span ℤ (Set.range (frequencyBasis b)) :=
  ⟨dualFrequency b (Pi.single i 1), dualFrequency_mem_span b (Pi.single i 1)⟩

/-- The selected dual coordinate unit pairs to one with its primal basis vector. -/
theorem inner_dualCoordinateUnit {E d : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype d] [DecidableEq d] (b : Basis d ℝ E) (i : d) :
    inner ℝ (dualCoordinateUnit b i : E) (b i) = 1 := by
  simpa only [dualCoordinateUnit, Pi.single_eq_same, Int.cast_one] using
    inner_dualFrequency_basis b (Pi.single i 1) i

/-- A nonzero dual-coordinate family has a controlled fraction of the Gaussian mass. -/
theorem gaussian_dual_coordinate_mass_le {E d : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype d] [DecidableEq d] (b : Basis d ℝ E) (i : d) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hbr : ‖b i‖ ≤ r) :
    Summable (fun y : Submodule.span ℤ (Set.range (frequencyBasis b)) =>
      if dualCoordinate b i y = 0 then 0 else Real.exp (-a * ‖(y : E)‖ ^ 2)) ∧
    Summable (fun y : Submodule.span ℤ (Set.range (frequencyBasis b)) =>
      Real.exp (-a * ‖(y : E)‖ ^ 2)) ∧
    (∑' y : Submodule.span ℤ (Set.range (frequencyBasis b)),
      if dualCoordinate b i y = 0 then 0 else Real.exp (-a * ‖(y : E)‖ ^ 2)) ≤
      (2 * Real.exp (-a / r ^ 2)) *
        ∑' y : Submodule.span ℤ (Set.range (frequencyBasis b)), Real.exp (-a * ‖(y : E)‖ ^ 2) := by
  exact gaussian_nonzero_pairing_mass_le _ (b i) (b.linearIndependent.ne_zero i)
    (dualCoordinateUnit b i) (inner_dualCoordinateUnit b i) (dualCoordinate b i)
    (inner_eq_dualCoordinate b i) ha hr hbr

end Rigidity.Smoothing
