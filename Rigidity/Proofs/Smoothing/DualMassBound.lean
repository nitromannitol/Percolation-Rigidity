import Rigidity.Proofs.Smoothing.DualCoordinateMass
import Rigidity.Proofs.Smoothing.SliceMassBound
import Rigidity.Proofs.Smoothing.ScaleTail

/-!
# Gaussian mass bound on a dual basis lattice

The nonzero mass of the dual basis lattice is bounded by `ε` at the smoothing scale. This is the
finite-coordinate summation in Micciancio and Regev, *Worst-case to average-case reductions based
on Gaussian measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

open Classical Module

namespace Rigidity.Smoothing

/-- The nonzero Gaussian mass of a dual basis lattice is bounded at the smoothing scale. -/
theorem gaussian_dual_fin_mass_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (k : ℕ) (hk : 0 < k)
    (b : Basis (Fin k) ℝ E) (r : ℝ) (hr : 0 < r) (hbr : ∀ i, ‖b i‖ ≤ r)
    (ε : ℝ) (hε : 0 < ε) (s : ℝ)
    (hs : Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) * r ≤ s) :
    let L := Submodule.span ℤ (Set.range (frequencyBasis b))
    Summable (fun y : L => if y = 0 then 0 else Real.exp (-(Real.pi * s ^ 2) * ‖(y : E)‖ ^ 2)) ∧
    (∑' y : L, if y = 0 then 0 else Real.exp (-(Real.pi * s ^ 2) * ‖(y : E)‖ ^ 2)) ≤ ε := by
  classical
  let L := Submodule.span ℤ (Set.range (frequencyBasis b))
  let a : ℝ := Real.pi * s ^ 2
  let q : ℝ := Real.exp (-a / r ^ 2)
  let f : L → ℝ := fun y => Real.exp (-a * ‖(y : E)‖ ^ 2)
  let P : Fin k → L → Prop := fun i y => dualCoordinate b i y ≠ 0
  letI (i : Fin k) (y : L) : Decidable (P i y) := Classical.propDecidable _
  let p : Fin k → ℝ := fun _ => 2 * q
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hinv : 0 < 1 / ε := one_div_pos.mpr hε
  have harg : 1 < 2 * (k : ℝ) * (1 + 1 / ε) := by nlinarith
  have hroot : 0 < Real.sqrt (Real.log (2 * k * (1 + 1 / ε)) / Real.pi) :=
    Real.sqrt_pos.2 (div_pos (Real.log_pos harg) Real.pi_pos)
  have hspos : 0 < s := (mul_pos hroot hr).trans_le hs
  have ha : 0 < a := by dsimp [a]; positivity
  have hf : Summable f := summable_gaussian L ha
  have hf0 : f 0 = 1 := by simp [f]
  have hcover : ∀ y : L, y ≠ 0 → ∃ i, P i y := by
    intro y hy
    by_contra h
    apply hy
    apply (integerCoordinates (frequencyBasis b)).symm.injective
    funext i
    have hi : dualCoordinate b i y = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    have h0 : (integerCoordinates (frequencyBasis b)).symm (0 : L) = 0 := by
      change ((frequencyBasis b).restrictScalars ℤ).equivFun 0 = 0
      exact map_zero _
    simpa only [dualCoordinate, h0, Pi.zero_apply] using hi
  have hslice (i : Fin k) : Summable (fun y : L => if P i y then f y else 0) ∧
      (∑' y : L, if P i y then f y else 0) ≤ p i * ∑' y : L, f y := by
    have hsame : (fun y : L => if P i y then f y else 0) =
        fun y : L => if dualCoordinate b i y = 0 then 0 else f y := by
      funext y
      by_cases h : dualCoordinate b i y = 0 <;> simp [P, h]
    rw [hsame]
    have hd := gaussian_dual_coordinate_mass_le b i ha hr (hbr i)
    exact ⟨hd.1, hd.2.2⟩
  have hq : q = Real.exp (-Real.pi * (s / r) ^ 2) := by
    dsimp only [q, a]
    congr 1
    ring
  have hp : (∑ i, p i) ≤ ε / (1 + ε) := by
    have hscale := (geometric_ratio_of_scale hk hr hε hs).2.2
    simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hq]
    nlinarith
  simpa only [f, a] using
    tsum_off_point_le_of_slice_fraction f hf (fun _ => (Real.exp_pos _).le) 0 hf0
      P hcover p hslice hε hp

end Rigidity.Smoothing
