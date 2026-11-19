import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Descent of periodic functions to a torus

A continuous function on a finite-dimensional real coordinate space that is invariant under integer
translations descends continuously to the corresponding unit torus. This applies to lattice Gaussian
periodizations in Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian
measures*, SIAM J. Comput. 37 (2007), Lemma 2.9.
-/

namespace Rigidity.Smoothing

/-- A continuous integer-periodic function descends to the coordinate torus. -/
theorem exists_continuous_torus_lift {d : Type*} [Fintype d] {F : Type*} [TopologicalSpace F]
    (f : (d → ℝ) → F) (hf : Continuous f)
    (hp : ∀ (x : d → ℝ) (n : d → ℤ), f (x + fun i => (n i : ℝ)) = f x) :
    ∃ g : C(UnitAddTorus d, F), ∀ x : d → ℝ, g (fun i => (x i : UnitAddCircle)) = f x := by
  classical
  let q : (d → ℝ) → UnitAddTorus d := fun x i => (x i : UnitAddCircle)
  have hq : IsOpenQuotientMap q := by
    exact IsOpenQuotientMap.piMap (fun _ : d => QuotientAddGroup.isOpenQuotientMap_mk)
  let g : UnitAddTorus d → F := fun z => f (Function.surjInv hq.surjective z)
  have hfactor : g ∘ q = f := by
    funext x
    let y := Function.surjInv hq.surjective (q x)
    have hy : q y = q x := Function.surjInv_eq hq.surjective (q x)
    have hd : ∀ i, ∃ n : ℤ, (n : ℝ) = y i - x i := by
      intro i
      have heq : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub]
        have := congrFun hy i
        change (y i : UnitAddCircle) = (x i : UnitAddCircle) at this
        rw [this, sub_self]
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp heq
      exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn⟩
    choose n hn using hd
    have hy' : y = x + fun i => (n i : ℝ) := by
      funext i
      simp only [Pi.add_apply]
      linarith [hn i]
    change f y = f x
    rw [hy', hp]
  have hg : Continuous g := hq.isQuotientMap.continuous_iff.mpr (by rw [hfactor]; exact hf)
  exact ⟨⟨g, hg⟩, fun x => congrFun hfactor x⟩

end Rigidity.Smoothing
