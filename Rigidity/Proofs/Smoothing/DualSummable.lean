import Rigidity.Proofs.Smoothing.DualBasis
import Rigidity.Proofs.Smoothing.GaussianSummable

/-!
# Convergence of the dual lattice Gaussian

The dual lattice Gaussian sum converges at every positive scale. This is the convergence part of
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- The Gaussian over the nonzero dual lattice vectors is summable for every positive coefficient. -/
theorem summable_dualLattice {N k : ℕ} (b : Fin k → EuclideanSpace ℝ (Fin N))
    (hb : LinearIndependent ℝ b) {a : ℝ} (ha : 0 < a) :
    Summable (fun y : {y // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0} =>
      Real.exp (-a * ‖(y : EuclideanSpace ℝ (Fin N))‖ ^ 2)) := by
  let V := Submodule.span ℝ (Set.range b)
  let L : Submodule ℤ V := Submodule.span ℤ (Set.range (dualBasis b hb))
  let f : {y // y ∈ Rigidity.External.dualLattice b ∧ y ≠ 0} → L := fun y =>
    ⟨⟨y.1, y.2.1.1⟩, (mem_span_dualBasis_iff b hb _).mpr y.2.1.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : L => ((z : V) : EuclideanSpace ℝ (Fin N))) h
  apply ((summable_gaussian L ha).comp_injective hf).congr
  intro y
  simp only [Function.comp_apply, Submodule.coe_norm, f]

end Rigidity.Smoothing
