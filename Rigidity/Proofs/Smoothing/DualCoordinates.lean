import Rigidity.External.SmoothingParameter

/-!
# Coordinates of a dual lattice vector

A nonzero vector in the span of a family has nonzero inner product with at least one member of the
family. This is the covering by nonzero coordinate slices used in the proof of Micciancio and
Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37
(2007), Lemma 3.3.
-/

namespace Rigidity.External

/-- A nonzero vector in the span has a nonzero inner product with a generator. -/
theorem exists_inner_ne_zero_of_mem_span {N k : ℕ}
    (b : Fin k → EuclideanSpace ℝ (Fin N)) {y : EuclideanSpace ℝ (Fin N)}
    (hy : y ∈ Submodule.span ℝ (Set.range b)) (hzero : y ≠ 0) :
    ∃ i, inner ℝ y (b i) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hspan : Submodule.span ℝ (Set.range b) ≤ LinearMap.ker (innerₗ _ y) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change inner ℝ y (b i) = 0
    exact h i
  have : inner ℝ y y = 0 := by
    simpa only [LinearMap.mem_ker, innerₗ_apply_apply] using hspan hy
  exact hzero (inner_self_eq_zero.mp this)

end Rigidity.External
