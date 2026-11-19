import Rigidity.Proofs.Smoothing.LatticeFiber

/-!
# Gaussian mass of a pairing fiber

Every integer pairing fiber is a translate of the zero-pairing sublattice, so the Gaussian mass of
the fiber is controlled by the zero fiber. This is the slice estimate in Micciancio and Regev,
*Worst-case to average-case reductions based on Gaussian measures*, SIAM J. Comput. 37 (2007),
Lemma 3.3.
-/

namespace Rigidity.Smoothing

/-- A pairing fiber has Gaussian mass bounded by a Gaussian factor times the zero fiber mass. -/
theorem gaussian_lattice_fiber_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (b : E) (hb : b ≠ 0) (v : L)
    (hv : inner ℝ (v : E) b = 1) {a : ℝ} (ha : 0 < a) (n : ℤ) :
    Summable (fun y : {y : L // inner ℝ (y : E) b = (n : ℝ)} =>
      Real.exp (-a * ‖(y : E)‖ ^ 2)) ∧
    Summable (fun k : orthogonalLattice L b => Real.exp (-a * ‖(k : E)‖ ^ 2)) ∧
    (∑' y : {y : L // inner ℝ (y : E) b = (n : ℝ)}, Real.exp (-a * ‖(y : E)‖ ^ 2)) ≤
      Real.exp (-a * ((n : ℝ) ^ 2 / ‖b‖ ^ 2)) *
        ∑' k : orthogonalLattice L b, Real.exp (-a * ‖(k : E)‖ ^ 2) := by
  let K := orthogonalLattice L b
  letI : DiscreteTopology K := discreteTopology_orthogonalLattice L b
  let e := latticeFiberEquiv L b v hv n
  have hK (k : K) : inner ℝ (k : E) b = 0 := ((mem_orthogonalLattice L b _).mp k.2).2
  have hs := gaussian_integer_slice_le K b (v : E) hb hv hK ha n
  have heval (k : K) : (((e k).1 : L) : E) = n • (v : E) + (k : E) := rfl
  have hsum : Summable (fun y : {y : L // inner ℝ (y : E) b = (n : ℝ)} =>
      Real.exp (-a * ‖(y : E)‖ ^ 2)) := by
    have h := hs.1.comp_injective e.symm.injective
    apply h.congr
    intro y
    have he := congrArg (fun z : {y : L // inner ℝ (y : E) b = (n : ℝ)} => ((z.1 : L) : E))
      (e.apply_symm_apply y)
    rw [heval] at he
    simp only [Function.comp_apply]
    rw [he]
  refine ⟨hsum, hs.2.1, ?_⟩
  have htsum : (∑' y : {y : L // inner ℝ (y : E) b = (n : ℝ)},
      Real.exp (-a * ‖(y : E)‖ ^ 2)) =
      ∑' k : K, Real.exp (-a * ‖n • (v : E) + (k : E)‖ ^ 2) := by
    simpa only [heval] using
      (e.tsum_eq (fun y : {y : L // inner ℝ (y : E) b = (n : ℝ)} =>
        Real.exp (-a * ‖(y : E)‖ ^ 2))).symm
  rw [htsum]
  exact hs.2.2

end Rigidity.Smoothing
