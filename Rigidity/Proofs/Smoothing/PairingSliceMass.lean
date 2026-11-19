import Rigidity.Proofs.Smoothing.GaussianFiber
import Rigidity.Proofs.Smoothing.SliceDecay
import Rigidity.Proofs.Smoothing.SliceFraction
import Rigidity.Proofs.Smoothing.FiberSummation

/-!
# Total mass of the nonzero pairing slices

For a discrete lattice with integral pairing coordinates, the Gaussian mass of all nonzero
coordinate slices is at most twice the geometric ratio times the total mass. This is the slice
summation in Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian
measures*, SIAM J. Comput. 37 (2007), Lemma 3.3.
-/

open Classical

namespace Rigidity.Smoothing

/-- The nonzero pairing slices have a controlled fraction of the total Gaussian mass. -/
theorem gaussian_nonzero_pairing_mass_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (b : E) (hb : b ≠ 0) (v : L)
    (hv : inner ℝ (v : E) b = 1) (c : L → ℤ) (hc : ∀ y : L, inner ℝ (y : E) b = (c y : ℝ))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hbr : ‖b‖ ≤ r) :
    Summable (fun y : L => if c y = 0 then 0 else Real.exp (-a * ‖(y : E)‖ ^ 2)) ∧
    Summable (fun y : L => Real.exp (-a * ‖(y : E)‖ ^ 2)) ∧
    (∑' y : L, if c y = 0 then 0 else Real.exp (-a * ‖(y : E)‖ ^ 2)) ≤
      (2 * Real.exp (-a / r ^ 2)) * ∑' y : L, Real.exp (-a * ‖(y : E)‖ ^ 2) := by
  let f : L → ℝ := fun y => Real.exp (-a * ‖(y : E)‖ ^ 2)
  let S : ℤ → ℝ := fun n => ∑' y : {y : L // c y = n}, f y.1
  let q : ℝ := Real.exp (-a / r ^ 2)
  let K := orthogonalLattice L b
  let Z : ℝ := ∑' k : K, Real.exp (-a * ‖(k : E)‖ ^ 2)
  let T : ℝ := ∑' n : ℤ, if n = 0 then 0 else S n
  letI : DiscreteTopology K := discreteTopology_orthogonalLattice L b
  have hfull : Summable f := summable_gaussian L ha
  obtain ⟨_, hS, hT, hoff, htotal, hoffeq⟩ :=
    summable_and_tsum_fibers c f hfull (fun _ => (Real.exp_pos _).le)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_lt_zero.mpr ha) (sq_pos_of_pos hr)
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hFibEq (n : ℤ) : S n =
      ∑' y : {y : L // inner ℝ (y : E) b = (n : ℝ)}, f y.1 := by
    let e : {y : L // c y = n} ≃ {y : L // inner ℝ (y : E) b = (n : ℝ)} :=
      Equiv.subtypeEquivRight (fun y => by simp only [hc y, Int.cast_inj])
    have he (y : {y : L // c y = n}) : (e y).1 = y.1 := rfl
    simpa only [S, he] using e.tsum_eq (fun y : {y : L // inner ℝ (y : E) b = (n : ℝ)} => f y.1)
  have hFn (n : ℤ) : S n ≤ q ^ (n.natAbs ^ 2) * Z := by
    rw [hFibEq n]
    have h := gaussian_lattice_fiber_le L b hb v hv ha n
    calc
      (∑' y : {y : L // inner ℝ (y : E) b = (n : ℝ)}, f y.1) ≤
          Real.exp (-a * ((n : ℝ) ^ 2 / ‖b‖ ^ 2)) * Z := h.2.2
      _ ≤ q ^ (n.natAbs ^ 2) * Z :=
        mul_le_mul_of_nonneg_right (exp_integer_slice_le_pow ha.le (norm_pos_iff.mpr hb) hr hbr n) hZ
  have hS0 : S 0 = Z := by
    rw [hFibEq 0]
    let e := latticeFiberEquiv L b v hv 0
    have he (k : K) : (((e k).1 : L) : E) = (k : E) := by
      change (0 : ℤ) • (v : E) + (k : E) = _
      simp only [zero_zsmul, zero_add]
    simpa only [f, Z, he] using
      (e.tsum_eq (fun y : {y : L // inner ℝ (y : E) b = ((0 : ℤ) : ℝ)} => f y.1)).symm
  have hTail := summable_int_pow_sq_and_tsum_le hq.le hq1
  have hTbound : T ≤ (2 * q / (1 - q)) * Z := by
    have hpoint (n : ℤ) : (if n = 0 then 0 else S n) ≤
        (if n = 0 then 0 else q ^ (n.natAbs ^ 2)) * Z := by
      by_cases hn : n = 0
      · simp only [hn, if_true, zero_mul, le_refl]
      · simpa only [hn, if_false] using hFn n
    calc
      T ≤ ∑' n : ℤ, (if n = 0 then 0 else q ^ (n.natAbs ^ 2)) * Z :=
        hT.tsum_le_tsum hpoint (hTail.1.mul_right Z)
      _ = (∑' n : ℤ, if n = 0 then 0 else q ^ (n.natAbs ^ 2)) * Z := tsum_mul_right
      _ ≤ (2 * (q / (1 - q))) * Z := mul_le_mul_of_nonneg_right hTail.2 hZ
      _ = (2 * q / (1 - q)) * Z := by ring
  have hM : Z + T = ∑' y, f y := by
    calc
      Z + T = ∑' n, S n := by
        have hp : (∑' n, S n) = S 0 + T := hS.tsum_eq_add_tsum_ite 0
        rw [hS0] at hp
        exact hp.symm
      _ = ∑' y, f y := htotal.symm
  have hTnonneg : 0 ≤ T := tsum_nonneg fun n => by
    split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨hoff, hfull, ?_⟩
  rw [hoffeq]
  exact le_two_mul_ratio_of_zero_slice hq.le hq1 hTnonneg hM.le hTbound

end Rigidity.Smoothing
