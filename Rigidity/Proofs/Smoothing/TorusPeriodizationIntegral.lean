import Rigidity.Proofs.Smoothing.LatticeIntegralUnconditional
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier coefficients of a periodization

If a torus function is a lattice periodization and its Fourier integrand is integrable, its Fourier
coefficient is the corresponding integral over the coordinate space. This is the unfolding step in
Micciancio and Regev, *Worst-case to average-case reductions based on Gaussian measures*, SIAM J.
Comput. 37 (2007), Lemma 2.9.
-/

open MeasureTheory Module

namespace Rigidity.Smoothing

/-- Fourier coefficients of an integrable periodization unfold to integrals over coordinate space. -/
theorem mFourierCoeff_eq_integral_of_periodization {d : Type*} [Fintype d]
    (g : C(UnitAddTorus d, ℂ)) (H : (d → ℝ) → ℂ)
    (hper : ∀ x : d → ℝ, g (fun i => (x i : UnitAddCircle)) =
      ∑' z : Submodule.span ℤ (Set.range (Pi.basisFun ℝ d)), H ((z : d → ℝ) + x))
    (n : d → ℤ)
    (hint : Integrable (fun x : d → ℝ =>
      UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) * H x)) :
    UnitAddTorus.mFourierCoeff g n = ∫ x : d → ℝ,
      UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) * H x := by
  classical
  let b : Basis d ℝ (d → ℝ) := Pi.basisFun ℝ d
  let L : Submodule ℤ (d → ℝ) := Submodule.span ℤ (Set.range b)
  let D := ZSpan.fundamentalDomain b
  have hzq (z : L) : (fun i => ((z : d → ℝ) i : UnitAddCircle)) = 0 := by
    funext i
    have hi := ((b.mem_span_iff_repr_mem ℤ (z : d → ℝ)).mp z.2) i
    obtain ⟨k, hk⟩ := hi
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    refine ⟨k, ?_⟩
    simp only [b, Pi.basisFun_repr, algebraMap_int_eq] at hk
    change (k : ℝ) = (z : d → ℝ) i at hk
    simpa only [zsmul_eq_mul, mul_one] using hk
  have hqadd (z : L) (x : d → ℝ) :
      (fun i => (((z : d → ℝ) + x) i : UnitAddCircle)) =
        (fun i => (x i : UnitAddCircle)) := by
    funext i
    have hi := congrFun (hzq z) i
    simp only [Pi.zero_apply] at hi
    simp only [Pi.add_apply, AddCircle.coe_add, hi, zero_add]
  have hsets : {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =ᵐ[volume] D := by
    have hset : {x : d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ (fun _ : d => Set.Ioc (0 : ℝ) 1) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    rw [hset]
    dsimp only [D, b]
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi]
    exact Measure.pi_Ioc_ae_eq_pi_Icc.trans Measure.pi_Ico_ae_eq_pi_Icc.symm
  calc
    UnitAddTorus.mFourierCoeff g n =
        ∫ x in D, UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) *
          g (fun i => (x i : UnitAddCircle)) := by
      rw [UnitAddTorus.mFourierCoeff_eq_integral g n (0 : d → ℝ)]
      simp only [Pi.zero_apply, zero_add, smul_eq_mul]
      exact setIntegral_congr_set hsets
    _ = ∫ x in D, ∑' z : L,
        (UnitAddTorus.mFourier (-n) (fun i => (((z : d → ℝ) + x) i : UnitAddCircle)) *
          H ((z : d → ℝ) + x)) := by
      apply setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet b)
      intro x _
      dsimp only
      rw [hper x, ← tsum_mul_left]
      apply tsum_congr
      intro z
      rw [hqadd]
    _ = ∫ x : d → ℝ,
        UnitAddTorus.mFourier (-n) (fun i => (x i : UnitAddCircle)) * H x :=
      integral_tsum_lattice_add_of_integrable b volume _ hint

end Rigidity.Smoothing
