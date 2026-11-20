import Rigidity.Proofs.Section5.TrichotomyMeasurable
import Rigidity.Proofs.Section5.PlanarGreenUniqueness

/-!
# The planar potential kernel and Green columns

A sublinear potential kernel with the unit-pole equation gives a normalized Green column.
-/

open LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

/-- A constant function has sublinear growth. -/
theorem isSublinearOn_const {ω : Configuration 2} (C : OpenComponent ω) (c : ℝ) :
    IsSublinearOn C (fun _ => c) := by
  intro ε hε
  refine ⟨|c| / ε, fun x hx => ?_⟩
  simpa [mul_comm] using (div_le_iff₀ hε).mp hx

/-- A logarithmic bound implies sublinear growth on a planar component. -/
theorem isSublinearOn_of_log_bound {ω : Configuration 2} (C : OpenComponent ω)
    (a : C → ℝ) (K R₀ : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x : C, R₀ ≤ eucl x.val → |a x| ≤ K * Real.log (eucl x.val)) :
    IsSublinearOn C a := by
  intro ε hε
  have hεK : 0 < ε / (K + 1) := by positivity
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (Real.isLittleO_log_id_atTop.bound hεK)
  refine ⟨max (max R R₀) 1, fun x hx => ?_⟩
  have hxR : R ≤ eucl x.val := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxR₀ : R₀ ≤ eucl x.val := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx1 : 1 ≤ eucl x.val := (le_max_right _ _).trans hx
  have hlog : Real.log (eucl x.val) ≤ ε / (K + 1) * eucl x.val := by
    have h := hR _ hxR
    change ‖Real.log (eucl x.val)‖ ≤ ε / (K + 1) * ‖eucl x.val‖ at h
    rw [Real.norm_eq_abs (eucl x.val), abs_of_nonneg (by linarith : 0 ≤ eucl x.val)] at h
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)
  have hcoeff : K * (ε / (K + 1)) ≤ ε := by
    have hh : (K * ε) / (K + 1) ≤ ε := by
      apply (div_le_iff₀ (by positivity : 0 < K + 1)).2
      nlinarith
    simpa only [mul_div_assoc] using hh
  calc
    |a x| ≤ K * Real.log (eucl x.val) := hbound x hxR₀
    _ ≤ K * (ε / (K + 1) * eucl x.val) := mul_le_mul_of_nonneg_left hlog hK
    _ = (K * (ε / (K + 1))) * eucl x.val := by ring
    _ ≤ ε * eucl x.val := mul_le_mul_of_nonneg_right hcoeff (by linarith)

/-- A sublinear unit-pole potential kernel gives a normalized planar Green column. -/
theorem isGreenColumn_of_potentialKernel {ω : Configuration 2} (C : OpenComponent ω)
    (y : C) (a : C → ℝ)
    (ha : ∀ x, componentLaplacian C a x = if x = y then 1 else 0)
    (hsub : IsSublinearOn C a) :
    IsGreenColumn 2 le_rfl C y (fun x => a y - a x) := by
  have hG : IsSublinearOn C (fun x => a y - a x) := (isSublinearOn_const C _).sub hsub
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hΔ : componentLaplacian C (fun z => a y - a z) x =
        -componentLaplacian C a x := by
      simp only [componentLaplacian, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hΔ, neg_neg, ha x]
  · intro _
    refine ⟨sub_self _, fun ε hε => ?_⟩
    obtain ⟨R, hR⟩ := hG ε hε
    exact ⟨max R 1, by positivity, fun x hx => hR x ((le_max_left _ _).trans hx)⟩
  · intro h
    omega

/-- Sublinear Liouville upgrades the potential kernel construction to a unique Green column. -/
theorem existsUnique_greenColumn_of_potentialKernel {ω : Configuration 2} (C : OpenComponent ω)
    (hL : HasSublinearLiouville C) (y : C) (a : C → ℝ)
    (ha : ∀ x, componentLaplacian C a x = if x = y then 1 else 0)
    (hsub : IsSublinearOn C a) : ∃! g, IsGreenColumn 2 le_rfl C y g := by
  refine ⟨fun x => a y - a x, isGreenColumn_of_potentialKernel C y a ha hsub, ?_⟩
  intro g hg
  exact eq_of_isGreenColumn hL hg (isGreenColumn_of_potentialKernel C y a ha hsub)


/-- Logarithmic potential kernels provide the planar Green-column existence input. -/
theorem greenColumnExistsTwo_of_potentialKernel
    (hkernel : ∀ p : unitInterval, criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
      ∀ y : Vertex 2, ∀ᵐ ω ∂latticeBondLaw 2 p,
        ∀ h : HasUniqueInfiniteOpenComponent ω,
          ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
            ∃ (a : uniqueInfiniteComponent h → ℝ) (K R₀ : ℝ), 0 ≤ K ∧
              (∀ x, componentLaplacian (uniqueInfiniteComponent h) a x =
                if x = ⟨y, hy⟩ then 1 else 0) ∧
              (∀ x, R₀ ≤ eucl x.val → |a x| ≤ K * Real.log (eucl x.val))) :
    Rigidity.External.SupercriticalBondGreenColumnExistsTwo := by
  intro p hp hp1 y
  filter_upwards [hkernel p hp hp1 y] with ω hω h hy
  obtain ⟨a, K, R₀, hK, ha, hbound⟩ := hω h hy
  exact ⟨fun x => a ⟨y, hy⟩ - a x,
    isGreenColumn_of_potentialKernel _ ⟨y, hy⟩ a ha
      (isSublinearOn_of_log_bound _ a K R₀ hK hbound)⟩

end Rigidity.Proofs.Section5
