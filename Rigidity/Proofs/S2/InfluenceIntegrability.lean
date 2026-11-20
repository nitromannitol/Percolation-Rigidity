import Rigidity.Proofs.S2.ClusterDensityResampleLaw

/-!
# Integrability of finite-cube density influences

A single-bond influence on a finite cluster count is measurable and bounded, so all of its
nonnegative integer moments are integrable.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

/-- The absolute single-bond count influence is a measurable function of two configurations. -/
theorem measurable_count_influence {d : ℕ} (m : ℕ) (k : Vertex d) (e : Bond d) :
    Measurable fun q : Configuration d × Configuration d =>
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| := by
  let F : Configuration d → ℝ := fun ω => infiniteClusterCount (triadicCube d m k) ω
  have hF : Measurable F := measurable_infiniteClusterCount_triadicCube m k
  have hR : Measurable (fun q : Configuration d × Configuration d => resampleBond q.1 q.2 e) :=
    (measurePreserving_resampleBond d 0 e).measurable
  exact ((hF.comp measurable_fst).sub (hF.comp hR)).abs

/-- Every finite-cube density-count influence is at most the cube's cardinality. -/
theorem count_influence_le_card {d : ℕ} (m : ℕ) (k : Vertex d)
    (ω η : Configuration d) (e : Bond d) :
    |(infiniteClusterCount (triadicCube d m k) ω : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e) : ℝ)| ≤
      (triadicCubeFinset d m k).card := by
  classical
  have hbound (ξ : Configuration d) :
      (infiniteClusterCount (triadicCube d m k) ξ : ℝ) ≤ (triadicCubeFinset d m k).card := by
    have hc : infiniteClusterCount (triadicCube d m k) ξ ≤ (triadicCubeFinset d m k).card := by
      rw [infiniteClusterCount_triadicCube]
      exact Finset.card_filter_le _ _
    exact_mod_cast hc
  rw [abs_le]
  constructor <;> linarith [hbound ω, hbound (resampleBond ω η e),
    Nat.cast_nonneg (α := ℝ) (infiniteClusterCount (triadicCube d m k) ω),
    Nat.cast_nonneg (α := ℝ) (infiniteClusterCount (triadicCube d m k) (resampleBond ω η e))]

/-- All nonnegative integer moments of a finite-cube single-bond influence are integrable. -/
theorem integrable_count_influence_pow {d : ℕ} (p : unitInterval) (m : ℕ)
    (k : Vertex d) (e : Bond d) (r : ℕ) :
    Integrable (fun q : Configuration d × Configuration d =>
      |(infiniteClusterCount (triadicCube d m k) q.1 : ℝ) -
        (infiniteClusterCount (triadicCube d m k) (resampleBond q.1 q.2 e) : ℝ)| ^ r)
      ((latticeBondLaw d p).prod (latticeBondLaw d p)) := by
  refine (integrable_const (((triadicCubeFinset d m k).card : ℝ) ^ r)).mono'
    ((measurable_count_influence m k e).pow_const r).aestronglyMeasurable ?_
  filter_upwards with q
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) (count_influence_le_card m k q.1 q.2 e) r

end Rigidity.Proofs.S2
