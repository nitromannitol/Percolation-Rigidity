import LatticeProb.Prob.Percolation.NeighborRadialScale
import LatticeProb.Prob.Percolation.GreenLocalizationGeometry

/-! # Working-scale bounds for the neighboring-threshold field -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LatticeProb.Percolation

namespace Rigidity.Support

/-- The strict neighboring-field bound gives the local-gradient and threshold scales. -/
theorem neighbor_working_scale_bounds {d : ℕ} {Ω : Type*}
    (X T : Vertex d → Ω → ℝ) (y x : Vertex d) (ω : Ω) (D α : ℝ)
    (hD : 0 ≤ D) (hα : 0 < α) (hαhalf : α ≤ 1 / 2)
    (hwork : neighborRadialField X T y x ω < D ^ α) :
    4096 < D ∧ max 2 (X x ω) < D / 64 ∧
      neighborMaximum T y ω < D / 128 ∧ 8 * max 2 (X x ω) ≤ D / 4 := by
  have h64 : (64 : ℝ) ≤ neighborRadialField X T y x ω := le_max_left _ _
  have hX : X x ω ≤ neighborRadialField X T y x ω :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hT : 2 * neighborMaximum T y ω ≤ neighborRadialField X T y x ω :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hmax : max (max 64 (max 2 (X x ω))) (2 * neighborMaximum T y ω) ≤
      neighborRadialField X T y x ω := by
    apply max_le
    · apply max_le h64
      apply max_le
      · linarith
      · exact hX
    · exact hT
  exact localization_scale_bounds hD hα hαhalf (lt_of_le_of_lt hmax hwork)

end Rigidity.Support
