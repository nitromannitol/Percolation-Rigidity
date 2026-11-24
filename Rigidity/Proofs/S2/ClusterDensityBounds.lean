import PercolationClusterHomogenization.Proofs.Density.ClusterDensityMean
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityBounds

/-!
# Boundedness of cluster-density fluctuations

The normalized infinite-cluster count is between zero and one. This supplies the finitely many
initial scales in stretched-exponential density estimates.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.External

variable {d : ℕ} {p : unitInterval}

/-- An `O_s` estimate is monotone in a measurable random variable. -/
theorem IsOsBond.mono_variable {X Y : Configuration d → ℝ} {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hX : Measurable X) (hXY : ∀ ω, X ω ≤ Y ω)
    (hY : IsOsBond d p Y s θ) : IsOsBond d p X s θ := by
  have hpoint : ∀ ω, Real.exp (Real.rpow (Max.max (X ω / θ) 0) s) ≤
      Real.exp (Real.rpow (Max.max (Y ω / θ) 0) s) := by
    intro ω
    apply Real.exp_le_exp.mpr
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le_max (div_le_div_of_nonneg_right (hXY ω) hθ.le) le_rfl) hs.le
  have hXi : Integrable (fun ω => Real.exp (Real.rpow (Max.max (X ω / θ) 0) s))
      (latticeBondLaw d p) := by
    refine Integrable.mono' hY.1 (measurable_exp_rpow_max_div s hX).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hpoint ω
  exact ⟨hXi, (integral_mono hXi hY.1 hpoint).trans hY.2⟩

/-- Every fixed finite range of planar triadic scales satisfies the density estimate with one
constant. -/
theorem planar_density_initial_scales (p : unitInterval) (m₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m ≤ m₀, ∀ k : Vertex 2,
      IsOsBond 2 p
        (fun ω => |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
          ((triadicCube 2 m k).ncard : ℝ) - theta 2 p|)
        (2 / 15 : ℝ) (C * (3 : ℝ) ^ (-(m : ℝ))) := by
  let s : ℝ := 2 / 15
  let θ : ℝ := (3 : ℝ) ^ (1 / s)
  let C : ℝ := θ * (3 : ℝ) ^ m₀
  have hs : 0 < s := by dsimp [s]; norm_num
  have hθ : 0 < θ := by dsimp [θ]; positivity
  refine ⟨C, by dsimp [C]; positivity, fun m hm k => ?_⟩
  have hmeas : Measurable (fun ω : Configuration 2 =>
      |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
        ((triadicCube 2 m k).ncard : ℝ) - theta 2 p|) :=
    ((measurable_infiniteClusterCount_triadicCube m k).div_const _).sub_const _ |>.abs
  have hbase : IsOsBond 2 p (fun _ => (1 : ℝ)) s θ := by
    simpa only [θ, one_mul] using (isOsBond_const (d := 2) (p := p) (κ := 1) one_pos hs)
  have hbounded : IsOsBond 2 p
      (fun ω => |(infiniteClusterCount (triadicCube 2 m k) ω : ℝ) /
        ((triadicCube 2 m k).ncard : ℝ) - theta 2 p|) s θ :=
    IsOsBond.mono_variable hs hθ hmeas (fun ω => abs_centered_clusterDensity_le_one p m k ω) hbase
  have hscale : θ ≤ C * (3 : ℝ) ^ (-(m : ℝ)) := by
    dsimp [C]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
    have hpow : (3 : ℝ) ^ m ≤ (3 : ℝ) ^ m₀ := pow_le_pow_right₀ (by norm_num) hm
    have hpowpos : 0 < (3 : ℝ) ^ m := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpowpos]
    nlinarith
  exact IsOsBond.mono_scale hs hθ hscale hmeas hbounded

end Rigidity.Proofs.S2
