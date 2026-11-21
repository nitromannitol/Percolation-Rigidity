import Rigidity.Proofs.Green.SupercriticalGreenColumn
import Rigidity.Proofs.Green.ClusterHeatKernel
import Rigidity.Proofs.Green.GreenGlobalBound

/-!
# Heat kernel and Green column bounds on the supercritical cluster

For `d ≥ 2` and `p_c(d) < p < 1`, the graph balls of radius `R` around a pole of the infinite
cluster satisfy, almost surely for all large `R`, the Faber-Krahn inequality of dimension `d` with
constant `a₀ R^{-1/(50d)}` (`clusterFaberKrahn_of_two_le`, from the isoperimetric inequality of the
cluster in `ClusterIsoperimetryWellConnected.lean`). The transition bounds of
`ClusterHeatKernel.lean` and the Green function bounds of `ClusterGreenUpperBound.lean` and
`GreenGlobalBound.lean` therefore hold with `D = d` and `η = 1/(50d)`:

* `p_n(x, y) ≤ K n^{-(d/2)(1 - 1/(50d))(1 - t)} exp(-t |x - y|²/(2n))`, where
  `(d/2)(1 - 1/(50d)) = d/2 - 1/100`, for `0 ≤ t ≤ 1` and all large `n` (`heat_le_of_two_le`);
* for `d ≥ 3` and every `δ > 0`, the Green column `g` with pole `y` satisfies
  `0 ≤ g(x) ≤ K |x - y|^{2 - d + 1/50 + δ}` for `|x - y| ≥ R` (`greenColumn_le_rpow_of_three_le`)
  and `0 ≤ g(x) ≤ K (1 + |x - y|)^{2 - d + 1/50 + δ}` for all `x`
  (`greenColumn_le_one_add_rpow_of_three_le`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

variable {d : ℕ}

/-- The loss exponent of the Faber-Krahn constant: `2 · 0 + 2 · d/(10d)² = 1/(50d)`. -/
theorem coarseLoss_two_mul (hd : 1 ≤ d) :
    2 * 0 + 2 * (1 / (10 * (d : ℝ)) ^ 2 * d) = 1 / (50 * d) := by
  have : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp
  ring

/-- The exponent `d (1 - 1/(50d)) = d - 1/50`. -/
theorem mul_one_sub_coarseLoss (hd : 1 ≤ d) : (d : ℝ) * (1 - 1 / (50 * d)) = d - 1 / 50 := by
  have : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp

/-- For `d ≥ 3`, the transition exponent `(d/2)(1 - 1/(50d))` exceeds one. -/
theorem one_lt_half_mul_one_sub_coarseLoss (hd : 3 ≤ d) :
    1 < (d : ℝ) / 2 * (1 - 1 / (50 * d)) := by
  have h := mul_one_sub_coarseLoss (by omega : 1 ≤ d)
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have : (d : ℝ) / 2 * (1 - 1 / (50 * d)) = ((d : ℝ) - 1 / 50) / 2 := by
    rw [← h]; ring
  rw [this]
  linarith

/-- **Faber-Krahn inequalities on the balls of the supercritical cluster**, `d ≥ 2`. -/
theorem clusterFaberKrahn_of_two_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ClusterFaberKrahn d p d (1 / (50 * d)) := by
  have h := clusterFaberKrahn_of_clusterIsoperimetry (by omega) le_rfl (by positivity)
    (clusterIsoperimetry_of_latticeIsoperimetry hd hp hp1 (latticeIsoperimetry hd))
  rwa [coarseLoss_two_mul (by omega)] at h

/-- **Transition bounds on the supercritical cluster**, `d ≥ 2`: almost surely, for each
`0 ≤ t ≤ 1`, `p_n(x, y) ≤ K n^{-(d/2)(1 - 1/(50d))(1 - t)} exp(-t |x - y|²/(2n))` for all large
`n`. -/
theorem heat_le_of_two_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ (K : ℝ) (N : ℕ), 0 ≤ K ∧
          ∀ (x : uniqueInfiniteComponent h) (n : ℕ), N ≤ n →
            LatticeProb.Graph.heat (componentGraph (uniqueInfiniteComponent h)) n x ⟨y, hy⟩ ≤
              K * (n : ℝ) ^ (-((d : ℝ) / 2 * (1 - 1 / (50 * d)) * (1 - t))) *
                Real.exp (-(t * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^ 2 /
                  (2 * n))) :=
  clusterHeat_le_of_clusterFaberKrahn (by exact_mod_cast (by omega : 0 < d))
    (clusterFaberKrahn_of_two_le hd hp hp1) y

/-- **Decay of the Green columns of the supercritical cluster**, `d ≥ 3`: almost surely, for every
`δ > 0`, the Green column `g` with pole `y` satisfies `0 ≤ g(x) ≤ K |x - y|^{2 - d + 1/50 + δ}`
for `|x - y| ≥ R`. -/
theorem greenColumn_le_rpow_of_three_le [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
            ∀ δ : ℝ, 0 < δ → ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧
              ∀ x : uniqueInfiniteComponent h,
                R ≤ ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ →
                  0 ≤ g x ∧ g x ≤
                    K * ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖ ^
                      (2 - d + 1 / 50 + δ) := by
  filter_upwards [clusterGreenColumn_le_of_clusterFaberKrahn hd hd2
    (by exact_mod_cast (by omega : 0 < d))
    (one_lt_half_mul_one_sub_coarseLoss hd) (clusterFaberKrahn_of_two_le hd2 hp hp1) y]
    with ω hω
  intro h hy g hg δ hδ
  obtain ⟨K, R, hK, hR, hb⟩ := hω h hy g hg δ hδ
  refine ⟨K, R, hK, hR, fun x hx => ?_⟩
  have hexp : (2 : ℝ) - d + 1 / 50 + δ = 2 - d * (1 - 1 / (50 * d)) + δ := by
    rw [mul_one_sub_coarseLoss (by omega)]; ring
  rw [hexp]
  exact hb x hx

/-- **Global decay of the Green columns of the supercritical cluster**, `d ≥ 3`: almost surely,
for every `δ > 0`, the Green column `g` with pole `y` satisfies
`0 ≤ g(x) ≤ K (1 + |x - y|)^{2 - d + 1/50 + δ}` at every vertex `x`. -/
theorem greenColumn_le_one_add_rpow_of_three_le [NeZero d] (hd : 3 ≤ d) (hd2 : 2 ≤ d)
    {p : unitInterval} (hp : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (y : Vertex d) :
    ∀ᵐ ω ∂latticeBondLaw d p,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ hy : y ∈ (uniqueInfiniteComponent h).supp,
        ∀ g : uniqueInfiniteComponent h → ℝ,
          IsGreenColumn d hd2 (uniqueInfiniteComponent h) ⟨y, hy⟩ g →
            ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : uniqueInfiniteComponent h,
              0 ≤ g x ∧ g x ≤
                K * (1 + ‖latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y‖) ^
                  (2 - d + 1 / 50 + δ) := by
  filter_upwards [clusterGreenColumn_le_one_add_norm_of_clusterFaberKrahn hd hd2
    (by exact_mod_cast (by omega : 0 < d))
    (one_lt_half_mul_one_sub_coarseLoss hd) (clusterFaberKrahn_of_two_le hd2 hp hp1) y]
    with ω hω
  intro h hy g hg δ hδ
  obtain ⟨K, hK, hb⟩ := hω h hy g hg δ hδ
  refine ⟨K, hK, fun x => ?_⟩
  have hexp : (2 : ℝ) - d + 1 / 50 + δ = 2 - d * (1 - 1 / (50 * d)) + δ := by
    rw [mul_one_sub_coarseLoss (by omega)]; ring
  rw [hexp]
  exact hb x

end Rigidity.Green
