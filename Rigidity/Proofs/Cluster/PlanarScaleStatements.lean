import Rigidity.Proofs.Cluster.PlanarRHPartition
import Rigidity.Proofs.Cluster.PlanarOmegaSupRate
import Rigidity.External.CorrectorQuantitative

/-!
# The minimal scales of Proposition 2.4 and the scale of Proposition 5.13, in dimension two

Two statements of Armstrong and Dario in the form `X ≤ O_s(C)` (`IsOsBond`), in dimension two.

* `PlanarMinimalScales p`: the partition `𝓡` of Definition 3.7 (maximal stopping cubes of the
  local family `planarRHGood A₀` of reverse Hölder cubes), with the minimal scales of
  Proposition 2.4: for every exponent `t > 0` and `α > 0` there is a random scale `M ≤ O_r(θ)` such
  that, whenever `M ≤ 3ᵐ`, on `□_m` the `t`-th moment of the sizes of the cells of `𝓡`, of the
  planar partition cubes and of the reach of the planar partition are at most `K |□_m|`, and all
  these sizes are at most `3^{α m}`.
* `PlanarBoundN p`: Proposition 5.13 (the random scale `𝒩` of Definition 5.12): there is a
  random scale `N ≤ O_r(θ)` such that, whenever `N ≤ 3ᵐ`, with `n = ⌈m/4⌉`,
  `|μ(V, q) + (1/2) q · ā⁻¹ q| ≤ C |q|² 3^{-mα}` and `|ν(V, ξ) - (1/2) ξ · ā ξ| ≤ C |ξ|² 3^{-mα}`
  for every triadic cube `V` of scale `n` contained in `□_m`, and the same bounds hold for `□_n`
  in the configuration translated by `-z`, for every `z ∈ □_m` (the cube `z + □_n` of the source,
  the source taking `z ∈ 3^{⌈m/8⌉} ℤ²`). The partition event holds and the cubes are resolved.
  The source prints the two displays with `μ - (1/2) q · ā⁻¹ q` and `(1/2) p · ā p + ν`; the signs
  here are those of Proposition 5.2.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal Matrix

/-- **Armstrong and Dario, Definition 3.7 with Propositions 2.1 and 2.4, in the form `O_s`**
(dimension two): the cells `cube (s x) x` of the partition `𝓡` form a partition with comparable
neighbours whose predecessors are reverse Hölder cubes, and for all `t, α > 0` there is a minimal
scale `M ≤ O_r(θ)` above which the `t`-th moments on `□_m` of the sizes of the cells of `𝓡`, of
the planar partition cubes and of the reach are at most `K |□_m|` and every such size on `□_m` is
at most `3^{α m}`. -/
def PlanarMinimalScales (p : unitInterval) : Prop :=
  ∃ A₀ : ℝ, ∃ s : Configuration 2 → Vertex 2 → ℕ,
    (∀ᵐ ω ∂(latticeBondLaw 2 p),
      (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω) ∧
    ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α → ∃ K r θ : ℝ, 0 ≤ K ∧ 0 < r ∧ 0 < θ ∧
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ m : ℕ, M ω ≤ 3 ^ m →
          ∑ x ∈ cube m (0 : Vertex 2), ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube m (0 : Vertex 2)).card ∧
          (∀ x ∈ cube m (0 : Vertex 2), (3 : ℝ) ^ s ω x ≤ ((3 : ℝ) ^ m) ^ α) ∧
          ∑ x ∈ cube m (0 : Vertex 2), ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t ≤
            K * (cube m (0 : Vertex 2)).card ∧
          (∀ x ∈ cube m (0 : Vertex 2), (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ α) ∧
          ∑ x ∈ cube m (0 : Vertex 2), planarReach ω x ^ ⌈t⌉₊ ≤
            ENNReal.ofReal (K * (cube m (0 : Vertex 2)).card) ∧
          ∀ x ∈ cube m (0 : Vertex 2), planarReach ω x ≤ ENNReal.ofReal (((3 : ℝ) ^ m) ^ α)

/-- **Armstrong and Dario, Proposition 5.13** (dimension two): a random scale `N ≤ O_r(θ)` above
which, with `n = ⌈m/4⌉`, `μ(·, q)` and `ν(·, ξ)` are within `C |q|² 3^{-mα}` and
`C |ξ|² 3^{-mα}` of `-(1/2) q · ā⁻¹ q` and `(1/2) ξ · ā ξ` on every triadic cube of scale `n`
contained in `□_m`, and on `□_n` in the configuration translated by `-z` for every `z ∈ □_m`. -/
def PlanarBoundN (p : unitInterval) : Prop :=
  ∃ α r θ C : ℝ, 0 < α ∧ 0 < r ∧ 0 < θ ∧ 0 ≤ C ∧
    ∃ N : Configuration 2 → ℝ, Measurable N ∧ (∀ ω, 0 ≤ N ω) ∧ IsOsBond 2 p N r θ ∧
      ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ m : ℕ, N ω ≤ 3 ^ m →
        (∀ V : TriadicCube 2, V.scale = (m + 3) / 4 →
          V.vertices ⊆ (⟨m, 0⟩ : TriadicCube 2).vertices →
          PlanarPartitionEvent ω ∧ PlanarResolved ω V ∧
          (∀ q : Fin 2 → ℝ, |planarMu ω V q + 1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
            C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * α)) ∧
          ∀ ξ : Fin 2 → ℝ, |planarNu ω V ξ - 1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
            C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * α)) ∧
        ∀ z ∈ (⟨m, 0⟩ : TriadicCube 2).vertices,
          PlanarPartitionEvent (configurationTranslation (-z) ω) ∧
          PlanarResolved (configurationTranslation (-z) ω) ⟨(m + 3) / 4, 0⟩ ∧
          (∀ q : Fin 2 → ℝ, |planarMu (configurationTranslation (-z) ω) ⟨(m + 3) / 4, 0⟩ q +
              1 / 2 * ∑ i, q i * ((planarAhom p)⁻¹ *ᵥ q) i| ≤
            C * (q 0 ^ 2 + q 1 ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * α)) ∧
          ∀ ξ : Fin 2 → ℝ, |planarNu (configurationTranslation (-z) ω) ⟨(m + 3) / 4, 0⟩ ξ -
              1 / 2 * ∑ i, ξ i * (planarAhom p *ᵥ ξ) i| ≤
            C * (ξ 0 ^ 2 + ξ 1 ^ 2) * (3 : ℝ) ^ (-(m : ℝ) * α)

end Rigidity.Proofs.Cluster
