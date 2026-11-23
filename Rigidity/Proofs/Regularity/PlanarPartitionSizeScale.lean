import Rigidity.Proofs.Regularity.PlanarHarmonicApproximationTwo
import Rigidity.Proofs.Cluster.PlanarRHLocal
import Rigidity.Proofs.Cluster.GehringCubes
import Rigidity.Proofs.Cluster.Caccioppoli
import Rigidity.Proofs.Percolation.PlanarCoarseWeights

/-!
# The scales of the planar partition cubes from the minimal scales of Proposition 2.4

`PlanarMinimalScalesTwo p` is the statement of the minimal scales of Armstrong and Dario
(arXiv:1609.09431v2), Definition 3.7 with Propositions 2.1 and 2.4, in dimension two and in the
form `O_s`: the cells of the reverse Hölder partition form a partition with comparable neighbours,
and for all `t, α > 0` there is a minimal scale `M ≤ O_r(θ)` above which the `t`-th moments on
`□_m` of the sizes of the cells, of the planar partition cubes and of the reach are at most
`K |□_m|` and each of these sizes on `□_m` is at most `3^{α m}`.

`planarPartitionSizeScale_of_minimalScales` deduces `PlanarPartitionSizeScale p`, the hypothesis of
`planarHarmonicApproximationTwo_of_squareEstimates`: with `t = 1` and `α = 1/2`, above
`max(M, 81)` the partition cubes of the vertices of `□_m` have side at most `3^{m/2}`, hence scale
at most `m - 2`.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2
open scoped ENNReal

/-- **The minimal scales of Proposition 2.4 for the planar partitions** (Armstrong and Dario,
Definition 3.7 with Propositions 2.1 and 2.4, dimension two, form `O_s`). -/
def PlanarMinimalScalesTwo (p : unitInterval) : Prop :=
  ∃ A₀ : ℝ, ∃ s : Configuration 2 → Vertex 2 → ℕ,
    (∀ᵐ ω ∂(latticeBondLaw 2 p),
      (∀ x, ∀ z ∈ Rigidity.Proofs.Cluster.cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (⟨k, Rigidity.Proofs.Cluster.idx k y⟩ : TriadicCube 2) ∈
          Rigidity.Proofs.Cluster.planarRHGood A₀ ω) ∧
    ∀ t : ℝ, 0 < t → ∀ α : ℝ, 0 < α → ∃ K r θ : ℝ, 0 ≤ K ∧ 0 < r ∧ 0 < θ ∧
      ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M r θ ∧
        ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ m : ℕ, M ω ≤ 3 ^ m →
          ∑ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2), ((3 : ℝ) ^ s ω x) ^ t ≤
              K * (Rigidity.Proofs.Cluster.cube m (0 : Vertex 2)).card ∧
          (∀ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
            (3 : ℝ) ^ s ω x ≤ ((3 : ℝ) ^ m) ^ α) ∧
          ∑ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
              ((3 : ℝ) ^ (planarPartCube ω x).scale) ^ t ≤
            K * (Rigidity.Proofs.Cluster.cube m (0 : Vertex 2)).card ∧
          (∀ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
            (3 : ℝ) ^ (planarPartCube ω x).scale ≤ ((3 : ℝ) ^ m) ^ α) ∧
          ∑ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2), planarReach ω x ^ ⌈t⌉₊ ≤
            ENNReal.ofReal (K * (Rigidity.Proofs.Cluster.cube m (0 : Vertex 2)).card) ∧
          ∀ x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2),
            planarReach ω x ≤ ENNReal.ofReal (((3 : ℝ) ^ m) ^ α)

/-- The square `□_m` lies in the triadic cube of scale `m` containing the origin. -/
theorem mem_cube_zero_of_mem_square {m : ℕ} {x : Vertex 2} (hx : x ∈ triadicCubeFinset 2 m 0) :
    x ∈ Rigidity.Proofs.Cluster.cube m (0 : Vertex 2) := by
  rw [Rigidity.Proofs.Cluster.cube, Rigidity.Proofs.Cluster.mem_box]
  intro i
  have h3 := Rigidity.Proofs.Cluster.two_mul_halfSide_add_one m
  have h0 := Rigidity.Proofs.Cluster.halfSide_nonneg m
  have hc : Rigidity.Proofs.Cluster.center m (0 : Vertex 2) i = 0 := by
    simp only [Rigidity.Proofs.Cluster.center, Rigidity.Proofs.Cluster.idx, Pi.zero_apply,
      zero_add]
    rw [Int.ediv_eq_zero_of_lt h0 (by omega), mul_zero]
  rw [hc, sub_zero]
  have h2 := (mem_square_iff_int.1 hx) i
  generalize |x i| = a at h2 ⊢
  generalize (3 : ℤ) ^ m = b at h2 h3
  omega

/-- **The scales of the planar partition cubes**: `PlanarPartitionSizeScale p` from the minimal
scales of Proposition 2.4. -/
theorem planarPartitionSizeScale_of_minimalScales {p : unitInterval}
    (h : PlanarMinimalScalesTwo p) : PlanarPartitionSizeScale p := by
  obtain ⟨-, s, -, hall⟩ := h
  obtain ⟨K, r, θ, -, hr, hθ, M, hMm, hM0, hMos, hae⟩ := hall 1 one_pos (1 / 2) (by norm_num)
  have hOs := IsOsBond.max hr hθ (by positivity) hMm measurable_const hMos
    (isOsBond_const (p := p) (d := 2) (by norm_num : (0 : ℝ) < 81) hr)
  refine ⟨r, _, hr, by positivity, fun ω => max (M ω) 81, hMm.max measurable_const,
    fun ω => (hM0 ω).trans (le_max_left _ _), hOs, ?_⟩
  filter_upwards [hae] with ω hω m hm x hx
  have hm1 : M ω ≤ 3 ^ m := (le_max_left _ _).trans hm
  have hm81 : (3 : ℝ) ^ 4 ≤ 3 ^ m := by
    have h81 : (81 : ℝ) ≤ 3 ^ m := (le_max_right _ _).trans hm
    calc (3 : ℝ) ^ 4 = 81 := by norm_num
      _ ≤ 3 ^ m := h81
  have hm4 : 4 ≤ m := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hm81
  obtain ⟨-, -, -, hsize, -⟩ := hω m hm1
  have hb := hsize x (mem_cube_zero_of_mem_square hx)
  have hsq := pow_le_pow_left₀ (by positivity) hb 2
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), ← pow_mul] at hsq
  have h2 : (planarPartCube ω x).scale * 2 ≤ m :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hsq
  omega

end Rigidity.Proofs.Regularity
