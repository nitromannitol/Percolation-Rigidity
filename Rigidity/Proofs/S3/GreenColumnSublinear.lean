import Rigidity.Steps.S3.CompareDifferentPlanes

/-!
# Lemma 3.3: Green columns grow sublinearly

Step `step:3.3-green-sublinear` of Lemma 3.3 (paper L899-900 of the corrected draft, there from
Proposition 2.6). A Green column `g` on a cluster `C` is normalized at infinity: in dimension two
`|g(x)| ≤ ε |x|` for `|x|` large, and in dimension at least three `|g(x)| ≤ ε` for `|x|` large.
In both cases `|g(x)| ≤ ε |x|` outside a large ball, and the finitely many vertices of the cluster
inside that ball contribute a bounded error, so that `g` is `o(R)` uniformly on the Euclidean ball
of radius `R`: it has slope asymptotics with slope zero.
-/

namespace Rigidity.Proofs.S3

open LatticeProb.Percolation Rigidity.Steps.S3

variable {d : ℕ}

/-- The Euclidean distance of a lattice point to the origin is its Euclidean norm. -/
theorem dist_latticeEuclideanEmbedding_zero (x : Vertex d) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding (0 : Vertex d)) =
      ‖latticeEuclideanEmbedding x‖ := by
  have hz : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  rw [dist_eq_norm, hz, sub_zero]

/-- A function on a cluster bounded by `ε |x|` outside a large ball, for every `ε > 0`, has slope
asymptotics with slope zero: the vertices of the cluster in the large ball are finitely many. -/
theorem componentSlopeAsymptotics_zero_of_tail {ω : Configuration d} (C : OpenComponent ω)
    (g : C → ℝ)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ x : C, R ≤ ‖latticeEuclideanEmbedding x.val‖ →
      |g x| ≤ ε * ‖latticeEuclideanEmbedding x.val‖) :
    componentSlopeAsymptotics C 0 g := by
  intro ε hε
  obtain ⟨R₁, hR₁, hR₁g⟩ := hg ε hε
  set M : ℝ := ∑ x ∈ componentEuclideanBall C 0 R₁, |g x| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨R₁ + M / ε, by positivity, fun R hR x hx => ?_⟩
  have hslope : componentSlope C 0 x = 0 := by simp [componentSlope]
  rw [hslope, sub_zero]
  have hxR : ‖latticeEuclideanEmbedding x.val‖ < R := by
    rw [← dist_latticeEuclideanEmbedding_zero]
    exact (mem_componentEuclideanBall C 0 R x).1 hx
  by_cases hx₁ : R₁ ≤ ‖latticeEuclideanEmbedding x.val‖
  · exact (hR₁g x hx₁).trans (mul_le_mul_of_nonneg_left hxR.le hε.le)
  · have hxball : x ∈ componentEuclideanBall C 0 R₁ := by
      rw [mem_componentEuclideanBall, dist_latticeEuclideanEmbedding_zero]
      exact not_le.1 hx₁
    have h1 : |g x| ≤ M :=
      Finset.single_le_sum (f := fun y => |g y|) (fun _ _ => abs_nonneg _) hxball
    have h2 : M ≤ ε * R := by
      have h3 : M / ε ≤ R := by linarith
      rw [div_le_iff₀ hε] at h3
      linarith
    linarith

/-- Step `step:3.3-green-sublinear`: a Green column on a cluster grows sublinearly. -/
theorem greenColumnSublinearStep (hd : 2 ≤ d) : GreenColumnSublinearStep d hd := by
  intro ω C y g hg
  apply componentSlopeAsymptotics_zero_of_tail C g
  intro ε hε
  rcases Nat.lt_or_ge d 3 with h3 | h3
  · exact (hg.2.1 (by omega)).2 ε hε
  · obtain ⟨R, hR, hRg⟩ := hg.2.2 h3 1 one_pos
    refine ⟨max R ε⁻¹, lt_max_of_lt_left hR, fun x hx => ?_⟩
    calc
      |g x| ≤ 1 := hRg x ((le_max_left _ _).trans hx)
      _ = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
      _ ≤ ε * ‖latticeEuclideanEmbedding x.val‖ :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hx) hε.le

end Rigidity.Proofs.S3
