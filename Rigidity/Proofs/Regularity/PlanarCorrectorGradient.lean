import Rigidity.Proofs.Regularity.PlanarScaleMaxima
import Rigidity.Proofs.Regularity.ClusterBallGeometry
import Rigidity.Proofs.S2.GreenGradientCore

/-!
# The gradient of a corrector from the Lipschitz estimate at its centre

Armstrong and Dario (arXiv:1609.09431v2), Remark after (1.19): the Lipschitz estimate at the centre
`x`, in the form of the approximation by a constant `c` on `𝒞_∞ ∩ B_ρ(x)` at the minimal scale
`ρ`, bounds the increments of a harmonic function `u` between neighbours `x, y`:
`|u(y) - u(x)| ≤ 2 |B_ρ| C (ρ/R) ‖u - a‖_{L̲²(𝒞_∞ ∩ B_R(x))}` for every constant `a`
(`abs_sub_le_of_constant_approximation`). With `a = q · x` and the corrector `χ = u - q · x` this
gives `|χ(y) - χ(x)| ≤ 2 |B_ρ| C (ρ/R) (‖χ‖_{L̲²(B_R(x))} + |q| R) + |q|`
(`abs_corrector_sub_le`); the normalized norm on `B_R(x)` is bounded by the one on a ball around
the origin that contains it (`componentBallL2_le_of_subset`).
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb LatticeProb.Percolation Rigidity.Percolation

variable {ω : Configuration 2}

/-- The corrector `χ_q = u - q · x` of a function on a component. -/
noncomputable def componentCorrector (C : OpenComponent ω) (q : Fin 2 → ℝ) (u : C → ℝ) :
    C → ℝ :=
  fun x => u x - componentSlope C q x

/-- The normalized norm on a ball against the one on a ball containing it. -/
theorem componentBallL2_le_of_subset (C : OpenComponent ω) {x z : Vertex 2} {r R : ℝ}
    (hsub : componentEuclideanBall C x r ⊆ componentEuclideanBall C z R)
    (hpos : 0 < (componentEuclideanBall C x r).card) (f : C → ℝ) :
    componentBallL2 C x r f ≤
      Real.sqrt (((componentEuclideanBall C z R).card : ℝ) /
        ((componentEuclideanBall C x r).card : ℝ)) * componentBallL2 C z R f := by
  unfold componentBallL2
  have hn : (0 : ℝ) < (componentEuclideanBall C x r).card := by exact_mod_cast hpos
  have hN : (0 : ℝ) < (componentEuclideanBall C z R).card :=
    lt_of_lt_of_le hn (by exact_mod_cast Finset.card_le_card hsub)
  rw [← Real.sqrt_mul (div_nonneg hN.le hn.le)]
  refine Real.sqrt_le_sqrt ?_
  rw [div_mul_div_comm, mul_comm (↑(componentEuclideanBall C z R).card : ℝ),
    mul_div_mul_right _ _ hN.ne']
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _) hn.le

/-- **Increments from the approximation by a constant** at the scale `ρ` around `x`. -/
theorem abs_sub_le_of_constant_approximation (C : OpenComponent ω) (x : Vertex 2) (v : C → ℝ)
    {ρ c : ℝ} {x' y' : C} (hx' : x' ∈ componentEuclideanBall C x ρ)
    (hy' : y' ∈ componentEuclideanBall C x ρ) :
    |v y' - v x'| ≤ 2 * ((componentEuclideanBall C x ρ).card : ℝ) *
      componentBallL2 C x ρ (v - fun _ => c) := by
  have h1 := Rigidity.Proofs.S2.abs_le_card_mul_componentBallL2 C x ρ (v - fun _ => c) hy'
  have h2 := Rigidity.Proofs.S2.abs_le_card_mul_componentBallL2 C x ρ (v - fun _ => c) hx'
  simp only [Pi.sub_apply] at h1 h2
  calc |v y' - v x'| = |(v y' - c) - (v x' - c)| := by ring_nf
    _ ≤ |v y' - c| + |v x' - c| := abs_sub _ _
    _ ≤ _ := by linarith

theorem abs_componentSlope_sub_le (C : OpenComponent ω) (q : Fin 2 → ℝ) {x y : C} {R : ℝ}
    (h : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) ≤ R) :
    |componentSlope C q y - componentSlope C q x| ≤ (|q 0| + |q 1|) * R := by
  unfold componentSlope
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h0 := (abs_sub_le_dist_latticeEuclideanEmbedding y.val x.val 0).trans h
  have h1 := (abs_sub_le_dist_latticeEuclideanEmbedding y.val x.val 1).trans h
  have e : q 0 * (y.val 0 : ℝ) + q 1 * (y.val 1 : ℝ) - (q 0 * (x.val 0 : ℝ) + q 1 * (x.val 1 : ℝ)) =
      q 0 * ((y.val 0 : ℝ) - (x.val 0 : ℝ)) + q 1 * ((y.val 1 : ℝ) - (x.val 1 : ℝ)) := by ring
  rw [e]
  calc |q 0 * ((y.val 0 : ℝ) - (x.val 0 : ℝ)) + q 1 * ((y.val 1 : ℝ) - (x.val 1 : ℝ))|
      ≤ |q 0| * |(y.val 0 : ℝ) - (x.val 0 : ℝ)| + |q 1| * |(y.val 1 : ℝ) - (x.val 1 : ℝ)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |q 0| * R + |q 1| * R := by gcongr
    _ = (|q 0| + |q 1|) * R := by ring

/-- **The gradient of the corrector at `x`** from the approximation of `u - a` by constants at the
scale `ρ` around `x`, for every constant `a`. -/
theorem abs_corrector_sub_le (C : OpenComponent ω) (q : Fin 2 → ℝ) (u : C → ℝ) (x : C)
    {ρ R C₀ : ℝ} (hR : 0 < R) (hC₀ : 0 ≤ C₀) (hρ : 0 ≤ ρ)
    (happ : ∀ a : ℝ, ∃ c : ℝ, componentBallL2 C x.val ρ ((fun y => u y - a) - fun _ => c) ≤
      C₀ * (ρ / R) * componentBallL2 C x.val R (fun y => u y - a))
    {y : C} (hx : x ∈ componentEuclideanBall C x.val ρ) (hy : y ∈ componentEuclideanBall C x.val ρ)
    (hyx : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) ≤ 1) :
    |componentCorrector C q u y - componentCorrector C q u x| ≤
      2 * (2 * ρ + 3) ^ 2 * C₀ * (ρ / R) *
        (componentBallL2 C x.val R (componentCorrector C q u) + (|q 0| + |q 1|) * R) +
      (|q 0| + |q 1|) := by
  obtain ⟨c, hc⟩ := happ (componentSlope C q x)
  have hinc := abs_sub_le_of_constant_approximation C x.val (fun y => u y - componentSlope C q x)
    (c := c) hx hy
  have hcard := card_componentEuclideanBall_le C x.val hρ
  have hL2 : componentBallL2 C x.val R (fun y => u y - componentSlope C q x) ≤
      componentBallL2 C x.val R (componentCorrector C q u) + (|q 0| + |q 1|) * R := by
    have e : (fun y => u y - componentSlope C q x) = fun y =>
        componentCorrector C q u y + (componentSlope C q y - componentSlope C q x) := by
      funext y; unfold componentCorrector; ring
    rw [e]
    refine (Rigidity.Proofs.S2.componentBallL2_add_le C x.val R _ _).trans ?_
    gcongr
    refine componentBallL2_le_of_abs_le C x.val R (by positivity) fun y hy => ?_
    have hd : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) < R := by
      rw [mem_componentEuclideanBall] at hy; exact hy
    exact abs_componentSlope_sub_le C q hd.le
  have hslope := abs_componentSlope_sub_le C q hyx
  have hL0 : 0 ≤ componentBallL2 C x.val ρ ((fun y => u y - componentSlope C q x) - fun _ => c) :=
    componentBallL2_nonneg _ _ _ _
  have hu : |u y - u x| ≤ 2 * (2 * ρ + 3) ^ 2 * C₀ * (ρ / R) *
      (componentBallL2 C x.val R (componentCorrector C q u) + (|q 0| + |q 1|) * R) := by
    have h1 : |u y - u x| ≤ 2 * ((componentEuclideanBall C x.val ρ).card : ℝ) *
        componentBallL2 C x.val ρ ((fun y => u y - componentSlope C q x) - fun _ => c) := by
      have : (u y - componentSlope C q x) - (u x - componentSlope C q x) = u y - u x := by ring
      rw [← this]; exact hinc
    calc |u y - u x| ≤ _ := h1
      _ ≤ 2 * (2 * ρ + 3) ^ 2 *
          (C₀ * (ρ / R) * componentBallL2 C x.val R (fun y => u y - componentSlope C q x)) := by
          gcongr
      _ ≤ 2 * (2 * ρ + 3) ^ 2 * (C₀ * (ρ / R) *
          (componentBallL2 C x.val R (componentCorrector C q u) + (|q 0| + |q 1|) * R)) := by
          gcongr
      _ = _ := by ring
  have e : componentCorrector C q u y - componentCorrector C q u x =
      (u y - u x) - (componentSlope C q y - componentSlope C q x) := by
    unfold componentCorrector; ring
  rw [e]
  calc |(u y - u x) - (componentSlope C q y - componentSlope C q x)|
      ≤ |u y - u x| + |componentSlope C q y - componentSlope C q x| := abs_sub _ _
    _ ≤ _ := by
        have h1 : (|q 0| + |q 1|) * 1 = |q 0| + |q 1| := mul_one _
        linarith

end Rigidity.Proofs.Regularity
