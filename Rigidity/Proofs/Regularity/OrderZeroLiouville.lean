import LatticeProb.Prob.Percolation.LatticeHarmonicGrowth
import Rigidity.Proofs.Regularity.ClusterBallExcess

/-!
# Liouville theorem of order zero from excess decay

The order-zero regularity of Armstrong and Dario (arXiv:1609.09431v2, Theorem 2 (iii), `k = 0`)
has two parts: the space `𝒜_0` of harmonic functions on the cluster with sublinear growth has
dimension one, and a function harmonic in `B_R` is approximated on every `B_r`,
`X ≤ r ≤ R / 2`, by an element of `𝒜_0` with error `C (r / R) ‖u‖_{L̲²(B_R)}`. When the
approximating functions are constants (as in `armstrongDario_orderZero_origin_cluster`), the first
part follows from the second: for `u ∈ 𝒜_0` the distance of `u` to the constants on `B_r` is at most
`C r ‖u‖_{L̲²(B_R)} / R → 0`, so `u` is constant on every ball, hence constant
(`harmonicGrowthSpace_zero_eq_span_of_decay`, `finrank_harmonicGrowthSpace_zero_of_decay`).
-/

namespace Rigidity.Proofs.Regularity

open Filter LatticeProb LatticeProb.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- `u` is harmonic at the vertices of `C ∩ B_R(0)` all of whose neighbours lie in the ball. -/
def IsHarmonicInBall (C : OpenComponent ω) (R : ℝ) (u : C → ℝ) : Prop :=
  ∀ x ∈ componentEuclideanBall C 0 R,
    (∀ y : C, (componentGraph C).Adj x y → y ∈ componentEuclideanBall C 0 R) →
      componentLaplacian C u x = 0

/-- A function whose distance to the constants on a cluster ball is arbitrarily small is constant
on the ball. -/
theorem eq_of_forall_componentBallL2_sub_const_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) (h : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, componentBallL2 C z r (u - fun _ => c) ≤ ε)
    {x y : C} (hx : x ∈ componentEuclideanBall C z r) (hy : y ∈ componentEuclideanBall C z r) :
    u x = u y := by
  classical
  by_contra hxy
  have hne : x ≠ y := fun h' => hxy (by rw [h'])
  set n := ((componentEuclideanBall C z r).card : ℝ) with hn
  have hcard : 0 < n := by
    rw [hn]; exact_mod_cast Finset.card_pos.2 ⟨x, hx⟩
  set δ := (u x - u y) ^ 2 / 2 with hδ
  have hδ0 : 0 < δ := by
    have : u x - u y ≠ 0 := sub_ne_zero.2 hxy
    positivity
  obtain ⟨c, hc⟩ := h (Real.sqrt (δ / n) / 2) (by positivity)
  have hsum : δ ≤ ∑ w ∈ componentEuclideanBall C z r, (u w - c) ^ 2 := by
    have hsub : ({x, y} : Finset C) ⊆ componentEuclideanBall C z r := by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hx
      · rw [Finset.mem_singleton.1 hw]; exact hy
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun w => (u w - c) ^ 2) fun _ _ _ => sq_nonneg _
    rw [Finset.sum_pair hne] at h1
    have h2 : (u x - u y) ^ 2 / 2 ≤ (u x - c) ^ 2 + (u y - c) ^ 2 := by
      nlinarith [sq_nonneg (u x + u y - 2 * c)]
    linarith
  have hL2 : Real.sqrt (δ / n) ≤ componentBallL2 C z r (u - fun _ => c) := by
    unfold componentBallL2
    simp only [Pi.sub_apply]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hsum hcard.le)
  have : 0 < Real.sqrt (δ / n) := Real.sqrt_pos.2 (by positivity)
  linarith

/-- **Liouville theorem of order zero.** If every function harmonic in `C ∩ B_R(0)`, `R ≥ 2 X`, is
within `K (r / R) ‖u‖_{L̲²(B_R)}` of a constant on every `B_r(0)`, `X ≤ r ≤ R / 2`, then every
element of `𝒜_0 = harmonicGrowthSpace C 0` is constant. -/
theorem exists_eq_const_of_decay (C : OpenComponent ω) {X K : ℝ}
    (hdecay : ∀ R : ℝ, 2 * X ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
      ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 C 0 r (u - fun _ => c) ≤ K * (r / R) * componentBallL2 C 0 R u)
    {u : C → ℝ} (hu : u ∈ harmonicGrowthSpace C 0) : ∃ c : ℝ, u = fun _ => c := by
  obtain ⟨hharm, hgrowth⟩ := hu
  have hball : ∀ R, IsHarmonicInBall C R u := fun R x _ _ => hharm x
  -- on every ball of radius `r ≥ max X 1`, `u` is constant
  have hconst : ∀ r : ℝ, max X 1 ≤ r → ∀ x ∈ componentEuclideanBall C 0 r,
      ∀ y ∈ componentEuclideanBall C 0 r, u x = u y := by
    intro r hr x hx y hy
    apply eq_of_forall_componentBallL2_sub_const_le C 0 r u _ hx hy
    intro ε hε
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hr)
    have hKr : 0 < (|K| + 1) * r := by positivity
    obtain ⟨R₀, hR₀, hR₀'⟩ := (componentL2Subpolynomial_iff_tail C 0 u).1 hgrowth
      (ε / ((|K| + 1) * r)) (by positivity)
    set R := max R₀ (2 * r) with hR
    have hR2r : 2 * r ≤ R := le_max_right _ _
    have hRpos : 0 < R := by linarith
    have hXR : 2 * X ≤ R := by
      have := le_max_left X 1
      linarith
    obtain ⟨c, hc⟩ := hdecay R hXR u (hball R)
    refine ⟨c, (hc r ((le_max_left _ _).trans hr) (by linarith)).trans ?_⟩
    have hsmall := hR₀' R (le_max_left _ _)
    rw [zero_add, pow_one] at hsmall
    have hN := componentBallL2_nonneg C 0 R u
    have e : K * (r / R) * componentBallL2 C 0 R u = K * r * (R⁻¹ * componentBallL2 C 0 R u) := by
      field_simp
    rw [e]
    have hRN : 0 ≤ R⁻¹ * componentBallL2 C 0 R u := mul_nonneg (inv_nonneg.2 hRpos.le) hN
    calc K * r * (R⁻¹ * componentBallL2 C 0 R u)
        ≤ (|K| + 1) * r * (R⁻¹ * componentBallL2 C 0 R u) := by
          apply mul_le_mul_of_nonneg_right _ hRN
          apply mul_le_mul_of_nonneg_right _ hr0.le
          linarith [le_abs_self K]
      _ ≤ (|K| + 1) * r * (ε / ((|K| + 1) * r)) :=
          mul_le_mul_of_nonneg_left hsmall.le hKr.le
      _ = ε := by field_simp
  -- every two vertices lie in a common ball
  by_cases hC : Nonempty C
  · obtain ⟨x₀⟩ := hC
    refine ⟨u x₀, funext fun y => ?_⟩
    set r := max (max X 1)
      (max (dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding 0))
        (dist (latticeEuclideanEmbedding x₀.val) (latticeEuclideanEmbedding 0)) + 1) with hr
    have hy : y ∈ componentEuclideanBall C 0 r := by
      rw [mem_componentEuclideanBall]
      have := le_max_left (dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding 0))
        (dist (latticeEuclideanEmbedding x₀.val) (latticeEuclideanEmbedding 0))
      have := le_max_right (max X 1)
        (max (dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding 0))
          (dist (latticeEuclideanEmbedding x₀.val) (latticeEuclideanEmbedding 0)) + 1)
      linarith
    have hx₀ : x₀ ∈ componentEuclideanBall C 0 r := by
      rw [mem_componentEuclideanBall]
      have := le_max_right (dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding 0))
        (dist (latticeEuclideanEmbedding x₀.val) (latticeEuclideanEmbedding 0))
      have := le_max_right (max X 1)
        (max (dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding 0))
          (dist (latticeEuclideanEmbedding x₀.val) (latticeEuclideanEmbedding 0)) + 1)
      linarith
    exact hconst r (le_max_left _ _) y hy x₀ hx₀
  · exact ⟨0, funext fun y => absurd ⟨y⟩ hC⟩

/-- Under the order-zero decay with constants, `𝒜_0` is the span of the constant function `1`. -/
theorem harmonicGrowthSpace_zero_eq_span_of_decay (C : OpenComponent ω) {X K : ℝ}
    (hdecay : ∀ R : ℝ, 2 * X ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
      ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 C 0 r (u - fun _ => c) ≤ K * (r / R) * componentBallL2 C 0 R u) :
    harmonicGrowthSpace C 0 = Submodule.span ℝ {fun _ : C => (1 : ℝ)} := by
  apply le_antisymm
  · intro u hu
    obtain ⟨c, rfl⟩ := exists_eq_const_of_decay C hdecay hu
    rw [Submodule.mem_span_singleton]
    exact ⟨c, funext fun _ => by simp⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact const_mem_harmonicGrowthSpace C 0 1

/-- **Dimension one of `𝒜_0`** from the order-zero decay with constants, on a nonempty cluster. -/
theorem finrank_harmonicGrowthSpace_zero_of_decay (C : OpenComponent ω) [Nonempty C] {X K : ℝ}
    (hdecay : ∀ R : ℝ, 2 * X ≤ R → ∀ u : C → ℝ, IsHarmonicInBall C R u →
      ∃ c : ℝ, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        componentBallL2 C 0 r (u - fun _ => c) ≤ K * (r / R) * componentBallL2 C 0 R u) :
    FiniteDimensional ℝ (harmonicGrowthSpace C 0) ∧
      Module.finrank ℝ (harmonicGrowthSpace C 0) = 1 := by
  have h := harmonicGrowthSpace_zero_eq_span_of_decay C hdecay
  have hne : (fun _ : C => (1 : ℝ)) ≠ 0 := by
    obtain ⟨x⟩ := ‹Nonempty C›
    intro h'
    have := congrFun h' x
    simp at this
  rw [h]
  exact ⟨inferInstance, finrank_span_singleton hne⟩

end Rigidity.Proofs.Regularity
