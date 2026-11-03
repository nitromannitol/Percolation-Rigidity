import Rigidity.Steps.S4.RationalMatrix
import LatticeProb.Prob.Percolation.CorrectedPlaneTranslation
import LatticeProb.External.SupercriticalBondCorrectorInput

/-!
# The difference of two translated quadratic-growth solutions

Proof of `Rigidity.Steps.S4.TranslateDifferenceStep` (`step:4.10-difference`, paper L1463-1496 of
the corrected draft). If `τ_{y₁} ω` and `τ_{y₂} ω` carry integer-valued harmonic functions `u₁`,
`u₂` with `|uₖ(x) - p̄(x)| = o(|x|)`, then on the cluster of `ω` the function
`v(x) = u₁(x + y₁) - u₂(x + y₂)` is integer-valued and harmonic, and since
`p̄(x + y₁) - p̄(x + y₂) = 2 (M (y₁ - y₂)) · x + p̄(y₁) - p̄(y₂)` for symmetric `M`, it lies within
`o(|x|)` of an affine function of slope `q = 2 M (y₁ - y₂)`. Hence `v` has linear growth and is a
corrected plane of slope `q`. The paper leaves the nonconstancy of `v` implicit: a constant is a
corrected plane of slope `0`, and the cited corrector input
(`LatticeProb.External.SupercriticalBondCorrectorInput`, Armstrong-Dario) makes the slope of an
element of `A₁(C_∞)` unique, so `q ≠ 0` forces `v` to be nonconstant.
-/

namespace Rigidity.Proofs.S4

open MeasureTheory Filter Topology LatticeProb.Percolation Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-- Away from the origin the `ℓ¹` norm of a lattice point is at least `1`. -/
theorem one_le_sum_abs_of_ne_zero {x : Vertex d} (hx : x ≠ 0) : 1 ≤ ∑ i, |(x i : ℝ)| := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (Finset.single_le_sum (fun j _ => abs_nonneg ((x j : ℤ) : ℝ)) (Finset.mem_univ i))

/-- Along the cofinite filter of a component, `x + y` stays away from the origin. -/
theorem eventually_one_le_sum_abs_add {ω : Configuration d} (C : OpenComponent ω) (y : Vertex d) :
    ∀ᶠ x : C in cofinite, 1 ≤ ∑ i, |((x.val + y) i : ℝ)| := by
  have hfin : {x : C | x.val + y = 0}.Finite :=
    ((Set.finite_singleton (-y)).preimage Subtype.val_injective.injOn).subset
      fun x hx => add_eq_zero_iff_eq_neg.mp hx
  filter_upwards [hfin.compl_mem_cofinite] with x hx
  exact one_le_sum_abs_of_ne_zero hx

/-- The `ℓ¹` norm of a vertex of the Euclidean ball `B_R` is at most `d R`. -/
theorem sum_abs_le_of_mem_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    {R : ℝ} {x : C} (hx : x ∈ componentEuclideanBall C 0 R) :
    ∑ i, |(x.val i : ℝ)| ≤ d * R := by
  rw [mem_componentEuclideanBall] at hx
  have hi : ∀ i, |(x.val i : ℝ)| ≤ R := by
    intro i
    have := PiLp.dist_apply_le (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding (0 : Vertex d)) i
    simp only [latticeEuclideanEmbedding, Function.Embedding.coeFn_mk] at this hx
    simp only [Pi.zero_apply, Int.cast_zero] at hx
    simp at this
    exact this.trans hx.le
  calc ∑ i, |(x.val i : ℝ)| ≤ ∑ _i : Fin d, R := Finset.sum_le_sum fun i _ => hi i
    _ = d * R := by simp

/-- A harmonic function within `o(|x|)` of the affine function `x ↦ q · x + K` is a corrected
plane of slope `q`. -/
theorem isCorrectedPlane_of_tendsto {ω : Configuration d} (C : OpenComponent ω) (q : Fin d → ℝ)
    (K : ℝ) (w : C → ℝ) (hharm : ∀ x, componentLaplacian C w x = 0)
    (ht : Tendsto (fun x : C => |w x - quadratic 0 q K x.val| / ∑ i, |(x.val i : ℝ)|)
      cofinite (𝓝 0)) :
    IsCorrectedPlane C q w := by
  rw [isCorrectedPlane_iff_harmonic_and_slope_asymptotics]
  refine ⟨hharm, fun ε hε => ?_⟩
  set δ : ℝ := ε / (2 * (d + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hq : ∀ x : C, quadratic 0 q K x.val = componentSlope C q x + K := by
    intro x
    simp [quadratic, componentSlope]
  set S : Set C := {x | ¬ (|w x - quadratic 0 q K x.val| / ∑ i, |(x.val i : ℝ)| < δ ∧
      1 ≤ ∑ i, |(x.val i : ℝ)|)}
  have hS : S.Finite := by
    have h0 := eventually_one_le_sum_abs_add C 0
    simp only [add_zero] at h0
    exact Filter.eventually_cofinite.mp ((ht.eventually (gt_mem_nhds hδ)).and h0)
  obtain ⟨B, hB⟩ := (hS.image fun x => |w x - quadratic 0 q K x.val|).bddAbove
  set A : ℝ := |B| + |K| + 1
  have hA : 0 < A := by positivity
  refine ⟨2 * A / ε, by positivity, fun R hR x hx => ?_⟩
  have hAR : 2 * A ≤ ε * R := by
    rw [div_le_iff₀ hε] at hR
    linarith
  have hsplit : |w x - componentSlope C q x| ≤ |w x - quadratic 0 q K x.val| + |K| := by
    rw [hq]
    calc |w x - componentSlope C q x| = |(w x - (componentSlope C q x + K)) + K| := by ring_nf
      _ ≤ |w x - (componentSlope C q x + K)| + |K| := abs_add_le _ _
  by_cases hxS : x ∈ S
  · have h1 : |w x - quadratic 0 q K x.val| ≤ B := hB ⟨x, hxS, rfl⟩
    have h2 : B ≤ |B| := le_abs_self B
    linarith
  · simp only [S, Set.mem_setOf_eq, not_not] at hxS
    obtain ⟨hlt, hn⟩ := hxS
    have hn0 : 0 < ∑ i, |(x.val i : ℝ)| := lt_of_lt_of_le one_pos hn
    have h1 : |w x - quadratic 0 q K x.val| < δ * ∑ i, |(x.val i : ℝ)| :=
      (div_lt_iff₀ hn0).mp hlt
    have h2 : ∑ i, |(x.val i : ℝ)| ≤ d * R := sum_abs_le_of_mem_componentEuclideanBall C hx
    have hR0 : 0 ≤ R := by
      have : 0 ≤ ε * R := by linarith
      exact nonneg_of_mul_nonneg_right (by linarith) hε
    have hdd : (d : ℝ) / (d + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h3 : δ * (d * R) ≤ ε * R / 2 := by
      calc δ * (d * R) = ε * R / 2 * ((d : ℝ) / (d + 1)) := by
            rw [hδdef]
            field_simp
        _ ≤ ε * R / 2 := mul_le_of_le_one_right (by positivity) hdd
    have h4 : δ * ∑ i, |(x.val i : ℝ)| ≤ δ * (d * R) := mul_le_mul_of_nonneg_left h2 hδ.le
    have hKA : |K| + 1 ≤ A := by
      simp only [A]
      linarith [abs_nonneg B]
    linarith

/-- For symmetric `M`, the difference of two translates of `p̄(x) = xᵀ M x + bᵀ x + c` is the
affine function of slope `2 M (y₁ - y₂)` with constant term `p̄(y₁) - p̄(y₂)`. -/
theorem quadratic_add_sub_quadratic_add (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsSymm)
    (b : Fin d → ℝ) (c : ℝ) (x y₁ y₂ : Vertex d) :
    quadratic M b c (x + y₁) - quadratic M b c (x + y₂) =
      quadratic 0 ((2 : ℝ) • M.mulVec (fun i => ((y₁ i - y₂ i : ℤ) : ℝ)))
        (quadratic M b c y₁ - quadratic M b c y₂) x := by
  have hexp : ∀ a : Vertex d,
      ∑ i, ∑ j, M i j * ((x i : ℝ) + (a i : ℝ)) * ((x j : ℝ) + (a j : ℝ)) =
        ∑ i, ∑ j, M i j * (x i : ℝ) * (x j : ℝ) +
          2 * ∑ i, ∑ j, M i j * (a j : ℝ) * (x i : ℝ) + ∑ i, ∑ j, M i j * (a i : ℝ) * (a j : ℝ) := by
    intro a
    have hsw : ∑ i, ∑ j, M i j * (a i : ℝ) * (x j : ℝ) = ∑ i, ∑ j, M i j * (a j : ℝ) * (x i : ℝ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM.apply]
    have hsplit : ∑ i, ∑ j, M i j * ((x i : ℝ) + (a i : ℝ)) * ((x j : ℝ) + (a j : ℝ)) =
        ∑ i, ∑ j, M i j * (x i : ℝ) * (x j : ℝ) + ∑ i, ∑ j, M i j * (a j : ℝ) * (x i : ℝ) +
          ∑ i, ∑ j, M i j * (a i : ℝ) * (x j : ℝ) + ∑ i, ∑ j, M i j * (a i : ℝ) * (a j : ℝ) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, hsw]
    ring
  have hlin : ∑ i, (2 * ∑ j, M i j * ((y₁ j : ℝ) - (y₂ j : ℝ))) * (x i : ℝ) =
      2 * ∑ i, ∑ j, M i j * (y₁ j : ℝ) * (x i : ℝ) -
        2 * ∑ i, ∑ j, M i j * (y₂ j : ℝ) * (x i : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [quadratic, Pi.add_apply, Int.cast_add, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul,
    Int.cast_sub]
  rw [hexp y₁, hexp y₂, hlin]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- Pulling a quadratic-growth solution on the translated cluster `C + y` back to `C`: the
function `x ↦ u(x + y)` is harmonic, integer-valued and within `o(|x|)` of `p̄(x + y)`. -/
theorem exists_pullback_translation {ω : Configuration d} (C : OpenComponent ω) (y : Vertex d)
    (D : OpenComponent (configurationTranslation y ω)) (hD : openComponentTranslation y ω C = D)
    (M : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (c : ℝ) (u : D → ℝ)
    (hu : ∀ x, componentLaplacian D u x = 0) (hi : ∀ x, ∃ z : ℤ, u x = (z : ℝ))
    (ht : Tendsto (fun x : D => |u x - quadratic M b c x.val| / ∑ i, |(x.val i : ℝ)|)
      cofinite (𝓝 0)) :
    ∃ w : C → ℝ, (∀ x, componentLaplacian C w x = 0) ∧ (∀ x, ∃ z : ℤ, w x = (z : ℝ)) ∧
      Tendsto (fun x : C => |w x - quadratic M b c (x.val + y)| / ∑ i, |(x.val i : ℝ)|)
        cofinite (𝓝 0) := by
  subst hD
  set e := openComponentTranslationIso y C
  refine ⟨fun x => u (e x), fun x => ?_, fun x => hi (e x), ?_⟩
  · have hl := componentLaplacian_translation y C (fun x => u (e x)) x
    simp only [e, RelIso.apply_symm_apply] at hl
    rw [← hl]
    exact hu _
  · have hte : Tendsto (fun x : C =>
        |u (e x) - quadratic M b c (x.val + y)| / ∑ i, |((x.val + y) i : ℝ)|) cofinite (𝓝 0) :=
      ht.comp e.injective.tendsto_cofinite
    set Y : ℝ := ∑ i, |(y i : ℝ)|
    have hY : 0 ≤ Y := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hK := hte.const_mul (1 + Y)
    rw [mul_zero] at hK
    refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hK
    filter_upwards [eventually_one_le_sum_abs_add C y, eventually_one_le_sum_abs_add C 0]
      with x h1 h0
    simp only [add_zero] at h0
    set r : ℝ := |u (e x) - quadratic M b c (x.val + y)|
    have hn' : ∑ i, |((x.val + y) i : ℝ)| ≤ (1 + Y) * ∑ i, |(x.val i : ℝ)| := by
      calc ∑ i, |((x.val + y) i : ℝ)| ≤ ∑ i, (|(x.val i : ℝ)| + |(y i : ℝ)|) :=
            Finset.sum_le_sum fun i _ => by rw [Pi.add_apply, Int.cast_add]; exact abs_add_le _ _
        _ = ∑ i, |(x.val i : ℝ)| + Y := Finset.sum_add_distrib
        _ ≤ ∑ i, |(x.val i : ℝ)| + Y * ∑ i, |(x.val i : ℝ)| := by nlinarith
        _ = (1 + Y) * ∑ i, |(x.val i : ℝ)| := by ring
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
    calc r * ∑ i, |((x.val + y) i : ℝ)| ≤ r * ((1 + Y) * ∑ i, |(x.val i : ℝ)|) :=
          mul_le_mul_of_nonneg_left hn' (abs_nonneg _)
      _ = (1 + Y) * r * ∑ i, |(x.val i : ℝ)| := by ring

/-- **Step `step:4.10-difference`.** Almost surely, if `τ_{y₁} ω` and `τ_{y₂} ω` lie in the
event `E` of Proposition 4.10 and `M (y₁ - y₂) ≠ 0`, then `v(x) = u₁(x + y₁) - u₂(x + y₂)` is a
nonconstant integer-valued harmonic function of linear growth on the cluster of `ω`. -/
theorem translateDifference [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcorrector : LatticeProb.External.SupercriticalBondCorrectorInput) :
    TranslateDifferenceStep d p := by
  intro M b c hM
  filter_upwards [hcorrector d hd p hpc hp1] with ω hω h y₁ y₂ hne hE₁ hE₂
  set C := uniqueInfiniteComponent h
  obtain ⟨h₁, u₁, hu₁, hi₁, ht₁, -⟩ := hE₁
  obtain ⟨h₂, u₂, hu₂, hi₂, ht₂, -⟩ := hE₂
  obtain ⟨w₁, hw₁, hwi₁, hwt₁⟩ := exists_pullback_translation C y₁ _
    (openComponentTranslation_uniqueInfiniteComponent y₁ h) M b c u₁ hu₁ hi₁ ht₁
  obtain ⟨w₂, hw₂, hwi₂, hwt₂⟩ := exists_pullback_translation C y₂ _
    (openComponentTranslation_uniqueInfiniteComponent y₂ h) M b c u₂ hu₂ hi₂ ht₂
  set q : Fin d → ℝ := (2 : ℝ) • M.mulVec (fun i => ((y₁ i - y₂ i : ℤ) : ℝ))
  set K : ℝ := quadratic M b c y₁ - quadratic M b c y₂
  set v : C → ℝ := fun x => w₁ x - w₂ x
  have hv : ∀ x, componentLaplacian C v x = 0 := by
    intro x
    have hsub : componentLaplacian C v x =
        componentLaplacian C w₁ x - componentLaplacian C w₂ x := by
      simp only [componentLaplacian, v, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsub, hw₁, hw₂, sub_zero]
  have hvi : ∀ x, ∃ z : ℤ, v x = (z : ℝ) := by
    intro x
    obtain ⟨z₁, hz₁⟩ := hwi₁ x
    obtain ⟨z₂, hz₂⟩ := hwi₂ x
    exact ⟨z₁ - z₂, by simp [v, hz₁, hz₂]⟩
  have hvt : Tendsto (fun x : C => |v x - quadratic 0 q K x.val| / ∑ i, |(x.val i : ℝ)|)
      cofinite (𝓝 0) := by
    have hsum := hwt₁.add hwt₂
    rw [add_zero] at hsum
    refine squeeze_zero (fun x => by positivity) (fun x => ?_) hsum
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => abs_nonneg _)
    rw [← quadratic_add_sub_quadratic_add M hM b c x.val y₁ y₂]
    calc |v x - (quadratic M b c (x.val + y₁) - quadratic M b c (x.val + y₂))|
        = |(w₁ x - quadratic M b c (x.val + y₁)) - (w₂ x - quadratic M b c (x.val + y₂))| := by
          simp only [v]
          ring_nf
      _ ≤ |w₁ x - quadratic M b c (x.val + y₁)| + |w₂ x - quadratic M b c (x.val + y₂)| :=
          abs_sub _ _
  have hplane : IsCorrectedPlane C q v := isCorrectedPlane_of_tendsto C q K v hv hvt
  refine ⟨v, hv, hvi, componentPointwiseLinearGrowth_of_tendsto_affine C v q K hvt, ?_⟩
  by_contra hconst
  push Not at hconst
  obtain ⟨o, ho⟩ := C.nonempty_supp
  have heq : v = fun _ => v ⟨o, ho⟩ := funext fun x => hconst x _
  have hzero : IsCorrectedPlane C 0 v := by
    rw [heq]
    exact isCorrectedPlane_const _ _
  obtain ⟨_, _, hunique⟩ := (hω h).2 v hplane.1
  exact smul_ne_zero two_ne_zero hne ((hunique q hplane).trans (hunique 0 hzero).symm)

end Rigidity.Proofs.S4
