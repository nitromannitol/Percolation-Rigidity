import Rigidity.Proofs.S2.ScaleInputs
import PercolationClusterHomogenization.Proofs.Density.ScaleInputsFaithful

/-!
# Proposition 2.6, step:2.6-inputs: the literature inputs as printed

The two local proposed inputs of `Rigidity.Proofs.S2` (`ArmstrongDarioOrderOneProposed`,
`ClusterDensityInputProposed`) are stronger than the sentences of the corrected draft that cite
them. This file states the two inputs exactly as printed and
derives the proposed forms from them.

* `ClusterDensityInputFaithful`: paper L508-511: beyond `M_dense(x) ≤ O_s(C)`, any ball of radius
  `r/100` containing the vertex `x` contains at least `𝔠 r^d` vertices of `𝒞_∞`. Source
  (correction C35): Dario–Gu, arXiv:1909.10439v4, Proposition A.1, with a union bound over
  triadic cubes (`clusterDensityInputFaithful_of_concentration`, `ClusterDensityFromDarioGu.lean`).
* `ArmstrongDarioOrderOneFaithful`: eq. (large scale-regularity), paper L513-518: for
  `R ≥ 2 M_reg(x)` and `u ∈ 𝒜(𝒞_∞ ∩ B_{2R}(x))` there is a slope `ξ` with
  `inf_a ‖u - ℓ_ξ - a‖_{L̲²(𝒞_∞ ∩ B_r(x))} ≤ C (r/R)² ‖u‖_{L̲²(𝒞_∞ ∩ B_R(x))}` for
  `r ∈ [M_reg(x), R/2]`.

Main results.
* `clusterDensityInputProposed_of_faithful`: the printed density sentence at every centre gives
  `ClusterDensityInputProposed` (centres in `B̄_r(x)`), with the same exponent `s`: a union bound over
  the centres (`tailOfOsStep`, `exists_radial_scale_exp_moment`) and the scale
  `max (100 M_rad(x)) M_dense(x)`; centres within `M_rad(x)` of `x` are covered by balls containing `x`.
* `armstrongDarioOrderOneProposed_of_faithful`: `ArmstrongDarioOrderOneProposed` from the printed
  form, the printed density and `CorrectorQuantitativeInput` (at `α = 1/2`). The deterministic part
  is `regularityProposedAt_of_faithfulAt`: the printed form at radius `R/2` covers `r ≤ R/4`; one
  constant serves all scales by a dyadic chain of near-minimizing constants (density ratios,
  `componentBallL2_le_sqrt_card_div_mul`); the range `r ∈ (R/4, R/2]` uses the doubling of `ℓ_ξ + a`
  (`correctedPlane_doubling`, from the corrector bounds and `affineMajorizationStep`).
* `regularityScaleStep_of_faithful`, `densityScaleStep_of_faithful`,
  `greenGradientHomogenization_of_faithfulInputs`: steps 2.6-inputs and Proposition 2.6 from the
  printed inputs.

The consumer step `RegularityAt` (harmonic in `B_R`, estimate up to `r = R/2`) is stronger than the
printed form (harmonic in `B_{2R}`); its only consumer (`GreenGradientCore.lean`) applies it to a
function harmonic in `B_{2R}(x)`. The doubling estimate bridges the two here.
-/

namespace Rigidity.Proofs.S2

open MeasureTheory LatticeProb.Percolation Rigidity.Steps.S2
open Rigidity.External (IsOsBond)

/-- **Large-scale `C^{1,1}` regularity**, eq. (large scale-regularity) as printed at paper
L513-518 (literature input; Armstrong–Dario, CPAM 71 (2018), the large-scale `C^{k,1}` estimate
at `k = 1`, with the first-order correctors of Theorem 2.5): there are `s, C > 0` and, for every
vertex `x`, a minimal scale `M_reg(x) ≤ O_s(C)` such that for every `R ≥ 2 M_reg(x)` and every
`u` harmonic in `𝒞_∞ ∩ B_{2R}(x)` there is a slope `ξ` (with a corrected plane `ℓ_ξ` of slope `ξ`)
such that `inf_a ‖u - ℓ_ξ - a‖_{L̲²(𝒞_∞ ∩ B_r(x))} ≤ C (r/R)² ‖u‖_{L̲²(𝒞_∞ ∩ B_R(x))}` for every
`r ∈ [M_reg(x), R/2]`. The constant `a` may depend on `r`. Harmonicity in `𝒞_∞ ∩ B_{2R}(x)` is
imposed at the vertices of the ball all of whose cluster neighbours lie in the ball. -/
def ArmstrongDarioOrderOneFaithful : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d → ∀ p : unitInterval,
    criticalProbability d < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, 2 * M ω ≤ R → ∀ u : uniqueInfiniteComponent h → ℝ,
          (∀ z ∈ componentEuclideanBall (uniqueInfiniteComponent h) x (2 * R),
            (∀ w, (componentGraph (uniqueInfiniteComponent h)).Adj z w →
              w ∈ componentEuclideanBall (uniqueInfiniteComponent h) x (2 * R)) →
            componentLaplacian (uniqueInfiniteComponent h) u z = 0) →
          ∃ (ξ : Fin d → ℝ) (ℓ : uniqueInfiniteComponent h → ℝ),
            IsCorrectedPlane (uniqueInfiniteComponent h) ξ ℓ ∧
            ∀ r : ℝ, M ω ≤ r → r ≤ R / 2 →
              (⨅ a : ℝ, componentBallL2 (uniqueInfiniteComponent h) x r (fun z => u z - ℓ z - a))
                ≤ C * (r / R) ^ 2 * componentBallL2 (uniqueInfiniteComponent h) x R u

/-! ### The `O_s` calculus and the density input -/

section Density

variable {d : ℕ} {p : unitInterval}

theorem ncard_eq_card_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    ({w : C | dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z) < r}.ncard : ℝ) =
      ((componentEuclideanBall C z r).card : ℝ) := by
  rw [Set.ncard_eq_toFinset_card _ (finite_componentEuclideanBall C z r)]
  rfl

/-- The uniform density lower bound at a fixed dimension and bond parameter. -/
def ClusterDensityInputProposedAt (d : ℕ) (p : unitInterval) : Prop :=
  ∃ s C c : ℝ, 0 < s ∧ 0 < C ∧ 0 < c ∧ ∀ x : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ r : ℝ, M ω ≤ r → ∀ z : Vertex d,
          dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) ≤ r →
            c * r ^ d ≤
              ((componentEuclideanBall (uniqueInfiniteComponent h) z (r / 100)).card : ℝ)

/-- The density sentence at every centre implies the uniform bound at that dimension. -/
theorem clusterDensityInputProposedAt_of_faithfulAt [NeZero d] (p : unitInterval)
    (hD : ClusterDensityInputFaithfulAt d p) : ClusterDensityInputProposedAt d p := by
  obtain ⟨s, C, c, hs, hC, hc, hx⟩ := hD
  choose Md hMdm hMd0 hMdO hMda using hx
  obtain ⟨Ct, hCt, htail⟩ := tailOfOsStep d p s C hs hC
  have hTail : ∀ z, HasStretchedExpTail d p (Md z) s Ct :=
    fun z => htail (Md z) (hMdm z) (hMdO z)
  obtain ⟨C₀, hC₀, hrad⟩ := exists_radial_scale_exp_moment (d := d) (Ω := Configuration d)
    Ct s 1 hCt hs one_pos
  refine ⟨s, max (100 * C₀) C * 4 ^ (1 / s), c, hs, ?_, hc, fun x => ?_⟩
  · exact mul_pos (lt_max_of_lt_right hC) (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨Mr, hMrm, hMr1, hint, hmom, hae⟩ := hrad (latticeBondLaw d p) (fun z => Md z) hMdm
    (fun z t ht => hTail z t ht.le) x
  have hMrO : IsOsBond d p Mr s C₀ := by
    have e : ∀ ω, Real.rpow (max (Mr ω / C₀) 0) s = (Mr ω / C₀) ^ (1 * s) := by
      intro ω
      rw [one_mul, max_eq_left (div_nonneg (zero_le_one.trans (hMr1 ω)) hC₀.le)]
      rfl
    unfold IsOsBond
    simp only [e]
    exact ⟨hint, hmom⟩
  have hA : IsOsBond d p (fun ω => 100 * Mr ω) s (100 * C₀) :=
    IsOsBond.const_mul (by norm_num) hMrO
  have hM' : IsOsBond d p (fun ω => max (100 * Mr ω) (Md x ω)) s (max (100 * C₀) C * 4 ^ (1 / s)) :=
    IsOsBond.max hs (by positivity) hC (hMrm.const_mul 100) (hMdm x) hA (hMdO x)
  refine ⟨fun ω => max (100 * Mr ω) (Md x ω), (hMrm.const_mul 100).max (hMdm x),
    fun ω => le_max_of_le_left (by linarith [hMr1 ω]), hM', ?_⟩
  have hfaith := ae_all_iff.2 (fun z => hMda z)
  filter_upwards [hfaith, hae] with ω hf hr
  intro h r hr' z hz
  have h1 : 100 * Mr ω ≤ r := le_trans (le_max_left _ _) hr'
  have h2 : Md x ω ≤ r := le_trans (le_max_right _ _) hr'
  have hMr := hMr1 ω
  have hr0 : 0 < r / 100 := by linarith
  rw [← ncard_eq_card_componentEuclideanBall]
  by_cases hlt : ‖latticeEuclideanEmbedding z - latticeEuclideanEmbedding x‖ < Mr ω
  · refine hf x h r h2 (latticeEuclideanEmbedding z) ?_
    rw [dist_comm, dist_eq_norm]
    linarith
  · push Not at hlt
    have h3 := hr z hlt
    rw [Real.rpow_one] at h3
    refine hf z h r ?_ (latticeEuclideanEmbedding z) ?_
    · rw [dist_eq_norm] at hz
      linarith
    · rw [dist_self]
      exact hr0

/-- The printed density sentence at every centre gives the proposed form (centres in `B̄_r(x)`). -/
theorem clusterDensityInputProposed_of_faithful (hD : ClusterDensityInputFaithful) :
    ClusterDensityInputProposed := by
  intro d _ hd p hpc hp1
  exact clusterDensityInputProposedAt_of_faithfulAt p (hD d hd p hpc hp1)

end Density

/-! ### Large-scale regularity: from the printed form to the proposed form -/

section Regularity

variable {d : ℕ}

/-- eq. (large scale-regularity) at `x` beyond the scale `M`, as printed: `u` harmonic in
`𝒞 ∩ B_{2R}(x)`, the constant `a` may depend on `r`. -/
def RegularityFaithfulAt {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d) (C₁ M : ℝ) :
    Prop :=
  ∀ R : ℝ, 2 * M ≤ R → ∀ u : C → ℝ,
    (∀ z ∈ componentEuclideanBall C x (2 * R),
      (∀ w, (componentGraph C).Adj z w → w ∈ componentEuclideanBall C x (2 * R)) →
        componentLaplacian C u z = 0) →
    ∃ (ξ : Fin d → ℝ) (ℓ : C → ℝ), IsCorrectedPlane C ξ ℓ ∧
      ∀ r : ℝ, M ≤ r → r ≤ R / 2 →
        (⨅ a : ℝ, componentBallL2 C x r (fun z => u z - ℓ z - a)) ≤
          C₁ * (r / R) ^ 2 * componentBallL2 C x R u

/-- The proposed form at `x` beyond `M`: `u` harmonic in `𝒞 ∩ B_R(x)`, one `φ ∈ 𝒜₁` for every
`r ∈ [M, R/2]`. -/
def RegularityProposedAt {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d) (C₀ M : ℝ) :
    Prop :=
  ∀ R : ℝ, 2 * M ≤ R → ∀ u : C → ℝ,
    (∀ z ∈ componentEuclideanBall C x R,
      (∀ w, (componentGraph C).Adj z w → w ∈ componentEuclideanBall C x R) →
        componentLaplacian C u z = 0) →
    ∃ φ ∈ harmonicGrowthSpace C 1, ∀ r : ℝ, M ≤ r → r ≤ R / 2 →
      componentBallL2 C x r (u - φ) ≤ C₀ * (r / R) ^ 2 * componentBallL2 C x R u

/-- A coordinate difference is at most the Euclidean distance. -/
theorem regDet_abs_coord_le (z x : Vertex d) (i : Fin d) :
    |(z i : ℝ) - (x i : ℝ)| ≤
      dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) := by
  have hi := PiLp.norm_apply_le (latticeEuclideanEmbedding z - latticeEuclideanEmbedding x) i
  change |(z i : ℝ) - (x i : ℝ)| ≤
    ‖latticeEuclideanEmbedding z - latticeEuclideanEmbedding x‖ at hi
  rwa [← dist_eq_norm] at hi

/-- A linear form `η · (z - x)` on `B_r(x)` is at most `r |η|₁`. -/
theorem regDet_abs_affine_le (ξ : Fin d → ℝ) (z x : Vertex d) {r : ℝ}
    (hz : dist (latticeEuclideanEmbedding z) (latticeEuclideanEmbedding x) < r) :
    |∑ i, ξ i * ((z i : ℝ) - (x i : ℝ))| ≤ r * ∑ i, |ξ i| := by
  calc |∑ i, ξ i * ((z i : ℝ) - (x i : ℝ))| ≤ ∑ i, |ξ i * ((z i : ℝ) - (x i : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, r * |ξ i| := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, mul_comm r]
        exact mul_le_mul_of_nonneg_left ((regDet_abs_coord_le z x i).trans hz.le) (abs_nonneg _)
    _ = r * ∑ i, |ξ i| := by rw [Finset.mul_sum]

/-- Under (H4), `#B_ρ(x) ≥ c (100ρ)^d` for `ρ ≥ X`. -/
theorem regDet_card_ge {ω : Configuration d} {C : OpenComponent ω} {x : Vertex d} {c X ρ : ℝ}
    (hD : DenseAt C x c X) (hXρ : X ≤ ρ) (hρ : 0 ≤ ρ) :
    c * (100 * ρ) ^ d ≤ ((componentEuclideanBall C x ρ).card : ℝ) := by
  have h := hD (100 * ρ) (by linarith) x (by rw [dist_self]; linarith)
  rwa [show 100 * ρ / 100 = ρ by ring] at h

/-- `‖f‖ ≤ ‖g‖ + ‖f - g‖`. -/
theorem regDet_le_add_sub {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d) (r : ℝ)
    (f g : C → ℝ) :
    componentBallL2 C x r f ≤ componentBallL2 C x r g + componentBallL2 C x r (fun z => f z - g z) := by
  have h := componentBallL2_add_le C x r g (fun z => f z - g z)
  simpa only [add_sub_cancel] using h

/-- `Cc (2ρ)^{1/2} ≤ m ρ` once `ρ ≥ 2 Cc² / m²`. -/
theorem regDet_rpow_bound {Cc m ρ : ℝ} (hCc : 0 < Cc) (hm : 0 < m)
    (hρ : 2 * Cc ^ 2 / m ^ 2 ≤ ρ) : Cc * (2 * ρ) ^ (1 / 2 : ℝ) ≤ m * ρ := by
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  rw [← Real.sqrt_eq_rpow]
  set t := Real.sqrt (2 * ρ) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 2 * ρ := Real.sq_sqrt (by linarith)
  have hlow : 2 * Cc / m ≤ t := by
    rw [ht, Real.le_sqrt (x := 2 * Cc / m) (y := 2 * ρ) (by positivity) (by linarith)]
    have e : (2 * Cc / m) ^ 2 = 2 * (2 * Cc ^ 2 / m ^ 2) := by ring
    rw [e]; linarith
  have h1 : 2 * Cc ≤ m * t := by rw [div_le_iff₀ hm] at hlow; linarith
  nlinarith [mul_le_mul_of_nonneg_right h1 ht0]

/-- Doubling of `ℓ_ξ + a` beyond the density and corrector scales. -/
theorem correctedPlane_doubling [NeZero d] {c Cc : ℝ} (hc : 0 < c) (hCc : 0 < Cc) :
    ∃ K ρ₀ : ℝ, 0 < K ∧ 1 ≤ ρ₀ ∧ ∀ {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d)
      (X : ℝ), DenseAt C x c X → CorrectorBoundAt C x Cc (1 / 2) X →
      ∀ (ξ : Fin d → ℝ) (ℓ : C → ℝ), IsCorrectedPlane C ξ ℓ → ∀ a ρ : ℝ, X ≤ ρ → ρ₀ ≤ ρ →
        componentBallL2 C x (2 * ρ) (fun z => ℓ z + a) ≤
          K * componentBallL2 C x ρ (fun z => ℓ z + a) := by
  obtain ⟨c₁, R₀, hc₁, hR₀, hAM⟩ := affineMajorizationStep (d := d) c hc
  set m := min (c₁ / 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  refine ⟨2 * (1 + 4 / c₁), max (max 1 R₀) (max (2 / c) (2 * Cc ^ 2 / m ^ 2)), by positivity,
    le_max_of_le_left (le_max_left _ _), ?_⟩
  intro ω C x X hD hCB ξ ℓ hℓ a ρ hXρ hρ₀
  have hρ1 : 1 ≤ ρ := le_trans (le_max_of_le_left (le_max_left _ _)) hρ₀
  have hρR : R₀ ≤ ρ := le_trans (le_max_of_le_left (le_max_right _ _)) hρ₀
  have hρc : 2 / c ≤ ρ := le_trans (le_max_of_le_right (le_max_left _ _)) hρ₀
  have hρE : 2 * Cc ^ 2 / m ^ 2 ≤ ρ := le_trans (le_max_of_le_right (le_max_right _ _)) hρ₀
  set E := Cc * (2 * ρ) ^ (1 / 2 : ℝ) with hEdef
  have hE : E ≤ m * ρ := regDet_rpow_bound hCc hm0 hρE
  have hE1 : E ≤ c₁ / 2 * ρ :=
    hE.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith))
  have hE2 : E ≤ ρ := by
    have := mul_le_mul_of_nonneg_right (min_le_right (c₁ / 2) 1) (show 0 ≤ ρ by linarith)
    rw [← hm] at this; linarith
  have hE0 : 0 ≤ E := mul_nonneg hCc.le (Real.rpow_nonneg (by linarith) _)
  -- an open edge `(o, o')` with `o ∈ B_ρ(x)`
  have hcard := regDet_card_ge hD hXρ (by linarith)
  have hcard2 : (1 : ℝ) < (componentEuclideanBall C x ρ).card := by
    have h100 : 100 * ρ ≤ (100 * ρ) ^ d := le_self_pow₀ (by linarith) (NeZero.ne d)
    have : 2 ≤ c * ρ := by rw [div_le_iff₀ hc] at hρc; linarith
    nlinarith
  have hcardN : 1 < (componentEuclideanBall C x ρ).card := by exact_mod_cast hcard2
  obtain ⟨o, ho⟩ := Finset.card_pos.mp (by omega : 0 < (componentEuclideanBall C x ρ).card)
  have hne : (componentEuclideanBall C x ρ).Nonempty := ⟨o, ho⟩
  obtain ⟨o', hadj⟩ := exists_componentGraph_adj o hcardN
  have hoo' : dist (latticeEuclideanEmbedding o'.val) (latticeEuclideanEmbedding o.val) = 1 :=
    dist_embedding_adj (ω := ω) (show (openGraph ω).Adj o'.val o.val from hadj.symm)
  have hoD := (mem_componentEuclideanBall C x ρ o).mp ho
  have ho2 : ‖latticeEuclideanEmbedding o.val - latticeEuclideanEmbedding x‖ < 2 * ρ := by
    rw [← dist_eq_norm]; linarith
  have ho'2 : ‖latticeEuclideanEmbedding o'.val - latticeEuclideanEmbedding x‖ < 2 * ρ := by
    rw [← dist_eq_norm]
    linarith [dist_triangle (latticeEuclideanEmbedding o'.val) (latticeEuclideanEmbedding o.val)
      (latticeEuclideanEmbedding x)]
  set s := ∑ i, |ξ i| with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => abs_nonneg _
  -- oscillation of the corrector on `B_{2ρ}(x)`
  have hosc : ∀ z ∈ componentEuclideanBall C x (2 * ρ),
      |(ℓ z - ∑ i, ξ i * (z.val i : ℝ)) - (ℓ o - ∑ i, ξ i * (o.val i : ℝ))| ≤ E * s := by
    intro z hz
    rw [mem_componentEuclideanBall, dist_eq_norm] at hz
    have h := hCB ξ ℓ hℓ (2 * ρ) (by linarith) z o o o' hz ho2 ho2 ho'2 hadj
    have := abs_nonneg ((ℓ o - ∑ i, ξ i * (o.val i : ℝ)) - (ℓ o' - ∑ i, ξ i * (o'.val i : ℝ)))
    have e : Cc * s * (2 * ρ) ^ (1 / 2 : ℝ) = E * s := by rw [hEdef]; ring
    linarith
  -- the affine comparison function
  set b₀ := ℓ o + a - ∑ i, ξ i * ((o.val i : ℝ) - (x i : ℝ)) with hb₀
  set A : C → ℝ := fun z => b₀ + ∑ i, ξ i * ((z.val i : ℝ) - (x i : ℝ)) with hA
  have hwA : ∀ z : C, (ℓ z + a) - A z =
      (ℓ z - ∑ i, ξ i * (z.val i : ℝ)) - (ℓ o - ∑ i, ξ i * (o.val i : ℝ)) := by
    intro z
    simp only [hA, hb₀, mul_sub, Finset.sum_sub_distrib]
    ring
  have hN := hAM C x X ρ hD hXρ hρR b₀ ξ
  have hsub : componentEuclideanBall C x ρ ⊆ componentEuclideanBall C x (2 * ρ) :=
    componentEuclideanBall_mono C x (by linarith)
  have hdiffρ : componentBallL2 C x ρ (fun z => A z - (ℓ z + a)) ≤ E * s :=
    componentBallL2_le_of_abs_le C x ρ _ (mul_nonneg hE0 hs0) fun z hz => by
      rw [abs_sub_comm, hwA]; exact hosc z (hsub hz)
  have hdiff2 : componentBallL2 C x (2 * ρ) (fun z => (ℓ z + a) - A z) ≤ E * s :=
    componentBallL2_le_of_abs_le C x (2 * ρ) _ (mul_nonneg hE0 hs0) fun z hz => by
      rw [hwA]; exact hosc z hz
  have hlow := regDet_le_add_sub C x ρ A (fun z => ℓ z + a)
  have hup := regDet_le_add_sub C x (2 * ρ) (fun z => ℓ z + a) A
  have hb : |b₀| ≤ componentBallL2 C x ρ A + ρ * s := by
    rw [← componentBallL2_const C x ρ b₀ hne]
    refine (regDet_le_add_sub C x ρ (fun _ => b₀) A).trans ?_
    have : componentBallL2 C x ρ (fun z => b₀ - A z) ≤ ρ * s :=
      componentBallL2_le_of_abs_le _ _ _ _ (mul_nonneg (by linarith) hs0) fun z hz => by
        rw [mem_componentEuclideanBall] at hz
        have h := regDet_abs_affine_le ξ z.val x hz
        have e : b₀ - A z = -∑ i, ξ i * ((z.val i : ℝ) - (x i : ℝ)) := by
          simp only [hA]; ring
        rw [e, abs_neg]; exact h
    linarith
  have hA2 : componentBallL2 C x (2 * ρ) A ≤ |b₀| + 2 * ρ * s :=
    componentBallL2_le_of_abs_le _ _ _ _ (add_nonneg (abs_nonneg _)
      (mul_nonneg (by linarith) hs0)) fun z hz => by
      rw [mem_componentEuclideanBall] at hz
      have h := regDet_abs_affine_le ξ z.val x hz
      exact (abs_add_le _ _).trans (by linarith)
  set N := componentBallL2 C x ρ A
  set W := componentBallL2 C x ρ (fun z => ℓ z + a)
  have h1 : E * s ≤ c₁ / 2 * ρ * s := mul_le_mul_of_nonneg_right hE1 hs0
  have h2 : E * s ≤ ρ * s := mul_le_mul_of_nonneg_right hE2 hs0
  have hNW : N ≤ 2 * W := by linarith
  have hq : ρ * s ≤ N / c₁ := by rw [le_div_iff₀ hc₁]; linarith
  calc componentBallL2 C x (2 * ρ) (fun z => ℓ z + a) ≤ N + 4 * (ρ * s) := by linarith
    _ ≤ N + 4 * (N / c₁) := by linarith
    _ = (1 + 4 / c₁) * N := by ring
    _ ≤ (1 + 4 / c₁) * (2 * W) := mul_le_mul_of_nonneg_left hNW (by positivity)
    _ = 2 * (1 + 4 / c₁) * W := by ring

/-- Under (H4), the ball `B_ρ(x)`, `ρ ≥ X`, `ρ > 0`, is nonempty. -/
theorem regDet_nonempty {ω : Configuration d} {C : OpenComponent ω} {x : Vertex d} {c X ρ : ℝ}
    (hD : DenseAt C x c X) (hc : 0 < c) (hXρ : X ≤ ρ) (hρ : 0 < ρ) :
    (componentEuclideanBall C x ρ).Nonempty := by
  have h := regDet_card_ge hD hXρ hρ.le
  have : 0 < c * (100 * ρ) ^ d := by positivity
  exact Finset.card_pos.mp (by exact_mod_cast this.trans_le h)

/-- Restriction from `B_σ` to `B_ρ`, `X ≤ ρ ≤ σ ≤ Lρ`, under (H4) with `X ≥ 1`. -/
theorem regDet_restrict {ω : Configuration d} {C : OpenComponent ω} {x : Vertex d} {c X L : ℝ}
    (hD : DenseAt C x c X) (hc : 0 < c) (hX : 1 ≤ X) (f : C → ℝ) {ρ σ : ℝ} (hXρ : X ≤ ρ)
    (hρσ : ρ ≤ σ) (hσL : σ ≤ L * ρ) :
    componentBallL2 C x ρ f ≤ Real.sqrt (5 ^ d * L ^ d / c) * componentBallL2 C x σ f := by
  have hρ1 : 1 ≤ ρ := hX.trans hXρ
  have hσ1 : 1 ≤ σ := hρ1.trans hρσ
  have hL : 0 ≤ L := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hcard := regDet_card_ge hD hXρ (by linarith)
  have hcρ : c * ρ ^ d ≤ c * (100 * ρ) ^ d :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) d) hc.le
  have hρd : 0 < ρ ^ d := pow_pos (by linarith) d
  have hNρ : (0 : ℝ) < (componentEuclideanBall C x ρ).card := by
    have : 0 < c * ρ ^ d := by positivity
    linarith
  have hNσ := card_componentEuclideanBall_le C x hσ1
  have hσd : σ ^ d ≤ L ^ d * ρ ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) hσL d
  refine (componentBallL2_le_sqrt_card_div_mul C x hρσ (by exact_mod_cast hNρ) f).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (componentBallL2_nonneg _ _ _ _)
  rw [div_le_div_iff₀ hNρ hc]
  calc ((componentEuclideanBall C x σ).card : ℝ) * c ≤ 5 ^ d * (L ^ d * ρ ^ d) * c :=
        mul_le_mul_of_nonneg_right (hNσ.trans (mul_le_mul_of_nonneg_left hσd (by positivity)))
          hc.le
    _ = 5 ^ d * L ^ d * (c * ρ ^ d) := by ring
    _ ≤ 5 ^ d * L ^ d * ((componentEuclideanBall C x ρ).card : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Dyadic chaining of the constants: one-step bounds `|a_r - a_{r'}| ≤ K (r/R)²` for
`X ≤ r' ≤ r ≤ 2r'` give `|a_r - a_X| ≤ (4/3) K (r/R)²`. -/
theorem regDet_chain {X R K : ℝ} (a : ℝ → ℝ) (hX : 0 < X) (hK : 0 ≤ K)
    (hstep : ∀ r r' : ℝ, X ≤ r' → r' ≤ r → r ≤ 2 * r' → r ≤ R / 4 →
      |a r - a r'| ≤ K * (r / R) ^ 2) :
    ∀ r : ℝ, X ≤ r → r ≤ R / 4 → |a r - a X| ≤ 4 / 3 * K * (r / R) ^ 2 := by
  have key : ∀ n : ℕ, ∀ r : ℝ, X ≤ r → r ≤ 2 ^ n * X → r ≤ R / 4 →
      |a r - a X| ≤ 4 / 3 * K * (r / R) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro r h1 h2 _
      rw [pow_zero, one_mul] at h2
      rw [le_antisymm h2 h1, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hK) (sq_nonneg _)
    | succ n ih =>
      intro r h1 h2 h3
      have hKr : 0 ≤ K * (r / R) ^ 2 := mul_nonneg hK (sq_nonneg _)
      by_cases hr2 : r ≤ 2 * X
      · have := hstep r X le_rfl h1 hr2 h3
        linarith
      · rw [not_le] at hr2
        rw [pow_succ] at h2
        have h' := ih (r / 2) (by linarith) (by linarith) (by linarith)
        have hs := hstep r (r / 2) (by linarith) (by linarith) (by linarith) h3
        have e : (r / 2 / R) ^ 2 = (r / R) ^ 2 / 4 := by ring
        rw [e] at h'
        calc |a r - a X| ≤ |a r - a (r / 2)| + |a (r / 2) - a X| := abs_sub_le _ _ _
          _ ≤ 4 / 3 * K * (r / R) ^ 2 := by linarith
  intro r h1 h3
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r / X) one_lt_two
  exact key n r h1 (by rw [div_lt_iff₀ hX] at hn; linarith) h3

/-- The main case `R ≥ 8X`, `‖u‖_R > 0` of `regularityProposedAt_of_faithfulAt`, with the
restriction constants `D2`, `D4` and the doubling constant `K` as hypotheses. -/
theorem regDet_caseC {ω : Configuration d} {C : OpenComponent ω} {x : Vertex d}
    {C₁ K ρ₁ M X R D2 D4 G : ℝ} (hC₁ : 0 < C₁) (hK : 0 < K) (hD2 : 0 < D2) (hD4 : 0 ≤ D4)
    (hG : G = 8 * C₁ * D2 + 4 / 3 * (8 * C₁ * D2 * (1 + D2)))
    (hX : 0 < X) (hMX : 2 * M ≤ X) (hρX : ρ₁ ≤ X) (hR : 8 * X ≤ R)
    (hne : ∀ ρ : ℝ, X ≤ ρ → (componentEuclideanBall C x ρ).Nonempty)
    (hres2 : ∀ (f : C → ℝ) (ρ σ : ℝ), X ≤ ρ → ρ ≤ σ → σ ≤ 2 * ρ →
      componentBallL2 C x ρ f ≤ D2 * componentBallL2 C x σ f)
    (hres4 : ∀ (f : C → ℝ) (ρ σ : ℝ), X ≤ ρ → ρ ≤ σ → σ ≤ 4 * ρ →
      componentBallL2 C x ρ f ≤ D4 * componentBallL2 C x σ f)
    (hdoub : ∀ (ξ : Fin d → ℝ) (ℓ : C → ℝ), IsCorrectedPlane C ξ ℓ → ∀ a ρ : ℝ, X ≤ ρ →
      ρ₁ ≤ ρ → componentBallL2 C x (2 * ρ) (fun z => ℓ z + a) ≤
        K * componentBallL2 C x ρ (fun z => ℓ z + a))
    (hF : RegularityFaithfulAt C x C₁ M) (u : C → ℝ)
    (hu : ∀ z ∈ componentEuclideanBall C x R,
      (∀ w, (componentGraph C).Adj z w → w ∈ componentEuclideanBall C x R) →
        componentLaplacian C u z = 0)
    (hU : 0 < componentBallL2 C x R u) :
    ∃ φ ∈ harmonicGrowthSpace C 1, ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
      componentBallL2 C x r (u - φ) ≤
        (G + 16 * (D4 + D2 * K * (D4 + G / 16))) * (r / R) ^ 2 * componentBallL2 C x R u := by
  set U := componentBallL2 C x R u with hUdef
  have hR0 : 0 < R := by linarith
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hu' : ∀ z ∈ componentEuclideanBall C x (2 * (R / 2)),
      (∀ w, (componentGraph C).Adj z w → w ∈ componentEuclideanBall C x (2 * (R / 2))) →
        componentLaplacian C u z = 0 := by
    rw [show 2 * (R / 2) = R by ring]; exact hu
  obtain ⟨ξ, ℓ, hℓ, hfa⟩ := hF (R / 2) (by linarith) u hu'
  have hUhalf : componentBallL2 C x (R / 2) u ≤ D2 * U :=
    hres2 u (R / 2) R (by linarith) (by linarith) (by linarith)
  have hinf : ∀ r : ℝ, X ≤ r → r ≤ R / 4 →
      (⨅ a : ℝ, componentBallL2 C x r (fun z => u z - ℓ z - a)) ≤
        4 * C₁ * D2 * (r / R) ^ 2 * U := by
    intro r h1 h2
    calc _ ≤ C₁ * (r / (R / 2)) ^ 2 * componentBallL2 C x (R / 2) u :=
          hfa r (by linarith) (by linarith)
      _ ≤ C₁ * (r / (R / 2)) ^ 2 * (D2 * U) := by gcongr
      _ = 4 * C₁ * D2 * (r / R) ^ 2 * U := by field_simp; ring
  have hchoice : ∀ r : ℝ, ∃ a : ℝ, X ≤ r → r ≤ R / 4 →
      componentBallL2 C x r (fun z => u z - ℓ z - a) ≤ 8 * C₁ * D2 * (r / R) ^ 2 * U := by
    intro r
    by_cases h : X ≤ r ∧ r ≤ R / 4
    · have hr0 : 0 < r := by linarith [h.1]
      have hpos : 0 < 4 * C₁ * D2 * (r / R) ^ 2 * U := by positivity
      obtain ⟨a, ha⟩ := exists_lt_of_ciInf_lt (lt_of_le_of_lt (hinf r h.1 h.2)
        (by linarith : 4 * C₁ * D2 * (r / R) ^ 2 * U < 8 * C₁ * D2 * (r / R) ^ 2 * U))
      exact ⟨a, fun _ _ => ha.le⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose a ha using hchoice
  have hstep : ∀ r r' : ℝ, X ≤ r' → r' ≤ r → r ≤ 2 * r' → r ≤ R / 4 →
      |a r - a r'| ≤ 8 * C₁ * D2 * (1 + D2) * U * (r / R) ^ 2 := by
    intro r r' h1 h2 h3 h4
    have hc : componentBallL2 C x r' (fun _ => a r - a r') = |a r - a r'| :=
      componentBallL2_const C x r' _ (hne r' h1)
    rw [← hc]
    have e : (fun _ : C => a r - a r') =
        fun z => (u z - ℓ z - a r') + -(u z - ℓ z - a r) := by funext z; ring
    rw [e]
    refine (componentBallL2_add_le C x r' _ _).trans ?_
    have hneg : componentBallL2 C x r' (fun z => -(u z - ℓ z - a r)) =
        componentBallL2 C x r' (fun z => u z - ℓ z - a r) := componentBallL2_neg C x r' _
    rw [hneg]
    have hr' : 0 < r' := by linarith
    have b1 := ha r' h1 (by linarith)
    have b2 := ha r (by linarith) h4
    have b3 := hres2 (fun z => u z - ℓ z - a r) r' r h1 h2 h3
    have hrr : (r' / R) ^ 2 ≤ (r / R) ^ 2 := by gcongr
    have b4 : D2 * componentBallL2 C x r (fun z => u z - ℓ z - a r) ≤
        D2 * (8 * C₁ * D2 * (r / R) ^ 2 * U) := mul_le_mul_of_nonneg_left b2 hD2.le
    have b5 : 8 * C₁ * D2 * (r' / R) ^ 2 * U ≤ 8 * C₁ * D2 * (r / R) ^ 2 * U := by gcongr
    linarith
  have hchain := regDet_chain a hX (by positivity) hstep
  refine ⟨fun z => ℓ z + a X,
    (harmonicGrowthSpace C 1).add_mem hℓ.1 (const_mem_harmonicGrowthSpace C 1 (a X)), ?_⟩
  have hsmall : ∀ r : ℝ, X ≤ r → r ≤ R / 4 →
      componentBallL2 C x r (fun z => u z - (ℓ z + a X)) ≤ G * (r / R) ^ 2 * U := by
    intro r h1 h2
    have e : (fun z => u z - (ℓ z + a X)) = fun z => (u z - ℓ z - a r) + (a r - a X) := by
      funext z; ring
    rw [e]
    refine (componentBallL2_add_le C x r _ _).trans ?_
    rw [componentBallL2_const C x r _ (hne r h1)]
    have b1 := ha r h1 h2
    have b2 := hchain r h1 h2
    rw [hG]; linarith
  have hR4 : componentBallL2 C x (R / 4) (fun z => ℓ z + a X) ≤ (D4 + G / 16) * U := by
    have e : (fun z => ℓ z + a X) = fun z => u z + -(u z - (ℓ z + a X)) := by funext z; ring
    rw [e]
    refine (componentBallL2_add_le C x (R / 4) _ _).trans ?_
    have hneg : componentBallL2 C x (R / 4) (fun z => -(u z - (ℓ z + a X))) =
        componentBallL2 C x (R / 4) (fun z => u z - (ℓ z + a X)) := componentBallL2_neg C x _ _
    rw [hneg]
    have b1 := hres4 u (R / 4) R (by linarith) (by linarith) (by linarith)
    have b2 := hsmall (R / 4) (by linarith) le_rfl
    have e2 : (R / 4 / R) ^ 2 = 1 / 16 := by
      rw [div_right_comm, div_self hR0.ne']; norm_num
    rw [e2] at b2
    linarith
  have hR2 : componentBallL2 C x (R / 2) (fun z => ℓ z + a X) ≤
      K * componentBallL2 C x (R / 4) (fun z => ℓ z + a X) := by
    have h := hdoub ξ ℓ hℓ (a X) (R / 4) (by linarith) (by linarith)
    rwa [show 2 * (R / 4) = R / 2 by ring] at h
  have hT : 0 ≤ (D4 + D2 * K * (D4 + G / 16)) * U := by positivity
  have hlarge : ∀ r : ℝ, R / 4 < r → r ≤ R / 2 →
      componentBallL2 C x r (fun z => u z - (ℓ z + a X)) ≤
        16 * (D4 + D2 * K * (D4 + G / 16)) * (r / R) ^ 2 * U := by
    intro r h1 h2
    have e : (fun z => u z - (ℓ z + a X)) = fun z => u z + -(ℓ z + a X) := by funext z; ring
    rw [e]
    refine (componentBallL2_add_le C x r _ _).trans ?_
    have hneg : componentBallL2 C x r (fun z => -(ℓ z + a X)) =
        componentBallL2 C x r (fun z => ℓ z + a X) := componentBallL2_neg C x _ _
    rw [hneg]
    have b1 := hres4 u r R (by linarith) (by linarith) (by linarith)
    have b2 := hres2 (fun z => ℓ z + a X) r (R / 2) (by linarith) h2 (by linarith)
    have hq : 1 ≤ 16 * (r / R) ^ 2 := by
      have : 1 / 4 ≤ r / R := by rw [le_div_iff₀ hR0]; linarith
      nlinarith
    have b3 : D2 * componentBallL2 C x (R / 2) (fun z => ℓ z + a X) ≤
        D2 * (K * ((D4 + G / 16) * U)) :=
      mul_le_mul_of_nonneg_left (hR2.trans (mul_le_mul_of_nonneg_left hR4 hK.le)) hD2.le
    calc _ ≤ D4 * U + D2 * (K * ((D4 + G / 16) * U)) := by linarith
      _ = 1 * ((D4 + D2 * K * (D4 + G / 16)) * U) := by ring
      _ ≤ 16 * (r / R) ^ 2 * ((D4 + D2 * K * (D4 + G / 16)) * U) :=
          mul_le_mul_of_nonneg_right hq hT
      _ = _ := by ring
  intro r h1 h2
  show componentBallL2 C x r (fun z => u z - (ℓ z + a X)) ≤ _
  by_cases hr : r ≤ R / 4
  · have b := hsmall r h1 hr
    have : 0 ≤ 16 * (D4 + D2 * K * (D4 + G / 16)) * (r / R) ^ 2 * U := by positivity
    linarith
  · have b := hlarge r (lt_of_not_ge hr) h2
    have : 0 ≤ G * (r / R) ^ 2 * U := by positivity
    linarith

/-- The printed form, density and corrector bounds give the proposed form. -/
theorem regularityProposedAt_of_faithfulAt [NeZero d] {c Cc C₁ : ℝ} (hc : 0 < c)
    (hCc : 0 < Cc) (hC₁ : 0 < C₁) :
    ∃ C₀ ρ₀ : ℝ, 0 < C₀ ∧ 1 ≤ ρ₀ ∧ ∀ {ω : Configuration d} (C : OpenComponent ω) (x : Vertex d)
      (M X : ℝ), RegularityFaithfulAt C x C₁ M → DenseAt C x c X →
      CorrectorBoundAt C x Cc (1 / 2) X → 2 * M ≤ X → ρ₀ ≤ X → RegularityProposedAt C x C₀ X := by
  obtain ⟨K, ρ₁, hK, hρ₁, hdoub⟩ := correctedPlane_doubling (d := d) hc hCc
  set D2 := Real.sqrt (5 ^ d * 2 ^ d / c) with hD2
  set D4 := Real.sqrt (5 ^ d * 4 ^ d / c) with hD4
  set D8 := Real.sqrt (5 ^ d * 8 ^ d / c) with hD8
  set G := 8 * C₁ * D2 + 4 / 3 * (8 * C₁ * D2 * (1 + D2)) with hG
  have hD2p : 0 < D2 := Real.sqrt_pos.mpr (by positivity)
  have hD4p : 0 < D4 := Real.sqrt_pos.mpr (by positivity)
  have hD8p : 0 < D8 := Real.sqrt_pos.mpr (by positivity)
  have hG0 : 0 ≤ G := by positivity
  have hT0 : 0 ≤ G + 16 * (D4 + D2 * K * (D4 + G / 16)) := by positivity
  refine ⟨64 * D8 + (G + 16 * (D4 + D2 * K * (D4 + G / 16))), ρ₁, by positivity, hρ₁, ?_⟩
  intro ω C x M X hF hD hCB hMX hρX R hR u hu
  have hX1 : 1 ≤ X := hρ₁.trans hρX
  have hres : ∀ L : ℝ, ∀ (f : C → ℝ) (ρ σ : ℝ), X ≤ ρ → ρ ≤ σ → σ ≤ L * ρ →
      componentBallL2 C x ρ f ≤ Real.sqrt (5 ^ d * L ^ d / c) * componentBallL2 C x σ f :=
    fun L f ρ σ h1 h2 h3 => regDet_restrict hD hc hX1 f h1 h2 h3
  have hne : ∀ ρ : ℝ, X ≤ ρ → (componentEuclideanBall C x ρ).Nonempty :=
    fun ρ h => regDet_nonempty hD hc h (by linarith)
  set U := componentBallL2 C x R u with hU
  have hU0 : 0 ≤ U := componentBallL2_nonneg _ _ _ _
  by_cases hcase : R < 8 * X ∨ U = 0
  · refine ⟨0, (harmonicGrowthSpace C 1).zero_mem, fun r h1 h2 => ?_⟩
    rw [sub_zero]
    rcases hcase with hR8 | hUz
    · have b := hres 8 u r R h1 (by linarith) (by linarith)
      have hq : 1 ≤ 64 * (r / R) ^ 2 := by
        have : 1 / 8 ≤ r / R := by rw [le_div_iff₀ (by linarith)]; linarith
        nlinarith
      have b1 := mul_le_mul_of_nonneg_left hq (mul_nonneg hD8p.le hU0)
      have b2 : 0 ≤ (G + 16 * (D4 + D2 * K * (D4 + G / 16))) * (r / R) ^ 2 * U := by positivity
      calc componentBallL2 C x r u ≤ D8 * U := b
        _ ≤ (64 * D8 + (G + 16 * (D4 + D2 * K * (D4 + G / 16)))) * (r / R) ^ 2 * U := by
          linarith
    · have b := componentBallL2_le_sqrt_card_div_mul C x (σ := R) (by linarith)
        (Finset.card_pos.mpr (hne r h1)) u
      rw [← hU, hUz, mul_zero] at b
      rw [hUz, mul_zero]
      exact b
  · rw [not_or] at hcase
    obtain ⟨hR8, hUne⟩ := hcase
    obtain ⟨φ, hφ, hbound⟩ := regDet_caseC (G := G) hC₁ hK hD2p hD4p.le rfl (by linarith) hMX
      hρX (le_of_not_gt hR8) hne (fun f ρ σ h1 h2 h3 => hres 2 f ρ σ h1 h2 h3)
      (fun f ρ σ h1 h2 h3 => hres 4 f ρ σ h1 h2 h3)
      (fun ξ ℓ hℓ a ρ h1 h2 => hdoub C x X hD hCB ξ ℓ hℓ a ρ h1 h2) hF u hu
      (lt_of_le_of_ne hU0 (Ne.symm hUne))
    refine ⟨φ, hφ, fun r h1 h2 => (hbound r h1 h2).trans ?_⟩
    have : 0 ≤ 64 * D8 * (r / R) ^ 2 * U := by positivity
    linarith

/-- Monotonicity of the corrector bounds in the scale. -/
theorem correctorBoundAt_mono {ω : Configuration d} {C : OpenComponent ω} {x : Vertex d}
    {Cc η X Y : ℝ} (h : CorrectorBoundAt C x Cc η X) (hXY : X ≤ Y) : CorrectorBoundAt C x Cc η Y :=
  fun q ℓ hℓ r hr => h q ℓ hℓ r (hXY.trans hr)

/-- The proposed form of the order-one regularity input follows from the printed eq. (large
scale-regularity), the printed density estimate and the corrector bounds of Theorem 2.5. -/
theorem armstrongDarioOrderOneProposed_of_faithful (hAD : ArmstrongDarioOrderOneFaithful)
    (hD : ClusterDensityInputFaithful) (hCQ : Rigidity.External.CorrectorQuantitativeInput) :
    ArmstrongDarioOrderOneProposed := by
  intro d _ hd p hpc hp1
  obtain ⟨s₁, C₁, hs₁, hC₁, hx₁⟩ := hAD d hd p hpc hp1
  obtain ⟨s₂, C₂, c, hs₂, hC₂, hc, hx₂⟩ := clusterDensityInputProposed_of_faithful hD d hd p hpc hp1
  obtain ⟨s₃, C₃, hs₃, hC₃, hx₃⟩ := hCQ d hd p hpc hp1 (1 / 2) (by norm_num)
  obtain ⟨C₀, ρ₀, hC₀, hρ₀, hdet⟩ := regularityProposedAt_of_faithfulAt (d := d) hc hC₃ hC₁
  set s : ℝ := min s₁ (min s₂ s₃) with hsdef
  have hs : 0 < s := lt_min hs₁ (lt_min hs₂ hs₃)
  have hss₁ : s ≤ s₁ := min_le_left _ _
  have hss₂ : s ≤ s₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hss₃ : s ≤ s₃ := (min_le_right _ _).trans (min_le_right _ _)
  set θ₁ : ℝ := 2 * C₁ * 6 ^ (1 / s)
  set θ₂ : ℝ := C₂ * 6 ^ (1 / s)
  set θ₃ : ℝ := C₃ * 6 ^ (1 / s)
  set θ₄ : ℝ := ρ₀ * 3 ^ (1 / s)
  set θ₁₂ : ℝ := max θ₁ θ₂ * 4 ^ (1 / s)
  set θ₃₄ : ℝ := max θ₃ θ₄ * 4 ^ (1 / s)
  set θ : ℝ := max θ₁₂ θ₃₄ * 4 ^ (1 / s)
  have h6 : 0 < (6 : ℝ) ^ (1 / s) := by positivity
  have h4 : 0 < (4 : ℝ) ^ (1 / s) := by positivity
  have hθ₁ : 0 < θ₁ := by positivity
  have hθ₂ : 0 < θ₂ := by positivity
  have hθ₃ : 0 < θ₃ := by positivity
  have hθ₄ : 0 < θ₄ := by have : (0 : ℝ) < ρ₀ := by linarith
                          positivity
  have hθ₁₂ : 0 < θ₁₂ := by positivity
  have hθ₃₄ : 0 < θ₃₄ := by positivity
  have hθ : 0 < θ := by positivity
  refine ⟨s, max C₀ θ, hs, lt_max_of_lt_left hC₀, fun x => ?_⟩
  obtain ⟨M₁, hM₁m, hM₁0, hM₁os, hae₁⟩ := hx₁ x
  obtain ⟨M₂, hM₂m, hM₂0, hM₂os, hae₂⟩ := hx₂ x
  obtain ⟨M₃, hM₃m, hM₃0, hM₃os, hae₃⟩ := hx₃ x
  set X : Configuration d → ℝ :=
    fun ω => max (max (2 * M₁ ω) (M₂ ω)) (max (M₃ ω) ρ₀) with hXdef
  have hXm : Measurable X :=
    ((hM₁m.const_mul 2).max hM₂m).max (hM₃m.max measurable_const)
  have hOs₁ : IsOsBond d p (fun ω => 2 * M₁ ω) s θ₁ := by
    have := IsOsBond.mono_exponent hs hss₁ (hM₁m.const_mul 2)
      (IsOsBond.const_mul (c := 2) two_pos hM₁os)
    simpa [θ₁, mul_assoc] using this
  have hOs₂ : IsOsBond d p M₂ s θ₂ := IsOsBond.mono_exponent hs hss₂ hM₂m hM₂os
  have hOs₃ : IsOsBond d p M₃ s θ₃ := IsOsBond.mono_exponent hs hss₃ hM₃m hM₃os
  have hOs₄ : IsOsBond d p (fun _ => ρ₀) s θ₄ := isOsBond_const (by linarith) hs
  have hOs₁₂ := IsOsBond.max hs hθ₁ hθ₂ (hM₁m.const_mul 2) hM₂m hOs₁ hOs₂
  have hOs₃₄ := IsOsBond.max hs hθ₃ hθ₄ hM₃m measurable_const hOs₃ hOs₄
  have hOs := IsOsBond.max hs hθ₁₂ hθ₃₄ ((hM₁m.const_mul 2).max hM₂m)
    (hM₃m.max measurable_const) hOs₁₂ hOs₃₄
  refine ⟨X, hXm, fun ω => le_max_of_le_right (le_max_of_le_right (by linarith)),
    IsOsBond.mono_scale hs hθ (le_max_right _ _) hXm hOs, ?_⟩
  filter_upwards [hae₁, hae₂, hae₃] with ω h₁ h₂ h₃
  intro h R hR u hu
  have hdetω := hdet (uniqueInfiniteComponent h) x (M₁ ω) (X ω) (h₁ h)
    (DenseAt.mono (h₂ h) (le_max_of_le_left (le_max_right _ _)))
    (correctorBoundAt_mono (h₃ h) (le_max_of_le_right (le_max_left _ _)))
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_right (le_max_right _ _))
  obtain ⟨φ, hφ, hbd⟩ := hdetω R hR u hu
  refine ⟨φ, hφ, fun r hr hrR => (hbd r hr hrR).trans ?_⟩
  gcongr
  · exact componentBallL2_nonneg _ _ _ _
  · exact le_max_left _ _

/-- step:2.6-inputs, regularity, from the printed inputs: eq. (large scale-regularity)
(`ArmstrongDarioOrderOneFaithful`), the printed density (`ClusterDensityInputFaithful`), the
corrector bounds (`CorrectorQuantitativeInput`) and the classification of `𝒜₁`
(`SupercriticalBondCorrectorInput`). -/
theorem regularityScaleStep_of_faithful [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hAD : ArmstrongDarioOrderOneFaithful) (hD : ClusterDensityInputFaithful)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput) : RegularityScaleStep d p :=
  regularityScaleStep hd p (armstrongDarioOrderOneProposed_of_faithful hAD hD hCQ) hU

/-- step:2.6-inputs, density, from the printed density sentence (`ClusterDensityInputFaithful`). -/
theorem densityScaleStep_of_faithful [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hD : ClusterDensityInputFaithful) : DensityScaleStep d p :=
  densityScaleStep hd p (clusterDensityInputProposed_of_faithful hD)

/-- **Proposition 2.6** from the literature inputs `SupercriticalBondGreenQuantitative`,
`CorrectorQuantitativeInput`, `SupercriticalBondCorrectorInput` and the two inputs as printed,
`ArmstrongDarioOrderOneFaithful` (eq. (large scale-regularity)) and `ClusterDensityInputFaithful`
(paper L508-511; Dario–Gu, Proposition A.1, with a union bound, correction C35). -/
theorem greenGradientHomogenization_of_faithfulInputs [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hU : LatticeProb.External.SupercriticalBondCorrectorInput)
    (hAD : ArmstrongDarioOrderOneFaithful) (hD : ClusterDensityInputFaithful) :
    Rigidity.Section2.GreenGradientHomogenizationStmt d hd p :=
  greenGradientHomogenization_of_inputs hd p hpc hp1 hGQ hCQ hU
    (armstrongDarioOrderOneProposed_of_faithful hAD hD hCQ)
    (clusterDensityInputProposed_of_faithful hD)

end Regularity

end Rigidity.Proofs.S2
