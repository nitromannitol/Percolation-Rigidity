import Rigidity.Proofs.Green.GeneralTwoScaleSource
import PercolationClusterHomogenization.Proofs.Regularity.GeneralCorrectorInput
import PercolationClusterHomogenization.External.CorrectorQuantitative

/-!
# Proposition 2.12 of Dario–Gu on `ℤ^d` and the initial error of the two-scale expansion

* `exists_isDGCorrectorD`: almost surely, at every point `y` of the infinite cluster of `ℤ^d`, the
  correctors `χ_{e_k}` normalized at `y` exist (Dario–Gu, §2.3.1; the qualitative corrector input,
  proved in every dimension as `supercriticalBondCorrectorInput_holds`).
* `correctorGrowthD_of_input`: Proposition 2.12 (`CorrectorQuantitativeInput`) gives, above a minimal
  scale `M ≤ O_s(C)`, the growth `|χ_{e_k}(x)| ≤ C (ρ + |x - y| + 2)^α` on the cluster for every
  `ρ ≥ M` (the oscillation of the corrector on the ball of radius `ρ + |x - y| + 2`, `χ_{e_k}(y) = 0`).
* `l2norm_initialErrorD_le`: the initial error of the two-scale expansion,
  `h(s, ·, y) - θ^{-1} p̄(s, · - y) = θ^{-1} Σ_k D_{e_k} p̄(s, · - y) χ_{e_k}` on the cluster, has
  `ℓ²` norm at most `C B s^{α/2 - d/4 - 1/2}` when `|χ_{e_k}(x)| ≤ B (√s + |x - y| + 2)^α`: this is the
  fourth item of the base case of §4.3 of Dario–Gu (lines 2558-2562, "the details are left to the
  reader"), with the order `s^{-d/4 - 1/2 + α}` of the source.
-/

open scoped Classical
open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

/-- The normalized correctors of Dario–Gu, §2.3.1, on `ℤ^d`, from the qualitative corrector
input. -/
theorem exists_isDGCorrectorD_of_unique {ω : Configuration d} {K : OpenComponent ω}
    (hK : ∀ (q : Fin d → ℝ) (o : K), ∃! u : K → ℝ, IsCorrectedPlane K q u ∧ u o = 0)
    {z : Vertex d} (hz : z ∈ K.supp) : ∃ χ : Fin d → Vertex d → ℝ, IsDGCorrectorD K z χ := by
  choose u hu using fun k : Fin d => (hK (Pi.single k 1) ⟨z, hz⟩).exists
  refine ⟨fun k x => if hx : x ∈ K.supp then u k ⟨x, hx⟩ + (z k : ℝ) - x k else 0, fun k => ?_⟩
  constructor
  · have key := isCorrectedPlane_add K (hu k).1 (isCorrectedPlane_const K (z k : ℝ))
    rw [add_zero] at key
    convert key using 1
    funext a
    simp only [Pi.add_apply]
    split_ifs with ha
    · rw [Subtype.coe_eta]; ring
    · exact absurd a.2 ha
  · simp [(hu k).2]

/-- **The correctors exist** almost surely at every point of the infinite cluster of `ℤ^d`. -/
theorem exists_isDGCorrectorD [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ y ∈ (uniqueInfiniteComponent h).supp,
        ∃ χ : Fin d → Vertex d → ℝ, IsDGCorrectorD (uniqueInfiniteComponent h) y χ := by
  filter_upwards [Rigidity.Proofs.Regularity.GeneralDim.supercriticalBondCorrectorInput_holds d hd
    p hpc hp1] with ω hω
  intro h y hy
  exact exists_isDGCorrectorD_of_unique (hω h).1 hy

/-- A vertex of an infinite component has a neighbour in it. -/
theorem exists_adj_nearD {ω : Configuration d} {K : OpenComponent ω} (hK : K.supp.Infinite)
    (x : K) : ∃ b : K, (componentGraph K).Adj x b ∧ ∀ y, ‖edzD b.val y‖ ≤ ‖edzD x.val y‖ + 1 := by
  obtain ⟨w, hw, hwx⟩ := hK.nontrivial.exists_ne x.val
  have hreach : (openGraph ω).Reachable x.val w :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 x.2).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw).symm)
  obtain ⟨q⟩ := hreach
  cases q with
  | nil => exact absurd rfl hwx
  | @cons _ v _ hadj _ =>
    have hv : v ∈ K.supp := mem_supp_of_openAdjD x.2 hadj
    exact ⟨⟨v, hv⟩, (K.toSimpleGraph_adj x.2 hv).2 hadj, fun y => norm_edzD_le_of_adj hadj y⟩

theorem sum_single_mul_coeD (i : Fin d) (v : Vertex d) :
    ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * (v j : ℝ) = v i := by
  simp [Pi.single_apply]

theorem sum_abs_single_coeD (i : Fin d) : ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
  simp [Pi.single_apply, apply_ite]

/-- **Proposition 2.12 of Dario–Gu on `ℤ^d`, the growth of the corrector**: above a minimal scale
`M ≤ O_s(C)`, `|χ_{e_k}(x)| ≤ C (ρ + |x - y| + 2)^α` on the cluster for every `ρ ≥ M`. -/
theorem correctorGrowthD_of_input (hCQ : CorrectorQuantitativeInput) [NeZero d] (hd : 2 ≤ d)
    {p : unitInterval} (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) {α : ℝ}
    (hα : 0 < α) : ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
          y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin d → Vertex d → ℝ,
            IsDGCorrectorD (uniqueInfiniteComponent h) y χ → ∀ ρ : ℝ, M ω ≤ ρ →
              ∀ x ∈ (uniqueInfiniteComponent h).supp, ∀ k : Fin d,
                |χ k x| ≤ C * (ρ + ‖edzD x y‖ + 2) ^ α := by
  obtain ⟨s, C, hs, hC, h5⟩ := hCQ d hd p hpc hp1 α hα
  refine ⟨C, s, hC, hs, fun y => ?_⟩
  obtain ⟨M, hMm, hM0, hMos, hMae⟩ := h5 y
  refine ⟨M, hMm, hM0, hMos, ?_⟩
  filter_upwards [hMae] with ω hω
  intro h hy χ hχ ρ hρ x hx k
  obtain ⟨b', hadj, hb'd⟩ := exists_adj_nearD (uniqueInfiniteComponent_infinite h) ⟨x, hx⟩
  have hd0 := norm_nonneg (edzD x y)
  have hρ0 : 0 ≤ ρ := (hM0 ω).trans hρ
  set r := ρ + ‖edzD x y‖ + 2 with hr
  have hMr : M ω ≤ r := by linarith
  have hb'y := hb'd y
  have hyy : ‖latticeEuclideanEmbedding y - latticeEuclideanEmbedding y‖ < r := by
    rw [sub_self, norm_zero]
    linarith [hM0 ω]
  have := hω h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 r hMr
    ⟨x, hx⟩ ⟨y, hy⟩ ⟨x, hx⟩ b' (by show ‖edzD x y‖ < r; linarith) hyy
    (by show ‖edzD x y‖ < r; linarith) (by show ‖edzD b'.val y‖ < r; linarith) hadj
  simp only [sum_single_mul_coeD, sum_abs_single_coeD, mul_one] at this
  have e1 : (x k : ℝ) + χ k x - x k - ((y k : ℝ) + χ k y - y k) = χ k x := by
    rw [(hχ k).2]; ring
  rw [e1] at this
  exact le_of_add_le_of_nonneg_left this (abs_nonneg _)

/-- The `O_s` bound of a square, on `ℤ^d`. -/
theorem IsOsBond.sq_of_nonnegD {p : unitInterval} {X : Configuration d → ℝ} {s θ : ℝ}
    (hθ : 0 < θ) (hX : ∀ ω, 0 ≤ X ω) (h : IsOsBond d p X s θ) :
    IsOsBond d p (fun ω => X ω ^ 2) (s / 2) (θ ^ 2) := by
  have e : ∀ ω, Real.rpow (max (X ω ^ 2 / θ ^ 2) 0) (s / 2) = Real.rpow (max (X ω / θ) 0) s := by
    intro ω
    have h0 : 0 ≤ X ω / θ := div_nonneg (hX ω) hθ.le
    rw [max_eq_left (by positivity), max_eq_left h0, ← div_pow]
    change ((X ω / θ) ^ 2) ^ (s / 2) = (X ω / θ) ^ s
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
    ring_nf
  unfold IsOsBond
  simp only [e]
  exact h

/-! ### The initial error -/

theorem clusterInitD_sub_eq {ω : Configuration d} (K : OpenComponent ω) (σ θ : ℝ)
    (χ : Fin d → Vertex d → ℝ) (s : ℝ) (y x : Vertex d) :
    clusterInitD K σ θ χ s y x - θ⁻¹ * clusterInd K σ s y x =
      if x ∈ K.supp then θ⁻¹ * ∑ k, fwdDiffD k (fun z => latticeGaussianD σ s z y) x * χ k x
        else 0 := by
  unfold clusterInitD clusterInd dgTwoScaleD
  split_ifs
  · unfold latticeGaussianD
    ring
  · ring

/-- **The initial error of the two-scale expansion** (Proposition 2.12, §4.3 of Dario–Gu):
`‖1_𝒞 (h(s, ·, y) - θ^{-1} p̄(s, · - y))‖_{ℓ²} ≤ C B s^{α/2 - d/4 - 1/2}`. -/
theorem l2norm_initialErrorD_le {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : Configuration d) (K : OpenComponent ω) (y : Vertex d) (χ : Fin d → Vertex d → ℝ)
      (B α s : ℝ), 0 ≤ B → 0 ≤ α → α ≤ 1 → 1 ≤ s →
      (∀ x ∈ K.supp, ∀ k, |χ k x| ≤ B * (Real.sqrt s + ‖edzD x y‖ + 2) ^ α) →
      Summable (fun x => (clusterInitD K σ θ χ s y x - θ⁻¹ * clusterInd K σ s y x) ^ 2) ∧
        l2norm (fun x => clusterInitD K σ θ χ s y x - θ⁻¹ * clusterInd K σ s y x) ≤
          C * B * s ^ (α / 2 - (d : ℝ) / 4 - 1 / 2) := by
  set c₁ := gaussConstD d σ 1 with hc₁
  have hc₁0 : 0 < c₁ := gaussConstD_pos hσ 1
  set G := growthConstD d σ with hG
  have hG0 : 0 ≤ G := growthConstD_nonneg hσ
  refine ⟨θ⁻¹ * d * c₁ * Real.sqrt G + 1, by positivity,
    fun ω K y χ B α s hB hα0 hα1 hs hχ => ?_⟩
  have hs0 : 0 < s := by linarith
  set L := θ⁻¹ * d * c₁ * B * (s ^ (-((d : ℝ) / 2)) / Real.sqrt s ^ 1) with hL
  have hbd : ∀ x, |clusterInitD K σ θ χ s y x - θ⁻¹ * clusterInd K σ s y x| ≤
      L * ((Real.sqrt s + ‖edzD x y‖ + 2) ^ α * Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * s)))) := by
    intro x
    rw [clusterInitD_sub_eq]
    split_ifs with hx
    · set Gx := (Real.sqrt s + ‖edzD x y‖ + 2) ^ α with hGx
      set E := Real.exp (-(‖edzD x y‖ ^ 2 / (32 * σ * s))) with hE
      set R := s ^ (-((d : ℝ) / 2)) / Real.sqrt s ^ 1 with hR
      have hR0 : 0 ≤ R := by positivity
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hk : ∀ k, |fwdDiffD k (fun z => latticeGaussianD σ s z y) x * χ k x| ≤
          c₁ * R * E * (B * Gx) := by
        intro k
        rw [abs_mul]
        have h1 := abs_fwdDiffD_latticeGaussianD_le hσ hs k x y
        have h1' : |fwdDiffD k (fun z => latticeGaussianD σ s z y) x| ≤ c₁ * R * E := by
          rw [hc₁, hR, hE, pow_one]
          refine h1.trans (le_of_eq ?_)
          ring
        exact mul_le_mul h1' (hχ x hx k) (abs_nonneg _) (by positivity)
      rw [abs_mul, abs_of_pos (inv_pos.2 hθ)]
      calc θ⁻¹ * |∑ k, fwdDiffD k (fun z => latticeGaussianD σ s z y) x * χ k x|
          ≤ θ⁻¹ * ∑ _k : Fin d, c₁ * R * E * (B * Gx) :=
            mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun k _ => hk k)) (inv_pos.2 hθ).le
        _ = L * (Gx * E) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL]
            ring
    · rw [abs_zero]
      have : 0 ≤ L := by rw [hL]; positivity
      positivity
  obtain ⟨hsum, htsum⟩ := summable_tsum_sq_le_growth hσ hs hα0 hα1 hbd
  refine ⟨hsum, ?_⟩
  have hsc := scale_sq_mul (d := d) (β := α) hs0 1
  push_cast at hsc
  have hsq : L ^ 2 * G * s ^ (α + (d : ℝ) / 2) =
      (θ⁻¹ * d * c₁ * B) ^ 2 * G * s ^ (α - (d : ℝ) / 2 - 1) := by
    calc L ^ 2 * G * s ^ (α + (d : ℝ) / 2) = (θ⁻¹ * d * c₁ * B) ^ 2 * G *
        ((s ^ (-((d : ℝ) / 2)) / Real.sqrt s ^ 1) ^ 2 * s ^ (α + (d : ℝ) / 2)) := by
          rw [hL]; ring
      _ = _ := by rw [hsc]
  rw [hsq] at htsum
  have hA0 : 0 ≤ θ⁻¹ * d * c₁ * B := by positivity
  have hpow : Real.sqrt (s ^ (α - (d : ℝ) / 2 - 1)) = s ^ (α / 2 - (d : ℝ) / 4 - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs0.le]
    congr 1
    ring
  have hP0 : 0 ≤ s ^ (α / 2 - (d : ℝ) / 4 - 1 / 2) := by positivity
  calc l2norm (fun x => clusterInitD K σ θ χ s y x - θ⁻¹ * clusterInd K σ s y x)
      = Real.sqrt (∑' x, (clusterInitD K σ θ χ s y x - θ⁻¹ * clusterInd K σ s y x) ^ 2) := rfl
    _ ≤ Real.sqrt ((θ⁻¹ * d * c₁ * B) ^ 2 * G * s ^ (α - (d : ℝ) / 2 - 1)) :=
        Real.sqrt_le_sqrt htsum
    _ = θ⁻¹ * d * c₁ * B * Real.sqrt G * s ^ (α / 2 - (d : ℝ) / 4 - 1 / 2) := by
        rw [Real.sqrt_mul (mul_nonneg (sq_nonneg (θ⁻¹ * d * c₁ * B)) hG0),
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, hpow]
    _ ≤ (θ⁻¹ * d * c₁ * Real.sqrt G + 1) * B * s ^ (α / 2 - (d : ℝ) / 4 - 1 / 2) := by
        have : 0 ≤ B * s ^ (α / 2 - (d : ℝ) / 4 - 1 / 2) := by positivity
        nlinarith

end Rigidity.Green.GeneralDim
