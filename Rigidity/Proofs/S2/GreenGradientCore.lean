import Rigidity.Proofs.S2.SlopeEstimate
import Rigidity.Proofs.S2.GreenOscillation
import Rigidity.Proofs.S2.ContinuumGreen
import Rigidity.Proofs.S2.MinimalScale
import Rigidity.Proofs.S2.TailOfOs

/-!
# Proposition 2.6: the deterministic core

`GreenGradientCoreStep` (step:2.6-expansion, paper L554-655). Write `R = |x - y|₂ / 2` and
`u = G(·, y) - K - Ḡ(x - y)`, harmonic in the interior of `𝒞 ∩ B_R(x)`.

* The large-scale `C^{1,1}` regularity (H2) at `R` gives a slope `ξ` and a constant `a`, and
  `GreenOscillationStep` bounds `‖u‖_{L̲²(B_R(x))} ≤ A₂ R^{2-d}`, so that
  `‖u - ∑ᵢ ξᵢ ℓᵢ - a‖_{L̲²(B_r(x))} ≤ Cr A₂ r² R^{-d}` for `r ∈ [X, R/2]`.
* `SlopeEstimateStep` then gives `|ξ - ∇Ḡ(x - y)|₁ ≤ A₁ R^{1/2 - d + δ/4}`.
* At the scale `X`, the value of `v = u - ∑ᵢ ξᵢ ℓᵢ - a` at a vertex of `B_X(x)` is at most
  `#B_X ‖v‖_{L̲²(B_X(x))} ≤ 5^d X^{d+2} Cr A₂ R^{-d}`, and the forward differences of the
  corrected planes are bounded by `1 + Cc X^{δ/4}` by (H3). Since
  `D_j G(x) - ∑ᵢ D_j ℓᵢ(x) ∂ᵢḠ = D_j v(x) + ∑ᵢ (ξᵢ - ∂ᵢḠ) D_j ℓᵢ(x)`, the threshold
  `|x - y|₁ ≥ A X^{2d+4}` (so that `X^{d+2} ≤ R^{1/2}`) gives the bound `A |x - y|₁^{1/2-d+δ}`.

This replaces the Caccioppoli inequality and the two-scale `L²` bound of the paper by the
pointwise bound of a function on a finite ball by its normalized `L²` norm at the minimal scale.
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

variable {d : ℕ} {ω : Configuration d}

/-- A value on the cluster ball is at most the number of its vertices times the normalized `L²`
norm. -/
theorem abs_le_card_mul_componentBallL2 (C : OpenComponent ω) (x : Vertex d) (r : ℝ) (v : C → ℝ)
    {z : C} (hz : z ∈ componentEuclideanBall C x r) :
    |v z| ≤ ((componentEuclideanBall C x r).card : ℝ) * componentBallL2 C x r v := by
  set n : ℝ := ((componentEuclideanBall C x r).card : ℝ) with hn
  set S : ℝ := ∑ w ∈ componentEuclideanBall C x r, v w ^ 2 with hS
  have hn1 : 1 ≤ n := by
    rw [hn]; exact_mod_cast Finset.card_pos.mpr ⟨z, hz⟩
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun w _ => sq_nonneg _
  have hvS : v z ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun w => v w ^ 2) (fun w _ => sq_nonneg _) hz
  have hL2 : componentBallL2 C x r v ^ 2 = S / n := by
    unfold componentBallL2
    rw [Real.sq_sqrt (div_nonneg hS0 (by linarith))]
  have hL0 := componentBallL2_nonneg C x r v
  have hsq : |v z| ^ 2 ≤ (n * componentBallL2 C x r v) ^ 2 := by
    rw [sq_abs, mul_pow, hL2]
    have : n ^ 2 * (S / n) = n * S := by field_simp
    rw [this]
    nlinarith
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsq

/-- The Laplacian does not see additive constants. -/
theorem componentLaplacian_sub_sub_const (C : OpenComponent ω) (g : C → ℝ) (K c : ℝ) (z : C) :
    componentLaplacian C (fun w => g w - K - c) z = componentLaplacian C g z := by
  unfold componentLaplacian
  exact Finset.sum_congr rfl fun w _ => by ring

/-- `R^e ≤ c^n L^e` for a nonpositive exponent `e ≥ -n`, when `L ≤ c R` and `c ≥ 1`. -/
theorem rpow_le_pow_mul_rpow_of_le_mul {R L c e : ℝ} {n : ℕ} (hL : 0 < L) (hc : 1 ≤ c)
    (hLR : L ≤ c * R) (he : e ≤ 0) (hen : -e ≤ n) : R ^ e ≤ c ^ n * L ^ e := by
  have hc0 : 0 < c := by linarith
  have hLc : L / c ≤ R := by rw [div_le_iff₀ hc0]; linarith
  calc R ^ e ≤ (L / c) ^ e := Real.rpow_le_rpow_of_nonpos (div_pos hL hc0) hLc he
    _ = L ^ e / c ^ e := Real.div_rpow hL.le hc0.le e
    _ ≤ c ^ n * L ^ e := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hc0 e)]
      have h1 : 1 ≤ c ^ n * c ^ e := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hc0]
        exact Real.one_le_rpow hc (by linarith)
      have hLe := Real.rpow_pos_of_pos hL e
      nlinarith

/-- The forward differences at `x` along the corrected planes: if `|v| ≤ P` on `B_X(x)` for
`v = G(·, y) - K - Gx - ∑ᵢ ξᵢ ℓᵢ - a` and `|ξ - ∇Ḡ|₁ ≤ S`, then
`|D_j G(x) - ∂_jḠ - ∑ᵢ (D_j ℓᵢ(x) - δᵢⱼ) ∂ᵢḠ| ≤ 2P + (1 + Cc X^η) S`, using (H3) at the
scale `X`. -/
theorem abs_forwardDiff_sub_le {C : OpenComponent ω} {g : C → ℝ} {ℓ : Fin d → C → ℝ} {x : C}
    {K Gx a Cc η X P S : ℝ} {ξ G : Fin d → ℝ} (hX : 1 < X)
    (hℓ : ∀ i, IsCorrectedPlane C (Pi.single i 1) (ℓ i)) (hcorr : CorrectorBoundAt C x.val Cc η X)
    (hP0 : 0 ≤ P) (hS0 : 0 ≤ S) (hCc : 0 ≤ Cc)
    (hpt : ∀ z ∈ componentEuclideanBall C x.val X,
      |g z - K - Gx - ∑ i, ξ i * ℓ i z - a| ≤ P)
    (hsl : ∑ i, |ξ i - G i| ≤ S) (j : Fin d) :
    |forwardDiff C g x j - G j - ∑ i, (forwardDiff C (ℓ i) x j - if i = j then 1 else 0) * G i|
      ≤ 2 * P + (1 + Cc * X ^ η) * S := by
  have hrhs : 0 ≤ 2 * P + (1 + Cc * X ^ η) * S := by
    have : 0 ≤ X ^ η := Real.rpow_nonneg (by linarith) η
    positivity
  have hGj : ∑ i, (if i = j then (1 : ℝ) else 0) * G i = G j := by
    simp [ite_mul]
  unfold forwardDiff
  split_ifs with hx
  · set x' : C := ⟨x.val + LatticeProb.unit j, C.mem_supp_of_adj_mem_supp x.property hx⟩
      with hx'
    have hadj : (componentGraph C).Adj x x' := hx
    have hx'X : ‖latticeEuclideanEmbedding x'.val - latticeEuclideanEmbedding x.val‖ < X := by
      rw [← dist_eq_norm, dist_embedding_adj (ω := ω)
        (show (openGraph ω).Adj x'.val x.val from hx.symm)]
      exact hX
    have hℓj : ∀ i, |ℓ i x' - ℓ i x| ≤ 1 + Cc * X ^ η := by
      intro i
      have h := abs_corrector_sub_le hℓ hcorr le_rfl (by linarith) hadj hx'X hx'X i
      have hi : |((x'.val i : ℤ) : ℝ) - (x.val i : ℝ)| ≤ 1 := by
        simp only [hx', Pi.add_apply, LatticeProb.unit, Pi.single_apply, Int.cast_add,
          add_sub_cancel_left]
        split_ifs <;> simp
      have := abs_sub_abs_le_abs_sub (ℓ i x' - ℓ i x)
        (((x'.val i : ℤ) : ℝ) - (x.val i : ℝ))
      have e : ℓ i x' - ℓ i x - (((x'.val i : ℤ) : ℝ) - (x.val i : ℝ)) =
          (ℓ i x' - (x'.val i : ℝ)) - (ℓ i x - (x.val i : ℝ)) := by ring
      rw [e] at this
      linarith
    have hvx' := hpt x' (by rw [mem_componentEuclideanBall, dist_eq_norm]; exact hx'X)
    have hvx := hpt x (by rw [mem_componentEuclideanBall, dist_self]; linarith)
    have h1 : ∑ i, (ℓ i x' - ℓ i x - if i = j then 1 else 0) * G i =
        ∑ i, (ℓ i x' - ℓ i x) * G i - G j := by
      rw [← hGj, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, (ξ i - G i) * (ℓ i x' - ℓ i x) =
        ∑ i, ξ i * ℓ i x' - ∑ i, ξ i * ℓ i x - ∑ i, (ℓ i x' - ℓ i x) * G i := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hid : g x' - g x - G j - ∑ i, (ℓ i x' - ℓ i x - if i = j then 1 else 0) * G i =
        ((g x' - K - Gx - ∑ i, ξ i * ℓ i x' - a) - (g x - K - Gx - ∑ i, ξ i * ℓ i x - a)) +
          ∑ i, (ξ i - G i) * (ℓ i x' - ℓ i x) := by
      rw [h1, h2]; ring
    have hsum : |∑ i, (ξ i - G i) * (ℓ i x' - ℓ i x)| ≤ (1 + Cc * X ^ η) * S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |(ξ i - G i) * (ℓ i x' - ℓ i x)|
          ≤ ∑ i, |ξ i - G i| * (1 + Cc * X ^ η) :=
            Finset.sum_le_sum fun i _ => by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hℓj i) (abs_nonneg _)
        _ = (1 + Cc * X ^ η) * ∑ i, |ξ i - G i| := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ (1 + Cc * X ^ η) * S :=
            mul_le_mul_of_nonneg_left hsl (by linarith [hℓj j, abs_nonneg (ℓ j x' - ℓ j x)])
    rw [hid]
    refine (abs_add_le _ _).trans ?_
    have := abs_sub (g x' - K - Gx - ∑ i, ξ i * ℓ i x' - a) (g x - K - Gx - ∑ i, ξ i * ℓ i x - a)
    linarith
  · have : ∑ i, ((0 : ℝ) - if i = j then 1 else 0) * G i = -G j := by
      rw [← hGj, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, show (0 : ℝ) - G j - -G j = 0 by ring, abs_zero]
    exact hrhs

/-- The exponents of the core estimate: with `X^{2d+4} ≤ R`, `1 ≤ R` and `L ≤ 2d R`,
`d (2 · 5^d X^{d+2} B R^{-d} + (1 + Cc X^{δ/4}) A₁ R^{1/2-d+δ/4})` is at most
`d (2 · 5^d B + A₁ (1 + Cc)) (2d)^d L^{1/2-d+δ}`. -/
theorem core_exponent_bound (hd : 2 ≤ d) {X R L δ Cc A₁ B : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hX1 : 1 ≤ X) (hXNR : X ^ (2 * d + 4) ≤ R) (hR1 : 1 ≤ R) (hLR : L ≤ 2 * d * R)
    (hL1 : 1 ≤ L) (hCc : 0 ≤ Cc) (hA₁ : 0 ≤ A₁) (hB : 0 ≤ B) :
    d * (2 * (5 ^ d * X ^ d * (B * X ^ 2 * R ^ (-(d : ℝ)))) +
        (1 + Cc * X ^ (δ / 4)) * (A₁ * R ^ ((1 : ℝ) / 2 - d + δ / 4))) ≤
      d * (2 * 5 ^ d * B + A₁ * (1 + Cc)) * (2 * d) ^ d * L ^ (-1 / 2 + δ + (1 - (d : ℝ))) := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < L := by linarith
  have hXR : X ≤ R := (le_self_pow₀ hX1 (by omega)).trans hXNR
  set e₂ : ℝ := 1 / 2 - d + δ / 2 with he₂
  have hP : 5 ^ d * X ^ d * (B * X ^ 2 * R ^ (-(d : ℝ))) ≤ 5 ^ d * B * R ^ e₂ := by
    have hsq : X ^ d * X ^ 2 ≤ R ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, ← pow_add]
      refine (Real.le_sqrt (by positivity) hR0.le).mpr ?_
      rw [← pow_mul]
      calc X ^ ((d + 2) * 2) = X ^ (2 * d + 4) := by ring_nf
        _ ≤ R := hXNR
    have hexp : R ^ ((1 : ℝ) / 2) * R ^ (-(d : ℝ)) ≤ R ^ e₂ := by
      rw [← Real.rpow_add hR0]
      exact Real.rpow_le_rpow_of_exponent_le hR1 (by rw [he₂]; linarith)
    have hRd : 0 ≤ R ^ (-(d : ℝ)) := Real.rpow_nonneg hR0.le _
    calc 5 ^ d * X ^ d * (B * X ^ 2 * R ^ (-(d : ℝ)))
        = 5 ^ d * B * ((X ^ d * X ^ 2) * R ^ (-(d : ℝ))) := by ring
      _ ≤ 5 ^ d * B * (R ^ ((1 : ℝ) / 2) * R ^ (-(d : ℝ))) := by gcongr
      _ ≤ 5 ^ d * B * R ^ e₂ := by gcongr
  have hS : (1 + Cc * X ^ (δ / 4)) * (A₁ * R ^ ((1 : ℝ) / 2 - d + δ / 4)) ≤
      A₁ * (1 + Cc) * R ^ e₂ := by
    have h1 : X ^ (δ / 4) ≤ R ^ (δ / 4) := Real.rpow_le_rpow (by linarith) hXR (by linarith)
    have h2 : R ^ (δ / 4) * R ^ ((1 : ℝ) / 2 - d + δ / 4) = R ^ e₂ := by
      rw [← Real.rpow_add hR0, he₂]; ring_nf
    have h3 : R ^ ((1 : ℝ) / 2 - d + δ / 4) ≤ R ^ e₂ :=
      Real.rpow_le_rpow_of_exponent_le hR1 (by rw [he₂]; linarith)
    have hRe₁ : 0 ≤ R ^ ((1 : ℝ) / 2 - d + δ / 4) := Real.rpow_nonneg hR0.le _
    calc (1 + Cc * X ^ (δ / 4)) * (A₁ * R ^ ((1 : ℝ) / 2 - d + δ / 4))
        ≤ (1 + Cc * R ^ (δ / 4)) * (A₁ * R ^ ((1 : ℝ) / 2 - d + δ / 4)) := by gcongr
      _ = A₁ * (R ^ ((1 : ℝ) / 2 - d + δ / 4) +
            Cc * (R ^ (δ / 4) * R ^ ((1 : ℝ) / 2 - d + δ / 4))) := by ring
      _ ≤ A₁ * (R ^ e₂ + Cc * R ^ e₂) := by rw [h2]; gcongr
      _ = A₁ * (1 + Cc) * R ^ e₂ := by ring
  have hRL : R ^ e₂ ≤ (2 * d) ^ d * L ^ (-1 / 2 + δ + (1 - (d : ℝ))) := by
    refine (rpow_le_pow_mul_rpow_of_le_mul hL0 (by linarith) hLR (by rw [he₂]; linarith)
      (by rw [he₂]; linarith)).trans ?_
    have : L ^ e₂ ≤ L ^ (-1 / 2 + δ + (1 - (d : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by rw [he₂]; linarith)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hK : 0 ≤ (d : ℝ) * (2 * 5 ^ d * B + A₁ * (1 + Cc)) := by positivity
  calc (d : ℝ) * (2 * (5 ^ d * X ^ d * (B * X ^ 2 * R ^ (-(d : ℝ)))) +
        (1 + Cc * X ^ (δ / 4)) * (A₁ * R ^ ((1 : ℝ) / 2 - d + δ / 4)))
      ≤ d * (2 * (5 ^ d * B * R ^ e₂) + A₁ * (1 + Cc) * R ^ e₂) := by gcongr
    _ = d * (2 * 5 ^ d * B + A₁ * (1 + Cc)) * R ^ e₂ := by ring
    _ ≤ d * (2 * 5 ^ d * B + A₁ * (1 + Cc)) *
          ((2 * d) ^ d * L ^ (-1 / 2 + δ + (1 - (d : ℝ)))) :=
        mul_le_mul_of_nonneg_left hRL hK
    _ = _ := by ring

/-- The scales of the core estimate: `|x - y|₁ ≥ 2d (1 + R₁) X^N` with `L ≤ 2d R` gives
`X^N ≤ R` and `R₁ ≤ R`. -/
theorem core_scales {X R L R₁ : ℝ} {d N : ℕ} (hd : 2 ≤ d) (hR₁ : 0 < R₁) (hXN1 : 1 ≤ X ^ N)
    (hLR : L ≤ 2 * d * R) (hAL : 2 * d * (1 + R₁) * X ^ N ≤ L) :
    X ^ N ≤ R ∧ R₁ ≤ R ∧ 1 ≤ L := by
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h2d : (0 : ℝ) < 2 * d := by positivity
  have hRXN : (1 + R₁) * X ^ N ≤ R := by
    have : 2 * d * ((1 + R₁) * X ^ N) ≤ 2 * d * R := by linarith
    exact le_of_mul_le_mul_left this h2d
  have h1 : 1 ≤ 2 * (d : ℝ) * (1 + R₁) := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  nlinarith

/-- step:2.6-expansion, the deterministic core (paper L554-655), from `GreenOscillationStep`,
`SlopeEstimateStep` and `ContinuumGreenStep`, with `N = 2d + 4`. -/
theorem greenGradientCoreStep (hd : 2 ≤ d) : GreenGradientCoreStep d hd := by
  intro κ δ Ch Cc Cr cD hδ hδ1 hCh hCc hCr hcD
  obtain ⟨A₂, hA₂, hosc⟩ := greenOscillationStep hd κ δ Ch hδ hδ1 hCh
  obtain ⟨A₁, R₁, hA₁, hR₁, hslope⟩ := slopeEstimateStep hd (continuumGreenStep d hd) κ δ Ch Cc
    cD (Cr * A₂) hδ hδ1 hCh hCc hcD (by positivity)
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = d * (2 * 5 ^ d * (Cr * A₂) + A₁ * (1 + Cc)) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  refine ⟨2 * d * (1 + R₁) + K₀ * (2 * d) ^ d + 1, 2 * d + 4, ?_, ?_⟩
  · have : 0 ≤ 2 * (d : ℝ) * (1 + R₁) + K₀ * (2 * d) ^ d := by positivity
    linarith
  intro ω C y g K ℓ x X hX hharm hℓ hclose hreg hcorr hdense hL
  obtain ⟨L, hLdef⟩ : ∃ L, L = Rigidity.Steps.S2.latticeL1Dist x.val y.val := ⟨_, rfl⟩
  rw [← hLdef] at hL ⊢
  obtain ⟨R, hR⟩ : ∃ R, R = dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding y.val) / 2 := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by linarith
  have hXN1 : 1 ≤ X ^ (2 * d + 4) := one_le_pow₀ hX1
  have hLR : L ≤ 2 * d * R := by
    have h := latticeL1Dist_le_mul_norm x.val y.val
    rw [← dist_eq_norm, ← hLdef] at h
    rw [hR]; linarith
  have hAL : 2 * d * (1 + R₁) * X ^ (2 * d + 4) ≤ L := by
    have : 0 ≤ (K₀ * (2 * d) ^ d + 1) * X ^ (2 * d + 4) := by positivity
    nlinarith
  obtain ⟨hXNR, hR₁R, hL1⟩ := core_scales hd hR₁ hXN1 hLR hAL
  have hX2R : X ^ 2 ≤ R := (pow_le_pow_right₀ hX1 (by omega)).trans hXNR
  have h2XR : 2 * X ≤ R := by nlinarith
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < L := by linarith
  have hDR : dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding y.val) = 2 * R := by
    rw [hR]; ring
  -- the size of `u = G(·, y) - K - Ḡ(x - y)` on `B_R(x)`
  obtain ⟨Gx, hGx⟩ : ∃ Gx, Gx = greenBar d hd κ (toReal x.val - toReal y.val) := ⟨_, rfl⟩
  have hu : componentBallL2 C x.val R (fun z => g z - K - Gx) ≤ A₂ * R ^ ((2 : ℝ) - d) := by
    refine componentBallL2_le_of_abs_le C x.val R _ (by positivity) fun z hz => ?_
    rw [mem_componentEuclideanBall] at hz
    have h := hosc C y g K x X hclose (by rw [← hR]; linarith) z (by rw [← hR]; exact hz)
    rw [hDR, ← hGx] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hA₂.le)
    have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact Real.rpow_le_rpow_of_nonpos hR0 (by linarith) (by linarith)
  -- large-scale regularity at the scale `R`
  obtain ⟨ξ, a, hξ⟩ := hreg R h2XR (fun z => g z - K - Gx) (by
    intro z hz _
    rw [componentLaplacian_sub_sub_const]
    refine hharm z fun hzy => ?_
    rw [mem_componentEuclideanBall, hzy, dist_comm, hDR] at hz
    linarith)
  have hB : ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
      componentBallL2 C x.val r (fun z => g z - K - Gx - ∑ i, ξ i * ℓ i z - a) ≤
        Cr * A₂ * r ^ 2 * R ^ (-(d : ℝ)) := by
    intro r hXr hrR
    have e : R ^ ((2 : ℝ) - d) = R ^ 2 * R ^ (-(d : ℝ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hR0, Real.rpow_two]
    calc componentBallL2 C x.val r (fun z => g z - K - Gx - ∑ i, ξ i * ℓ i z - a)
        ≤ Cr * (r / R) ^ 2 * componentBallL2 C x.val R (fun z => g z - K - Gx) := hξ r hXr hrR
      _ ≤ Cr * (r / R) ^ 2 * (A₂ * R ^ ((2 : ℝ) - d)) := by gcongr
      _ = Cr * A₂ * r ^ 2 * R ^ (-(d : ℝ)) := by
        rw [e]; field_simp
  -- the slope estimate
  have hsl := hslope C y g K ℓ x X hX1 hℓ hclose hcorr hdense R hR hR₁R hX2R ξ a
    (by rw [hGx] at hB; exact hB)
  -- the pointwise bound at the scale `X`
  have hpt : ∀ z ∈ componentEuclideanBall C x.val X,
      |g z - K - Gx - ∑ i, ξ i * ℓ i z - a| ≤
        5 ^ d * X ^ d * (Cr * A₂ * X ^ 2 * R ^ (-(d : ℝ))) := by
    intro z hz
    refine (abs_le_card_mul_componentBallL2 C x.val X
      (fun z => g z - K - Gx - ∑ i, ξ i * ℓ i z - a) hz).trans ?_
    exact mul_le_mul (card_componentEuclideanBall_le C x.val hX1) (hB X le_rfl (by linarith))
      (componentBallL2_nonneg _ _ _ _) (by positivity)
  have hj := abs_forwardDiff_sub_le (by linarith) hℓ hcorr (by positivity)
    (mul_nonneg hA₁.le (Real.rpow_nonneg hR0.le _)) hCc.le hpt hsl
  have hsumj := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hj j
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumj
  refine hsumj.trans ?_
  simp only [Real.rpow_eq_pow]
  rw [mul_assoc _ (L ^ _) (L ^ _), ← Real.rpow_add hL0]
  refine (core_exponent_bound hd hδ hδ1 hX1 hXNR hR1 hLR hL1 hCc.le hA₁.le
    (by positivity)).trans ?_
  rw [← hK₀]
  have hLE : 0 ≤ L ^ (-1 / 2 + δ + (1 - (d : ℝ))) := by positivity
  have : 0 ≤ 2 * (d : ℝ) * (1 + R₁) + 1 := by positivity
  nlinarith

/-- **Proposition 2.6** from the inputs `SupercriticalBondGreenQuantitative` and
`CorrectorQuantitativeInput` and the two remaining steps `RegularityScaleStep` (large-scale
regularity beyond a minimal scale) and `DensityScaleStep` (density of the cluster beyond a minimal
scale). -/
theorem greenGradientHomogenization_of_regularity_density [NeZero d] (hd : 2 ≤ d)
    (p : unitInterval) (hpc : LatticeProb.Percolation.criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput)
    (hReg : RegularityScaleStep d p) (hDense : DensityScaleStep d p) :
    GreenGradientHomogenizationStmt d hd p :=
  greenGradientHomogenization_of_steps hd p hpc hp1 hGQ hCQ hReg hDense (tailOfOsStep d p)
    (minimalScaleStep d p) (greenGradientCoreStep hd)

end Rigidity.Proofs.S2
