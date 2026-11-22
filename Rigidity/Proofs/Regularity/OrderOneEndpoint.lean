import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Rigidity.Proofs.Regularity.SinglePolynomial

/-!
# The endpoint iteration for regularity of order one

Armstrong and Dario (arXiv:1609.09431v2) deduce Theorem 2 (iii) from their Lemma 7.3 by the
argument of Armstrong, Kuusi and Mourrat, Proposition 3.1. This file proves, in an abstract form,
the deterministic part of the order-one case `k = 1`: from the mesoscopic estimate (7.18) at degree
two and a lift of the affine functions to global solutions with a small relative error, one lifted
affine function `φ` approximates `u` on all the balls `B_t`, `X ≤ t ≤ R / 2`, at the rate
`(t / R) ^ 2`.

The setting is an additive group `F` with seminorms `N t` (the normalized `L²` norms on the balls
`B_t`), a subgroup `P₂` (the `ā`-harmonic polynomials of degree at most two), additive maps
`ι : V →+ F` (the affine functions) and `κ : W →+ F` (the homogeneous quadratic parts), a lift
`L : V →+ F`, a size `sz t ℓ` of affine functions at the radius `t` and a size `nq q` of quadratic
parts. `OrderOneEndpointData` collects the hypotheses on the radii `[X, R]`: the comparison
`sz t ℓ + t ^ 2 nq q ≤ CL N t (ι ℓ + κ q)`, the lift error `N t (L ℓ - ι ℓ) ≤ ε sz t ℓ`, the
volume factor `RadiusMonotone`, and (7.18) at degree two,
`D₂(v, w) ≤ A (v / r) ^ 3 D₂(r, w) + A v ^ (-δ) (v / r) N r w` for `X ≤ v ≤ r / 2` and `w`
harmonic in `B_r`, `D₂ = ballExcess N P₂`.

* `orderOneEndpoint_step`: one comparison at the ratio `θ`. At the radius `r` write
  `u = L ℓ₀ + κ q + h` and `e = r ^ (-2) N r h`; a near-best `ι ℓ + κ q'` of `u - L ℓ₀` at the
  radius `v = θ r` gives the new pair `(ℓ₀ + ℓ, q')`, and the weighted quantity
  `nq q + K e` grows at most by the factor `1 + c v ^ (-δ)` (`weighted_endpoint_step`).
* `orderOneEndpoint_iterate`: on the radii `θ ^ j R ≥ X` the product of the factors is at most
  `exp (c (θ ^ j R) ^ (-δ) / (1 - θ ^ δ))`.
* `orderOneEndpoint_fit`: a lifted affine function at every radius `t ∈ [X, R / 2]`.
* `exists_forall_le_of_orderOneEndpoint`: one lifted affine function for all radii
  (`exists_mem_forall_le_of_ballExcess_le`).

The quadratic coefficient is carried as an ordinary homogeneous quadratic with its size `nq`; only
the affine functions are lifted, so no global solution of degree two is used.
-/

namespace Rigidity.Proofs.Regularity

/-- Combine the homogeneous coefficient and the normalized fitting error in one step. -/
theorem weighted_endpoint_step {b e b' e' h K B : ℝ}
    (he : 0 ≤ e) (hh : 0 ≤ h) (hK : 1 ≤ K) (hB : 2 * B ≤ K)
    (herror : e' ≤ e / 2 + h * (b + e))
    (hcoeff : b' ≤ b + B * e + h * (b + e)) :
    b' + K * e' ≤ (1 + (1 + K) * h) * (b + K * e) := by
  have hweight : 0 ≤ K := le_trans zero_le_one hK
  have hfit : (B + K / 2) * e ≤ K * e :=
    mul_le_mul_of_nonneg_right (by linarith) he
  have hsum : b + e ≤ b + K * e := by
    have := mul_le_mul_of_nonneg_right hK he
    linarith
  have hKh : 0 ≤ (1 + K) * h := mul_nonneg (by linarith) hh
  calc
    b' + K * e' ≤ (b + B * e + h * (b + e)) + K * (e / 2 + h * (b + e)) :=
      add_le_add hcoeff (mul_le_mul_of_nonneg_left herror hweight)
    _ = b + (B + K / 2) * e + (1 + K) * h * (b + e) := by ring
    _ ≤ b + K * e + (1 + K) * h * (b + K * e) :=
      add_le_add (add_le_add (le_refl b) hfit) (mul_le_mul_of_nonneg_left hsum hKh)
    _ = _ := by ring

variable {F V W : Type*} [AddCommGroup F] [AddCommGroup V] [AddCommGroup W]

/-- The hypotheses of the endpoint iteration of order one on the radii `[X, R]`: sizes of the
affine functions and of the quadratic parts, the comparison of these sizes with the norms, the
lift error `N t (L ℓ - ι ℓ) ≤ ε sz t ℓ`, the volume factor, the decomposition of `P₂`, the
harmonicity predicate `Hm r` (harmonic in `B_r`) and the mesoscopic estimate (7.18) at degree
two. -/
structure OrderOneEndpointData (N : ℝ → AddGroupSeminorm F) (P₂ : AddSubgroup F)
    (ι L : V →+ F) (κ : W →+ F) (sz : ℝ → V → ℝ) (nq : W → ℝ) (Hm : ℝ → F → Prop)
    (X R A δ CV γ cU CL ε : ℝ) : Prop where
  sz_nonneg : ∀ t ℓ, X ≤ t → 0 ≤ sz t ℓ
  nq_nonneg : ∀ q, 0 ≤ nq q
  nq_zero : nq 0 = 0
  nq_le_add : ∀ q q', nq q' ≤ nq q + nq (q' - q)
  quad_le : ∀ t, X ≤ t → t ≤ R → ∀ q, N t (κ q) ≤ cU * t ^ 2 * nq q
  affine_le : ∀ t, X ≤ t → t ≤ R → ∀ ℓ, N t (ι ℓ) ≤ sz t ℓ
  sz_le : ∀ t s, X ≤ t → t ≤ s → s ≤ R → ∀ ℓ, sz s ℓ ≤ s / t * sz t ℓ
  le_poly : ∀ t, X ≤ t → t ≤ R → ∀ ℓ q, sz t ℓ + t ^ 2 * nq q ≤ CL * N t (ι ℓ + κ q)
  lift_le : ∀ t, X ≤ t → t ≤ R → ∀ ℓ, N t (L ℓ - ι ℓ) ≤ ε * sz t ℓ
  mem_P₂ : ∀ q, κ q ∈ P₂
  exists_of_mem : ∀ p ∈ P₂, ∃ ℓ q, p = ι ℓ + κ q
  mono : RadiusMonotone N X R CV γ
  harm_anti : ∀ r r' w, r' ≤ r → Hm r w → Hm r' w
  harm_sub : ∀ r w ℓ, Hm r w → Hm r (w - L ℓ)
  meso : ∀ r w, 2 * X ≤ r → r ≤ R → Hm r w → ∀ v, X ≤ v → v ≤ r / 2 →
    ballExcess N P₂ v w ≤
      A * (v / r) ^ 3 * ballExcess N P₂ r w + A * v ^ (-δ) * (v / r) * N r w

/-- The constant `B` of one comparison step: the new affine part and the change of the quadratic
part are at most `B e` plus a mesoscopic error. -/
noncomputable def endpointSlopeConst (A CV γ CL θ : ℝ) : ℝ :=
  CL * (A * θ + CV * (1 / θ) ^ γ / θ ^ 2)

/-- The weight `K` of the normalized error in the iterated quantity `nq q + K e`. -/
noncomputable def endpointWeight (A CV γ CL θ : ℝ) : ℝ :=
  max 1 (2 * endpointSlopeConst A CV γ CL θ)

/-- The rate `c` of the factor `1 + c v ^ (-δ)` of one comparison step. -/
noncomputable def endpointRate (A CV γ cU CL θ : ℝ) : ℝ :=
  (1 + endpointWeight A CV γ CL θ) * ((1 + CL) * (A / θ * max 1 cU + 1))

/-- The constant of the fit at each radius. -/
noncomputable def endpointFitConst (A δ CV γ cU CL θ : ℝ) : ℝ :=
  (CV * (1 / θ) ^ γ + cU) * Real.exp (endpointRate A CV γ cU CL θ / (1 - θ ^ δ)) *
    endpointWeight A CV γ CL θ / θ ^ 2

theorem one_le_endpointWeight (A CV γ CL θ : ℝ) : 1 ≤ endpointWeight A CV γ CL θ :=
  le_max_left _ _

theorem endpointRate_nonneg {A CV γ cU CL θ : ℝ} (hA : 0 ≤ A) (hCL : 0 ≤ CL) (hθ : 0 < θ) :
    0 ≤ endpointRate A CV γ cU CL θ := by
  have hK := one_le_endpointWeight A CV γ CL θ
  have h1 : 0 ≤ A / θ * max 1 cU :=
    mul_nonneg (div_nonneg hA hθ.le) (zero_le_one.trans (le_max_left _ _))
  unfold endpointRate
  exact mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))

section

variable {N : ℝ → AddGroupSeminorm F} {P₂ : AddSubgroup F} {ι L : V →+ F} {κ : W →+ F}
  {sz : ℝ → V → ℝ} {nq : W → ℝ} {Hm : ℝ → F → Prop} {X R A δ CV γ cU CL ε θ : ℝ}

/-- **One comparison step of the endpoint iteration.** From the radius `r` to `θ r ≥ X`, the
quantity `nq q + K r ^ (-2) N r (u - L ℓ₀ - κ q)` grows at most by the factor
`1 + c (θ r) ^ (-δ)`. -/
theorem orderOneEndpoint_step
    (hD : OrderOneEndpointData N P₂ ι L κ sz nq Hm X R A δ CV γ cU CL ε)
    (hX : 0 < X) (hA : 0 ≤ A) (hCL : 0 ≤ CL)
    (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hAθ : A * θ ≤ 1 / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεB : ε * endpointSlopeConst A CV γ CL θ ≤ 1 / 4)
    {u : F} {r : ℝ} (hr : X ≤ θ * r) (hrR : r ≤ R) {ℓ₀ : V} (hu : Hm r (u - L ℓ₀)) (q : W) :
    ∃ ℓ₁ : V, ∃ q₁ : W,
      nq q₁ + endpointWeight A CV γ CL θ * (N (θ * r) (u - L ℓ₁ - κ q₁) / (θ * r) ^ 2) ≤
        (1 + endpointRate A CV γ cU CL θ * (θ * r) ^ (-δ)) *
          (nq q + endpointWeight A CV γ CL θ * (N r (u - L ℓ₀ - κ q) / r ^ 2)) := by
  set B := endpointSlopeConst A CV γ CL θ with hBdef
  set K := endpointWeight A CV γ CL θ with hKdef
  set c₁ := A / θ * max 1 cU + 1 with hc₁
  have hK1 : 1 ≤ K := le_max_left _ _
  have hBK : 2 * B ≤ K := le_max_right _ _
  have hrate : endpointRate A CV γ cU CL θ = (1 + K) * ((1 + CL) * c₁) := rfl
  have hc₁0 : 1 ≤ c₁ := by
    have : 0 ≤ A / θ * max 1 cU :=
      mul_nonneg (div_nonneg hA hθ.le) (zero_le_one.trans (le_max_left _ _))
    linarith
  have hvpos : 0 < θ * r := hX.trans_le hr
  have hr0 : 0 < r := by nlinarith
  set v := θ * r with hv
  have hvr : v / r = θ := by rw [hv]; field_simp
  have hrv : r / v = 1 / θ := by rw [hv]; field_simp
  have hXv : X ≤ v := hr
  have hvr2 : v ≤ r / 2 := by rw [hv]; nlinarith
  have h2X : 2 * X ≤ r := by linarith
  have hXr : X ≤ r := by linarith
  have hvR : v ≤ R := by linarith
  set ρ := v ^ (-δ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hvpos _
  set w := u - L ℓ₀ with hw
  set nh := N r (w - κ q) with hnh
  set b := nq q with hb
  set e := nh / r ^ 2 with he
  have hnh0 : 0 ≤ nh := apply_nonneg _ _
  have hb0 : 0 ≤ b := hD.nq_nonneg q
  have he0 : 0 ≤ e := div_nonneg hnh0 (by positivity)
  have hnhe : nh = r ^ 2 * e := by rw [he]; field_simp
  have hmono_h : N v (w - κ q) ≤ CV * (1 / θ) ^ γ * nh := by
    have := hD.mono (w - κ q) v r hXv (by linarith) hrR
    rwa [hrv] at this
  have hθγ : 0 ≤ (1 / θ) ^ γ := Real.rpow_nonneg (by positivity) _
  rcases (add_nonneg he0 hb0).eq_or_lt with h0 | hpos
  · have he' : e = 0 := by linarith
    have hb' : b = 0 := by linarith
    refine ⟨ℓ₀, q, ?_⟩
    have hz : N v (w - κ q) = 0 := by
      refine le_antisymm ?_ (apply_nonneg _ _)
      have : nh = 0 := by rw [hnhe, he', mul_zero]
      rw [this, mul_zero] at hmono_h
      exact hmono_h
    rw [hz, show nq q = 0 from hb', hb', he']
    simp
  · set η := v ^ 2 * ρ * (e + b) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨p, hp, hpη⟩ := exists_lt_ballExcess_add N P₂ hη0 v w
    obtain ⟨ℓ, q', rfl⟩ := hD.exists_of_mem p hp
    refine ⟨ℓ₀ + ℓ, q', ?_⟩
    have hmeso := hD.meso r w h2X hrR hu v hXv hvr2
    rw [hvr, ← hρ] at hmeso
    have hDr : ballExcess N P₂ r w ≤ nh := ballExcess_le N P₂ (hD.mem_P₂ q)
    have hNw : N r w ≤ nh + cU * r ^ 2 * b := by
      calc N r w = N r ((w - κ q) + κ q) := by rw [sub_add_cancel]
        _ ≤ N r (w - κ q) + N r (κ q) := map_add_le_add _ _ _
        _ ≤ nh + cU * r ^ 2 * b := add_le_add le_rfl (hD.quad_le r hXr hrR q)
    set S := N v (w - (ι ℓ + κ q')) with hS
    have hS1 : S ≤ A * θ ^ 3 * nh + A * ρ * θ * (nh + cU * r ^ 2 * b) + η := by
      have h1 : A * θ ^ 3 * ballExcess N P₂ r w ≤ A * θ ^ 3 * nh :=
        mul_le_mul_of_nonneg_left hDr (by positivity)
      have h2 : A * ρ * θ * N r w ≤ A * ρ * θ * (nh + cU * r ^ 2 * b) :=
        mul_le_mul_of_nonneg_left hNw (by positivity)
      linarith only [hpη, hmeso, h1, h2]
    have hcU' : e + cU * b ≤ max 1 cU * (e + b) := by
      have h1 : e ≤ max 1 cU * e := le_mul_of_one_le_left he0 (le_max_left _ _)
      have h2 : cU * b ≤ max 1 cU * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
      linarith only [h1, h2]
    have hθA : θ ^ 2 * (A / θ) = A * θ := by
      calc θ ^ 2 * (A / θ) = A * θ * (θ / θ) := by ring
        _ = A * θ := by rw [div_self hθ.ne', mul_one]
    have hv2e : v ^ 2 = θ ^ 2 * r ^ 2 := by rw [hv]; ring
    have hS2 : S ≤ v ^ 2 * (A * θ * e + c₁ * ρ * (e + b)) := by
      have h6 : A * ρ * θ * (nh + cU * r ^ 2 * b) ≤
          A * ρ * θ * r ^ 2 * (max 1 cU * (e + b)) := by
        have h7 : nh + cU * r ^ 2 * b = r ^ 2 * (e + cU * b) := by rw [hnhe]; ring
        have h8 : r ^ 2 * (e + cU * b) ≤ r ^ 2 * (max 1 cU * (e + b)) :=
          mul_le_mul_of_nonneg_left hcU' (by positivity)
        rw [h7]
        calc A * ρ * θ * (r ^ 2 * (e + cU * b)) ≤ A * ρ * θ * (r ^ 2 * (max 1 cU * (e + b))) :=
              mul_le_mul_of_nonneg_left h8 (by positivity)
          _ = A * ρ * θ * r ^ 2 * (max 1 cU * (e + b)) := by ring
      have h9 : v ^ 2 * (A * θ * e + c₁ * ρ * (e + b)) =
          A * θ ^ 3 * nh + A * ρ * θ * r ^ 2 * (max 1 cU * (e + b)) + η := by
        rw [hη, hc₁, hnhe, hv2e]
        linear_combination (r ^ 2 * max 1 cU * ρ * (e + b)) * hθA
      calc S ≤ A * θ ^ 3 * nh + A * ρ * θ * (nh + cU * r ^ 2 * b) + η := hS1
        _ ≤ A * θ ^ 3 * nh + A * ρ * θ * r ^ 2 * (max 1 cU * (e + b)) + η := by
            linarith only [h6]
        _ = v ^ 2 * (A * θ * e + c₁ * ρ * (e + b)) := h9.symm
    have hpq : N v (ι ℓ + κ (q' - q)) ≤ S + CV * (1 / θ) ^ γ * nh := by
      calc N v (ι ℓ + κ (q' - q)) = N v (-(w - (ι ℓ + κ q')) + (w - κ q)) := by
            congr 1; rw [map_sub]; abel
        _ ≤ N v (-(w - (ι ℓ + κ q'))) + N v (w - κ q) := map_add_le_add _ _ _
        _ = S + N v (w - κ q) := by rw [map_neg_eq_map]
        _ ≤ S + CV * (1 / θ) ^ γ * nh := add_le_add le_rfl hmono_h
    have hlow := hD.le_poly v hXv hvR ℓ (q' - q)
    have hE : N v (u - L (ℓ₀ + ℓ) - κ q') ≤ S + ε * sz v ℓ := by
      calc N v (u - L (ℓ₀ + ℓ) - κ q') = N v ((w - (ι ℓ + κ q')) + -(L ℓ - ι ℓ)) := by
            congr 1; rw [map_add, hw]; abel
        _ ≤ N v (w - (ι ℓ + κ q')) + N v (-(L ℓ - ι ℓ)) := map_add_le_add _ _ _
        _ = S + N v (L ℓ - ι ℓ) := by rw [map_neg_eq_map]
        _ ≤ S + ε * sz v ℓ := add_le_add le_rfl (hD.lift_le v hXv hvR ℓ)
    have hbq : nq q' ≤ b + nq (q' - q) := hD.nq_le_add q q'
    -- normalized quantities at the radius `v`
    have hv2 : 0 < v ^ 2 := by positivity
    set s := S / v ^ 2 with hs
    set z := sz v ℓ / v ^ 2 with hz
    set y := nq (q' - q) with hy
    set e' := N v (u - L (ℓ₀ + ℓ) - κ q') / v ^ 2 with he'
    have hy0 : 0 < y ∨ 0 ≤ y := Or.inr (hD.nq_nonneg _)
    have hy0' : 0 ≤ y := hD.nq_nonneg _
    have hz0 : 0 ≤ z := div_nonneg (hD.sz_nonneg v ℓ hXv) hv2.le
    have hSs : S = v ^ 2 * s := by rw [hs]; field_simp
    have hszz : sz v ℓ = v ^ 2 * z := by rw [hz]; field_simp
    have hEe : N v (u - L (ℓ₀ + ℓ) - κ q') = v ^ 2 * e' := by rw [he']; field_simp
    have hs1 : s ≤ A * θ * e + c₁ * ρ * (e + b) := by
      rw [hSs] at hS2
      exact le_of_mul_le_mul_left hS2 hv2
    have hT : z + y ≤ CL * (s + CV * (1 / θ) ^ γ / θ ^ 2 * e) := by
      have h1 : v ^ 2 * (z + y) ≤ v ^ 2 * (CL * (s + CV * (1 / θ) ^ γ / θ ^ 2 * e)) := by
        have h2 : CL * N v (ι ℓ + κ (q' - q)) ≤ CL * (S + CV * (1 / θ) ^ γ * nh) :=
          mul_le_mul_of_nonneg_left hpq hCL
        have hvθ : v ^ 2 / θ ^ 2 = r ^ 2 := by rw [hv2e]; field_simp
        have h3 : v ^ 2 * (CL * (s + CV * (1 / θ) ^ γ / θ ^ 2 * e)) =
            CL * (S + CV * (1 / θ) ^ γ * nh) := by
          calc v ^ 2 * (CL * (s + CV * (1 / θ) ^ γ / θ ^ 2 * e)) =
              CL * (v ^ 2 * s + CV * (1 / θ) ^ γ * (v ^ 2 / θ ^ 2) * e) := by ring
            _ = CL * (S + CV * (1 / θ) ^ γ * nh) := by rw [hvθ, ← hSs, hnhe]; ring
        rw [h3]
        rw [hszz] at hlow
        linarith only [hlow, h2]
      exact le_of_mul_le_mul_left h1 hv2
    have he'1 : e' ≤ s + ε * z := by
      have h1 : v ^ 2 * e' ≤ v ^ 2 * (s + ε * z) := by
        rw [← hEe]
        calc N v (u - L (ℓ₀ + ℓ) - κ q') ≤ S + ε * sz v ℓ := hE
          _ = v ^ 2 * (s + ε * z) := by rw [hSs, hszz]; ring
      exact le_of_mul_le_mul_left h1 hv2
    have hBe : B * e = CL * (A * θ) * e + CL * (CV * (1 / θ) ^ γ / θ ^ 2) * e := by
      rw [hBdef, endpointSlopeConst]; ring
    have hCLs : CL * s ≤ CL * (A * θ * e + c₁ * ρ * (e + b)) := mul_le_mul_of_nonneg_left hs1 hCL
    have hT2 : z + y ≤ B * e + CL * (c₁ * ρ * (e + b)) := by linarith only [hT, hCLs, hBe]
    have hm0 : 0 ≤ c₁ * ρ * (e + b) := by positivity
    have hεT : ε * z ≤ ε * (B * e + CL * (c₁ * ρ * (e + b))) :=
      mul_le_mul_of_nonneg_left (by linarith only [hT2, hy0']) hε
    have hεBe : ε * B * e ≤ 1 / 4 * e := mul_le_mul_of_nonneg_right hεB he0
    have hAθe : A * θ * e ≤ 1 / 4 * e := mul_le_mul_of_nonneg_right hAθ he0
    have hεCL : ε * (CL * (c₁ * ρ * (e + b))) ≤ CL * (c₁ * ρ * (e + b)) :=
      mul_le_of_le_one_left (mul_nonneg hCL hm0) hε1
    set hh := (1 + CL) * c₁ * ρ with hhh
    have hhh0 : 0 ≤ hh := by positivity
    have herror : e' ≤ e / 2 + hh * (b + e) := by
      have : hh * (b + e) = c₁ * ρ * (e + b) + CL * (c₁ * ρ * (e + b)) := by rw [hhh]; ring
      linarith only [he'1, hεT, hεBe, hAθe, hεCL, hs1, this]
    have hcoeff : nq q' ≤ b + B * e + hh * (b + e) := by
      have : hh * (b + e) = c₁ * ρ * (e + b) + CL * (c₁ * ρ * (e + b)) := by rw [hhh]; ring
      linarith only [hbq, hT2, hz0, this, hm0]
    have hstep := weighted_endpoint_step he0 hhh0 hK1 hBK herror hcoeff
    have hfac : (1 + K) * hh = endpointRate A CV γ cU CL θ * ρ := by rw [hrate, hhh]; ring
    rw [hfac] at hstep
    exact hstep

/-- **The endpoint iteration.** On every radius `θ ^ j R ≥ X` some lifted affine function
`L ℓ₀` and quadratic part `κ q` satisfy
`nq q + K (θ ^ j R) ^ (-2) N (u - L ℓ₀ - κ q) ≤ exp (c (θ ^ j R) ^ (-δ) / (1 - θ ^ δ)) K R ^ (-2)
N R u`. -/
theorem orderOneEndpoint_iterate
    (hD : OrderOneEndpointData N P₂ ι L κ sz nq Hm X R A δ CV γ cU CL ε)
    (hX : 0 < X) (hA : 0 ≤ A) (hCL : 0 ≤ CL) (hδ : 0 < δ)
    (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hAθ : A * θ ≤ 1 / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεB : ε * endpointSlopeConst A CV γ CL θ ≤ 1 / 4)
    (hR : 0 < R) {u : F} (hu : Hm R u) :
    ∀ j : ℕ, X ≤ θ ^ j * R → ∃ ℓ₀ : V, ∃ q : W,
      nq q + endpointWeight A CV γ CL θ * (N (θ ^ j * R) (u - L ℓ₀ - κ q) / (θ ^ j * R) ^ 2) ≤
        Real.exp (endpointRate A CV γ cU CL θ * (θ ^ j * R) ^ (-δ) / (1 - θ ^ δ)) *
          (endpointWeight A CV γ CL θ * (N R u / R ^ 2)) := by
  set K := endpointWeight A CV γ CL θ with hK
  set c := endpointRate A CV γ cU CL θ with hc
  have hc0 : 0 ≤ c := endpointRate_nonneg hA hCL hθ
  have hK1 : 1 ≤ K := one_le_endpointWeight _ _ _ _ _
  have hθ1 : θ < 1 := by linarith
  have hθδ : θ ^ δ < 1 := Real.rpow_lt_one hθ.le hθ1 hδ
  have hθδ0 : 0 < θ ^ δ := Real.rpow_pos_of_pos hθ _
  have h1θ : 0 < 1 - θ ^ δ := by linarith
  have hH0 : 0 ≤ K * (N R u / R ^ 2) :=
    mul_nonneg (by linarith) (div_nonneg (apply_nonneg _ _) (by positivity))
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, 0, ?_⟩
    simp only [pow_zero, one_mul, map_zero, sub_zero, hD.nq_zero, zero_add]
    refine le_mul_of_one_le_left hH0 (Real.one_le_exp ?_)
    exact div_nonneg (mul_nonneg hc0 (Real.rpow_nonneg hR.le _)) h1θ.le
  | succ j ih =>
    intro hj1
    have hpow : θ ^ (j + 1) * R = θ * (θ ^ j * R) := by rw [pow_succ]; ring
    have hrj0 : 0 < θ ^ j * R := by positivity
    have hrjR : θ ^ j * R ≤ R := by
      have : θ ^ j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
      calc θ ^ j * R ≤ 1 * R := mul_le_mul_of_nonneg_right this hR.le
        _ = R := one_mul R
    have hr : X ≤ θ * (θ ^ j * R) := by rwa [hpow] at hj1
    have hj : X ≤ θ ^ j * R := by
      have : θ * (θ ^ j * R) ≤ θ ^ j * R := mul_le_of_le_one_left hrj0.le hθ1.le
      linarith only [this, hr]
    obtain ⟨ℓ₀, q, hq⟩ := ih hj
    have hu' : Hm (θ ^ j * R) (u - L ℓ₀) := hD.harm_anti R _ _ hrjR (hD.harm_sub R u ℓ₀ hu)
    obtain ⟨ℓ₁, q₁, hstep⟩ := orderOneEndpoint_step hD hX hA hCL hθ hθ2 hAθ hε hε1 hεB
      hr hrjR hu' q
    refine ⟨ℓ₁, q₁, ?_⟩
    rw [hpow]
    set r := θ ^ j * R with hrdef
    set v := θ * r with hv
    have hv0 : 0 < v := by positivity
    have hρ : r ^ (-δ) = θ ^ δ * v ^ (-δ) := by
      rw [hv, Real.mul_rpow hθ.le hrj0.le, Real.rpow_neg hθ.le, ← mul_assoc,
        mul_inv_cancel₀ hθδ0.ne', one_mul]
    have hvρ : 0 ≤ v ^ (-δ) := Real.rpow_nonneg hv0.le _
    set E := Real.exp (c * r ^ (-δ) / (1 - θ ^ δ)) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have h1 : 0 ≤ 1 + c * v ^ (-δ) := by positivity
    calc nq q₁ + K * (N v (u - L ℓ₁ - κ q₁) / v ^ 2)
        ≤ (1 + c * v ^ (-δ)) * (nq q + K * (N r (u - L ℓ₀ - κ q) / r ^ 2)) := hstep
      _ ≤ (1 + c * v ^ (-δ)) * (E * (K * (N R u / R ^ 2))) :=
          mul_le_mul_of_nonneg_left hq h1
      _ ≤ Real.exp (c * v ^ (-δ)) * (E * (K * (N R u / R ^ 2))) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hE0 hH0)
          linarith [Real.add_one_le_exp (c * v ^ (-δ))]
      _ = Real.exp (c * v ^ (-δ) / (1 - θ ^ δ)) * (K * (N R u / R ^ 2)) := by
          rw [← mul_assoc, hE, ← Real.exp_add, hρ]
          congr 2
          field_simp
          ring

/-- **The fit at each radius.** For every `t ∈ [X, R / 2]` some lifted affine function `L ℓ₀`
satisfies `N t (u - L ℓ₀) ≤ C (t / R) ^ 2 N R u`. -/
theorem orderOneEndpoint_fit
    (hD : OrderOneEndpointData N P₂ ι L κ sz nq Hm X R A δ CV γ cU CL ε)
    (hX1 : 1 ≤ X) (hA : 0 ≤ A) (hCV : 0 ≤ CV) (hγ : 0 ≤ γ) (hcU : 0 ≤ cU) (hCL : 0 ≤ CL)
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hAθ : A * θ ≤ 1 / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεB : ε * endpointSlopeConst A CV γ CL θ ≤ 1 / 4)
    (hXR : 2 * X ≤ R) {u : F} (hu : Hm R u) {t : ℝ} (ht : X ≤ t) (htR : t ≤ R / 2) :
    ∃ ℓ₀ : V, N t (u - L ℓ₀) ≤ endpointFitConst A δ CV γ cU CL θ * (t / R) ^ 2 * N R u := by
  have hX : 0 < X := by linarith
  have hR0 : 0 < R := by linarith
  have ht0 : 0 < t := by linarith
  have hθ1 : θ < 1 := by linarith
  set K := endpointWeight A CV γ CL θ with hK
  set c := endpointRate A CV γ cU CL θ with hc
  have hc0 : 0 ≤ c := endpointRate_nonneg hA hCL hθ
  have hK1 : 1 ≤ K := one_le_endpointWeight _ _ _ _ _
  have hθδ : θ ^ δ < 1 := Real.rpow_lt_one hθ.le hθ1 hδ
  have h1θ : 0 < 1 - θ ^ δ := by linarith
  have hex : ∃ n : ℕ, θ ^ n * R < t := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos ht0 hR0) hθ1
    exact ⟨n, by rwa [lt_div_iff₀ hR0] at hn⟩
  classical
  have hnspec : θ ^ Nat.find hex * R < t := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hnspec
    linarith
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjlt : j < Nat.find hex := by omega
  have htj' : ¬ θ ^ j * R < t := Nat.find_min hex hjlt
  have htj : t ≤ θ ^ j * R := not_lt.1 htj'
  rw [hj, pow_succ] at hnspec
  obtain ⟨r, hrdef⟩ : ∃ r, r = θ ^ j * R := ⟨_, rfl⟩
  rw [← hrdef] at htj
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hθr : θ * r < t := by
    calc θ * r = θ ^ j * θ * R := by rw [hrdef]; ring
      _ < t := hnspec
  have hXr : X ≤ r := ht.trans htj
  have hr1 : 1 ≤ r := hX1.trans hXr
  have hrR : r ≤ R := by
    have : θ ^ j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
    calc r = θ ^ j * R := hrdef
      _ ≤ 1 * R := mul_le_mul_of_nonneg_right this hR0.le
      _ = R := one_mul R
  obtain ⟨ℓ₀, q, hq⟩ := orderOneEndpoint_iterate hD hX hA hCL hδ hθ hθ2 hAθ hε hε1 hεB
    hR0 hu j (hrdef ▸ hXr)
  rw [← hrdef] at hq
  refine ⟨ℓ₀, ?_⟩
  set h := u - L ℓ₀ - κ q with hh
  set e := N r h / r ^ 2 with he
  set b := nq q with hb
  have hb0 : 0 ≤ b := hD.nq_nonneg q
  have he0 : 0 ≤ e := div_nonneg (apply_nonneg _ _) (by positivity)
  have hNh : N r h = r ^ 2 * e := by rw [he]; field_simp
  -- the exponential factor is bounded independently of `j`
  set E₀ := Real.exp (c / (1 - θ ^ δ)) with hE₀
  have hEj : Real.exp (c * r ^ (-δ) / (1 - θ ^ δ)) ≤ E₀ := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ h1θ.le
    have : r ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
    exact mul_le_of_le_one_right hc0 this
  have hH0 : 0 ≤ K * (N R u / R ^ 2) :=
    mul_nonneg (by linarith) (div_nonneg (apply_nonneg _ _) (by positivity))
  have hH : b + K * e ≤ E₀ * (K * (N R u / R ^ 2)) :=
    hq.trans (mul_le_mul_of_nonneg_right hEj hH0)
  -- the norm at the radius `t`
  have hrt : r / t ≤ 1 / θ := by
    rw [div_le_div_iff₀ ht0 hθ]; linarith
  have hθγ : (r / t) ^ γ ≤ (1 / θ) ^ γ :=
    Real.rpow_le_rpow (div_nonneg hr0.le ht0.le) hrt hγ
  have hθγ0 : 0 ≤ (1 / θ) ^ γ := Real.rpow_nonneg (by positivity) _
  have hmono := hD.mono h t r ht htj hrR
  have hquad := hD.quad_le t ht (by linarith) q
  have htr2 : t ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ht0.le htj 2
  have hr2 : r ^ 2 ≤ t ^ 2 / θ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (θ * r) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) hθr.le 2
    calc r ^ 2 * θ ^ 2 = (θ * r) ^ 2 := by ring
      _ ≤ t ^ 2 := h1
  have hsplit : N t (u - L ℓ₀) ≤ N t h + N t (κ q) := by
    calc N t (u - L ℓ₀) = N t (h + κ q) := by rw [hh, sub_add_cancel]
      _ ≤ N t h + N t (κ q) := map_add_le_add _ _ _
  have hNth : N t h ≤ CV * (1 / θ) ^ γ * (r ^ 2 * e) := by
    rw [← hNh]
    calc N t h ≤ CV * (r / t) ^ γ * N r h := hmono
      _ ≤ CV * (1 / θ) ^ γ * N r h :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθγ hCV) (apply_nonneg _ _)
  have hKe : e ≤ b + K * e := by
    have := le_mul_of_one_le_left he0 hK1
    linarith only [this, hb0]
  have hbK : b ≤ b + K * e := by
    have : 0 ≤ K * e := mul_nonneg (by linarith only [hK1]) he0
    linarith only [this]
  have hsum : N t (u - L ℓ₀) ≤ r ^ 2 * ((CV * (1 / θ) ^ γ + cU) * (b + K * e)) := by
    have h1 : CV * (1 / θ) ^ γ * (r ^ 2 * e) ≤ r ^ 2 * (CV * (1 / θ) ^ γ * (b + K * e)) := by
      calc CV * (1 / θ) ^ γ * (r ^ 2 * e) = r ^ 2 * (CV * (1 / θ) ^ γ * e) := by ring
        _ ≤ r ^ 2 * (CV * (1 / θ) ^ γ * (b + K * e)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKe (mul_nonneg hCV hθγ0))
              (by positivity)
    have h2 : cU * t ^ 2 * b ≤ r ^ 2 * (cU * (b + K * e)) := by
      have h3 : cU * t ^ 2 * b ≤ cU * r ^ 2 * b :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htr2 hcU) hb0
      have h4 : cU * r ^ 2 * b ≤ cU * r ^ 2 * (b + K * e) :=
        mul_le_mul_of_nonneg_left hbK (by positivity)
      calc cU * t ^ 2 * b ≤ cU * r ^ 2 * (b + K * e) := h3.trans h4
        _ = r ^ 2 * (cU * (b + K * e)) := by ring
    calc N t (u - L ℓ₀) ≤ N t h + N t (κ q) := hsplit
      _ ≤ CV * (1 / θ) ^ γ * (r ^ 2 * e) + cU * t ^ 2 * b := add_le_add hNth hquad
      _ ≤ r ^ 2 * (CV * (1 / θ) ^ γ * (b + K * e)) + r ^ 2 * (cU * (b + K * e)) :=
          add_le_add h1 h2
      _ = r ^ 2 * ((CV * (1 / θ) ^ γ + cU) * (b + K * e)) := by ring
  have hC0 : 0 ≤ CV * (1 / θ) ^ γ + cU := by positivity
  calc N t (u - L ℓ₀) ≤ r ^ 2 * ((CV * (1 / θ) ^ γ + cU) * (b + K * e)) := hsum
    _ ≤ t ^ 2 / θ ^ 2 * ((CV * (1 / θ) ^ γ + cU) * (E₀ * (K * (N R u / R ^ 2)))) := by
        apply mul_le_mul hr2 (mul_le_mul_of_nonneg_left hH hC0)
          (mul_nonneg hC0 (by linarith)) (by positivity)
    _ = endpointFitConst A δ CV γ cU CL θ * (t / R) ^ 2 * N R u := by
        have hfc : endpointFitConst A δ CV γ cU CL θ =
            (CV * (1 / θ) ^ γ + cU) * E₀ * K / θ ^ 2 := rfl
        rw [hfc, div_pow]
        ring

/-- **One lifted affine function at all radii.** Under `OrderOneEndpointData`, with `θ` and `ε`
small, for `R ≥ 2 X` and `u` harmonic in `B_R` there is one `ℓ` with
`N t (u - L ℓ) ≤ C (t / R) ^ 2 N R u` for every `t ∈ [X, R / 2]`. -/
theorem exists_forall_le_of_orderOneEndpoint
    (hD : OrderOneEndpointData N P₂ ι L κ sz nq Hm X R A δ CV γ cU CL ε)
    (hX1 : 1 ≤ X) (hA : 0 ≤ A) (hCV : 0 ≤ CV) (hγ : 0 ≤ γ) (hcU₀ : 0 < cU) (hCL : 0 ≤ CL)
    (hδ : 0 < δ) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hAθ : A * θ ≤ 1 / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hεB : ε * endpointSlopeConst A CV γ CL θ ≤ 1 / 4)
    (hCLε : CL * ε ≤ 1 / 2) (hXR : 2 * X ≤ R) {u : F} (hu : Hm R u) :
    ∃ ℓ : V, ∀ t : ℝ, X ≤ t → t ≤ R / 2 →
      N t (u - L ℓ) ≤ singlePolynomialConst CV (2 * CL * (1 + ε)) γ 1 *
        endpointFitConst A δ CV γ cU CL θ * (t / R) ^ 2 * N R u := by
  have hcU : 0 ≤ cU := hcU₀.le
  have hX : 0 < X := by linarith
  have hR : 0 < R := by linarith
  have hXR2 : X ≤ R / 2 := by linarith
  set Cf := endpointFitConst A δ CV γ cU CL θ with hCf
  have hCfpos : 0 < Cf := by
    rw [hCf, endpointFitConst]
    have := one_le_endpointWeight A CV γ CL θ
    have : 0 ≤ (1 / θ) ^ γ := Real.rpow_nonneg (by positivity) _
    have : 0 < CV * (1 / θ) ^ γ + cU := by positivity
    have : 0 < endpointWeight A CV γ CL θ := by linarith
    positivity
  rcases (apply_nonneg (N R) u).eq_or_lt with hzero | hpos
  · refine ⟨0, fun t ht htR => ?_⟩
    have h := hD.mono u t R ht (by linarith) le_rfl
    rw [map_zero, sub_zero]
    rw [← hzero, mul_zero] at h
    rw [← hzero, mul_zero]
    exact h
  have hmono : RadiusMonotone N X (R / 2) CV γ := fun f s t hs hst ht =>
    hD.mono f s t hs hst (by linarith)
  have hgrowth : PolynomialGrowth N L.range 1 X (R / 2) (2 * CL * (1 + ε)) := by
    intro w hw ρ r hρ hρr hr
    obtain ⟨ℓ, rfl⟩ := AddMonoidHom.mem_range.1 hw
    have hρ0 : 0 < ρ := hX.trans_le hρ
    have hrR : r ≤ R := by linarith
    have hρR : ρ ≤ R := hρr.trans hrR
    have hszρ := hD.sz_nonneg ρ ℓ hρ
    have hup : N r (L ℓ) ≤ (1 + ε) * sz r ℓ := by
      calc N r (L ℓ) = N r (ι ℓ + (L ℓ - ι ℓ)) := by rw [add_sub_cancel]
        _ ≤ N r (ι ℓ) + N r (L ℓ - ι ℓ) := map_add_le_add _ _ _
        _ ≤ sz r ℓ + ε * sz r ℓ :=
            add_le_add (hD.affine_le r (hρ.trans hρr) hrR ℓ)
              (hD.lift_le r (hρ.trans hρr) hrR ℓ)
        _ = (1 + ε) * sz r ℓ := by ring
    have hsz := hD.sz_le ρ r hρ hρr hrR ℓ
    have hlow : sz ρ ℓ ≤ CL * N ρ (ι ℓ) := by
      have := hD.le_poly ρ hρ hρR ℓ 0
      rwa [map_zero, add_zero, hD.nq_zero, mul_zero, add_zero] at this
    have hιL : N ρ (ι ℓ) ≤ N ρ (L ℓ) + ε * sz ρ ℓ := by
      calc N ρ (ι ℓ) = N ρ (L ℓ + -(L ℓ - ι ℓ)) := by congr 1; abel
        _ ≤ N ρ (L ℓ) + N ρ (-(L ℓ - ι ℓ)) := map_add_le_add _ _ _
        _ = N ρ (L ℓ) + N ρ (L ℓ - ι ℓ) := by rw [map_neg_eq_map]
        _ ≤ N ρ (L ℓ) + ε * sz ρ ℓ := add_le_add le_rfl (hD.lift_le ρ hρ hρR ℓ)
    have hsz2 : sz ρ ℓ ≤ 2 * CL * N ρ (L ℓ) := by
      have h1 : CL * N ρ (ι ℓ) ≤ CL * (N ρ (L ℓ) + ε * sz ρ ℓ) :=
        mul_le_mul_of_nonneg_left hιL hCL
      have h2 : CL * ε * sz ρ ℓ ≤ 1 / 2 * sz ρ ℓ := mul_le_mul_of_nonneg_right hCLε hszρ
      linarith only [hlow, h1, h2]
    have hrρ : 0 ≤ r / ρ := div_nonneg (hρ0.le.trans hρr) hρ0.le
    calc N r (L ℓ) ≤ (1 + ε) * sz r ℓ := hup
      _ ≤ (1 + ε) * (r / ρ * sz ρ ℓ) := mul_le_mul_of_nonneg_left hsz (by linarith)
      _ ≤ (1 + ε) * (r / ρ * (2 * CL * N ρ (L ℓ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsz2 hrρ) (by linarith)
      _ = 2 * CL * (1 + ε) * (r / ρ) ^ 1 * N ρ (L ℓ) := by ring
  have hfit : ∀ ρ : ℝ, X ≤ ρ → ρ ≤ R / 2 →
      ballExcess N L.range ρ u ≤ Cf * N R u * (ρ / R) ^ (1 + 1) := by
    intro ρ hρ hρR
    obtain ⟨ℓ₀, hℓ₀⟩ := orderOneEndpoint_fit hD hX1 hA hCV hγ hcU hCL hδ hθ hθ2 hAθ hε hε1 hεB
      hXR hu hρ hρR
    calc ballExcess N L.range ρ u ≤ N ρ (u - L ℓ₀) :=
          ballExcess_le N L.range (AddMonoidHom.mem_range.2 ⟨ℓ₀, rfl⟩)
      _ ≤ Cf * (ρ / R) ^ 2 * N R u := hℓ₀
      _ = Cf * N R u * (ρ / R) ^ (1 + 1) := by ring
  obtain ⟨φ, hφ, hall⟩ := exists_mem_forall_le_of_ballExcess_le N L.range (k := 1) hX hXR2 hR
    (mul_pos hCfpos hpos) hCV (by positivity) hγ hmono hgrowth u hfit
  obtain ⟨ℓ, rfl⟩ := AddMonoidHom.mem_range.1 hφ
  refine ⟨ℓ, fun t ht htR => ?_⟩
  calc N t (u - L ℓ) ≤ _ := hall t ht htR
    _ = _ := by ring

end

end Rigidity.Proofs.Regularity
