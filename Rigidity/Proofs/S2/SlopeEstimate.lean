import Rigidity.Proofs.S2.AffineMajorization
import LatticeProb.Prob.Percolation.LatticeAnnularSup

/-!
# Proposition 2.6, step:2.6-expansion: the slope estimate

`SlopeEstimateStep` (paper L601-640, proof step `step:2.6-expansion`): if the regularity
estimate at the scale `R = |x - y| / 2` gives
`‖u - ∑ᵢ ξᵢ ℓᵢ - a‖_{L̲²(B_r(x))} ≤ B r² R^{-d}` for `r ∈ [X, R/2]`, with
`u = G(·, y) - K - Ḡ(x - y)`, then under (H1), (H3), (H4) the slope satisfies
`|ξ - ∇Ḡ(x - y)|₁ ≤ A₁ R^{1/2 - d + δ/4}` once `R ≥ R₁ ∨ X²`.

Proof, at the radius `r = R^{1/2}`. Write `ζ = ∇Ḡ(x - y) - ξ` and `χᵢ = ℓᵢ - xᵢ`. On `B_r(x)`,
`u - ∑ᵢ ξᵢ ℓᵢ - a = b' + ζ · (· - x) + Err` with `b' = -(a + ∑ᵢ ξᵢ ℓᵢ(x))` and
`Err(z) = [G(z, y) - Ḡ(z - y) - K] + [Ḡ(z - y) - Ḡ(x - y) - ∇Ḡ(x - y) · (z - x)]
  - ∑ᵢ ξᵢ (χᵢ(z) - χᵢ(x))`, so that by (H1), the Taylor bound of `ContinuumGreenStep` and (H3),
`|Err| ≤ Ch R^{1-d+δ/4} + Cg r² R^{-d} + Cc r^{δ/4} |ξ|₁`. The affine majorization
(`AffineMajorizationStep`, under (H4)) and the triangle inequality give
`c₁ r |ζ|₁ ≤ B r² R^{-d} + sup |Err|`; with `|ξ|₁ ≤ |ζ|₁ + d Cg R^{1-d}` and
`Cc r^{δ/4} ≤ c₁ r / 2` for `r` large, the term `Cc r^{δ/4} |ζ|₁` is absorbed.

(H3) is applied with an open edge `(x, x')` of the cluster at `x`, which exists because (H4) puts
at least two vertices of the cluster in `B_{r/100}(x)` (`exists_componentGraph_adj`).
-/

namespace Rigidity.Proofs.S2

open LatticeProb.Percolation Rigidity.Section2 Rigidity.Steps.S2

variable {d : ℕ} {ω : Configuration d}

/-- A continuous linear form on `ℝ^d` in coordinates. -/
theorem clm_apply_eq_sum (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    L u = ∑ i, L (EuclideanSpace.single i 1) * u i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.sum_repr u]
  simp [map_sum, map_smul, mul_comm]

/-- A vertex of a component whose ball contains two vertices of the component has a neighbour. -/
theorem exists_componentGraph_adj {C : OpenComponent ω} (x : C) {s : Finset C}
    (hs : 1 < s.card) : ∃ x' : C, (componentGraph C).Adj x x' := by
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_ne hs x
  obtain ⟨p⟩ := C.connected_toSimpleGraph.preconnected x u
  have hp : ¬ p.Nil := fun h => hu h.eq.symm
  exact ⟨p.snd, SimpleGraph.Walk.adj_snd hp⟩

/-- Under (H4) at a radius `r` with `c r^d ≥ 2`, the vertex `x` has a neighbour in the cluster. -/
theorem exists_componentGraph_adj_of_denseAt {C : OpenComponent ω} {x : C} {c X r : ℝ}
    (hD : DenseAt C x.val c X) (hXr : X ≤ r) (hr : 0 ≤ r) (h2 : 2 ≤ c * r ^ d) :
    ∃ x' : C, (componentGraph C).Adj x x' := by
  have hcard := hD r hXr x.val (by rw [dist_self]; exact hr)
  have h1 : (1 : ℝ) < ((componentEuclideanBall C x.val (r / 100)).card : ℝ) := by linarith
  exact exists_componentGraph_adj x (s := componentEuclideanBall C x.val (r / 100))
    (by exact_mod_cast h1)

/-- (H3) along the coordinate corrected planes: the oscillation of `χᵢ = ℓᵢ - xᵢ` between `z` and
`x` in `B_r(x)` is at most `Cc r^η`, given an open edge `(x, x')` inside `B_r(x)`. -/
theorem abs_corrector_sub_le {C : OpenComponent ω} {ℓ : Fin d → C → ℝ} {x x' z : C}
    {Cc η X r : ℝ} (hℓ : ∀ i, IsCorrectedPlane C (Pi.single i 1) (ℓ i))
    (hcorr : CorrectorBoundAt C x.val Cc η X) (hXr : X ≤ r) (hr0 : 0 < r)
    (hadj : (componentGraph C).Adj x x')
    (hx'r : ‖latticeEuclideanEmbedding x'.val - latticeEuclideanEmbedding x.val‖ < r)
    (hz : ‖latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding x.val‖ < r) (i : Fin d) :
    |(ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ))| ≤ Cc * r ^ η := by
  have h := hcorr (Pi.single i 1) (ℓ i) (hℓ i) r hXr z x x x' hz (by simpa using hr0)
    (by simpa using hr0) hx'r hadj
  have e1 : ∀ u : C, ∑ j, (Pi.single i (1 : ℝ) : Fin d → ℝ) j * (u.val j : ℝ) = u.val i := by
    intro u; simp [Pi.single_apply]
  have e2 : ∑ j, |(Pi.single i (1 : ℝ) : Fin d → ℝ) j| = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp
  simp only [e1, e2, mul_one] at h
  have := abs_nonneg ((ℓ i x - (x.val i : ℝ)) - (ℓ i x' - (x'.val i : ℝ)))
  linarith

/-- The pointwise error of the affine approximation of `u - ∑ᵢ ξᵢ ℓᵢ - a` on `B_r(x)`:
(H1), the Taylor bound of `Ḡ` and the oscillation of the correctors. -/
theorem abs_slope_error_le (hd : 2 ≤ d) (κ : {a : ℝ // 0 < a}) {C : OpenComponent ω}
    {y x z : C} {g : C → ℝ} {K a : ℝ} {ℓ : Fin d → C → ℝ} {ξ : Fin d → ℝ}
    {Ch Cg Cc δ X R r s : ℝ} {w : EuclideanSpace ℝ (Fin d)}
    (hw : w = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val)
    (hclose : GreenCloseAt hd κ C y g K Ch (δ / 4) X)
    (hTaylor : ∀ w' : EuclideanSpace ℝ (Fin d), 2 * ‖w'‖ ≤ ‖w‖ →
      |greenBar d hd κ (w + w') - greenBar d hd κ w - fderiv ℝ (greenBar d hd κ) w w'| ≤
        Cg * ‖w'‖ ^ 2 * ‖w‖ ^ (-(d : ℝ)))
    (hwR : ‖w‖ = 2 * R) (hR0 : 0 < R) (hrR : r ≤ R / 2) (hXR : X ≤ R)
    (hδ1 : δ ≤ 1) (hCh : 0 < Ch) (hCg : 0 < Cg)
    (hz : ‖latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding x.val‖ < r)
    (hchi : ∀ i, |(ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ))| ≤ Cc * s) :
    |(g z - K - greenBar d hd κ w - ∑ i, ξ i * ℓ i z - a) -
        (-(a + ∑ i, ξ i * ℓ i x) +
          ∑ i, (fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i) *
            ((z.val i : ℝ) - (x.val i : ℝ)))| ≤
      Ch * R ^ (δ / 4) * R * (R ^ d)⁻¹ + Cg * r ^ 2 * (R ^ d)⁻¹ + Cc * s * ∑ i, |ξ i| := by
  set Dg := fderiv ℝ (greenBar d hd κ) w with hDg
  set w' := latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding x.val with hw'
  set v := latticeEuclideanEmbedding z.val - latticeEuclideanEmbedding y.val with hv
  have hvw : w + w' = v := by rw [hw, hw', hv]; abel
  have hvR : R ≤ ‖v‖ := by
    have := norm_sub_norm_le w (-w')
    rw [sub_neg_eq_add, hvw, norm_neg] at this
    linarith
  have hv0 : v ≠ 0 := norm_pos_iff.mp (by linarith)
  -- (H1)
  have hH := hclose z ⟨v, hv0⟩ rfl (by simp only; linarith)
  have hH' : Ch / (Real.rpow ‖v‖ (1 - δ / 4) * ‖v‖ ^ (d - 2)) ≤
      Ch * R ^ (δ / 4) * R * (R ^ d)⁻¹ := by
    have hden : Real.rpow R (1 - δ / 4) * R ^ (d - 2) ≤
        Real.rpow ‖v‖ (1 - δ / 4) * ‖v‖ ^ (d - 2) :=
      mul_le_mul (Real.rpow_le_rpow hR0.le hvR (by linarith))
        (pow_le_pow_left₀ hR0.le hvR _) (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
    have hRt : Real.rpow R (1 - δ / 4) * R ^ (δ / 4) = R := by
      rw [Real.rpow_eq_pow, ← Real.rpow_add hR0]; simp
    have hRd : R ^ d = R ^ (d - 2) * R ^ 2 := by rw [← pow_add]; congr 1; omega
    have hpos : 0 < Real.rpow R (1 - δ / 4) := Real.rpow_pos_of_pos hR0 _
    calc Ch / (Real.rpow ‖v‖ (1 - δ / 4) * ‖v‖ ^ (d - 2))
        ≤ Ch / (Real.rpow R (1 - δ / 4) * R ^ (d - 2)) :=
          div_le_div_of_nonneg_left hCh.le (mul_pos hpos (pow_pos hR0 _)) hden
      _ = Ch * R ^ (δ / 4) * R * (R ^ d)⁻¹ := by
          have ht0 : R ^ (δ / 4) ≠ 0 := (Real.rpow_pos_of_pos hR0 _).ne'
          have hR' : R ≠ 0 := hR0.ne'
          have hRt' : Real.rpow R (1 - δ / 4) = R / R ^ (δ / 4) := by
            rw [eq_div_iff ht0]; exact hRt
          rw [hRt', hRd]
          field_simp
  -- the Taylor bound
  have hTay := hTaylor w' (by rw [hwR]; linarith)
  have hTay' : Cg * ‖w'‖ ^ 2 * ‖w‖ ^ (-(d : ℝ)) ≤ Cg * r ^ 2 * (R ^ d)⁻¹ := by
    have hwpos : 0 < ‖w‖ := by rw [hwR]; linarith
    rw [Real.rpow_neg hwpos.le, Real.rpow_natCast]
    have h1 : ‖w'‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz.le 2
    have h2 : (‖w‖ ^ d)⁻¹ ≤ (R ^ d)⁻¹ := inv_anti₀ (by positivity)
      (pow_le_pow_left₀ hR0.le (by rw [hwR]; linarith) d)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hCg.le) h2 (by positivity) (by positivity)
  have hDgw' : Dg w' = ∑ i, Dg (EuclideanSpace.single i 1) * ((z.val i : ℝ) - (x.val i : ℝ)) := by
    rw [clm_apply_eq_sum]; rfl
  have hGv : greenBar d hd κ (w + w') = continuumGreen d hd κ ⟨v, hv0⟩ := by
    rw [hvw]; exact dif_pos hv0
  -- the corrector term
  have hcorrsum : |∑ i, ξ i * ((ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ)))| ≤
      Cc * s * ∑ i, |ξ i| := by
    calc |∑ i, ξ i * ((ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ)))|
        ≤ ∑ i, |ξ i * ((ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |ξ i| * (Cc * s) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hchi i) (abs_nonneg _)
      _ = Cc * s * ∑ i, |ξ i| := by rw [← Finset.sum_mul]; ring
  -- the identity `E - F = H + T - corrector`
  have hid : (g z - K - greenBar d hd κ w - ∑ i, ξ i * ℓ i z - a) -
      (-(a + ∑ i, ξ i * ℓ i x) +
        ∑ i, (Dg (EuclideanSpace.single i 1) - ξ i) * ((z.val i : ℝ) - (x.val i : ℝ))) =
      (g z - continuumGreen d hd κ ⟨v, hv0⟩ - K) +
        (greenBar d hd κ (w + w') - greenBar d hd κ w - Dg w') -
        ∑ i, ξ i * ((ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ))) := by
    rw [hGv, hDgw']
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  have habs3 := abs_sub ((g z - continuumGreen d hd κ ⟨v, hv0⟩ - K) +
    (greenBar d hd κ (w + w') - greenBar d hd κ w - Dg w'))
    (∑ i, ξ i * ((ℓ i z - (z.val i : ℝ)) - (ℓ i x - (x.val i : ℝ))))
  have habs2 := abs_add_le (g z - continuumGreen d hd κ ⟨v, hv0⟩ - K)
    (greenBar d hd κ (w + w') - greenBar d hd κ w - Dg w')
  linarith [hH.trans hH', hTay.trans hTay']

/-- Absorption of the corrector term `Cc r^{δ/4}`: it is at most `c₁ r / 2` once
`r ≥ (2 Cc / c₁)²`. -/
theorem corrector_absorb {Cc c₁ r δ : ℝ} (hCc : 0 < Cc) (hc₁ : 0 < c₁) (hr1 : 1 ≤ r)
    (hδ1 : δ ≤ 1) (hrT : (2 * Cc / c₁) ^ 2 ≤ r) :
    Cc * r ^ (δ / 4) ≤ c₁ / 2 * r := by
  have hr0 : 0 < r := by linarith
  have hs_sqrt : r ^ (δ / 4) ≤ Real.sqrt r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hTs : 2 * Cc / c₁ ≤ Real.sqrt r := (Real.le_sqrt (by positivity) hr0.le).mpr hrT
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  have hCcT : Cc = c₁ / 2 * (2 * Cc / c₁) := by field_simp
  calc Cc * r ^ (δ / 4) ≤ Cc * Real.sqrt r := mul_le_mul_of_nonneg_left hs_sqrt hCc.le
    _ = c₁ / 2 * ((2 * Cc / c₁) * Real.sqrt r) := by rw [← mul_assoc, ← hCcT]
    _ ≤ c₁ / 2 * (Real.sqrt r * Real.sqrt r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTs (Real.sqrt_nonneg _))
          (by positivity)
    _ = c₁ / 2 * r := by rw [hsq]

/-- The final absorption of the slope estimate, as an inequality between reals. -/
theorem slope_absorb {c₁ r Z Ξ G B Ch Cg Cc t s W R n : ℝ} (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hZ0 : 0 ≤ Z) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : 1 ≤ t) (hW0 : 0 ≤ W) (hB : 0 ≤ B)
    (hCg : 0 ≤ Cg) (hCc : 0 ≤ Cc) (hn : 0 ≤ n) (hR : R = r ^ 2)
    (h1 : c₁ * r * Z ≤ B * r ^ 2 * W + (Ch * t * R * W + Cg * r ^ 2 * W + Cc * s * Ξ))
    (hΞ : Ξ ≤ Z + G) (hG : G ≤ n * Cg * R * W) (habs : Cc * s ≤ c₁ / 2 * r) :
    Z ≤ 2 / c₁ * (B + Ch + Cg + Cc * n * Cg) * (r * t * W) := by
  subst hR
  have h2 : Cc * s * Ξ ≤ Cc * s * Z + Cc * s * (n * Cg * r ^ 2 * W) := by
    have hΞ' : Ξ ≤ Z + n * Cg * r ^ 2 * W := by linarith
    have := mul_le_mul_of_nonneg_left hΞ' (mul_nonneg hCc hs0)
    linarith
  have h3 : Cc * s * Z ≤ c₁ / 2 * r * Z := mul_le_mul_of_nonneg_right habs hZ0
  have h4 : Cc * s * (n * Cg * r ^ 2 * W) ≤ Cc * t * (n * Cg * r ^ 2 * W) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hst hCc) (by positivity)
  have h5 : B * r ^ 2 * W ≤ B * r ^ 2 * W * t := le_mul_of_one_le_right (by positivity) ht1
  have h6 : Cg * r ^ 2 * W ≤ Cg * r ^ 2 * W * t := le_mul_of_one_le_right (by positivity) ht1
  have hmain : c₁ / 2 * r * Z ≤ c₁ / 2 * r * (2 / c₁ * (B + Ch + Cg + Cc * n * Cg) * (r * t * W)) := by
    have e : c₁ / 2 * r * (2 / c₁ * (B + Ch + Cg + Cc * n * Cg) * (r * t * W)) =
        B * r ^ 2 * W * t + Ch * t * r ^ 2 * W + Cg * r ^ 2 * W * t +
          Cc * t * (n * Cg * r ^ 2 * W) := by
      field_simp
    rw [e]
    linarith
  exact le_of_mul_le_mul_left hmain (by positivity)

/-- step:2.6-expansion, slope: `SlopeEstimateStep`, from the Taylor bound of
`ContinuumGreenStep`. -/
theorem slopeEstimateStep (hd : 2 ≤ d) (hCG : ContinuumGreenStep d hd) :
    SlopeEstimateStep d hd := by
  intro κ δ Ch Cc cD B hδ hδ1 hCh hCc hcD hB
  obtain ⟨Cg, hCg, hG⟩ := hCG κ
  obtain ⟨c₁, R₀, hc₁, hR₀, hAM⟩ := affineMajorizationStep (d := d) cD hcD
  refine ⟨2 / c₁ * (B + Ch + Cg + Cc * d * Cg),
    max 4 (max (R₀ ^ 2) (max (((2 * Cc / c₁) ^ 2) ^ 2) ((2 / cD) ^ 2))), by positivity,
    by positivity, ?_⟩
  intro ω C y g K ℓ x X hX1 hℓ hclose hcorr hdense R hR hR₁ hXR ξ a hreg
  simp only [max_le_iff] at hR₁
  obtain ⟨hR4, hRR₀, hRT, hRc⟩ := hR₁
  have hR0 : 0 < R := by linarith
  -- the radius `r = R^{1/2}`
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt R := ⟨_, rfl⟩
  have hr2 : r ^ 2 = R := by rw [hr]; exact Real.sq_sqrt hR0.le
  have hr_2 : 2 ≤ r := by rw [hr]; exact (Real.le_sqrt (by norm_num) hR0.le).mpr (by linarith)
  have hr0 : 0 < r := by linarith
  have hrR₀ : R₀ ≤ r := by rw [hr]; exact (Real.le_sqrt hR₀.le hR0.le).mpr hRR₀
  have hrT : (2 * Cc / c₁) ^ 2 ≤ r := by
    rw [hr]; exact (Real.le_sqrt (by positivity) hR0.le).mpr hRT
  have hrc : 2 / cD ≤ r := by rw [hr]; exact (Real.le_sqrt (by positivity) hR0.le).mpr hRc
  have hXr : X ≤ r := by rw [hr]; exact (Real.le_sqrt (by linarith) hR0.le).mpr hXR
  have hrR2 : r ≤ R / 2 := by
    have : 2 * r ≤ r * r := mul_le_mul_of_nonneg_right hr_2 hr0.le
    rw [← hr2]; linarith
  -- the pole
  obtain ⟨w, hw⟩ : ∃ w, w = latticeEuclideanEmbedding x.val - latticeEuclideanEmbedding y.val :=
    ⟨_, rfl⟩
  have hwR : ‖w‖ = 2 * R := by rw [hR, hw, ← dist_eq_norm]; ring
  have hw0 : w ≠ 0 := norm_pos_iff.mp (by rw [hwR]; linarith)
  obtain ⟨hDg, hTaylor⟩ := hG w hw0
  have hxy : toReal x.val - toReal y.val = w := by rw [hw]; rfl
  rw [hxy] at hreg ⊢
  -- an open edge at `x`
  obtain ⟨x', hadj⟩ : ∃ x' : C, (componentGraph C).Adj x x' := by
    refine exists_componentGraph_adj_of_denseAt hdense hXr hr0.le ?_
    have hrd : r ≤ r ^ d := le_self_pow₀ (by linarith) (by omega)
    have : 2 ≤ cD * r := by rw [div_le_iff₀ hcD] at hrc; linarith
    nlinarith
  have hx'r : ‖latticeEuclideanEmbedding x'.val - latticeEuclideanEmbedding x.val‖ < r := by
    rw [← dist_eq_norm, dist_embedding_adj (ω := ω)
      (show (openGraph ω).Adj x'.val x.val from hadj.symm)]
    linarith
  -- the gradient of `Ḡ` at `x - y`
  have hgradsum : ∑ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1)| ≤
      d * Cg * R * (R ^ d)⁻¹ := by
    have hle : ∀ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1)| ≤
        ‖fderiv ℝ (greenBar d hd κ) w‖ := fun i => by
      have := (fderiv ℝ (greenBar d hd κ) w).le_opNorm (EuclideanSpace.single i 1)
      rwa [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] at this
    have hw1 : ‖w‖ ^ (1 - (d : ℝ)) ≤ R * (R ^ d)⁻¹ := by
      have hwpos : 0 < ‖w‖ := by rw [hwR]; linarith
      rw [sub_eq_add_neg, Real.rpow_add hwpos, Real.rpow_one, Real.rpow_neg hwpos.le,
        Real.rpow_natCast, hwR, mul_pow, mul_inv]
      have h2d : (2 : ℝ) ≤ 2 ^ d := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2inv : 2 * ((2 : ℝ) ^ d)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]; exact h2d
      have hRW : 0 ≤ R * (R ^ d)⁻¹ := by positivity
      calc 2 * R * (((2 : ℝ) ^ d)⁻¹ * (R ^ d)⁻¹) = (2 * ((2 : ℝ) ^ d)⁻¹) * (R * (R ^ d)⁻¹) := by
            ring
        _ ≤ 1 * (R * (R ^ d)⁻¹) := mul_le_mul_of_nonneg_right h2inv hRW
        _ = R * (R ^ d)⁻¹ := one_mul _
    calc ∑ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1)|
        ≤ ∑ _i : Fin d, ‖fderiv ℝ (greenBar d hd κ) w‖ := Finset.sum_le_sum fun i _ => hle i
      _ = d * ‖fderiv ℝ (greenBar d hd κ) w‖ := by simp
      _ ≤ d * (Cg * ‖w‖ ^ (1 - (d : ℝ))) := mul_le_mul_of_nonneg_left hDg (by positivity)
      _ ≤ d * (Cg * (R * (R ^ d)⁻¹)) := by gcongr
      _ = d * Cg * R * (R ^ d)⁻¹ := by ring
  -- the `L̲²` bounds at the radius `r`
  have hErr := fun (z : C) (hz : z ∈ componentEuclideanBall C x.val r) =>
    abs_slope_error_le hd κ (a := a) (ξ := ξ) (s := r ^ (δ / 4)) hw hclose hTaylor hwR hR0
      hrR2 (by nlinarith) hδ1 hCh hCg
      (by rw [mem_componentEuclideanBall, dist_eq_norm] at hz; exact hz)
      (abs_corrector_sub_le hℓ hcorr hXr hr0 hadj hx'r
        (by rw [mem_componentEuclideanBall, dist_eq_norm] at hz; exact hz))
  obtain ⟨E, hE⟩ : ∃ E : C → ℝ,
      E = fun z => g z - K - greenBar d hd κ w - ∑ i, ξ i * ℓ i z - a := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : C → ℝ, F = fun z => -(a + ∑ i, ξ i * ℓ i x) +
      ∑ i, (fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i) *
        ((z.val i : ℝ) - (x.val i : ℝ)) := ⟨_, rfl⟩
  have hL2E : componentBallL2 C x.val r E ≤ B * r ^ 2 * (R ^ d)⁻¹ := by
    have := hreg r hXr hrR2
    rw [Real.rpow_neg hR0.le, Real.rpow_natCast] at this
    rw [hE]; exact this
  have hL2Err : componentBallL2 C x.val r (fun z => -(E z - F z)) ≤
      Ch * R ^ (δ / 4) * R * (R ^ d)⁻¹ + Cg * r ^ 2 * (R ^ d)⁻¹ +
        Cc * r ^ (δ / 4) * ∑ i, |ξ i| :=
    componentBallL2_le_of_abs_le C x.val r _ (by positivity)
      (fun z hz => by rw [abs_neg, hE, hF]; exact hErr z hz)
  have hL2F : componentBallL2 C x.val r F ≤
      componentBallL2 C x.val r E + componentBallL2 C x.val r (fun z => -(E z - F z)) := by
    have h := componentBallL2_add_le C x.val r E (fun z => -(E z - F z))
    have heq : (fun z => E z + -(E z - F z)) = F := by funext z; ring
    rwa [heq] at h
  have hmaj : c₁ * r * ∑ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i| ≤
      componentBallL2 C x.val r F := by
    rw [hF]
    exact hAM C x.val X r hdense hXr hrR₀ (-(a + ∑ i, ξ i * ℓ i x))
      (fun i => fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i)
  -- the absorption
  have hΞ : ∑ i, |ξ i| ≤ ∑ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i| +
      ∑ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1)| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := abs_sub (fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1))
      (fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i)
    rw [sub_sub_cancel] at this
    linarith
  have hgoal : ∑ i, |ξ i - fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1)| =
      ∑ i, |fderiv ℝ (greenBar d hd κ) w (EuclideanSpace.single i 1) - ξ i| :=
    Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  have hexp : R ^ ((1 : ℝ) / 2 - d + δ / 4) = r * R ^ (δ / 4) * (R ^ d)⁻¹ := by
    rw [show (1 : ℝ) / 2 - d + δ / 4 = 1 / 2 + δ / 4 + -(d : ℝ) by ring,
      Real.rpow_add hR0, Real.rpow_add hR0, ← Real.sqrt_eq_rpow, Real.rpow_neg hR0.le,
      Real.rpow_natCast, hr]
  rw [hgoal, hexp]
  exact slope_absorb hc₁ hr0 (Finset.sum_nonneg fun i _ => abs_nonneg _) (by positivity)
    (Real.rpow_le_rpow hr0.le (by linarith) (by linarith))
    (Real.one_le_rpow (by linarith) (by linarith)) (by positivity) hB.le hCg.le hCc.le
    (Nat.cast_nonneg d) hr2.symm (hmaj.trans (hL2F.trans (add_le_add hL2E hL2Err))) hΞ
    hgradsum (corrector_absorb hCc hc₁ (by linarith) hδ1 hrT)

end Rigidity.Proofs.S2
