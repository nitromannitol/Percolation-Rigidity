import Rigidity.Proofs.Green.DarioGuGaussian
import Rigidity.Proofs.Green.LazyCarneVaropoulos
import Rigidity.Proofs.Corrector.PlanarCorrectorQuantitative
import Rigidity.Proofs.S2.ScaleInputsFaithful

/-!
# The two-scale initial error of Dario–Gu from the sublinearity of the corrector

The fourth item of the base case of §4.3 of Dario–Gu (lines 2556-2562): with the correctors
normalized at `y ∈ 𝒞_∞`,
`h(t, x, y) - θ^{-1} p̄(t, x - y) = θ^{-1} Σ_k D_{e_k} p̄(t, · - y)(x) χ_{e_k}(x)` "can then be
estimated by using the sublinearity of the corrector stated in Proposition 2.12 and the assumption
`√t ≥ M_corr,α(z)` ... the details are left to the reader". The details are the following.

* Proposition 2.12 (`CorrectorQuantitativeInputTwo`) at the centre `y`, applied to the corrected
  plane `x ↦ x_k + χ_{e_k}(x)` on the ball of radius `√t + |x - y| + 2 ≥ M_corr(y)`, gives
  `|χ_{e_k}(x)| ≤ C (√t + |x - y| + 2)^α` (`χ_{e_k}(y) = 0`).
* `|D_{e_k} p̄(t, · - y)(x)| ≤ K t^{-3/2} exp(-|x - y|²/(8σt))` (`abs_gaussianHeat_sub_le`).
* Lattice sums of the Gaussian against `(1 + |x - y|/√t)` give the weighted `L²` norm
  `≤ C t^{-1+α/2}`, the order `t^{-d/4 - 1/2 + α}` of the source.

This proves `DarioGuTwoScaleInitialTwo` from `CorrectorQuantitativeInputTwo`
(`darioGuTwoScaleInitialTwo_of_correctorQuantitative`).
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- The Lipschitz bound of `p̄(τ, ·)` at scale `1`:
`|p̄(τ, u) - p̄(τ, u')| ≤ K τ^{-3/2} exp(-|u'|²/(8στ))` for `|u - u'| ≤ 1`, `τ ≥ 1`. -/
theorem abs_gaussianHeat_sub_le {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 1 ≤ τ)
    {u u' : EuclideanSpace ℝ (Fin 2)} (huu : ‖u - u'‖ ≤ 1) :
    |gaussianHeat σ τ u - gaussianHeat σ τ u'| ≤
      Real.exp (1 / (2 * σ)) * (4 * Real.sqrt σ + 1) / (4 * Real.pi * σ ^ 2) *
        ((τ⁻¹) ^ 2 * Real.sqrt τ) * Real.exp (-(1 / (8 * σ) * ‖u'‖ ^ 2 / τ)) := by
  have hτ0 : 0 < τ := by linarith
  have hsτ : 1 ≤ Real.sqrt τ := by rw [Real.one_le_sqrt]; exact hτ
  set r := ‖u'‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hdu : |‖u‖ - r| ≤ 1 := (abs_norm_sub_norm_le u u').trans huu
  have hu1 : ‖u‖ ≤ r + 1 := by linarith [(abs_le.1 hdu).2]
  have hu2 : r - 1 ≤ ‖u‖ := by linarith [(abs_le.1 hdu).1]
  set a := ‖u‖ ^ 2 / (2 * σ * τ)
  set b := r ^ 2 / (2 * σ * τ)
  have hab : |a - b| ≤ (2 * r + 1) / (2 * σ * τ) := by
    have : a - b = (‖u‖ - r) * (‖u‖ + r) / (2 * σ * τ) := by simp only [a, b]; ring
    rw [this, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * σ * τ),
      abs_of_nonneg (by linarith [norm_nonneg u] : (0 : ℝ) ≤ ‖u‖ + r)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [abs_nonneg (‖u‖ - r), norm_nonneg u]
  have hmin : (r ^ 2 / 2 - 1) / (2 * σ * τ) ≤ min a b := by
    apply le_min
    · apply div_le_div_of_nonneg_right _ (by positivity)
      rcases le_total 1 r with h1 | h1
      · nlinarith [sq_nonneg (r - 2)]
      · nlinarith [norm_nonneg u]
    · apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
  have hexp : Real.exp (-min a b) ≤ Real.exp (1 / (2 * σ)) * Real.exp (-(r ^ 2 / (4 * σ * τ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : 1 / (2 * σ * τ) ≤ 1 / (2 * σ) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : (r ^ 2 / 2 - 1) / (2 * σ * τ) = r ^ 2 / (4 * σ * τ) - 1 / (2 * σ * τ) := by
      field_simp; ring
    linarith
  have hpoly : (2 * r + 1) * Real.exp (-(r ^ 2 / (4 * σ * τ))) ≤
      (4 * Real.sqrt σ + 1) * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
    have h1 := mul_exp_neg_sq_le (c := 4 * σ * τ) (by positivity) hr0
    have h8 : r ^ 2 / (2 * (4 * σ * τ)) = 1 / (8 * σ) * r ^ 2 / τ := by field_simp; ring
    rw [h8, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      at h1
    have h2 : Real.exp (-(r ^ 2 / (4 * σ * τ))) ≤ Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff, show 1 / (8 * σ) * r ^ 2 / τ = r ^ 2 / (8 * σ * τ) by field_simp]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have hE := Real.exp_pos (-(1 / (8 * σ) * r ^ 2 / τ))
    have hss : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg _
    calc (2 * r + 1) * Real.exp (-(r ^ 2 / (4 * σ * τ)))
        = 2 * (r * Real.exp (-(r ^ 2 / (4 * σ * τ)))) + Real.exp (-(r ^ 2 / (4 * σ * τ))) := by
          ring
      _ ≤ 2 * (2 * Real.sqrt σ * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ))) +
          Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by linarith
      _ ≤ (4 * Real.sqrt σ + 1) * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ)) := by
          nlinarith [mul_le_mul_of_nonneg_right hsτ hE.le]
  have hdiff : gaussianHeat σ τ u - gaussianHeat σ τ u' =
      (2 * Real.pi * σ * τ)⁻¹ * (Real.exp (-a) - Real.exp (-b)) := by
    simp only [gaussianHeat, a, b, r]
    ring
  rw [hdiff, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi * σ * τ)⁻¹)]
  have hmain := abs_exp_neg_sub_exp_neg_le a b
  calc (2 * Real.pi * σ * τ)⁻¹ * |Real.exp (-a) - Real.exp (-b)|
      ≤ (2 * Real.pi * σ * τ)⁻¹ * ((2 * r + 1) / (2 * σ * τ) *
          (Real.exp (1 / (2 * σ)) * Real.exp (-(r ^ 2 / (4 * σ * τ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hmain.trans (mul_le_mul hab hexp (Real.exp_pos _).le (by positivity))
    _ = (2 * Real.pi * σ * τ)⁻¹ * (2 * σ * τ)⁻¹ * Real.exp (1 / (2 * σ)) *
          ((2 * r + 1) * Real.exp (-(r ^ 2 / (4 * σ * τ)))) := by ring
    _ ≤ (2 * Real.pi * σ * τ)⁻¹ * (2 * σ * τ)⁻¹ * Real.exp (1 / (2 * σ)) *
          ((4 * Real.sqrt σ + 1) * Real.sqrt τ * Real.exp (-(1 / (8 * σ) * r ^ 2 / τ))) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = _ := by field_simp; ring

theorem latticeDist_add_single (x : Vertex 2) (k : Fin 2) :
    latticeDist (x + Pi.single k 1) x = 1 := by
  rw [← Real.sqrt_one, ← Real.sqrt_sq (latticeDist_nonneg _ _), latticeDist_sq]
  congr 1
  fin_cases k <;> simp

/-- A vertex of an infinite component has a neighbour in it, at Euclidean distance at most `1`. -/
theorem exists_adj_near {ω : Configuration 2} {K : OpenComponent ω} (hK : K.supp.Infinite)
    (y : K) : ∃ y' : K, (componentGraph K).Adj y y' ∧ latticeDist y'.val y.val ≤ 1 := by
  obtain ⟨w, hw, hwy⟩ := hK.nontrivial.exists_ne y.val
  have hreach : (openGraph ω).Reachable y.val w :=
    SimpleGraph.ConnectedComponent.exact
      (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 y.2).trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 hw).symm)
  obtain ⟨q⟩ := hreach
  cases q with
  | nil => exact absurd rfl hwy
  | @cons _ v _ hadj _ =>
    have hv : v ∈ K.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hw ⊢
      rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).1 y.2]
      exact (SimpleGraph.ConnectedComponent.sound ⟨SimpleGraph.Walk.cons hadj .nil⟩).symm
    refine ⟨⟨v, hv⟩, (K.toSimpleGraph_adj y.2 hv).2 hadj, ?_⟩
    have := norm_edz_le_length (SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.nil : (openGraph ω).Walk v v))
    rw [latticeDist_comm]
    have h1 : ‖edz y.val v‖ ≤ 1 := by simpa using this
    exact h1

/-- The `O_s` bound of a square. -/
theorem IsOsBond.sq_of_nonneg {p : unitInterval} {X : Configuration 2 → ℝ} {s θ : ℝ}
    (hθ : 0 < θ) (hX : ∀ ω, 0 ≤ X ω) (h : IsOsBond 2 p X s θ) :
    IsOsBond 2 p (fun ω => X ω ^ 2) (s / 2) (θ ^ 2) := by
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

/-- `(√t + r + 2)^{2α} ≤ 3 t^α (1 + r/√t)` for `t ≥ 1`, `0 ≤ 2α ≤ 1`. -/
theorem rpow_sqrt_add_le {t r a : ℝ} (ht : 1 ≤ t) (hr : 0 ≤ r) (ha0 : 0 ≤ a) (ha1 : 2 * a ≤ 1) :
    (Real.sqrt t + r + 2) ^ (2 * a) ≤ 3 * t ^ a * (1 + r / Real.sqrt t) := by
  have ht0 : 0 < t := by linarith
  have hs1 : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact ht
  have hs0 : 0 < Real.sqrt t := by linarith
  have hb : Real.sqrt t + r + 2 ≤ 3 * Real.sqrt t * (1 + r / Real.sqrt t) := by
    have : 3 * Real.sqrt t * (1 + r / Real.sqrt t) = 3 * Real.sqrt t + 3 * r := by
      field_simp
    rw [this]; linarith
  have h1 : 1 ≤ 1 + r / Real.sqrt t := by have := div_nonneg hr hs0.le; linarith
  calc (Real.sqrt t + r + 2) ^ (2 * a) ≤ (3 * Real.sqrt t * (1 + r / Real.sqrt t)) ^ (2 * a) :=
        Real.rpow_le_rpow (by positivity) hb (by linarith)
    _ = 3 ^ (2 * a) * (Real.sqrt t) ^ (2 * a) * (1 + r / Real.sqrt t) ^ (2 * a) := by
        rw [Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow (by norm_num) hs0.le]
    _ ≤ 3 * t ^ a * (1 + r / Real.sqrt t) := by
        have e1 : (3 : ℝ) ^ (2 * a) ≤ 3 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ha1
          rwa [Real.rpow_one] at this
        have e2 : (Real.sqrt t) ^ (2 * a) = t ^ a := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]; ring_nf
        have e3 : (1 + r / Real.sqrt t) ^ (2 * a) ≤ 1 + r / Real.sqrt t := by
          have := Real.rpow_le_rpow_of_exponent_le h1 ha1
          rwa [Real.rpow_one] at this
        rw [e2]
        have : 0 ≤ t ^ a := by positivity
        have : 0 ≤ (3 : ℝ) ^ (2 * a) := by positivity
        calc 3 ^ (2 * a) * t ^ a * (1 + r / Real.sqrt t) ^ (2 * a)
            ≤ 3 * t ^ a * (1 + r / Real.sqrt t) := by gcongr
          _ = _ := rfl

/-- `Σ_{x ∈ S} (1 + |x - y|/√t) exp(-|x - y|²/(8σt)) ≤ L t`. -/
theorem sum_moment_le {σ : ℝ} (hσ : 0 < σ) : ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, 1 ≤ t →
    ∀ (y : Vertex 2) (S : Finset (Vertex 2)),
      ∑ x ∈ S, (1 + latticeDist x y / Real.sqrt t) *
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) ≤ L * t := by
  refine ⟨4 * Real.exp (1 / (8 * σ) / 2) * (1 + 1 / (1 / (8 * σ))) ^ 2 +
    Real.sqrt (8 * σ) * (4 * Real.exp (1 / (16 * σ) / 2) * (1 + 1 / (1 / (16 * σ))) ^ 2),
    by positivity, fun t ht y S => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hpt : ∀ x : Vertex 2, (1 + latticeDist x y / Real.sqrt t) *
      Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) ≤
      Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) +
        Real.sqrt (8 * σ) * Real.exp (-(1 / (16 * σ) * latticeDist x y ^ 2 / t)) := by
    intro x
    have h := mul_exp_neg_sq_le (c := 8 * σ * t) (by positivity) (latticeDist_nonneg x y)
    have e1 : latticeDist x y ^ 2 / (8 * σ * t) = 1 / (8 * σ) * latticeDist x y ^ 2 / t := by
      field_simp
    have e2 : latticeDist x y ^ 2 / (2 * (8 * σ * t)) = 1 / (16 * σ) * latticeDist x y ^ 2 / t := by
      field_simp; ring
    rw [e1, e2, Real.sqrt_mul (by positivity)] at h
    have hre : (1 + latticeDist x y / Real.sqrt t) *
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) =
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) +
          latticeDist x y * Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) / Real.sqrt t := by
      ring
    have : latticeDist x y * Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) / Real.sqrt t ≤
        Real.sqrt (8 * σ) * Real.exp (-(1 / (16 * σ) * latticeDist x y ^ 2 / t)) := by
      rw [div_le_iff₀ hst]; nlinarith
    rw [hre]
    linarith
  calc ∑ x ∈ S, (1 + latticeDist x y / Real.sqrt t) *
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t))
      ≤ ∑ x ∈ S, (Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) +
        Real.sqrt (8 * σ) * Real.exp (-(1 / (16 * σ) * latticeDist x y ^ 2 / t))) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x ∈ S, Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) +
        Real.sqrt (8 * σ) * ∑ x ∈ S, Real.exp (-(1 / (16 * σ) * latticeDist x y ^ 2 / t)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 * Real.exp (1 / (8 * σ) / 2) * (1 + 1 / (1 / (8 * σ))) ^ 2 * t +
        Real.sqrt (8 * σ) * (4 * Real.exp (1 / (16 * σ) / 2) * (1 + 1 / (1 / (16 * σ))) ^ 2 * t) :=
        add_le_add (sum_exp_neg_sq_div_le (by positivity) ht y S)
          (mul_le_mul_of_nonneg_left (sum_exp_neg_sq_div_le (by positivity) ht y S)
            (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- **The two-scale initial error** (Dario–Gu, lines 2556-2562) from Proposition 2.12. -/
theorem darioGuTwoScaleInitialTwo_of_correctorQuantitative
    (hR5 : CorrectorQuantitativeInputTwo) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ} (hσ : 0 < σ) :
    DarioGuTwoScaleInitialTwo p σ := by
  intro α hα
  set θ := theta 2 p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  set α' := min α (1 / 4) with hα'
  have hα'0 : 0 < α' := lt_min hα (by norm_num)
  have hα'1 : α' ≤ 1 / 4 := min_le_right _ _
  have hα'α : α' ≤ α := min_le_left _ _
  obtain ⟨s, C₅, hs, hC₅, h5⟩ := hR5 p hpc hp1 α' hα'0
  set KG := Real.exp (1 / (2 * σ)) * (4 * Real.sqrt σ + 1) / (4 * Real.pi * σ ^ 2) with hKG
  have hKG0 : 0 < KG := by positivity
  obtain ⟨L₂, hL₂, hmom⟩ := sum_moment_le hσ
  set A := 3 * (2 * θ⁻¹ * KG * C₅) ^ 2 with hA
  set Cb := Real.sqrt (A * L₂) with hCb
  set Cos := max (C₅ ^ 2) (1 * 3 ^ (1 / (s / 2))) * 4 ^ (1 / (s / 2)) with hCos
  set Cf := max (max (16 * σ) Cb) (max Cos 1) with hCf
  have hCf1 : 1 ≤ Cf := (le_max_right _ _).trans (le_max_right _ _)
  have hCf0 : 0 < Cf := by linarith
  refine ⟨Cf, s / 2, hCf0, by positivity, fun y => ?_⟩
  obtain ⟨M₅, hMm, hM0, hMos, hMae⟩ := h5 y
  have hMos2 := IsOsBond.sq_of_nonneg hC₅ hM0 hMos
  have hmeas : Measurable fun ω => max (M₅ ω ^ 2) 1 := (hMm.pow_const 2).max measurable_const
  have hMos' : IsOsBond 2 p (fun ω => max (M₅ ω ^ 2) 1) (s / 2) Cos :=
    Rigidity.Proofs.S2.IsOsBond.max (by positivity) (by positivity) (by positivity)
      (hMm.pow_const 2) measurable_const hMos2
      (Rigidity.Proofs.S2.isOsBond_const one_pos (by positivity))
  refine ⟨fun ω => max (M₅ ω ^ 2) 1, hmeas, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale (by positivity) (by positivity)
      ((le_max_left _ _).trans (le_max_right _ _)) hmeas hMos', ?_⟩
  filter_upwards [hMae] with ω hω
  intro h hy χ hχ t ht
  set K := uniqueInfiniteComponent h with hK
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := by linarith
  have hst : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact ht1
  have hM5t : M₅ ω ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq (hM0 ω)]
    exact Real.sqrt_le_sqrt ((le_max_left _ _).trans ht)
  -- the corrector bound (Proposition 2.12 at the centre `y`)
  have hχb : ∀ x ∈ K.supp, ∀ k : Fin 2,
      |χ k x| ≤ C₅ * (Real.sqrt t + latticeDist x y + 2) ^ α' := by
    intro x hx k
    obtain ⟨b', hadj, hb'd⟩ := exists_adj_near (uniqueInfiniteComponent_infinite h) ⟨x, hx⟩
    have hd0 := latticeDist_nonneg x y
    have hr : M₅ ω ≤ Real.sqrt t + latticeDist x y + 2 := by linarith
    have hb'y : latticeDist b'.val y ≤ latticeDist x y + 1 := by
      have := latticeDist_triangle b'.val x y
      rw [latticeDist_comm x b'.val] at this
      linarith
    have := hω h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 _ hr
      ⟨x, hx⟩ ⟨y, hy⟩ ⟨x, hx⟩ b' (by change latticeDist x y < _; linarith)
      (by change latticeDist y y < _
          rw [show latticeDist y y = 0 by simp [latticeDist]]; linarith)
      (by change latticeDist x y < _; linarith) (by change latticeDist b'.val y < _; linarith) hadj
    simp only [Rigidity.Corrector.sum_single_mul, Rigidity.Corrector.sum_abs_single,
      mul_one] at this
    have e1 : (x k : ℝ) + χ k x - x k - ((y k : ℝ) + χ k y - y k) = χ k x := by
      rw [(hχ k).2]; ring
    rw [e1] at this
    exact le_of_add_le_of_nonneg_left this (abs_nonneg _)
  -- the pointwise bound
  have hpt : ∀ x ∈ K.supp,
      |dgTwoScale σ θ χ t x y - θ⁻¹ * latticeGaussian σ t x y| ≤
        2 * θ⁻¹ * KG * C₅ * ((t⁻¹) ^ 2 * Real.sqrt t) *
          Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
            (Real.sqrt t + latticeDist x y + 2) ^ α' := by
    intro x hx
    have hD : ∀ k : Fin 2, |latticeGaussian σ t (x + Pi.single k 1) y - latticeGaussian σ t x y| ≤
        KG * ((t⁻¹) ^ 2 * Real.sqrt t) * Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) := by
      intro k
      apply abs_gaussianHeat_sub_le hσ ht1
      have : (latticeEuclideanEmbedding (x + Pi.single k 1) - latticeEuclideanEmbedding y) -
          (latticeEuclideanEmbedding x - latticeEuclideanEmbedding y) =
          latticeEuclideanEmbedding (x + Pi.single k 1) - latticeEuclideanEmbedding x := by abel
      rw [this]
      exact (latticeDist_add_single x k).le
    have hdec : dgTwoScale σ θ χ t x y - θ⁻¹ * latticeGaussian σ t x y =
        θ⁻¹ * ∑ k : Fin 2, (latticeGaussian σ t (x + Pi.single k 1) y -
          latticeGaussian σ t x y) * χ k x := by
      simp only [dgTwoScale]; ring
    rw [hdec, abs_mul, abs_of_pos (inv_pos.2 hθ)]
    have hsum : |∑ k : Fin 2, (latticeGaussian σ t (x + Pi.single k 1) y -
        latticeGaussian σ t x y) * χ k x| ≤
        2 * (KG * ((t⁻¹) ^ 2 * Real.sqrt t) * Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
          (C₅ * (Real.sqrt t + latticeDist x y + 2) ^ α')) := by
      rw [Fin.sum_univ_two]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, two_mul]
      exact add_le_add (mul_le_mul (hD 0) (hχb x hx 0) (abs_nonneg _) (by positivity))
        (mul_le_mul (hD 1) (hχb x hx 1) (abs_nonneg _) (by positivity))
    calc θ⁻¹ * |∑ k : Fin 2, (latticeGaussian σ t (x + Pi.single k 1) y -
          latticeGaussian σ t x y) * χ k x|
        ≤ θ⁻¹ * (2 * (KG * ((t⁻¹) ^ 2 * Real.sqrt t) *
          Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
            (C₅ * (Real.sqrt t + latticeDist x y + 2) ^ α'))) :=
          mul_le_mul_of_nonneg_left hsum (inv_pos.2 hθ).le
      _ = _ := by ring
  -- the weighted `L²` bound
  intro S hS
  have hw : ∀ x : Vertex 2, Real.exp (dgExponent Cf t (latticeDist x y)) ≤
      Real.exp (1 / (16 * σ) * latticeDist x y ^ 2 / t) := by
    intro x
    apply Real.exp_le_exp.2
    rw [dgExponent_eq]
    calc dgShape t (latticeDist x y) / Cf ≤ latticeDist x y ^ 2 / t / Cf :=
          div_le_div_of_nonneg_right (dgShape_le_sq ht0 (latticeDist_nonneg x y)) hCf0.le
      _ ≤ latticeDist x y ^ 2 / t / (16 * σ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            ((le_max_left _ _).trans (le_max_left _ _))
      _ = 1 / (16 * σ) * latticeDist x y ^ 2 / t := by field_simp
  have hterm : ∀ x ∈ S, (((fun x => dgTwoScale σ θ χ t x y - θ⁻¹ * latticeGaussian σ t x y) x) *
      Real.exp (dgExponent Cf t (latticeDist x y))) ^ 2 ≤
      A * ((t⁻¹) ^ 4 * t * t ^ α') * ((1 + latticeDist x y / Real.sqrt t) *
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t))) := by
    intro x hx
    have h1 := hpt x (hS x hx)
    have h2 := rpow_sqrt_add_le ht1 (latticeDist_nonneg x y) hα'0.le (by linarith)
    have hEsq : Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) ^ 2 *
        Real.exp (1 / (16 * σ) * latticeDist x y ^ 2 / t) ^ 2 =
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) := by
      rw [← mul_pow, ← Real.exp_add, exp_sq]
      congr 1
      field_simp
      ring
    have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0.le
    have e3 : ((Real.sqrt t + latticeDist x y + 2) ^ α') ^ 2 =
        (Real.sqrt t + latticeDist x y + 2) ^ (2 * α') := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by have := latticeDist_nonneg x y; positivity)]
      push_cast
      ring_nf
    have hB0 : 0 ≤ 2 * θ⁻¹ * KG * C₅ * ((t⁻¹) ^ 2 * Real.sqrt t) *
        Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
          (Real.sqrt t + latticeDist x y + 2) ^ α' := by
      have := latticeDist_nonneg x y; positivity
    calc ((dgTwoScale σ θ χ t x y - θ⁻¹ * latticeGaussian σ t x y) *
          Real.exp (dgExponent Cf t (latticeDist x y))) ^ 2
        = |dgTwoScale σ θ χ t x y - θ⁻¹ * latticeGaussian σ t x y| ^ 2 *
            Real.exp (dgExponent Cf t (latticeDist x y)) ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ (2 * θ⁻¹ * KG * C₅ * ((t⁻¹) ^ 2 * Real.sqrt t) *
            Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
              (Real.sqrt t + latticeDist x y + 2) ^ α') ^ 2 *
            Real.exp (1 / (16 * σ) * latticeDist x y ^ 2 / t) ^ 2 := by
          apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 2)
            (pow_le_pow_left₀ (Real.exp_pos _).le (hw x) 2) (by positivity) (by positivity)
      _ = (2 * θ⁻¹ * KG * C₅) ^ 2 * ((t⁻¹) ^ 4 * (Real.sqrt t) ^ 2) *
            (Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) ^ 2 *
              Real.exp (1 / (16 * σ) * latticeDist x y ^ 2 / t) ^ 2) *
              ((Real.sqrt t + latticeDist x y + 2) ^ α') ^ 2 := by ring
      _ = (2 * θ⁻¹ * KG * C₅) ^ 2 * ((t⁻¹) ^ 4 * t) *
            Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
              (Real.sqrt t + latticeDist x y + 2) ^ (2 * α') := by
          rw [hsq, hEsq, e3]
      _ ≤ (2 * θ⁻¹ * KG * C₅) ^ 2 * ((t⁻¹) ^ 4 * t) *
            Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) *
              (3 * t ^ α' * (1 + latticeDist x y / Real.sqrt t)) := by
          gcongr
      _ = A * ((t⁻¹) ^ 4 * t * t ^ α') * ((1 + latticeDist x y / Real.sqrt t) *
            Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t))) := by rw [hA]; ring
  calc ∑ x ∈ S, (((fun x => dgTwoScale σ θ χ t x y - θ⁻¹ * latticeGaussian σ t x y) x) *
        Real.exp (dgExponent Cf t (latticeDist x y))) ^ 2
      ≤ ∑ x ∈ S, A * ((t⁻¹) ^ 4 * t * t ^ α') * ((1 + latticeDist x y / Real.sqrt t) *
          Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t))) := Finset.sum_le_sum hterm
    _ = A * ((t⁻¹) ^ 4 * t * t ^ α') * ∑ x ∈ S, (1 + latticeDist x y / Real.sqrt t) *
          Real.exp (-(1 / (8 * σ) * latticeDist x y ^ 2 / t)) := by rw [Finset.mul_sum]
    _ ≤ A * ((t⁻¹) ^ 4 * t * t ^ α') * (L₂ * t) :=
        mul_le_mul_of_nonneg_left (hmom t ht1 y S) (by positivity)
    _ = (Cb * t ^ (-(1 : ℝ) + α' / 2)) ^ 2 := by
        have e2 : (t ^ (-(1 : ℝ) + α' / 2)) ^ 2 = (t⁻¹) ^ 2 * t ^ α' := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le,
            show (-(1 : ℝ) + α' / 2) * ((2 : ℕ) : ℝ) = -2 + α' by push_cast; ring,
            Real.rpow_add ht0, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg ht0.le, Real.rpow_natCast, inv_pow]
        rw [mul_pow, e2, hCb, Real.sq_sqrt (by positivity)]
        field_simp
    _ ≤ (Cf * t ^ (-(1 : ℝ) + α)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        apply mul_le_mul ((le_max_right _ _).trans (le_max_left _ _))
          (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by positivity) hCf0.le

end Rigidity.Green
