import Rigidity.Proofs.Green.DarioGuTwoScaleInitial
import Rigidity.Proofs.Green.DarioGuPhiConvolution
import Rigidity.Proofs.Green.DarioGuLevels
import PercolationClusterHomogenization.Proofs.Cluster.OsTailCalculus

/-!
# Lemma 4.2 of Dario–Gu in dimension two

Lemma 4.2 (lines 2159-2163, proof 2166-2225): for `t ≥ 3τ`, `t - τ ≥ T'_NA(y)` and
`√τ ≥ M_corr,α(y)`, `|v(t, x, τ, y)| ≤ C τ^{-1/2 + α/2} Φ_C(t, x - y)`. The proof of the source
uses, for `v(t, x, τ, y) = Σ_z p(t - τ, x, z) (h(τ, z, y) - θ^{-1} p̄(τ, z - y))`:

1. the sublinearity of the corrector (Proposition 2.12, R5), giving
   `|h(τ, z, y) - θ^{-1} p̄(τ, z - y)| ≤ K τ^{-1/2 + α/2} Φ_{16σ}(τ, z - y)` (with the Lipschitz
   bound of `p̄`, item (iv));
2. Theorem 4 at the points `z` with `|z - y| ≤ t - τ + 1` (the time `T'_NA(y)` of (3.52)), item (ii);
3. Proposition 2.15 at the other points, `p(t - τ, x, z) ≤ (t - τ) Φ_C(t - τ, x - z)`, item (iii),
   with `(t - τ) Φ_C(τ, z - y) ≤ C Φ_{2C}(τ, z - y)` there ((4.21) via (4.12));
4. the semigroup property (3.2) of `Φ_C` (`sum_dgPhi_mul_dgPhi_le`), (4.20).

This proves `DarioGuCorrectorLemmaTwo` from Proposition 2.12, Theorem 4 and Proposition 2.15
(`darioGuCorrectorLemmaTwo_of_inputs`).
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Green

variable {p : unitInterval}

/-- A stretched exponential tail gives the tail form `OsBound`. -/
theorem osBound_of_hasTail {X : Configuration 2 → ℝ} {C s : ℝ} (hC : 1 ≤ C) (hs : 0 < s)
    (h : HasTail p X C s) :
    LatticeProb.OsBound (latticeBondLaw 2 p) s ((C * (1 + Real.log C)) ^ (1 / s)) X := by
  intro t ht
  have hC0 : 0 < C := by linarith
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  set θ := (C * (1 + Real.log C)) ^ (1 / s) with hθ
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos (by positivity) _
  have hθs : θ ^ s = C * (1 + Real.log C) := by
    rw [hθ, ← Real.rpow_mul (by positivity), one_div_mul_cancel hs.ne', Real.rpow_one]
  have ht0 : 0 ≤ t := by linarith
  have hC0' : C ≠ 0 := hC0.ne'
  have hsub : {ω | t * θ < max (X ω) 0} ⊆ {ω | t * θ ≤ X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rcases le_total (X ω) 0 with h0 | h0
    · rw [max_eq_right h0] at hω
      exact absurd hω (not_lt.2 (by positivity))
    · rw [max_eq_left h0] at hω; exact hω.le
  refine (measure_mono hsub).trans ((h (t * θ) (by positivity)).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have hts : Real.rpow (t * θ) s = t ^ s * (C * (1 + Real.log C)) := by
    change (t * θ) ^ s = _
    rw [Real.mul_rpow (by linarith) hθ0.le, hθs]
  rw [hts, show -(t ^ s * (C * (1 + Real.log C))) / C = -(t ^ s * (1 + Real.log C)) by
    field_simp]
  have ht1 : 1 ≤ t ^ s := Real.one_le_rpow ht hs.le
  calc C * Real.exp (-(t ^ s * (1 + Real.log C)))
      = Real.exp (Real.log C + -(t ^ s * (1 + Real.log C))) := by
        rw [Real.exp_add, Real.exp_log hC0]
    _ ≤ Real.exp (-(t ^ s)) := Real.exp_le_exp.2 (by nlinarith)

/-- The Carne–Varopoulos bound in the form `p(s, x, z) ≤ s Φ_C(s, x - z)`. -/
theorem openHeat_le_mul_dgPhi {Ccv : ℝ} (hCcv : 0 < Ccv) {ω : Configuration 2}
    {x z : Vertex 2} {s : ℝ} (hs : 0 < s)
    (hcv : (latticeDist x z ≤ s → openHeat ω s x z ≤
        Ccv * Real.exp (-(latticeDist x z ^ 2 / (Ccv * s)))) ∧
      (s ≤ latticeDist x z → openHeat ω s x z ≤
        Ccv * Real.exp (-(latticeDist x z / Ccv * (1 + Real.log (latticeDist x z / s)))))) :
    openHeat ω s x z ≤ s * dgPhi Ccv s (latticeDist x z) := by
  rw [dgPhi, dgExponent]
  split_ifs with h
  · refine (hcv.1 h).trans (le_of_eq ?_)
    field_simp
  · push Not at h
    refine (hcv.2 h.le).trans (le_of_eq ?_)
    field_simp

/-- `s Φ_c(τ, d) ≤ c Φ_{2c}(τ, d)` for `τ ≤ s ≤ d`. -/
theorem mul_dgPhi_le {c τ s d : ℝ} (hc : 0 < c) (hτ : 0 < τ) (hτs : τ ≤ s) (hsd : s ≤ d) :
    s * dgPhi c τ d ≤ c * dgPhi (2 * c) τ d := by
  have hd0 : 0 ≤ d := by linarith
  rw [dgPhi_eq, dgPhi_eq]
  set g := dgShape τ d
  have hg : s ≤ g := by
    have hm := min_le_dgShape hτ hd0
    have : min (d ^ 2 / τ) d = d := by
      apply min_eq_right
      rw [le_div_iff₀ hτ]; nlinarith
    rw [this] at hm
    linarith
  have hu : s * Real.exp (-(s / (2 * c))) ≤ 2 * c := by
    have h1 : s / (2 * c) ≤ Real.exp (s / (2 * c)) := by
      have := Real.add_one_le_exp (s / (2 * c)); linarith
    have hu1 : s / (2 * c) * Real.exp (-(s / (2 * c))) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(s / (2 * c)))).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    calc s * Real.exp (-(s / (2 * c))) = 2 * c * (s / (2 * c) * Real.exp (-(s / (2 * c)))) := by
          field_simp
      _ ≤ 2 * c * 1 := mul_le_mul_of_nonneg_left hu1 (by positivity)
      _ = 2 * c := mul_one _
  have hsplit : Real.exp (-(g / c)) = Real.exp (-(g / (2 * c))) * Real.exp (-(g / (2 * c))) := by
    rw [← Real.exp_add]; congr 1; ring
  have hgs : Real.exp (-(g / (2 * c))) ≤ Real.exp (-(s / (2 * c))) :=
    Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right hg (by positivity)))
  have hs0 : 0 ≤ s := by linarith
  calc s * (c * τ⁻¹ * Real.exp (-(g / c)))
      = c * τ⁻¹ * Real.exp (-(g / (2 * c))) * (s * Real.exp (-(g / (2 * c)))) := by
        rw [hsplit]; ring
    _ ≤ c * τ⁻¹ * Real.exp (-(g / (2 * c))) * (s * Real.exp (-(s / (2 * c)))) := by gcongr
    _ ≤ c * τ⁻¹ * Real.exp (-(g / (2 * c))) * (2 * c) := by gcongr
    _ = c * (2 * c * τ⁻¹ * Real.exp (-(g / (2 * c)))) := by ring

/-- `(1 + d/√τ) exp(-d²/(8στ)) ≤ (1 + √(8σ)) exp(-d²/(16στ))`. -/
theorem one_add_div_mul_exp_le {σ τ d : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hd : 0 ≤ d) :
    (1 + d / Real.sqrt τ) * Real.exp (-(1 / (8 * σ) * d ^ 2 / τ)) ≤
      (1 + Real.sqrt (8 * σ)) * Real.exp (-(1 / (16 * σ) * d ^ 2 / τ)) := by
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have h := mul_exp_neg_sq_le (c := 8 * σ * τ) (by positivity) hd
  have e1 : d ^ 2 / (8 * σ * τ) = 1 / (8 * σ) * d ^ 2 / τ := by field_simp
  have e2 : d ^ 2 / (2 * (8 * σ * τ)) = 1 / (16 * σ) * d ^ 2 / τ := by field_simp; ring
  rw [e1, e2, Real.sqrt_mul (by positivity)] at h
  have h2 : Real.exp (-(1 / (8 * σ) * d ^ 2 / τ)) ≤ Real.exp (-(1 / (16 * σ) * d ^ 2 / τ)) := by
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ hτ.le
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply one_div_le_one_div_of_le (by positivity); linarith
  have h3 : d * Real.exp (-(1 / (8 * σ) * d ^ 2 / τ)) / Real.sqrt τ ≤
      Real.sqrt (8 * σ) * Real.exp (-(1 / (16 * σ) * d ^ 2 / τ)) := by
    rw [div_le_iff₀ hst]; nlinarith
  have hre : (1 + d / Real.sqrt τ) * Real.exp (-(1 / (8 * σ) * d ^ 2 / τ)) =
      Real.exp (-(1 / (8 * σ) * d ^ 2 / τ)) + d * Real.exp (-(1 / (8 * σ) * d ^ 2 / τ)) /
        Real.sqrt τ := by ring
  rw [hre]
  nlinarith

/-- The bound of the initial value of `v`: with `|χ_{e_k}(z)| ≤ C₅ (√τ + |z - y| + 2)^a`,
`|h(τ, z, y) - θ^{-1} p̄(τ, z - y)| ≤ K τ^{-1/2 + a/2} Φ_{16σ}(τ, z - y)`. -/
theorem abs_twoScale_sub_le {σ θ C₅ a τ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) (hC₅ : 0 < C₅) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hτ : 1 ≤ τ) {χ : Fin 2 → Vertex 2 → ℝ} {y z : Vertex 2}
    (hχ : ∀ k, |χ k z| ≤ C₅ * (Real.sqrt τ + latticeDist z y + 2) ^ a) :
    |dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y| ≤
      2 * θ⁻¹ * (Real.exp (1 / (2 * σ)) * (4 * Real.sqrt σ + 1) / (4 * Real.pi * σ ^ 2)) * C₅ *
        3 * (1 + Real.sqrt (8 * σ)) / (16 * σ) * τ ^ (-(1 / 2 : ℝ) + a / 2) *
          dgPhi (16 * σ) τ (latticeDist z y) := by
  set KG := Real.exp (1 / (2 * σ)) * (4 * Real.sqrt σ + 1) / (4 * Real.pi * σ ^ 2)
  have hτ0 : 0 < τ := by linarith
  have hd0 := latticeDist_nonneg z y
  have hD : ∀ k : Fin 2, |latticeGaussian σ τ (z + Pi.single k 1) y - latticeGaussian σ τ z y| ≤
      KG * ((τ⁻¹) ^ 2 * Real.sqrt τ) * Real.exp (-(1 / (8 * σ) * latticeDist z y ^ 2 / τ)) := by
    intro k
    apply abs_gaussianHeat_sub_le hσ hτ
    have : (latticeEuclideanEmbedding (z + Pi.single k 1) - latticeEuclideanEmbedding y) -
        (latticeEuclideanEmbedding z - latticeEuclideanEmbedding y) =
        latticeEuclideanEmbedding (z + Pi.single k 1) - latticeEuclideanEmbedding z := by abel
    rw [this]
    exact (latticeDist_add_single z k).le
  have hdec : dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y =
      θ⁻¹ * ∑ k : Fin 2, (latticeGaussian σ τ (z + Pi.single k 1) y -
        latticeGaussian σ τ z y) * χ k z := by
    simp only [dgTwoScale]; ring
  have hpow := rpow_sqrt_add_le (a := a / 2) hτ hd0 (by linarith) (by linarith)
  rw [show 2 * (a / 2) = a by ring] at hpow
  have hmom := one_add_div_mul_exp_le hσ hτ0 hd0
  have hsh : Real.exp (-(1 / (16 * σ) * latticeDist z y ^ 2 / τ)) ≤
      16 * σ * τ * (16 * σ)⁻¹ * τ⁻¹ * Real.exp (-(dgShape τ (latticeDist z y) / (16 * σ))) := by
    rw [show 16 * σ * τ * (16 * σ)⁻¹ * τ⁻¹ = 1 by field_simp, one_mul]
    apply Real.exp_le_exp.2
    rw [neg_le_neg_iff, show 1 / (16 * σ) * latticeDist z y ^ 2 / τ =
      latticeDist z y ^ 2 / τ / (16 * σ) by field_simp]
    exact div_le_div_of_nonneg_right (dgShape_le_sq hτ0 hd0) (by positivity)
  rw [hdec, abs_mul, abs_of_pos (inv_pos.2 hθ)]
  have hsum : |∑ k : Fin 2, (latticeGaussian σ τ (z + Pi.single k 1) y -
      latticeGaussian σ τ z y) * χ k z| ≤
      2 * (KG * ((τ⁻¹) ^ 2 * Real.sqrt τ) * Real.exp (-(1 / (8 * σ) * latticeDist z y ^ 2 / τ)) *
        (C₅ * (Real.sqrt τ + latticeDist z y + 2) ^ a)) := by
    rw [Fin.sum_univ_two]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, two_mul]
    exact add_le_add (mul_le_mul (hD 0) (hχ 0) (abs_nonneg _) (by positivity))
      (mul_le_mul (hD 1) (hχ 1) (abs_nonneg _) (by positivity))
  have hτa : (τ⁻¹) ^ 2 * Real.sqrt τ * τ ^ (a / 2) * τ = τ ^ (-(1 / 2 : ℝ) + a / 2) := by
    have hs := Real.mul_self_sqrt hτ0.le
    have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
    have h1 : (τ⁻¹) ^ 2 * Real.sqrt τ * τ = (Real.sqrt τ)⁻¹ := by
      calc (τ⁻¹) ^ 2 * Real.sqrt τ * τ = Real.sqrt τ / τ := by field_simp
        _ = Real.sqrt τ / (Real.sqrt τ * Real.sqrt τ) := by rw [hs]
        _ = (Real.sqrt τ)⁻¹ := by field_simp
    rw [Real.rpow_add hτ0, rpow_neg_half_eq hτ0, ← h1]
    ring
  calc θ⁻¹ * |∑ k : Fin 2, (latticeGaussian σ τ (z + Pi.single k 1) y -
        latticeGaussian σ τ z y) * χ k z|
      ≤ θ⁻¹ * (2 * (KG * ((τ⁻¹) ^ 2 * Real.sqrt τ) *
          Real.exp (-(1 / (8 * σ) * latticeDist z y ^ 2 / τ)) *
          (C₅ * (Real.sqrt τ + latticeDist z y + 2) ^ a))) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.2 hθ).le
    _ ≤ θ⁻¹ * (2 * (KG * ((τ⁻¹) ^ 2 * Real.sqrt τ) *
          Real.exp (-(1 / (8 * σ) * latticeDist z y ^ 2 / τ)) *
          (C₅ * (3 * τ ^ (a / 2) * (1 + latticeDist z y / Real.sqrt τ))))) := by
        gcongr
    _ = 2 * θ⁻¹ * KG * C₅ * 3 * ((τ⁻¹) ^ 2 * Real.sqrt τ * τ ^ (a / 2)) *
          ((1 + latticeDist z y / Real.sqrt τ) *
            Real.exp (-(1 / (8 * σ) * latticeDist z y ^ 2 / τ))) := by ring
    _ ≤ 2 * θ⁻¹ * KG * C₅ * 3 * ((τ⁻¹) ^ 2 * Real.sqrt τ * τ ^ (a / 2)) *
          ((1 + Real.sqrt (8 * σ)) * (16 * σ * τ * (16 * σ)⁻¹ * τ⁻¹ *
            Real.exp (-(dgShape τ (latticeDist z y) / (16 * σ))))) := by
        exact mul_le_mul_of_nonneg_left
          (hmom.trans (mul_le_mul_of_nonneg_left hsh (by positivity))) (by positivity)
    _ = 2 * θ⁻¹ * KG * C₅ * 3 * (1 + Real.sqrt (8 * σ)) / (16 * σ) *
          ((τ⁻¹) ^ 2 * Real.sqrt τ * τ ^ (a / 2) * τ) * dgPhi (16 * σ) τ (latticeDist z y) := by
        rw [dgPhi_eq]; field_simp
    _ = _ := by rw [hτa]

set_option maxHeartbeats 400000 in
/-- **Dario–Gu, Lemma 4.2** in dimension two, from Proposition 2.12, Theorem 4 and
Proposition 2.15. -/
theorem darioGuCorrectorLemmaTwo_of_inputs (hR5 : CorrectorQuantitativeInputTwo)
    (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ} (hσ : 0 < σ) :
    DarioGuCorrectorLemmaTwo p σ := by
  intro α hα
  set θ := theta 2 p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  set α' := min α (1 / 4) with hα'
  have hα'0 : 0 < α' := lt_min hα (by norm_num)
  have hα'1 : α' ≤ 1 / 4 := min_le_right _ _
  have hα'α : α' ≤ α := min_le_left _ _
  obtain ⟨s5, C₅, hs5, hC₅, h5⟩ := hR5 p hpc hp1 α' hα'0
  choose M₅ hM5m hM50 hM5os hM5ae using h5
  obtain ⟨sB, CB, hsB, hCB, hB'⟩ := hBar p hpc hp1
  choose TB hTBm hTB0 hTBos hTBae using hB'
  obtain ⟨Ccv, hCcv, hcv⟩ := hCV
  -- the time `T'_NA` of (3.52)
  have gB := goodTimes_of_isOsBond hsB hCB hTBm hTB0 hTBos
  obtain ⟨⟨hSm, hS0, CS, sS, hCS, hsS, hSt⟩, hbdd⟩ := goodTimes_latticeSup gB
  set θS := (CS * (1 + Real.log CS)) ^ (1 / sS) with hθS
  have hlogCS : 0 ≤ Real.log CS := Real.log_nonneg (by linarith)
  have hθS0 : 0 < θS := Real.rpow_pos_of_pos (by positivity) _
  have hSos : ∀ y, IsOsBond 2 p (latticeSup TB y) sS
      (θS * (2 : ℝ) ^ (1 / sS) * Real.exp 2 ^ (1 / sS)) := fun y =>
    Rigidity.Proofs.Cluster.isOsBond_of_osBound hsS hθS0 (hSm y)
      (osBound_of_hasTail (by linarith) hsS (hSt y))
  -- the common exponent and scale of the minimal time `M = max(M₅², T'_NA, 1)`
  set s' := min (s5 / 2) sS with hs'
  have hs'0 : 0 < s' := lt_min (by positivity) hsS
  set θ1 := C₅ ^ 2 * (6 : ℝ) ^ (1 / s') with hθ1
  set θ2 := θS * (2 : ℝ) ^ (1 / sS) * Real.exp 2 ^ (1 / sS) * (6 : ℝ) ^ (1 / s') with hθ2
  set θ3 := (1 : ℝ) * (3 : ℝ) ^ (1 / s') with hθ3
  set θM := max (max θ1 θ2 * (4 : ℝ) ^ (1 / s')) θ3 * (4 : ℝ) ^ (1 / s') with hθM
  -- the constants of the bound
  set KG := Real.exp (1 / (2 * σ)) * (4 * Real.sqrt σ + 1) / (4 * Real.pi * σ ^ 2) with hKG
  set K₃ := 2 * θ⁻¹ * KG * C₅ * 3 * (1 + Real.sqrt (8 * σ)) / (16 * σ) with hK₃
  set C₇ := max (max CB Ccv) (32 * σ) with hC₇
  have hC₇0 : 0 < C₇ := lt_max_of_lt_left (lt_max_of_lt_left hCB)
  obtain ⟨C₈, hC₈, hconv⟩ := sum_dgPhi_mul_dgPhi_le hC₇0
  set K₆ := max 1 (16 * σ) with hK₆
  set Cf := max (max θM C₈) (K₃ * K₆) with hCf
  have hCf0 : 0 < Cf := lt_max_of_lt_left (lt_max_of_lt_right hC₈)
  refine ⟨Cf, s', hCf0, hs'0, fun y => ?_⟩
  set M : Configuration 2 → ℝ := fun ω => max (max (M₅ y ω ^ 2) (latticeSup TB y ω)) 1 with hM
  have hMm : Measurable M :=
    (((hM5m y).pow_const 2).max (hSm y)).max measurable_const
  have hos1 : IsOsBond 2 p (fun ω => M₅ y ω ^ 2) s' θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0 (le_trans (min_le_left _ _) le_rfl)
      ((hM5m y).pow_const 2) (IsOsBond.sq_of_nonneg hC₅ (hM50 y) (hM5os y))
  have hos2 : IsOsBond 2 p (latticeSup TB y) s' θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0 (min_le_right _ _) (hSm y) (hSos y)
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity)
    ((hM5m y).pow_const 2) (hSm y) hos1 hos2
  have hosM : IsOsBond 2 p M s' θM :=
    Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity)
      (((hM5m y).pow_const 2).max (hSm y)) measurable_const hos12
      (Rigidity.Proofs.S2.isOsBond_const one_pos hs'0)
  refine ⟨M, hMm, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs'0 (by positivity)
      ((le_max_left _ _).trans (le_max_left _ _)) hMm hosM, ?_⟩
  filter_upwards [hM5ae y, ae_all_iff.2 hTBae, hbdd y] with ω hω hBω hbω
  intro h hy χ hχ t τ hMτ h3τ x hx
  set K := uniqueInfiniteComponent h with hK
  have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hMτ
  have hτ0 : 0 < τ := by linarith
  have hM5τ : M₅ y ω ≤ Real.sqrt τ := by
    rw [← Real.sqrt_sq (hM50 y ω)]
    exact Real.sqrt_le_sqrt ((le_max_left _ _).trans ((le_max_left _ _).trans hMτ))
  set s := t - τ with hsdef
  have hs2 : 2 * τ ≤ s := by rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have hSτ : latticeSup TB y ω ≤ s :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans hMτ)).trans (by linarith)
  -- the corrector bound (Proposition 2.12 at `y`)
  have hχb : ∀ z ∈ K.supp, ∀ k : Fin 2,
      |χ k z| ≤ C₅ * (Real.sqrt τ + latticeDist z y + 2) ^ α' := by
    intro z hz k
    obtain ⟨b', hadj, hb'd⟩ := exists_adj_near (uniqueInfiniteComponent_infinite h) ⟨z, hz⟩
    have hd0 := latticeDist_nonneg z y
    have hsτ0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
    have hr : M₅ y ω ≤ Real.sqrt τ + latticeDist z y + 2 := by linarith
    have hb'y : latticeDist b'.val y ≤ latticeDist z y + 1 := by
      have := latticeDist_triangle b'.val z y
      rw [latticeDist_comm z b'.val] at this
      linarith
    have := hω h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 _ hr
      ⟨z, hz⟩ ⟨y, hy⟩ ⟨z, hz⟩ b' (by change latticeDist z y < _; linarith)
      (by change latticeDist y y < _
          rw [show latticeDist y y = 0 by simp [latticeDist]]; linarith)
      (by change latticeDist z y < _; linarith) (by change latticeDist b'.val y < _; linarith) hadj
    simp only [Rigidity.Corrector.sum_single_mul, Rigidity.Corrector.sum_abs_single,
      mul_one] at this
    have e1 : (z k : ℝ) + χ k z - z k - ((y k : ℝ) + χ k y - y k) = χ k z := by
      rw [(hχ k).2]; ring
    rw [e1] at this
    exact le_of_add_le_of_nonneg_left this (abs_nonneg _)
  -- the bound of each term
  have hterm : ∀ z : Vertex 2, |openHeat ω s x z *
      (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y)| ≤
      K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) *
        (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) := by
    intro z
    have hφ0 : 0 ≤ dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z) :=
      mul_nonneg (dgPhi_nonneg hC₇0.le hτ0.le _) (dgPhi_nonneg hC₇0.le hs0.le _)
    by_cases hz : z ∈ K.supp
    · have hP0 := openHeat_nonneg' ω hs0.le x z
      have hzp := abs_twoScale_sub_le hσ hθ hC₅ hα'0.le (by linarith) hτ1 (hχb z hz)
      rw [abs_mul, abs_of_nonneg hP0]
      have hzd := latticeDist_nonneg z y
      have hxz := latticeDist_nonneg x z
      by_cases hnear : latticeDist z y ≤ s + 1
      · -- Theorem 4 at `z`
        have hTBz : TB z ω ≤ s := le_of_latticeSup_le hbω hSτ hnear
        have hbar := hBω z h hz s hs0 hTBz x hx
        have h1 : openHeat ω s x z ≤ dgPhi C₇ s (latticeDist x z) :=
          hbar.trans (dgPhi_mono hCB ((le_max_left _ _).trans (le_max_left _ _)) hs0 hxz)
        have h2 : |dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y| ≤
            K₃ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₇ τ (latticeDist z y) :=
          hzp.trans (mul_le_mul_of_nonneg_left (dgPhi_mono (by positivity)
            ((show 16 * σ ≤ 32 * σ by linarith).trans (le_max_right _ _)) hτ0 hzd) (by positivity))
        calc openHeat ω s x z * |dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y|
            ≤ dgPhi C₇ s (latticeDist x z) *
                (K₃ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₇ τ (latticeDist z y)) :=
              mul_le_mul h1 h2 (abs_nonneg _) (dgPhi_nonneg hC₇0.le hs0.le _)
          _ ≤ K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) *
                (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) := by
              have : K₃ * τ ^ (-(1 / 2 : ℝ) + α' / 2) ≤ K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) := by
                have hK : K₃ ≤ K₃ * K₆ := le_mul_of_one_le_right (by positivity) (le_max_left _ _)
                exact mul_le_mul_of_nonneg_right hK (by positivity)
              nlinarith [dgPhi_nonneg hC₇0.le hτ0.le (latticeDist z y),
                dgPhi_nonneg hC₇0.le hs0.le (latticeDist x z)]
      · -- Proposition 2.15 at the far points
        push Not at hnear
        have hcv' := hcv ω K (uniqueInfiniteComponent_infinite h) x hx z hz s hs0
        have h1 : openHeat ω s x z ≤ s * dgPhi C₇ s (latticeDist x z) :=
          (openHeat_le_mul_dgPhi hCcv hs0 hcv').trans
            (mul_le_mul_of_nonneg_left (dgPhi_mono hCcv
              ((le_max_right _ _).trans (le_max_left _ _)) hs0 hxz) hs0.le)
        have h2 : s * dgPhi (16 * σ) τ (latticeDist z y) ≤
            16 * σ * dgPhi (2 * (16 * σ)) τ (latticeDist z y) :=
          mul_dgPhi_le (by positivity) hτ0 (by linarith) (by linarith)
        have h32 : 2 * (16 * σ) ≤ C₇ := by
          rw [show 2 * (16 * σ) = 32 * σ by ring]; exact le_max_right _ _
        have h3 : dgPhi (2 * (16 * σ)) τ (latticeDist z y) ≤ dgPhi C₇ τ (latticeDist z y) :=
          dgPhi_mono (by positivity) h32 hτ0 hzd
        have hK6 : 16 * σ ≤ K₆ := le_max_right _ _
        calc openHeat ω s x z * |dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y|
            ≤ s * dgPhi C₇ s (latticeDist x z) *
                (K₃ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi (16 * σ) τ (latticeDist z y)) :=
              mul_le_mul h1 hzp (abs_nonneg _)
                (mul_nonneg hs0.le (dgPhi_nonneg hC₇0.le hs0.le _))
          _ = K₃ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₇ s (latticeDist x z) *
                (s * dgPhi (16 * σ) τ (latticeDist z y)) := by ring
          _ ≤ K₃ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₇ s (latticeDist x z) *
                (K₆ * dgPhi C₇ τ (latticeDist z y)) := by
              apply mul_le_mul_of_nonneg_left _ (by
                have := dgPhi_nonneg hC₇0.le hs0.le (latticeDist x z); positivity)
              exact h2.trans (mul_le_mul hK6 h3 (dgPhi_nonneg (by positivity) hτ0.le _)
                (by positivity))
          _ = _ := by ring
    · rw [openHeat_eq_zero_of_mem_of_notMem hx hz, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) hφ0
  -- the sum
  have hpart : ∀ S : Finset (Vertex 2), ∑ z ∈ S, |openHeat ω s x z *
      (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y)| ≤
      K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₈ t (latticeDist x y) := by
    intro S
    calc _ ≤ ∑ z ∈ S, K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) *
            (dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z)) :=
          Finset.sum_le_sum fun z _ => hterm z
      _ = K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) *
            ∑ z ∈ S, dgPhi C₇ τ (latticeDist z y) * dgPhi C₇ s (latticeDist x z) := by
          rw [Finset.mul_sum]
      _ ≤ K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₈ (τ + s) (latticeDist x y) :=
          mul_le_mul_of_nonneg_left (hconv τ s hτ1 (by linarith) x y S) (by positivity)
      _ = _ := by rw [show τ + s = t by rw [hsdef]; ring]
  have hsumm : Summable fun z => |openHeat ω s x z *
      (dgTwoScale σ θ χ τ z y - θ⁻¹ * latticeGaussian σ τ z y)| :=
    summable_of_sum_le (fun _ => abs_nonneg _) hpart
  have hv : |dgV ω σ θ χ t τ x y| ≤
      K₃ * K₆ * τ ^ (-(1 / 2 : ℝ) + α' / 2) * dgPhi C₈ t (latticeDist x y) := by
    exact (abs_tsum_le_tsum_abs hsumm).trans (hsumm.tsum_le_of_sum_le hpart)
  have ht0 : 0 < t := by linarith
  refine hv.trans ?_
  have hpow : τ ^ (-(1 / 2 : ℝ) + α' / 2) ≤ τ ^ (-(1 / 2 : ℝ) + α / 2) :=
    Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
  apply mul_le_mul (mul_le_mul ((le_max_right _ _)) hpow (by positivity) (by positivity))
    (dgPhi_mono hC₈ ((le_max_right _ _).trans (le_max_left _ _)) ht0 (latticeDist_nonneg x y))
    (dgPhi_nonneg hC₈.le ht0.le _) (by positivity)

end Rigidity.Green
