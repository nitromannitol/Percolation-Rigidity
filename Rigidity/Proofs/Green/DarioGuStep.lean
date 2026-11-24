import Rigidity.Proofs.Green.DarioGuLevels
import PercolationClusterHomogenization.Proofs.Percolation.SupercriticalUniqueness

/-!
# The iteration step of §4.3 of Dario–Gu: `H_k` implies `H_{k'}`

`heatLevel_step`: from the statement (4.45) at exponent `k ≤ 1/2 - δ` (with minimal times `T`) and
the results of §4.1–§4.2, Theorem 4, Proposition 2.15 and Proposition A.7, the statement holds at
exponent `k' = min((1 - κ) k + κ/2, 1/2 - δ)`, `κ = δ/4`, `α = δ/2` (the recursion (4.43)).

For `t ≥ T'(z)` and `x ∈ 𝒞_∞`:

* if `|x - z| ≥ t`, the far bound (Proposition 2.15, Remark 2.16);
* otherwise, with `s = t/2` and `τ = s^{1-κ}`: at `w ∈ {x, z}`, the decomposition (4.47)
  `p - θ^{-1} p̄ = (h - θ^{-1} p̄) - (q - p) - v - w` with Lemma 4.1 (fed with `H_k` at time `τ`,
  lines 2618-2622), Lemma 4.2, Proposition 4.3 and the estimate of `h - θ^{-1} p̄` gives the
  weighted `L²` estimate (4.49) `≤ c_L s^{-1/2-k'}`; then (4.48) with Theorem 4 at `z` and the
  term (4.48)-b.

`T'(z)` is the lattice minimal time (4.44) of the times of the points `w` at which these results
are used.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External
open scoped ENNReal

namespace Rigidity.Green

variable {p : unitInterval}

theorem le_of_rpow_inv_le {X s a : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (h : X ^ (1 / a) ≤ s) :
    X ≤ s ^ a := by
  have := Real.rpow_le_rpow (Real.rpow_nonneg hX _) h ha.le
  rwa [← Real.rpow_mul hX, one_div_mul_cancel ha.ne', Real.rpow_one] at this

/-- **The weighted `L²` estimate (4.49)** from the four estimates of the decomposition (4.47):
`F = G₄ - G₁ - G₂ - G₃` with `G₁ = q - p` (Lemma 4.1 fed with `H_k`), `G₂ = v` (Lemma 4.2),
`G₃ = w` (Proposition 4.3) and `G₄ = h - θ^{-1} p̄`, at time `s` with `τ = s^{1-δ/4}`. -/
theorem step_weightedL2 {K : Set (Vertex 2)} {w : Vertex 2} {s δ k c CA CV CP CH MA MV Cw : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hs : 1 ≤ s) (hc : 0 < c) (hCA : 0 < CA) (hCV : 0 < CV)
    (hCP : 0 < CP) (hCH : 0 < CH) (hMA : 0 < MA) (hMV : 0 < MV) (h1C : 2 * CA ≤ Cw)
    (h2C : 2 * CV ≤ Cw) (h3C : CP ≤ Cw) (h4C : CH ≤ Cw)
    {F G1 G2 G3 G4 : Vertex 2 → ℝ} (hF : ∀ y, F y = G4 y - G1 y - G2 y - G3 y)
    (h1 : WeightedL2Le K (2 * CA) s w G1 (MA * (CA * (c * (s ^ (1 - δ / 4)) ^ (-k) *
      (s ^ (1 - δ / 4) / s) ^ (1 / 2 : ℝ) + (s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2))) *
        s ^ (-(1 / 2 : ℝ))))
    (h2 : WeightedL2Le K (2 * CV) s w G2 (MV * (CV * (s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) +
      δ / 2 / 2)) * s ^ (-(1 / 2 : ℝ))))
    (h3 : WeightedL2Le K CP s w G3 (CP * (s / s ^ (1 - δ / 4)) ^ (1 / 2 : ℝ) *
      (s ^ (1 - δ / 4)) ^ (-(1 : ℝ) + δ / 2 / 2)))
    (h4 : WeightedL2Le K CH s w G4 (CH * s ^ (-(1 : ℝ) + δ / 2))) :
    WeightedL2Le K Cw s w F ((MA * CA * c + MA * CA + MV * CV + CP + CH) *
      s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ))) := by
  have hs0 : 0 < s := by linarith
  have hτ0 : 0 < s ^ (1 - δ / 4) := Real.rpow_pos_of_pos hs0 _
  have L1 := h1.mono_const (by positivity) h1C hs0
  have L2 := h2.mono_const (by positivity) h2C hs0
  have L3 := h3.mono_const hCP h3C hs0
  have L4 := h4.mono_const hCH h4C hs0
  have hsum := ((L4.sub L1 (by positivity) (by positivity)).sub L2 (by positivity)
    (by positivity)).sub L3 (by positivity) (by positivity)
  have hfun := hsum.of_abs_le (f := F) (fun y _ => le_of_eq (congrArg abs (hF y)))
  refine hfun.mono_bound (by positivity) ?_
  obtain ⟨e1, e2, e3, e4, e5⟩ := step_exponents (k := k) hδ hδ4 hs
  calc CH * s ^ (-(1 : ℝ) + δ / 2) +
        MA * (CA * (c * (s ^ (1 - δ / 4)) ^ (-k) * (s ^ (1 - δ / 4) / s) ^ (1 / 2 : ℝ) +
          (s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2))) * s ^ (-(1 / 2 : ℝ)) +
        MV * (CV * (s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2 / 2)) * s ^ (-(1 / 2 : ℝ)) +
        CP * (s / s ^ (1 - δ / 4)) ^ (1 / 2 : ℝ) * (s ^ (1 - δ / 4)) ^ (-(1 : ℝ) + δ / 2 / 2)
      = CH * s ^ (-(1 : ℝ) + δ / 2) +
        MA * CA * c * ((s ^ (1 - δ / 4)) ^ (-k) * (s ^ (1 - δ / 4) / s) ^ (1 / 2 : ℝ) *
          s ^ (-(1 / 2 : ℝ))) +
        MA * CA * ((s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2) * s ^ (-(1 / 2 : ℝ))) +
        MV * CV * ((s ^ (1 - δ / 4)) ^ (-(1 / 2 : ℝ) + δ / 2 / 2) * s ^ (-(1 / 2 : ℝ))) +
        CP * ((s / s ^ (1 - δ / 4)) ^ (1 / 2 : ℝ) * (s ^ (1 - δ / 4)) ^ (-(1 : ℝ) + δ / 2 / 2)) := by
        ring
    _ ≤ CH * s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) +
        MA * CA * c * s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) +
        MA * CA * s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) +
        MV * CV * s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) +
        CP * s ^ (-(1 / 2 : ℝ) - min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) := by
        gcongr
    _ = _ := by ring

/-- **The conversion of (4.48)** to `c' t^{-k'} Φ_{c'}(t, x - z)` (`s = t/2`). -/
theorem step_conversion {t k' δ M cL C₃ ML CD θ CG c' G r : ℝ} (ht : 8 ≤ t) (hk'0 : 0 ≤ k')
    (hk'1 : k' ≤ 1 / 2 - δ) (hδ : 0 < δ) (hM : 0 < M) (hcL : 0 < cL) (hC₃ : 0 < C₃)
    (hML : 0 < ML) (hCD : 0 < CD) (hθ : 0 < θ) (hCG : 0 < CG)
    (hG : G ≤ dgPhi CG t r) (hr : 0 ≤ r) (hc'1 : 4 * C₃ ≤ c') (hc'2 : CG ≤ c')
    (hc'3 : M * cL / C₃ + 2 * θ⁻¹ ^ 2 * (ML + CD) ≤ c') :
    M * (cL * (t / 2) ^ (-(1 / 2 : ℝ) - k')) * (t / 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(dgShape t r / (4 * C₃))) +
      θ⁻¹ * (G * θ⁻¹ * (ML * (t / 2 / 2) ^ (-(1 / 2 : ℝ)) +
        CD * (t / 2 / 2) ^ (-(1 / 2 - δ / 2)))) ≤ c' * t ^ (-k') * dgPhi c' t r := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hs0 : 0 < t / 2 := by positivity
  have hc'0 : 0 < c' := by linarith
  have hphi4 : dgPhi (4 * C₃) t r = 4 * C₃ * t⁻¹ * Real.exp (-(dgShape t r / (4 * C₃))) :=
    dgPhi_eq _ _ _
  have hpow1 : (t / 2) ^ (-(1 / 2 : ℝ) - k') * (t / 2) ^ (-(1 / 2 : ℝ)) ≤ 4 * (t ^ (-k') * t⁻¹) := by
    rw [← Real.rpow_add hs0, Real.div_rpow ht0.le (by norm_num)]
    have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ) - k' + -(1 / 2 : ℝ)) = ((2 : ℝ) ^ (1 + k'))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; ring_nf
    have h4 : (2 : ℝ) ^ (1 + k') ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show 1 + k' ≤ 2 by linarith)
      rwa [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at this
    have h5 : t ^ (-(1 / 2 : ℝ) - k' + -(1 / 2 : ℝ)) = t ^ (-k') * t⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]; ring_nf
    rw [h2, h5, div_inv_eq_mul]
    have : 0 ≤ t ^ (-k') * t⁻¹ := by positivity
    nlinarith
  have hE := Real.exp_pos (-(dgShape t r / (4 * C₃)))
  have hfirst : M * (cL * (t / 2) ^ (-(1 / 2 : ℝ) - k')) * (t / 2) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(dgShape t r / (4 * C₃))) ≤ M * cL / C₃ * t ^ (-k') * dgPhi (4 * C₃) t r := by
    rw [hphi4]
    have hC₃' : C₃ ≠ 0 := hC₃.ne'
    calc M * (cL * (t / 2) ^ (-(1 / 2 : ℝ) - k')) * (t / 2) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(dgShape t r / (4 * C₃)))
        = M * cL * ((t / 2) ^ (-(1 / 2 : ℝ) - k') * (t / 2) ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(dgShape t r / (4 * C₃))) := by ring
      _ ≤ M * cL * (4 * (t ^ (-k') * t⁻¹)) * Real.exp (-(dgShape t r / (4 * C₃))) := by
          gcongr
      _ = M * cL / C₃ * t ^ (-k') * (4 * C₃ * t⁻¹ * Real.exp (-(dgShape t r / (4 * C₃)))) := by
          field_simp
  have hs2 : 1 ≤ t / 2 / 2 := by linarith
  have hpow2 : ML * (t / 2 / 2) ^ (-(1 / 2 : ℝ)) + CD * (t / 2 / 2) ^ (-(1 / 2 - δ / 2)) ≤
      2 * (ML + CD) * t ^ (-k') := by
    have h1 : (t / 2 / 2) ^ (-(1 / 2 : ℝ)) ≤ (t / 2 / 2) ^ (-(1 / 2 - δ / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hs2 (by linarith)
    have h2 : (t / 2 / 2) ^ (-(1 / 2 - δ / 2)) ≤ 2 * t ^ (-k') := by
      have h4 : t / 2 / 2 = t / 4 := by ring
      rw [h4, Real.div_rpow ht0.le (by norm_num)]
      have h5 : t ^ (-(1 / 2 - δ / 2)) ≤ t ^ (-k') :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      have h6 : (4 : ℝ) ^ (-(1 / 2 - δ / 2)) ≥ 1 / 2 := by
        have h7 : (4 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (4 : ℝ) ^ (-(1 / 2 - δ / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h8 : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
            show (2 : ℝ) * -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
          norm_num
        linarith
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ t ^ (-k') := by positivity
      nlinarith
    have hD0 : 0 ≤ (t / 2 / 2) ^ (-(1 / 2 : ℝ)) := by positivity
    nlinarith
  have hsecond : θ⁻¹ * (G * θ⁻¹ * (ML * (t / 2 / 2) ^ (-(1 / 2 : ℝ)) +
      CD * (t / 2 / 2) ^ (-(1 / 2 - δ / 2)))) ≤ 2 * θ⁻¹ ^ 2 * (ML + CD) * t ^ (-k') * dgPhi CG t r := by
    calc θ⁻¹ * (G * θ⁻¹ * (ML * (t / 2 / 2) ^ (-(1 / 2 : ℝ)) +
          CD * (t / 2 / 2) ^ (-(1 / 2 - δ / 2))))
        = θ⁻¹ ^ 2 * G * (ML * (t / 2 / 2) ^ (-(1 / 2 : ℝ)) +
          CD * (t / 2 / 2) ^ (-(1 / 2 - δ / 2))) := by ring
      _ ≤ θ⁻¹ ^ 2 * dgPhi CG t r * (2 * (ML + CD) * t ^ (-k')) := by
          have hpos : 0 ≤ ML * (t / 2 / 2) ^ (-(1 / 2 : ℝ)) + CD * (t / 2 / 2) ^ (-(1 / 2 - δ / 2)) := by
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hG (by positivity)) hpow2 hpos
            (mul_nonneg (by positivity) (dgPhi_nonneg hCG.le ht0.le _))
      _ = _ := by ring
  have hP4 : dgPhi (4 * C₃) t r ≤ dgPhi c' t r := dgPhi_mono (by positivity) hc'1 ht0 hr
  have hPG : dgPhi CG t r ≤ dgPhi c' t r := dgPhi_mono hCG hc'2 ht0 hr
  have htk : 0 ≤ t ^ (-k') := by positivity
  have hφ : 0 ≤ dgPhi c' t r := dgPhi_nonneg hc'0.le ht0.le _
  calc _ ≤ M * cL / C₃ * t ^ (-k') * dgPhi (4 * C₃) t r +
        2 * θ⁻¹ ^ 2 * (ML + CD) * t ^ (-k') * dgPhi CG t r := add_le_add hfirst hsecond
    _ ≤ M * cL / C₃ * t ^ (-k') * dgPhi c' t r +
        2 * θ⁻¹ ^ 2 * (ML + CD) * t ^ (-k') * dgPhi c' t r := by gcongr
    _ = (M * cL / C₃ + 2 * θ⁻¹ ^ 2 * (ML + CD)) * t ^ (-k') * dgPhi c' t r := by ring
    _ ≤ c' * t ^ (-k') * dgPhi c' t r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc'3 htk) hφ

set_option maxHeartbeats 400000 in
/-- **The iteration step** (Dario–Gu, §4.3). -/
theorem heatLevel_step (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hSec : DarioGuSectionFourTwo p σ) (hBar : BarlowGaussianUpperBoundTwo)
    (hCV : CarneVaropoulosTwo) (hCorr : SupercriticalBondCorrectorInputTwo) {δ : ℝ}
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) {c k : ℝ} (hc : 0 < c) (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2 - δ)
    {T : Vertex 2 → Configuration 2 → ℝ} (hT : GoodTimes p T) (hH : HeatLevel p σ c k T) :
    ∃ c', 0 < c' ∧ ∃ T', GoodTimes p T' ∧
      HeatLevel p σ c' (min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ)) T' := by
  set θ := theta 2 p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  set k' := min ((1 - δ / 4) * k + δ / 4 / 2) (1 / 2 - δ) with hk'
  have hk'0 : 0 ≤ k' := le_min (by nlinarith) (by linarith)
  have hk'1 : k' ≤ 1 / 2 - δ := min_le_right _ _
  have hα : 0 < δ / 2 := by positivity
  have hκ : 0 < δ / 4 := by positivity
  have hκ1 : 0 < 1 - δ / 4 := by linarith
  obtain ⟨hA, hV, hP, hHt, hD⟩ := hSec
  obtain ⟨CA, sA, hCA, hsA, hA'⟩ := hA (δ / 2) hα c hc
  choose TA hTAm hTA0 hTAos hTAae using hA'
  obtain ⟨CV, sV, hCV0, hsV, hV'⟩ := hV (δ / 2) hα
  choose TV hTVm hTV0 hTVos hTVae using hV'
  obtain ⟨CP, sP, hCP, hsP, hP'⟩ := hP (δ / 2) hα
  choose TP hTPm hTP0 hTPos hTPae using hP'
  obtain ⟨CH, sH, hCH, hsH, hH'⟩ := hHt (δ / 2) hα
  choose TH hTHm hTH0 hTHos hTHae using hH'
  obtain ⟨CD, sD, hCD, hsD, hD'⟩ := hD (δ / 2) hα
  choose TD hTDm hTD0 hTDos hTDae using hD'
  obtain ⟨sB, CB, hsB, hCB, hB'⟩ := hBar p hpc hp1
  choose TB hTBm hTB0 hTBos hTBae using hB'
  obtain ⟨Ccv, hCcv, hcv⟩ := hCV
  have hcorr := hCorr p hpc hp1
  -- constants
  obtain ⟨MA, hMA, hMAb⟩ := weightedL2Le_of_abs_le_dgPhi hCA
  obtain ⟨MV, hMV, hMVb⟩ := weightedL2Le_of_abs_le_dgPhi hCV0
  set Cw := max (max (2 * CA) (2 * CV)) (max CP CH) with hCw
  have hCw0 : 0 < Cw := lt_max_of_lt_right (lt_max_of_lt_left hCP)
  obtain ⟨M, C₃, hM, hC₃, hpw⟩ := pointwise_of_weightedL2 hθ hσ hCw0 hCB
  obtain ⟨ML, hML, hLip⟩ := sum_abs_gaussianHeat_sub_le hσ
  obtain ⟨cf, hcf, hfar⟩ := far_bound hθ hσ hCcv
  set CG := max (2 * σ) (1 / (2 * Real.pi * σ)) with hCG
  have hCG0 : 0 < CG := lt_max_of_lt_left (by positivity)
  set cL := MA * CA * c + MA * CA + MV * CV + CP + CH with hcL
  have hcL0 : 0 < cL := by positivity
  set c' := max (max (4 * C₃) CG) (max cf (M * cL / C₃ + 2 * θ⁻¹ ^ 2 * (ML + CD))) with hc'
  have hc'0 : 0 < c' := lt_max_of_lt_left (lt_max_of_lt_left (by positivity))
  -- the minimal times
  set X : Vertex 2 → Configuration 2 → ℝ := fun w ω =>
    max (max (max (TA w ω) (TV w ω)) (max (TP w ω) (T w ω))) 1 with hX
  set Q : Vertex 2 → Configuration 2 → ℝ := fun w ω =>
    max (max (X w ω ^ (1 / (1 - δ / 4))) (TH w ω)) ((3 : ℝ) ^ (1 / (δ / 4))) with hQ
  set V : Vertex 2 → Configuration 2 → ℝ := fun w ω =>
    max (max (2 * Q w ω) (max (8 * TD w ω) 8)) (2 * TB w ω) with hV
  have gA := goodTimes_of_isOsBond hsA hCA hTAm hTA0 hTAos
  have gV := goodTimes_of_isOsBond hsV hCV0 hTVm hTV0 hTVos
  have gP := goodTimes_of_isOsBond hsP hCP hTPm hTP0 hTPos
  have gH := goodTimes_of_isOsBond hsH hCH hTHm hTH0 hTHos
  have gD := goodTimes_of_isOsBond hsD hCD hTDm hTD0 hTDos
  have gB := goodTimes_of_isOsBond hsB hCB hTBm hTB0 hTBos
  have gX : GoodTimes p X := ((gA.max gV).max (gP.max hT)).max_const zero_le_one
  have gQ : GoodTimes p Q :=
    ((gX.rpow (by positivity)).max gH).max_const (by positivity)
  have gV' : GoodTimes p V :=
    ((gQ.const_mul two_pos).max ((gD.const_mul (by norm_num)).max_const (by norm_num))).max
      (gB.const_mul two_pos)
  obtain ⟨gS, hbdd⟩ := goodTimes_latticeSup gV'
  refine ⟨c', hc'0, fun z ω => max (latticeSup V z ω) 8, gS.max_const (by norm_num), ?_⟩
  -- the almost sure set
  have aA := ae_all_iff.2 hTAae
  have aV := ae_all_iff.2 hTVae
  have aP := ae_all_iff.2 hTPae
  have aH := ae_all_iff.2 hTHae
  have aD := ae_all_iff.2 hTDae
  have aB := ae_all_iff.2 hTBae
  have aS := ae_all_iff.2 hbdd
  filter_upwards [aA, aV, aP, aH, aD, aB, aS, hH, hcorr] with ω hAω hVω hPω hHω hDω hBω hSω
    hLev hcω
  intro h z hz t ht1 htT x hx
  set K := uniqueInfiniteComponent h with hKdef
  have hball : ∀ w, latticeDist w z ≤ t + 1 → V w ω ≤ t := fun w hw =>
    le_of_latticeSup_le (hSω z) ((le_max_left _ _).trans htT) hw
  have ht8 : 8 ≤ t := (le_max_right _ _).trans htT
  have ht0 : 0 < t := by linarith
  have hr0 := latticeDist_nonneg x z
  by_cases hfarc : t ≤ latticeDist x z
  · -- the far region
    have hcv' := (hcv ω K (uniqueInfiniteComponent_infinite h) x hx z hz t ht0).2 hfarc
    have hb := hfar t (latticeDist x z) k' (openHeat ω t x z) ht1 hfarc hk'0 (by linarith)
      (openHeat_nonneg' ω ht0.le x z) hcv'
    rw [latticeGaussian_eq]
    refine hb.trans ?_
    apply mul_le_mul (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
      (Real.rpow_nonneg ht0.le _))
      (dgPhi_mono hcf ((le_max_left _ _).trans (le_max_right _ _)) ht0 hr0)
      (dgPhi_nonneg hcf.le ht0.le _) (by positivity)
  · push Not at hfarc
    set s := t / 2 with hsdef
    have hs1 : 1 ≤ s := by rw [hsdef]; linarith
    have hs0 : 0 < s := by linarith
    have hss : s + s = t := by rw [hsdef]; ring
    have hcorrK := (hcω h).1
    -- the weighted `L²` estimate (4.49) at a good point
    have hL2 : ∀ w ∈ K.supp, V w ω ≤ t →
        WeightedL2Le K.supp Cw s w
          (fun y => openHeat ω s y w - θ⁻¹ * latticeGaussian σ s y w)
          (cL * s ^ (-(1 / 2 : ℝ) - k')) := by
      intro w hw hVw
      have hQw : Q w ω ≤ s := by
        have : 2 * Q w ω ≤ V w ω := (le_max_left _ _).trans (le_max_left _ _)
        rw [hsdef]; linarith
      have hX0 : 0 ≤ X w ω := le_max_of_le_right zero_le_one
      have hXs : X w ω ≤ s ^ (1 - δ / 4) :=
        le_of_rpow_inv_le hX0 hκ1 ((le_max_left _ _).trans ((le_max_left _ _).trans hQw))
      have hTHs : TH w ω ≤ s := (le_max_right _ _).trans ((le_max_left _ _).trans hQw)
      have h3s : (3 : ℝ) ^ (1 / (δ / 4)) ≤ s := (le_max_right _ _).trans hQw
      set τ := s ^ (1 - δ / 4) with hτ
      have hτ1 : 1 ≤ τ := (le_max_right _ _).trans hXs
      have hτ0 : 0 < τ := by linarith
      have hTAw : TA w ω ≤ τ :=
        (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hXs))
      have hTVw : TV w ω ≤ τ :=
        (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hXs))
      have hTPw : TP w ω ≤ τ :=
        (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hXs))
      have hTw : T w ω ≤ τ :=
        (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hXs))
      have h3τ : 3 * τ ≤ s := by
        have h1 : (3 : ℝ) ≤ s ^ (δ / 4) := le_of_rpow_inv_le (by norm_num) hκ h3s
        have h2 : s ^ (δ / 4) * τ = s := by
          rw [hτ, ← Real.rpow_add hs0, show δ / 4 + (1 - δ / 4) = 1 by ring, Real.rpow_one]
        calc 3 * τ ≤ s ^ (δ / 4) * τ := mul_le_mul_of_nonneg_right h1 hτ0.le
          _ = s := h2
      obtain ⟨χ, hχ⟩ := exists_isDGCorrector hcorrK hw
      -- Lemma 4.1 fed with `H_k` at time `τ`
      have hε0 : 0 ≤ c * τ ^ (-k) := by positivity
      have hin : ∀ z' ∈ K.supp, |θ⁻¹ * latticeGaussian σ τ z' w - openHeat ω τ z' w| ≤
          c * τ ^ (-k) * dgPhi c τ (latticeDist z' w) := by
        intro z' hz'
        rw [abs_sub_comm]
        exact hLev h w hw τ hτ1 hTw z' hz'
      have hq := hAω w h hw s τ (c * τ ^ (-k)) hTAw h3τ hε0 hin
      have hv := hVω w h hw χ hχ s τ hTVw h3τ
      have hwt := hPω w h hw χ hχ s τ hTPw h3τ
      have hht := hHω w h hw χ hχ s hTHs
      have L1 := hMAb K.supp s hs1 w (fun y => dgQ ω σ θ s τ y w - openHeat ω s y w)
        (CA * (c * τ ^ (-k) * (τ / s) ^ (1 / 2 : ℝ) + τ ^ (-(1 / 2 : ℝ) + δ / 2)))
        (by positivity) hq
      have L2 := hMVb K.supp s hs1 w (fun y => dgV ω σ θ χ s τ y w)
        (CV * τ ^ (-(1 / 2 : ℝ) + δ / 2 / 2)) (by positivity) hv
      exact step_weightedL2 hδ hδ4 hs1 hc hCA hCV0 hCP hCH hMA hMV
        ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
        ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
        (fun y => by simp only [dgW]; ring) L1 L2 hwt hht
    -- the point `x` and the centre `z` are good
    have hVz : V z ω ≤ t := hball z (by rw [show latticeDist z z = 0 by simp [latticeDist]]; linarith)
    have hVx : V x ω ≤ t := hball x (by linarith)
    have hTBz : TB z ω ≤ s := by
      have : 2 * TB z ω ≤ V z ω := le_max_right _ _
      rw [hsdef]; linarith
    have hBarz : ∀ y ∈ K.supp, openHeat ω s y z ≤ dgPhi CB s (latticeDist y z) :=
      hBω z h hz s hs0 hTBz
    -- the term (4.48)-b
    obtain ⟨wm, hwm, hwmz⟩ := exists_lattice_near_midpoint x z
    have hVw : V wm ω ≤ t := hball wm (by linarith)
    have hTDw : TD wm ω < s / 2 := by
      have h1 : 8 * TD wm ω ≤ V wm ω :=
        (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
      rw [hsdef]; linarith
    have hdens := hDω wm h (s / 2) hTDw
    have hb := density_term_bound hθ hσ hLip K.supp (by linarith) x z wm hwm hdens
    have hpt := hpw ω K s (cL * s ^ (-(1 / 2 : ℝ) - k')) _ hs1 (by positivity) x hx z hz
      (hL2 x hx hVx) (hL2 z hz hVz) hBarz hb
    rw [hss] at hpt
    refine hpt.trans ?_
    have h2s : 2 * s = t := by rw [hsdef]; ring
    rw [h2s]
    have hG : latticeGaussian σ t x z ≤ dgPhi CG t (latticeDist x z) := by
      have := const_mul_latticeGaussian_le_dgPhi (c := 1) hσ ht0 (le_max_left _ _)
        (le_max_right _ _) x z
      rwa [one_mul] at this
    exact step_conversion ht8 hk'0 hk'1 hδ hM hcL0 hC₃ hML hCD hθ hCG0 hG hr0
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_right _ _))

end Rigidity.Green
