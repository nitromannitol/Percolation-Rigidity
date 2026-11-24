import Rigidity.Proofs.Green.DarioGuTwoScaleFluxBound
import Rigidity.Proofs.Green.DarioGuTwoScaleSourceBound

/-!
# Step 3 of Proposition 4.3 of Dario–Gu, and Proposition 4.3 from its inputs

`darioGuTwoScaleFluxTermTwo_of_inputs` proves the estimate of Step 3 of the proof of Proposition
4.3 of Dario–Gu (`DarioGuTwoScaleFluxTermTwo`, (4.30) after Young's inequality) from
Proposition 2.13 (`DarioGuFluxWeakNormTwo`, the weak norm of the centered flux) and Proposition
2.12 (R5, which gives the growth of the corrector and with it the absolute convergence of the
sums). For `r ≥ M(y) = max(M_flux², M_corr², 1)` every dyadic radius `2^{m+2} √r` is at least
`M_flux`, and `neg_tsum_flux_le` applies to the four components `(k, i)` of the flux.

`darioGuTwoScaleErrorTwo_of_inputs` is Proposition 4.3 of Dario–Gu (`DarioGuTwoScaleErrorTwo`)
from Proposition 2.13 and Proposition 2.12.
-/

open scoped Classical
open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

/-- The growth of the centered flux on the cluster. -/
theorem abs_centeredFlux_le {ω : Configuration 2} {K : OpenComponent ω} {σ C₅ β r : ℝ}
    {χ : Fin 2 → Vertex 2 → ℝ} {y : Vertex 2} (hσ : 0 ≤ σ) (hC₅ : 0 ≤ C₅) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hχb : ∀ z ∈ K.supp, ∀ k : Fin 2, |χ k z| ≤ C₅ * (Real.sqrt r + latticeDist z y + 2) ^ β)
    {x : Vertex 2} (hx : x ∈ K.supp) (k i : Fin 2) :
    |centeredFlux ω σ χ k i x| ≤
      (1 + σ / 2 + 2 * C₅) * (Real.sqrt r + latticeDist x y + 3) := by
  have hd := latticeDist_nonneg x y
  have hs := Real.sqrt_nonneg r
  set B := Real.sqrt r + latticeDist x y + 3 with hB
  have hB1 : 1 ≤ B := by linarith
  have hpow : ∀ z : Vertex 2, latticeDist z y ≤ latticeDist x y + 1 →
      (Real.sqrt r + latticeDist z y + 2) ^ β ≤ B := by
    intro z hz
    have hz0 := latticeDist_nonneg z y
    calc (Real.sqrt r + latticeDist z y + 2) ^ β ≤ B ^ β :=
          Real.rpow_le_rpow (by positivity) (by linarith) hβ0
      _ ≤ B ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 hβ1
      _ = B := Real.rpow_one B
  have h1 : |χ k x| ≤ C₅ * B :=
    (hχb x hx k).trans (mul_le_mul_of_nonneg_left (hpow x (by linarith)) hC₅)
  have hδ : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  have hδ0 : 0 ≤ (if i = k then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  unfold centeredFlux
  set δ : ℝ := if i = k then 1 else 0 with hδdef
  by_cases hadj : (openGraph ω).Adj x (x + Pi.single i 1)
  · rw [if_pos hadj]
    have hK' : x + Pi.single i 1 ∈ K.supp := K.mem_supp_of_adj_mem_supp hx hadj
    have hd' : latticeDist (x + Pi.single i 1) y ≤ latticeDist x y + 1 := by
      have h1 := latticeDist_add_single x i
      have h2 := latticeDist_triangle (x + Pi.single i 1) x y
      have h3 := latticeDist_comm x (x + Pi.single i 1)
      linarith
    have h2 : |χ k (x + Pi.single i 1)| ≤ C₅ * B :=
      (hχb _ hK' k).trans (mul_le_mul_of_nonneg_left (hpow _ hd') hC₅)
    calc |δ + (χ k (x + Pi.single i 1) - χ k x) - σ / 2 * δ|
        ≤ |δ| + (|χ k (x + Pi.single i 1)| + |χ k x|) + σ / 2 * |δ| := by
          refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add le_rfl (abs_sub _ _))) (le_of_eq ?_))
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ / 2)]
      _ ≤ 1 + (C₅ * B + C₅ * B) + σ / 2 * 1 := by gcongr
      _ ≤ (1 + σ / 2 + 2 * C₅) * B := by nlinarith
  · rw [if_neg hadj, zero_sub, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ / 2)]
    calc σ / 2 * |δ| ≤ σ / 2 * 1 := mul_le_mul_of_nonneg_left hδ (by positivity)
      _ ≤ (1 + σ / 2 + 2 * C₅) * B := by nlinarith

/-- The flux against the coefficient is square summable on the cluster. -/
theorem summable_sq_flux_coeff {σ : ℝ} (hσ : 0 < σ) : ∀ (C C₅ r R : ℝ) (ω : Configuration 2)
    (K : OpenComponent ω) (χ : Fin 2 → Vertex 2 → ℝ) (y : Vertex 2) (k i : Fin 2),
    128 * σ ≤ C → 0 ≤ C₅ → 1 ≤ r → 0 ≤ R →
    (∀ z ∈ K.supp, ∀ k : Fin 2, |χ k z| ≤ C₅ * (Real.sqrt r + latticeDist z y + 2) ^ (1 / 2 : ℝ)) →
    Summable fun x => (if x ∈ K.supp then centeredFlux ω σ χ k i x *
      (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x)
      else 0) ^ 2 := by
  obtain ⟨K₂, hK₂, h2⟩ := abs_secondDiff_mul_weight_le hσ
  obtain ⟨Q₀, hQ₀, hW⟩ := tsum_weightGauss_le (show 0 < 2 * σ by positivity)
  intro C C₅ r R ω K χ y k i hC hC₅ hr hR hχb
  have hr0 : 0 < r := by linarith
  obtain ⟨hs, -⟩ := hW (256 * σ) 1 r y (by linarith) zero_le_one le_rfl hr
  set c := 1 + σ / 2 + 2 * C₅ with hc
  set M := (c * (3 / 2) * (K₂ / r ^ 2)) ^ 2 with hM
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) (hs.mul_left M)
  split_ifs with hx
  · have hg := abs_centeredFlux_le hσ.le hC₅ (by norm_num) (by norm_num) hχb hx k i
    have hD := h2 C r R x y i k (by linarith) hr hR
    have hd := latticeDist_nonneg x y
    have hsr := Real.sqrt_nonneg r
    set B := Real.sqrt r + latticeDist x y + 2 with hB
    have hB3 : Real.sqrt r + latticeDist x y + 3 ≤ 3 / 2 * B := by linarith
    have hprod : |centeredFlux ω σ χ k i x *
        (fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x)| ≤
        c * (3 / 2) * (K₂ / r ^ 2) * (B * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r)))) := by
      rw [abs_mul]
      calc _ ≤ (c * (3 / 2 * B)) * (K₂ / r ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r)))) :=
            mul_le_mul (hg.trans (mul_le_mul_of_nonneg_left hB3 (by positivity))) hD
              (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hprod 2
    rw [sq_abs] at hsq
    refine hsq.trans ?_
    have hwg : B ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) ^ 2 ≤
        weightGauss (2 * σ) (256 * σ) 1 r y x := by
      unfold weightGauss
      rw [show 32 * (2 * σ) * r = 64 * σ * r by ring, mul_one, Real.rpow_two, ← hB]
      have h1 : 1 ≤ Real.exp (4 * latticeDist x y ^ 2 / (256 * σ * r)) :=
        Real.one_le_exp (by positivity)
      have h2' : 1 ≤ 1 + latticeDist x y ^ 2 / r := by
        have : 0 ≤ latticeDist x y ^ 2 / r := by positivity
        linarith
      have h0 : 0 ≤ B ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) ^ 2 := by positivity
      calc B ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) ^ 2
          ≤ Real.exp (4 * latticeDist x y ^ 2 / (256 * σ * r)) *
              (B ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) ^ 2) *
              (1 + latticeDist x y ^ 2 / r) := by
            have := mul_le_mul h1 h2' zero_le_one (by positivity)
            nlinarith
        _ = _ := by ring
    calc (c * (3 / 2) * (K₂ / r ^ 2) * (B * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))))) ^ 2
        = M * (B ^ 2 * Real.exp (-(latticeDist x y ^ 2 / (64 * σ * r))) ^ 2) := by
          rw [hM]
          ring
      _ ≤ M * weightGauss (2 * σ) (256 * σ) 1 r y x :=
          mul_le_mul_of_nonneg_left hwg (by positivity)
  · rw [sq, zero_mul]
    exact mul_nonneg (by positivity) (weightGauss_nonneg hr0 y x)

/-- **Step 3 of the proof of Proposition 4.3 of Dario–Gu** from Propositions 2.12 and 2.13. -/
theorem darioGuTwoScaleFluxTermTwo_of_inputs (hR5 : CorrectorQuantitativeInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hflux : DarioGuFluxWeakNormTwo p σ) : DarioGuTwoScaleFluxTermTwo p σ := by
  intro α hα
  set θ := theta 2 p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  set α' := min α 1 with hα'
  have hα'0 : 0 < α' := lt_min hα one_pos
  have hα'1 : α' ≤ 1 := min_le_right _ _
  have hα'α : α' ≤ α := min_le_left _ _
  obtain ⟨Cf, sf, hCf, hsf, hfl⟩ := hflux α' hα'0
  obtain ⟨s₅, C₅, hs₅, hC₅, h5⟩ := hR5 p hpc hp1 (1 / 2) (by norm_num)
  refine ⟨128 * σ, by positivity, fun C hC => ?_⟩
  obtain ⟨L, hL, hbound⟩ := neg_tsum_flux_le hσ hC
  choose Mf hMfm hMf0 hMfos hMfae using hfl
  choose M₅ hM5m hM50 hM5os hM5ae using h5
  set A := 4 * θ⁻¹ * L * Cf with hA
  set s := min (sf / 2) (s₅ / 2) with hs
  have hs0 : 0 < s := lt_min (by positivity) (by positivity)
  set θ1 := Cf ^ 2 * (6 : ℝ) ^ (1 / s) with hθ1
  set θ2 := C₅ ^ 2 * (6 : ℝ) ^ (1 / s) with hθ2
  set θ3 := (1 : ℝ) * (3 : ℝ) ^ (1 / s) with hθ3
  set θM := max (max θ1 θ2 * (4 : ℝ) ^ (1 / s)) θ3 * (4 : ℝ) ^ (1 / s) with hθM
  have hθM0 : 0 < θM := by positivity
  refine ⟨max (3 * A ^ 2) θM, s, lt_max_of_lt_right hθM0, hs0, fun y => ?_⟩
  set M : Configuration 2 → ℝ := fun ω => max (max (Mf y ω ^ 2) (M₅ y ω ^ 2)) 1 with hM
  have hMm : Measurable M :=
    (((hMfm y).pow_const 2).max ((hM5m y).pow_const 2)).max measurable_const
  have hos1 : IsOsBond 2 p (fun ω => Mf y ω ^ 2) s θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_left _ _) ((hMfm y).pow_const 2)
      (IsOsBond.sq_of_nonneg hCf (hMf0 y) (hMfos y))
  have hos2 : IsOsBond 2 p (fun ω => M₅ y ω ^ 2) s θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_right _ _) ((hM5m y).pow_const 2)
      (IsOsBond.sq_of_nonneg hC₅ (hM50 y) (hM5os y))
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
    ((hMfm y).pow_const 2) ((hM5m y).pow_const 2) hos1 hos2
  have hosM : IsOsBond 2 p M s θM :=
    Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
      (((hMfm y).pow_const 2).max ((hM5m y).pow_const 2)) measurable_const hos12
      (Rigidity.Proofs.S2.isOsBond_const one_pos hs0)
  refine ⟨M, hMm, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs0 hθM0 (le_max_right _ _) hMm hosM, ?_⟩
  filter_upwards [hMfae y, hM5ae y] with ω hωf hω5
  intro h hy χ hχ r hr R hR v hv hvK
  set K := uniqueInfiniteComponent h with hK
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hsqr : ∀ X : Configuration 2 → ℝ, (∀ ω, 0 ≤ X ω) →
      X ω ^ 2 ≤ r → X ω ≤ Real.sqrt r := by
    intro X hX0 hXr
    rw [← Real.sqrt_sq (hX0 ω)]
    exact Real.sqrt_le_sqrt hXr
  have hMfr : Mf y ω ≤ Real.sqrt r :=
    hsqr (Mf y) (hMf0 y) ((le_max_left _ _).trans ((le_max_left _ _).trans hr))
  have hM5r : M₅ y ω ≤ Real.sqrt r :=
    hsqr (M₅ y) (hM50 y) ((le_max_right _ _).trans ((le_max_left _ _).trans hr))
  -- the growth of the corrector on the cluster (Proposition 2.12)
  have hχb : ∀ x ∈ K.supp, ∀ k : Fin 2,
      |χ k x| ≤ C₅ * (Real.sqrt r + latticeDist x y + 2) ^ (1 / 2 : ℝ) := by
    intro x hx k
    obtain ⟨b', hadj, hb'd⟩ := exists_adj_near (uniqueInfiniteComponent_infinite h) ⟨x, hx⟩
    have hd0 := latticeDist_nonneg x y
    have hsq0 := Real.sqrt_nonneg r
    have hrr : M₅ y ω ≤ Real.sqrt r + latticeDist x y + 2 := by linarith
    have hb'y : latticeDist b'.val y ≤ latticeDist x y + 1 := by
      have := latticeDist_triangle b'.val x y
      rw [latticeDist_comm x b'.val] at this
      linarith
    have := hω5 h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 _ hrr
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
  -- the weak norm bounds on the dyadic balls (Proposition 2.13)
  have hWk : ∀ k i : Fin 2, ∀ m : ℕ, WeakNormLe ω (clusterBall K y (2 ^ (m + 2) * Real.sqrt r))
      (centeredFlux ω σ χ k i) (Cf * (2 ^ (m + 2) * Real.sqrt r) ^ α') := by
    intro k i m
    refine hωf h hy χ hχ _ ?_ k i
    have : Real.sqrt r ≤ 2 ^ (m + 2) * Real.sqrt r := by
      have h1 : (1 : ℝ) ≤ 2 ^ (m + 2) := one_le_pow₀ (by norm_num)
      nlinarith [Real.sqrt_nonneg r]
    linarith
  -- `u = ψ v`
  have hψb : ∀ x, |dgWeightTrunc C r R y x| ≤ Real.exp (R ^ 2 / r / C) := fun x =>
    abs_dgWeightTrunc_le (by linarith) hr0 hR y x
  have hus : Summable fun x => (dgWeightTrunc C r R y x * v x) ^ 2 :=
    summable_sq_mul_of_abs_le hψb hv
  have huK : ∀ x, x ∉ K.supp → dgWeightTrunc C r R y x * v x = 0 := fun x hx => by
    rw [hvK x hx, mul_zero]
  -- the four components
  have hGs : ∀ k i : Fin 2, Summable fun x => |centeredFlux ω σ χ k i x *
      ((fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x) *
        (dgWeightTrunc C r R y x * v x))| := by
    intro k i
    have hsq := summable_sq_flux_coeff hσ C C₅ r R ω K χ y k i hC hC₅.le hr1 hR hχb
    have hm := summable_mul_of_sq hsq hus
    refine hm.abs.congr fun x => ?_
    by_cases hx : x ∈ K.supp
    · rw [if_pos hx, mul_assoc]
    · rw [if_neg hx, hvK x hx]
      simp
  have hFk : ∀ k i : Fin 2, -(∑' x, centeredFlux ω σ χ k i x *
      ((fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x) *
        (dgWeightTrunc C r R y x * v x))) ≤
      L * Cf * r ^ (α' / 2) * (Real.sqrt (∑' x, (dgWeightTrunc C r R y x * v x) ^ 2) / r ^ 2 +
        Real.sqrt (openEnergy ω (fun x => dgWeightTrunc C r R y x * v x)) /
          (r * Real.sqrt r)) := fun k i =>
    hbound ω K y χ k i Cf α' r R (fun x => dgWeightTrunc C r R y x * v x) hCf.le hα'0 hα'1 hr1
      hR hus huK (hWk k i) (hGs k i)
  set Fl : Fin 2 → Fin 2 → Vertex 2 → ℝ := fun k i x => centeredFlux ω σ χ k i x *
    ((fwdDiff i (fwdDiff k fun z => latticeGaussian σ r z y) x * dgWeightTrunc C r R y x) *
      (dgWeightTrunc C r R y x * v x)) with hFl
  -- the identity `Σ ψ² v ξ = Σ_{k,i} Σ g̃ (D_i D_k p̄ ψ) (ψ v)`
  have hpt : ∀ x, dgWeightTrunc C r R y x ^ 2 * v x * clusterXi K σ χ r y x =
      ∑ k : Fin 2, ∑ i : Fin 2, Fl k i x := by
    intro x
    simp only [hFl, clusterXi]
    split_ifs with hx
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [hvK x hx]
      simp
  have hsumm : ∀ k i : Fin 2, Summable (Fl k i) := fun k i => (hGs k i).of_abs
  have hsumξ : Summable fun x => dgWeightTrunc C r R y x ^ 2 * v x * clusterXi K σ χ r y x := by
    simp only [hpt]
    exact summable_sum fun k _ => summable_sum fun i _ => hsumm k i
  refine ⟨hsumξ, ?_⟩
  have htsum : ∑' x, dgWeightTrunc C r R y x ^ 2 * v x * clusterXi K σ χ r y x =
      ∑ k : Fin 2, ∑ i : Fin 2, ∑' x, Fl k i x := by
    rw [tsum_congr hpt, Summable.tsum_finsetSum fun k _ =>
      summable_sum fun i _ => hsumm k i]
    exact Finset.sum_congr rfl fun k _ => Summable.tsum_finsetSum fun i _ => hsumm k i
  rw [htsum]
  -- the four bounds and Young's inequality
  set U := Real.sqrt (∑' x, (dgWeightTrunc C r R y x * v x) ^ 2) with hU
  set E := Real.sqrt (openEnergy ω (fun x => dgWeightTrunc C r R y x * v x)) with hE
  set ra := r ^ (α' / 2) with hra
  set Z := L * Cf * ra * (U / r ^ 2 + E / (r * Real.sqrt r)) with hZ
  have hsum4 : -(∑ k : Fin 2, ∑ i : Fin 2, ∑' x, Fl k i x) ≤ 4 * Z := by
    have e : -(∑ k : Fin 2, ∑ i : Fin 2, ∑' x, Fl k i x) =
        -(∑' x, Fl 0 0 x) + -(∑' x, Fl 0 1 x) + -(∑' x, Fl 1 0 x) + -(∑' x, Fl 1 1 x) := by
      simp only [Fin.sum_univ_two]
      ring
    rw [e]
    have h00 := hFk 0 0
    have h01 := hFk 0 1
    have h10 := hFk 1 0
    have h11 := hFk 1 1
    have e4 : 4 * Z = Z + Z + Z + Z := by ring
    rw [e4]
    exact add_le_add (add_le_add (add_le_add h00 h01) h10) h11
  have hθ0 : 0 ≤ θ⁻¹ := inv_nonneg.2 hθ.le
  have hstep : -(θ⁻¹ * ∑ k : Fin 2, ∑ i : Fin 2, ∑' x, Fl k i x) ≤ θ⁻¹ * (4 * Z) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hsum4 hθ0
  refine hstep.trans ?_
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hsr2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hEE : E ^ 2 = openEnergy ω (fun x => dgWeightTrunc C r R y x * v x) :=
    Real.sq_sqrt (tsum_nonneg fun x => Finset.sum_nonneg fun i _ =>
      mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _))
  have hUU : U ^ 2 = ∑' x, (dgWeightTrunc C r R y x * v x) ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun x => sq_nonneg _)
  have hra0 : 0 ≤ ra := Real.rpow_nonneg hr0.le _
  have hra2 : ra ^ 2 = r ^ α' := by
    rw [hra, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
    norm_num
  have hrα3 : r ^ α' / r ^ 3 = r ^ (α' - 3) := (rpow_sub_nat_eq hr0 α' 3 3 (by norm_num)).symm
  -- Young's inequality for the two terms
  have y1 : A * ra * (E / (r * Real.sqrt r)) ≤ E ^ 2 / 4 + A ^ 2 * r ^ (α' - 3) := by
    set z := A * ra / (r * Real.sqrt r) with hz
    have hr3 : (r * Real.sqrt r) ^ 2 = r ^ 3 := by
      rw [mul_pow, Real.sq_sqrt hr0.le]
      ring
    have hz2 : z ^ 2 = A ^ 2 * r ^ (α' - 3) := by
      calc z ^ 2 = (A * ra) ^ 2 / (r * Real.sqrt r) ^ 2 := by rw [hz, div_pow]
        _ = A ^ 2 * (ra ^ 2 / r ^ 3) := by rw [hr3]; ring
        _ = A ^ 2 * r ^ (α' - 3) := by rw [hra2, hrα3]
    have h := sq_nonneg (E / 2 - z)
    have e2 : A * ra * (E / (r * Real.sqrt r)) = E * z := by
      rw [hz]
      ring
    have e3 : E ^ 2 / 4 + z ^ 2 - E * z = (E / 2 - z) ^ 2 := by ring
    rw [e2, ← hz2]
    linarith only [e3, h]
  have y2 : A * ra * (U / r ^ 2) ≤ 1 / (8 * r) * U ^ 2 + 2 * A ^ 2 * r ^ (α' - 3) := by
    set w := A * ra / r ^ 2 with hw
    have key : U * w ≤ 1 / (8 * r) * U ^ 2 + 2 * r * w ^ 2 := by
      have h := sq_nonneg (U - 4 * r * w)
      have e : 1 / (8 * r) * U ^ 2 + 2 * r * w ^ 2 - U * w = (U - 4 * r * w) ^ 2 / (8 * r) := by
        field_simp
        ring
      have h0 : 0 ≤ (U - 4 * r * w) ^ 2 / (8 * r) := by positivity
      linarith only [e, h0]
    have e1 : A * ra * (U / r ^ 2) = U * w := by
      rw [hw]
      ring
    have e2 : 2 * r * w ^ 2 = 2 * A ^ 2 * r ^ (α' - 3) := by
      rw [← hrα3, ← hra2, hw]
      field_simp
    rw [e1, ← e2]
    exact key
  have hZe : θ⁻¹ * (4 * Z) = A * ra * (U / r ^ 2) + A * ra * (E / (r * Real.sqrt r)) := by
    rw [hZ, hA]
    ring
  have hpow : r ^ (α' - 3) ≤ r ^ (α - 3) := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hpos : 0 ≤ r ^ (α' - 3) := Real.rpow_nonneg hr0.le _
  have hQ : 3 * A ^ 2 * r ^ (α' - 3) ≤ max (3 * A ^ 2) θM * r ^ (α - 3) :=
    mul_le_mul (le_max_left _ _) hpow hpos (le_trans (by positivity) (le_max_left _ _))
  rw [hZe, ← hEE, ← hUU]
  calc A * ra * (U / r ^ 2) + A * ra * (E / (r * Real.sqrt r))
      ≤ (1 / (8 * r) * U ^ 2 + 2 * A ^ 2 * r ^ (α' - 3)) +
          (E ^ 2 / 4 + A ^ 2 * r ^ (α' - 3)) := add_le_add y2 y1
    _ = E ^ 2 / 4 + 1 / (8 * r) * U ^ 2 + 3 * A ^ 2 * r ^ (α' - 3) := by ring
    _ ≤ E ^ 2 / 4 + 1 / (8 * r) * U ^ 2 + max (3 * A ^ 2) θM * r ^ (α - 3) := by
        linarith only [hQ]

/-- **Proposition 4.3 of Dario–Gu** (`DarioGuTwoScaleErrorTwo`) from Proposition 2.13
(`DarioGuFluxWeakNormTwo`) and Proposition 2.12 (R5). -/
theorem darioGuTwoScaleErrorTwo_of_inputs (hR5 : CorrectorQuantitativeInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hσ : 0 < σ) (hflux : DarioGuFluxWeakNormTwo p σ) : DarioGuTwoScaleErrorTwo p σ :=
  darioGuTwoScaleErrorTwo_of_fluxTerm hR5 hpc hp1 hσ
    (darioGuTwoScaleFluxTermTwo_of_inputs hR5 hpc hp1 hσ hflux)

end Rigidity.Green
