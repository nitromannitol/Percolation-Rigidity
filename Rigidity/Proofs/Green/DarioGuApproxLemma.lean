import Rigidity.Proofs.Green.DarioGuApproxEstimate
import Rigidity.Proofs.Green.DarioGuDensityGaussian
import PercolationClusterHomogenization.Proofs.Density.ClusterDensityConcentration

/-!
# Lemma 4.1 of Dario–Gu in dimension two

`darioGuApproxLemmaTwo_of_inputs`: Lemma 4.1 of Dario–Gu in the form used in the iteration of
§4.3 (`DarioGuApproxLemmaTwo`) holds for every diffusivity `σ > 0`, from

* Theorem 3 in the form of Remark 1.3 (`DarioGuGradientBoundTwo`, proved in §3 of the source and
  here as `darioGuGradientBoundTwo_holds`),
* the Poincaré inequality, Proposition 2.7 (`ClusterPoincareTwo`, proved as
  `clusterPoincareTwo_holds`),
* Theorem 4 (`BarlowGaussianUpperBoundTwo`) and Proposition 2.15 (`CarneVaropoulosTwo`), proved as
  `barlowGaussianUpperBoundTwo_holds` and `carneVaropoulosTwo_holds`,

with Proposition A.7 (`darioGuDensityGaussianTwo_holds`) and the lower bound on the volume of the
cluster in balls from Proposition A.1 (`clusterDensityInputFaithful_of_concentration`).

The minimal time is `T(y) = max(M_reg(y)², M_Poinc(y)², M_dens(y)², 2 max(T_dense,α(y), 1),
T'_NA(y), 1)`, with `T'_NA(y)` the supremum of the times of Theorem 4 at the points `z` with
`|z - y| ≤ T_NA(z) + 1` (as in Lemma 4.2), so that every `τ ≥ T(y)` satisfies the assumptions of
`approx_estimate` at time `τ` and `t - τ ≥ 2τ`. The source takes
`T_approx,α(y) = max(M_reg(y)², T_dense,α(y))` and uses the other minimal times in the proof
(lines 1995-1998); the lower bound `|𝒞_∞ ∩ B_√τ(y)| ≥ c τ` stated "under the assumption
`T_dense`" (line 2000) is taken from Proposition A.1 through `M_dens`.
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green

variable {p : unitInterval}

/-- `|{z ∈ K : |z - y| < r}| = |K ∩ B_r(y)|`. -/
theorem ncard_eq_card_clusterBall {ω : Configuration 2} (K : OpenComponent ω) (y : Vertex 2)
    (r : ℝ) :
    ({z : K | dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding y) < r}.ncard) =
      (clusterBall K y r).card := by
  set S := {z : K | dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding y) < r}
  rw [← Set.ncard_image_of_injective S Subtype.val_injective, ← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Set.mem_image, Finset.mem_coe, mem_clusterBall, S, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, by rw [dist_eq_norm] at hz; exact hz⟩
  · rintro ⟨hv, hd⟩
    exact ⟨⟨v, hv⟩, by rw [dist_eq_norm]; exact hd, rfl⟩

/-- **Dario–Gu, Lemma 4.1** (in the form of the iteration step of §4.3) in dimension two, from
Theorem 3, Proposition 2.7, Theorem 4 and Proposition 2.15. -/
theorem darioGuApproxLemmaTwo_of_inputs (hG3 : DarioGuGradientBoundTwo)
    (hPo : ClusterPoincareTwo) (hBar : BarlowGaussianUpperBoundTwo) (hCV : CarneVaropoulosTwo)
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ} (hσ : 0 < σ) :
    DarioGuApproxLemmaTwo p σ := by
  intro α hα C₀ hC₀
  set θ := theta 2 p with hθdef
  have hθ : 0 < θ := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  -- the inputs
  obtain ⟨CA, sA, hCA, hsA, hA⟩ := darioGuDensityGaussianTwo_holds hpc hp1 hσ α hα
  choose TA hTAm hTA0 hTAos hTAae using hA
  obtain ⟨sP, CP, CL, hsP, hCP, hCL, hP⟩ := hPo p hpc hp1
  choose MP hMPm hMP0 hMPos hMPae using hP
  obtain ⟨sG, CG, hsG, hCG, hG⟩ := hG3 p hpc hp1
  choose MG hMGm hMG0 hMGt hMGae using hG
  obtain ⟨sD, CD, cD, hsD, hCD, hcD, hD⟩ :=
    Rigidity.Proofs.S2.clusterDensityInputFaithful_of_concentration
      Rigidity.Proofs.S2.cluster_density_concentration 2 le_rfl p hpc hp1
  choose MD hMDm hMD0 hMDos hMDae using hD
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
  -- the minimal scale of Theorem 3 in `O_s` form
  set CG' := max CG 1 with hCG'
  have hCG'1 : 1 ≤ CG' := le_max_right _ _
  set θG := (CG' * (1 + Real.log CG')) ^ (1 / sG) with hθG
  have hθG0 : 0 < θG := Real.rpow_pos_of_pos (by
    have := Real.log_nonneg hCG'1; positivity) _
  have hGos : ∀ y, IsOsBond 2 p (MG y) sG (θG * (2 : ℝ) ^ (1 / sG) * Real.exp 2 ^ (1 / sG)) :=
    fun y => Rigidity.Proofs.Cluster.isOsBond_of_osBound hsG hθG0 (hMGm y)
      (osBound_of_hasTail hCG'1 hsG ((hMGt y).mono hCG (le_max_left _ _)))
  -- the deterministic estimate
  obtain ⟨Cest, hCest, hest⟩ := approx_estimate (α := α) (CA := CA) hσ hθ hC₀ hCB hCcv hCP hCL hCG
    (by positivity : (0 : ℝ) < cD * 100 ^ 2)
  -- the exponent and the scale of the minimal time
  set s' := min (min (min (sG / 2) (sP / 2)) (min (sD / 2) sA)) sS with hs'
  have hs'0 : 0 < s' := lt_min (lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) hsA)) hsS
  set θ1 := (θG * (2 : ℝ) ^ (1 / sG) * Real.exp 2 ^ (1 / sG)) ^ 2 * (6 : ℝ) ^ (1 / s') with hθ1
  set θ2 := CP ^ 2 * (6 : ℝ) ^ (1 / s') with hθ2
  set θ3 := CD ^ 2 * (6 : ℝ) ^ (1 / s') with hθ3
  set θ4 := 2 * (max (CA * (6 : ℝ) ^ (1 / s')) (1 * 3 ^ (1 / s')) * (4 : ℝ) ^ (1 / s')) with hθ4
  set θ5 := θS * (2 : ℝ) ^ (1 / sS) * Real.exp 2 ^ (1 / sS) * (6 : ℝ) ^ (1 / s') with hθ5
  set θ6 := (1 : ℝ) * (3 : ℝ) ^ (1 / s') with hθ6
  set θ12 := max θ1 θ2 * (4 : ℝ) ^ (1 / s') with hθ12
  set θ34 := max θ3 θ4 * (4 : ℝ) ^ (1 / s') with hθ34
  set θ56 := max θ5 θ6 * (4 : ℝ) ^ (1 / s') with hθ56
  set θ1234 := max θ12 θ34 * (4 : ℝ) ^ (1 / s') with hθ1234
  set θM := max θ1234 θ56 * (4 : ℝ) ^ (1 / s') with hθM
  set Cf := max Cest θM with hCf
  have hCf0 : 0 < Cf := lt_max_of_lt_left hCest
  refine ⟨Cf, s', hCf0, hs'0, fun y => ?_⟩
  -- the minimal time
  set M : Configuration 2 → ℝ := fun ω =>
    max (max (max (MG y ω ^ 2) (MP y ω ^ 2)) (max (MD y ω ^ 2) (2 * max (TA y ω) 1)))
      (max (latticeSup TB y ω) 1) with hM
  have hm1 : Measurable fun ω => MG y ω ^ 2 := (hMGm y).pow_const 2
  have hm2 : Measurable fun ω => MP y ω ^ 2 := (hMPm y).pow_const 2
  have hm3 : Measurable fun ω => MD y ω ^ 2 := (hMDm y).pow_const 2
  have hm4 : Measurable fun ω => 2 * max (TA y ω) 1 :=
    measurable_const.mul ((hTAm y).max measurable_const)
  have hm12 := hm1.max hm2
  have hm34 := hm3.max hm4
  have hm56 : Measurable fun ω => max (latticeSup TB y ω) 1 := (hSm y).max measurable_const
  have hMm : Measurable M := (hm12.max hm34).max hm56
  have hos1 : IsOsBond 2 p (fun ω => MG y ω ^ 2) s' θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))) hm1
      (IsOsBond.sq_of_nonneg (by positivity) (hMG0 y) (hGos y))
  have hos2 : IsOsBond 2 p (fun ω => MP y ω ^ 2) s' θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))) hm2
      (IsOsBond.sq_of_nonneg hCP (hMP0 y) (hMPos y))
  have hos3 : IsOsBond 2 p (fun ω => MD y ω ^ 2) s' θ3 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0
      ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hm3
      (IsOsBond.sq_of_nonneg hCD (hMD0 y) (hMDos y))
  have hos4 : IsOsBond 2 p (fun ω => 2 * max (TA y ω) 1) s' θ4 := by
    have hA' := Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0
      ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) (hTAm y) (hTAos y)
    have h1 := Rigidity.Proofs.S2.isOsBond_const (d := 2) (p := p) one_pos hs'0
    have hmax := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity) (hTAm y)
      measurable_const hA' h1
    exact Rigidity.Proofs.S2.IsOsBond.const_mul two_pos hmax
  have hos5 : IsOsBond 2 p (latticeSup TB y) s' θ5 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs'0 (min_le_right _ _) (hSm y) (hSos y)
  have hos6 : IsOsBond 2 p (fun _ => (1 : ℝ)) s' θ6 :=
    Rigidity.Proofs.S2.isOsBond_const one_pos hs'0
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity) hm1 hm2
    hos1 hos2
  have hos34 := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity) hm3 hm4
    hos3 hos4
  have hos56 := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity) (hSm y)
    measurable_const hos5 hos6
  have hos1234 := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity) hm12 hm34
    hos12 hos34
  have hosM := Rigidity.Proofs.S2.IsOsBond.max hs'0 (by positivity) (by positivity)
    (hm12.max hm34) hm56 hos1234 hos56
  refine ⟨M, hMm, fun ω => le_max_of_le_right (le_max_of_le_right zero_le_one),
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs'0 (by positivity) (le_max_right _ _) hMm hosM, ?_⟩
  filter_upwards [hTAae y, hMPae y, hMGae y, hMDae y, ae_all_iff.2 hTBae, hbdd y] with ω hAω hPω
    hGω hDω hBω hbω
  intro h hy t τ ε hMτ h3τ hε hw x hx
  set K := uniqueInfiniteComponent h with hK
  -- the minimal times at `ω`
  have hM1 : MG y ω ^ 2 ≤ τ := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hMτ))
  have hM2 : MP y ω ^ 2 ≤ τ := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_left _ _).trans hMτ))
  have hM3 : MD y ω ^ 2 ≤ τ := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hMτ))
  have hM4 : 2 * max (TA y ω) 1 ≤ τ := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_left _ _).trans hMτ))
  have hM5 : latticeSup TB y ω ≤ τ := (le_max_left _ _).trans ((le_max_right _ _).trans hMτ)
  have hτ1 : 1 ≤ τ := (le_max_right _ _).trans ((le_max_right _ _).trans hMτ)
  have hτ0 : 0 < τ := by linarith
  have hsqrt : ∀ {a : ℝ}, 0 ≤ a → a ^ 2 ≤ τ → a ≤ Real.sqrt τ := fun ha h2 => by
    rw [← Real.sqrt_sq ha]; exact Real.sqrt_le_sqrt h2
  have hMGτ := hsqrt (hMG0 y ω) hM1
  have hMPτ := hsqrt (hMP0 y ω) hM2
  have hMDτ := hsqrt (hMD0 y ω) hM3
  have hTAτ : TA y ω < τ := by
    have := le_max_left (TA y ω) 1
    have := le_max_right (TA y ω) 1
    linarith
  set s := t - τ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hSs : latticeSup TB y ω ≤ s := hM5.trans (by rw [hsdef]; linarith)
  -- the deterministic estimate
  have hmass := hAω h τ hTAτ
  rw [show -(1 / 2 - α) = -(1 / 2 : ℝ) + α by ring] at hmass
  have hvol : cD * 100 ^ 2 * τ ≤ (clusterBall K y (Real.sqrt τ)).card := by
    have h1 := hDω h (100 * Real.sqrt τ) (by linarith [Real.sqrt_nonneg τ])
      (latticeEuclideanEmbedding y) (by
        rw [dist_self]
        have := Real.sqrt_pos.2 hτ0
        positivity)
    rw [show 100 * Real.sqrt τ / 100 = Real.sqrt τ by ring, ncard_eq_card_clusterBall] at h1
    calc cD * 100 ^ 2 * τ = cD * (100 * Real.sqrt τ) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hτ0.le]; ring
      _ ≤ _ := h1
  have hBnear : ∀ z ∈ K.supp, latticeDist z y ≤ s + 1 →
      openHeat ω s x z ≤ dgPhi CB s (latticeDist x z) := by
    intro z hz hnear
    exact hBω z h hz s hs0 (le_of_latticeSup_le hbω hSs hnear) x hx
  have hcv' := fun z (hz : z ∈ K.supp) => hcv ω K (uniqueInfiniteComponent_infinite h) x hx z hz s
    hs0
  have hbound := hest ω K x y t τ ε hτ1 h3τ hε hx hy hw hmass
    (fun R hR u => hPω h R (hMPτ.trans hR) u)
    (fun R hR h4 hd => hGω h R (hMGτ.trans hR) x hx s h4 hd) hvol hBnear hcv'
  refine hbound.trans ?_
  have ht0 : 0 < t := by linarith
  have hfac : 0 ≤ ε * (τ / t) ^ (1 / 2 : ℝ) + τ ^ (-(1 / 2 : ℝ) + α) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hfac)
    (dgPhi_mono hCest (le_max_left _ _) ht0 (latticeDist_nonneg x y))
    (dgPhi_nonneg hCest.le ht0.le _) (mul_nonneg hCf0.le hfac)

end Rigidity.Green
