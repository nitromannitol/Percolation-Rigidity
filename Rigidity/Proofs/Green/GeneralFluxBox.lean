import Rigidity.Proofs.Green.GeneralFluxDyadic
import Rigidity.Proofs.Green.GeneralFluxSpatialAverage
import Rigidity.Proofs.Green.DarioGuFluxWeakNormBox

/-!
# The weak norm of the centered flux on boxes of `ℤ^d`

The extension of `DarioGuFluxWeakNormBox.lean` from `ℤ²` to `ℤ^d`: the estimate (eq.gsmallH-1) of
Dario–Gu, Appendix B, in the lattice form of `GeneralFluxDyadic`. For the centered flux
`g = a(Dχ_{e_k} + e_k) - ā e_k` on `ℤ^d` (component `i`, zero off the infinite cluster), every
finite set `S`, every `J` and every `w` vanishing off `S` with gradient supported in `T`,

`|Σ_S g w| ≤ Y ‖w‖_{ℓ²(S)} + Z ‖∇w‖_{ℓ²(T)}`

almost surely (`exists_fluxWeakNormBoxD`), where `Y` and `Z` do not depend on `w` and have moments
`E[Y^q] ≤ (A √|S| 2^{-J} q^κ)^q` and `E[Z^q] ≤ (A (J + 1) √|T| q^κ)^q`. The heat averages of the
centered flux at the dyadic times `4^j ≥ 1` are bounded by Gu's Proposition 1.1
(`exists_fluxSpatialAverageD`, used in the weaker form `O_s(C/r)` valid for `d ≥ 2`), and the times
below `2` by the moments of the flux itself, from the Lipschitz bound of the corrected planes
(Dario, Proposition 2.15, `lipschitz_correctedPlane_origin`), which is (fluxbounded.est). The bound
takes (3.4) as the hypothesis `FluxVarianceBoundD`, which is proved for `d = 2`
(`fluxVarianceBoundD_two`) and for every `d ≥ 3` (`fluxVarianceBoundThree_of_stepTwoWeight`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare.GeneralDim
  Rigidity.Corrector Rigidity.Percolation Rigidity.External Rigidity.Section3 Rigidity.Steps.S3
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} [NeZero d] {p : unitInterval}

omit [NeZero d] in
/-- **A corrected plane grows at most linearly.** -/
theorem exists_abs_le_of_isCorrectedPlaneD {ω : Configuration d} {C : OpenComponent ω}
    {q : Fin d → ℝ} {ℓ : C → ℝ} (hℓ : IsCorrectedPlane C q ℓ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : C, |ℓ z| ≤ B * (1 + ‖latticeEuclideanEmbedding z.val‖) := by
  obtain ⟨R₀, hR₀, hR⟩ := hℓ.2 1 one_pos
  refine ⟨∑ i, |q i| + R₀ + 1, by positivity, fun z => ?_⟩
  set n := ‖latticeEuclideanEmbedding z.val‖
  have hn : 0 ≤ n := norm_nonneg _
  have hz : z ∈ componentEuclideanBall C 0 (R₀ + n + 1) := by
    rw [mem_componentEuclideanBall]
    have : dist (latticeEuclideanEmbedding z.val)
        (latticeEuclideanEmbedding (0 : Vertex d)) = n := by
      rw [dist_eq_norm, ← LatticeProb.Percolation.latticeEuclideanEmbedding_sub, sub_zero]
    rw [this]
    linarith
  have h1 := hR (R₀ + n + 1) (by linarith) z hz
  rw [one_mul] at h1
  have hslope : |componentSlope C q z| ≤ (∑ i, |q i|) * n := by
    unfold componentSlope
    calc |∑ i, q i * (z.val i : ℝ)| ≤ ∑ i, |q i * (z.val i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |q i| * n := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (GeneralDim.abs_coord_le_norm z.val i) (abs_nonneg _)
      _ = (∑ i, |q i|) * n := by rw [Finset.sum_mul]
  have hq0 : 0 ≤ ∑ i, |q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc |ℓ z| ≤ |ℓ z - componentSlope C q z| + |componentSlope C q z| := by
        have := abs_add_le (ℓ z - componentSlope C q z) (componentSlope C q z)
        rwa [sub_add_cancel] at this
    _ ≤ (R₀ + n + 1) + (∑ i, |q i|) * n := add_le_add h1 hslope
    _ ≤ (∑ i, |q i| + R₀ + 1) * (1 + n) := by nlinarith

omit [NeZero d] in
theorem norm_latticeEuclideanEmbedding_add_unit_le (z : Vertex d) (i : Fin d) :
    ‖latticeEuclideanEmbedding (z + unit i)‖ ≤ ‖latticeEuclideanEmbedding z‖ + 1 := by
  have e : latticeEuclideanEmbedding (z + unit i) =
      latticeEuclideanEmbedding z + (latticeEuclideanEmbedding (unit i : Vertex d) -
        latticeEuclideanEmbedding 0) := by
    rw [Rigidity.Corrector.GeneralDim.latticeEuclideanEmbedding_zero, sub_zero]
    have := LatticeProb.Percolation.latticeEuclideanEmbedding_sub (z + unit i) z
    rw [add_sub_cancel_left] at this
    rw [this]
    abel
  rw [e]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl (Rigidity.Proofs.S3.FluxEvent.norm_latticeEuclideanEmbedding_unit_sub_zero i))

section Flux

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

omit [NeZero d] in
/-- **The flux grows at most linearly** on `G`. -/
theorem exists_abs_fluxValD_le {k i : Fin d} {ω : Configuration d} (hω : ω ∈ G) :
    ∃ A : ℝ, ∀ z : Vertex d, |fluxValD hG hGv k ω z i| ≤
      A * (1 + ‖latticeEuclideanEmbedding z‖) := by
  obtain ⟨h, -⟩ := hGv hω
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) (uniqueInfiniteComponent_infinite h)
    (Pi.single k 1)
  obtain ⟨B, hB, hBℓ⟩ := exists_abs_le_of_isCorrectedPlaneD hℓ
  refine ⟨3 * B, fun z => ?_⟩
  have hext : ∀ w : Vertex d, |Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ w| ≤
      B * (1 + ‖latticeEuclideanEmbedding w‖) := by
    intro w
    by_cases hw : w ∈ (uniqueInfiniteComponent h).supp
    · rw [show Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ w = ℓ ⟨w, hw⟩ from dif_pos hw]
      exact hBℓ ⟨w, hw⟩
    · rw [show Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ w = 0 from dif_neg hw, abs_zero]
      positivity
  have hhead := norm_latticeEuclideanEmbedding_add_unit_le z i
  rw [fluxValD_eq_edgeDifference hG hGv hω h hℓ z i]
  unfold edgeDifference
  split_ifs
  · calc |Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ (z + unit i) - Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ z|
        ≤ |Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ (z + unit i)| + |Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ z| :=
          abs_sub _ _
      _ ≤ B * (1 + ‖latticeEuclideanEmbedding (z + unit i)‖) +
          B * (1 + ‖latticeEuclideanEmbedding z‖) := add_le_add (hext _) (hext _)
      _ ≤ 3 * B * (1 + ‖latticeEuclideanEmbedding z‖) := by
          nlinarith [norm_nonneg (latticeEuclideanEmbedding z)]
  · rw [abs_zero]
    positivity

/-- On `G`, the centered flux is summable against every heat kernel and its heat average at time
`r²` is the heat average `fluxObsD` of the flux minus the constant. -/
theorem heatAvgD_flux_eq {k i : Fin d} {ω : Configuration d} (hω : ω ∈ G) (c : ℝ) :
    HeatSummableAllD (fun z => fluxValD hG hGv k ω z i - c) ∧ ∀ r : ℝ, 0 < r → ∀ u : Vertex d,
      heatAvgD (r ^ 2) (fun z => fluxValD hG hGv k ω z i - c) u =
        fluxObsD hG hGv k i r u ω - c := by
  obtain ⟨A, hgrow⟩ := exists_abs_fluxValD_le hG hGv (k := k) (i := i) hω
  have hsum : HeatSummableAllD (fun z => fluxValD hG hGv k ω z i) :=
    heatSummableAllD_of_abs_le hgrow
  refine ⟨heatSummableAllD_of_abs_le (A := |A| + |c|) fun z => ?_, fun r hr u => ?_⟩
  · have h1 := hgrow z
    have h2 : 0 ≤ ‖latticeEuclideanEmbedding z‖ := norm_nonneg _
    have h3 : A * (1 + ‖latticeEuclideanEmbedding z‖) ≤ |A| * (1 + ‖latticeEuclideanEmbedding z‖) :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    calc |fluxValD hG hGv k ω z i - c| ≤ |fluxValD hG hGv k ω z i| + |c| := abs_sub _ _
      _ ≤ (|A| + |c|) * (1 + ‖latticeEuclideanEmbedding z‖) := by
          nlinarith [abs_nonneg c, abs_nonneg A]
  · have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have hs1 := hsum.summable hr2 u
    have hs2 := (hasSum_zdHeat hr2 u).summable
    unfold heatAvgD
    rw [show (fun z => zdHeat d (r ^ 2) u z * (fluxValD hG hGv k ω z i - c)) =
        fun z => zdHeat d (r ^ 2) u z * fluxValD hG hGv k ω z i -
          zdHeat d (r ^ 2) u z * c from funext fun z => mul_sub _ _ _,
      hs1.tsum_sub (hs2.mul_right c), tsum_mul_right, (hasSum_zdHeat hr2 u).tsum_eq, one_mul]
    rfl

omit [NeZero d] in
/-- **Moments of powers.** -/
theorem GrowthMomentsD.pow_nat {Y : Configuration d → ℝ≥0∞} {B κ : ℝ} (hB : 0 ≤ B)
    (h : GrowthMomentsD p Y B κ) (n : ℕ) (hn : 1 ≤ n) :
    GrowthMomentsD p (fun ω => Y ω ^ (n : ℝ)) (B ^ n * (n : ℝ) ^ (n * κ)) (n * κ) := by
  intro q hq
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnq : 1 ≤ (n : ℝ) * q := by nlinarith
  have hq0 : 0 ≤ q := by linarith
  have e1 : (fun ω => (Y ω ^ (n : ℝ)) ^ q) = fun ω => Y ω ^ ((n : ℝ) * q) := by
    funext ω
    rw [← ENNReal.rpow_mul]
  rw [e1]
  refine (h _ hnq).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hx : 0 ≤ B * ((n : ℝ) * q) ^ κ := by positivity
  rw [Real.rpow_mul hx]
  congr 1
  rw [Real.mul_rpow hB (by positivity), ← Real.rpow_mul (by positivity),
    Real.mul_rpow hn0 hq0, Real.rpow_natCast, mul_comm κ (n : ℝ)]
  ring

/-- The moments of the centered flux at a point, from the Lipschitz bound of the corrector and the
stationarity of the flux. -/
theorem exists_growthMomentsD_flux (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {abar : ℝ} (habar : 0 ≤ abar) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧ ∀ (k i : Fin d) (u : Vertex d),
      GrowthMomentsD p (fun ω =>
        ENNReal.ofReal |fluxValD hG hGv k ω u i - if i = k then abar else 0|) B κ := by
  obtain ⟨s, θ, L, hs, hθ, hL, X, hXm, hX0, hXos, hlip⟩ :=
    Rigidity.Corrector.GeneralDim.lipschitz_correctedPlane_origin hd hpc hp1
  set θ₂ : ℝ := max θ (2 * 3 ^ (1 / s)) * 4 ^ (1 / s) with hθ₂
  have hθ₂0 : 0 < θ₂ := by positivity
  have hX2 : IsOsBond d p (fun ω => max (X ω) 2) s θ₂ :=
    Rigidity.Proofs.S2.IsOsBond.max hs hθ (by positivity) hXm measurable_const hXos
      (Rigidity.Proofs.S2.isOsBond_const (by norm_num) hs)
  have hM := growthMomentsD_of_isOsBond (p := p)
    (fun ω => le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_right (X ω) 2)) hs hθ₂0 hX2
  set B₀ : ℝ := 2 * θ₂ * (1 / s) ^ (1 / s) with hB₀
  set κ₀ : ℝ := 1 / s with hκ₀
  have hMd := hM.pow_nat (by positivity) d (by omega)
  have hY := hMd.const_mul (c := L + abar) (by positivity) (by positivity)
  refine ⟨(L + abar) * (B₀ ^ d * (d : ℝ) ^ (d * κ₀)), d * κ₀, by positivity, by positivity,
    fun k i u => ?_⟩
  have hpt0 : ∀ᵐ ω ∂latticeBondLaw d p,
      ENNReal.ofReal |fluxValD hG hGv k ω 0 i - if i = k then abar else 0| ≤
        ENNReal.ofReal (L + abar) * ENNReal.ofReal (max (X ω) 2) ^ (d : ℝ) := by
    filter_upwards [hGae, hlip] with ω hω hb
    obtain ⟨h, -⟩ := hGv hω
    obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω)
      (uniqueInfiniteComponent_infinite h) (Pi.single k 1)
    set M := max (X ω) 2 with hMdef
    have hM2 : (2 : ℝ) ≤ M := le_max_right _ _
    have hM1 : 1 ≤ M ^ d := one_le_pow₀ (by linarith)
    have hflux : |fluxValD hG hGv k ω 0 i| ≤ L * M ^ d := by
      rw [fluxValD_eq_edgeDifference hG hGv hω h hℓ 0 i, zero_add]
      unfold edgeDifference
      split_ifs with h0
      · have h0' : (0 : Vertex d) ∈ (uniqueInfiniteComponent h).supp :=
          (uniqueInfiniteComponent h).mem_supp_of_adj_mem_supp h0.1 h0.2
        let a : uniqueInfiniteComponent h := ⟨unit i, h0.1⟩
        let b : uniqueInfiniteComponent h := ⟨0, h0'⟩
        have hab : (componentGraph (uniqueInfiniteComponent h)).Adj a b :=
          ((uniqueInfiniteComponent h).toSimpleGraph_adj a.2 b.2).2 h0.2
        have hna : ‖latticeEuclideanEmbedding a.val‖ < 2 := by
          have := Rigidity.Proofs.S3.FluxEvent.norm_latticeEuclideanEmbedding_unit_sub_zero
            (d := d) i
          rw [Rigidity.Corrector.GeneralDim.latticeEuclideanEmbedding_zero, sub_zero] at this
          exact this.trans_lt (by norm_num)
        have hbd := hb h (Pi.single k 1) ℓ hℓ a b hab hna
        rw [sum_abs_singleD, mul_one] at hbd
        have ea : Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ (unit i) = ℓ a :=
          dif_pos h0.1
        have eb : Rigidity.Section3.extend (uniqueInfiniteComponent h) ℓ 0 = ℓ b := dif_pos h0'
        rw [ea, eb]
        exact hbd
      · rw [abs_zero]
        positivity
    have hc : |(if i = k then abar else 0)| ≤ abar := by
      split_ifs
      · exact (abs_of_nonneg habar).le
      · rw [abs_zero]; exact habar
    rw [ENNReal.ofReal_rpow_of_nonneg (by linarith : (0 : ℝ) ≤ M) (Nat.cast_nonneg d),
      ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_natCast]
    calc |fluxValD hG hGv k ω 0 i - if i = k then abar else 0|
        ≤ |fluxValD hG hGv k ω 0 i| + |(if i = k then abar else 0)| := abs_sub _ _
      _ ≤ L * M ^ d + abar * M ^ d :=
          add_le_add hflux (hc.trans (le_mul_of_one_le_right habar hM1))
      _ = (L + abar) * M ^ d := by ring
  intro q hq
  have hmeas : Measurable fun ω =>
      ENNReal.ofReal |fluxValD hG hGv k ω 0 i - if i = k then abar else 0| ^ q :=
    (((measurable_fluxValD hG hGv k 0 i).sub_const _).abs.ennreal_ofReal).pow_const q
  have e : ∫⁻ ω, ENNReal.ofReal |fluxValD hG hGv k ω u i - if i = k then abar else 0| ^ q
      ∂latticeBondLaw d p =
      ∫⁻ ω, ENNReal.ofReal |fluxValD hG hGv k ω 0 i - if i = k then abar else 0| ^ q
      ∂latticeBondLaw d p := by
    have hae : (fun ω => ENNReal.ofReal |fluxValD hG hGv k ω u i - if i = k then abar else 0| ^ q)
        =ᵐ[latticeBondLaw d p] fun ω => ENNReal.ofReal
          |fluxValD hG hGv k (configurationTranslation (-u) ω) 0 i - if i = k then abar else 0| ^ q := by
      filter_upwards [fluxValD_ae_eq_comp hG hGv hGae k i u] with ω h
      rw [h]
    rw [lintegral_congr_ae hae]
    exact (measurePreserving_configurationTranslation p (-u)).lintegral_comp hmeas
  rw [e]
  exact GrowthMomentsD.mono_ae hY hpt0 q hq

/-- **Gu, Proposition 1.1, on `ℤ^d`** in the weaker form `O_s(C/r)` (`r^{-d/2} ≤ r^{-1}` for
`r ≥ 1`, `d ≥ 2`). -/
theorem exists_fluxSpatialAverageD_inv (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (hV : FluxVarianceBoundD d p) :
    ∃ abar s C : ℝ, 0 < abar ∧ 0 < s ∧ 0 < C ∧ ∀ (k i : Fin d) (r : ℝ), 1 ≤ r → ∀ x : Vertex d,
      IsOsBond d p (fun ω => |fluxObsD hG hGv k i r x ω - if i = k then abar else 0|) s
        (C / r) := by
  obtain ⟨abar, s, C, ha, hs, hC, h⟩ := exists_fluxSpatialAverageD hG hGv hd hpc hp1 hGae hV
  refine ⟨abar, s, C, ha, hs, hC, fun k i r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  refine Rigidity.Proofs.S2.IsOsBond.mono_scale hs (by positivity) ?_
    ((measurable_fluxObsD hG hGv k i r x).sub_const _).abs (h k i r hr x)
  have h1 : r ≤ r ^ ((d : ℝ) / 2) := by
    calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
      _ ≤ r ^ ((d : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hr (by
          have : (2 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
  exact div_le_div_of_nonneg_left hC.le hr0 h1


/-! ### The random variables of the bound -/

/-- `‖Φ_{t_J} g‖_{ℓ²(S)}`, `t_J = 2·4^J`. -/
noncomputable def fluxBoxY (k i : Fin d) (abar : ℝ) (J : ℕ) (S : Finset (Vertex d))
    (ω : Configuration d) : ℝ≥0∞ :=
  sqSum S (fun x => fluxObsD hG hGv k i (Real.sqrt (2 * 4 ^ J)) x ω -
    if i = k then abar else 0) ^ (1 / 2 : ℝ)

/-- The weighted `ℓ²` norm of `Φ_{4^j} g` at the dyadic step `j`. -/
noncomputable def fluxBoxR (k i : Fin d) (abar : ℝ) (T : Finset (Vertex d)) (j : ℕ)
    (ω : Configuration d) : ℝ≥0∞ :=
  (∑' u, ENNReal.ofReal ((fluxObsD hG hGv k i (2 ^ j) u ω - if i = k then abar else 0) ^ 2) *
    dyadicWeight T (4 ^ j) (7 * 4 ^ j) u) ^ (1 / 2 : ℝ)

/-- The weighted `ℓ²` norm of `g` for the first step. -/
noncomputable def fluxBoxR0 (k i : Fin d) (abar : ℝ) (T : Finset (Vertex d))
    (ω : Configuration d) : ℝ≥0∞ :=
  (∑' u, ENNReal.ofReal ((fluxValD hG hGv k ω u i - if i = k then abar else 0) ^ 2) *
    dyadicWeight T 0 2 u) ^ (1 / 2 : ℝ)

/-- The coefficient of `‖∇w‖`. -/
noncomputable def fluxBoxZ (CH : ℝ) (k i : Fin d) (abar : ℝ) (J : ℕ) (T : Finset (Vertex d))
    (ω : Configuration d) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, fluxBoxR hG hGv k i abar T j ω * ENNReal.ofReal (6 * CH * 2 ^ j) ^ (1 / 2 : ℝ) +
    fluxBoxR0 hG hGv k i abar T ω * ENNReal.ofReal 4 ^ (1 / 2 : ℝ)

omit [NeZero d] in
theorem measurable_fluxBoxY (k i : Fin d) (abar : ℝ) (J : ℕ) (S : Finset (Vertex d)) :
    Measurable (fluxBoxY hG hGv k i abar J S) :=
  (Finset.measurable_sum _ fun x _ =>
    (((measurable_fluxObsD hG hGv k i _ x).sub_const _).pow_const 2).ennreal_ofReal).pow_const _

omit [NeZero d] in
theorem measurable_fluxBoxR (k i : Fin d) (abar : ℝ) (T : Finset (Vertex d)) (j : ℕ) :
    Measurable (fluxBoxR hG hGv k i abar T j) :=
  (Measurable.tsum fun u => ((((measurable_fluxObsD hG hGv k i _ u).sub_const _).pow_const
    2).ennreal_ofReal).mul_const _).pow_const _

omit [NeZero d] in
theorem measurable_fluxBoxR0 (k i : Fin d) (abar : ℝ) (T : Finset (Vertex d)) :
    Measurable (fluxBoxR0 hG hGv k i abar T) :=
  (Measurable.tsum fun u => ((((measurable_fluxValD hG hGv k u i).sub_const _).pow_const
    2).ennreal_ofReal).mul_const _).pow_const _

omit [NeZero d] in
theorem measurable_fluxBoxZ (CH : ℝ) (k i : Fin d) (abar : ℝ) (J : ℕ) (T : Finset (Vertex d)) :
    Measurable (fluxBoxZ hG hGv CH k i abar J T) :=
  (Finset.measurable_sum _ fun j _ => (measurable_fluxBoxR hG hGv k i abar T j).mul_const _).add
    ((measurable_fluxBoxR0 hG hGv k i abar T).mul_const _)

/-- **The deterministic bound** on `G`. -/
theorem ofReal_abs_sum_flux_mul_le {CH : ℝ} (hCH : 0 ≤ CH)
    (hHeat : ∀ t : ℝ, 0 < t → ∀ j : Fin d, ∑' v : Vertex d, ENNReal.ofReal
      |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| ≤
        ENNReal.ofReal (CH / Real.sqrt t))
    {k i : Fin d} (abar : ℝ) (J : ℕ) {S T : Finset (Vertex d)} {ω : Configuration d} (hω : ω ∈ G)
    {w : Vertex d → ℝ} (hw : ∀ y ∉ S, w y = 0) (hT : ∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x) :
    ENNReal.ofReal |∑ x ∈ S, (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x| ≤
      fluxBoxY hG hGv k i abar J S ω * sqSum S w ^ (1 / 2 : ℝ) +
        fluxBoxZ hG hGv CH k i abar J T ω * gradSqSum T w ^ (1 / 2 : ℝ) := by
  obtain ⟨hf, heq⟩ := heatAvgD_flux_eq hG hGv (k := k) (i := i) hω (if i = k then abar else 0)
  have key := ofReal_abs_sum_mul_le_dyadic hCH hHeat hf hw hT J
  refine key.trans (le_of_eq ?_)
  have e1 : heatAvgD (2 * 4 ^ J) (fun z => fluxValD hG hGv k ω z i - if i = k then abar else 0) =
      fun x => fluxObsD hG hGv k i (Real.sqrt (2 * 4 ^ J)) x ω - if i = k then abar else 0 := by
    funext x
    have h := heq (Real.sqrt (2 * 4 ^ J)) (Real.sqrt_pos.2 (by positivity)) x
    rw [Real.sq_sqrt (by positivity)] at h
    exact h
  have e2 : ∀ j : ℕ,
      heatAvgD (4 ^ j) (fun z => fluxValD hG hGv k ω z i - if i = k then abar else 0) =
        fun u => fluxObsD hG hGv k i (2 ^ j) u ω - if i = k then abar else 0 := by
    intro j
    funext u
    have h := heq (2 ^ j) (by positivity) u
    have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4] at h
    exact h
  rw [e1]
  simp only [e2]
  rfl

/-! ### Moments -/

omit [NeZero d] in
theorem growthMoments_fluxBoxY {k i : Fin d} {abar B₀ κ : ℝ} (hB₀ : 0 < B₀) (hκ : 0 ≤ κ)
    (hobs : ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex d, GrowthMomentsD p (fun ω => ENNReal.ofReal
      |fluxObsD hG hGv k i r x ω - if i = k then abar else 0|) (B₀ / r) κ)
    (J : ℕ) (S : Finset (Vertex d)) :
    GrowthMomentsD p (fluxBoxY hG hGv k i abar J S) (B₀ * 2 ^ κ * Real.sqrt S.card / 2 ^ J) κ := by
  have hr : 1 ≤ Real.sqrt (2 * 4 ^ J) := Real.one_le_sqrt.2 (by
    have : (1 : ℝ) ≤ 4 ^ J := one_le_pow₀ (by norm_num)
    linarith)
  have hm : ∑' u : Vertex d, (if u ∈ S then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal S.card := by
    refine le_of_eq ?_
    rw [tsum_eq_sum (s := S) (fun u hu => if_neg hu), Finset.sum_ite_mem, Finset.inter_self,
      Finset.sum_const, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
  have hr0 : 0 < Real.sqrt (2 * 4 ^ J) := by linarith
  have h := growthMoments_sqrt_weighted_tsum
    (X := fun u ω => fluxObsD hG hGv k i (Real.sqrt (2 * 4 ^ J)) u ω - if i = k then abar else 0)
    (fun u => (measurable_fluxObsD hG hGv k i _ u).sub_const _) (div_nonneg hB₀.le hr0.le) hκ
    (fun u => hobs _ hr u) (Nat.cast_nonneg _) hm
  have h2J : (2 : ℝ) ^ J ≤ Real.sqrt (2 * 4 ^ J) := by
    rw [show (2 * 4 ^ J : ℝ) = 2 * (2 ^ J) ^ 2 by rw [← pow_mul, mul_comm J 2, pow_mul]; norm_num,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    have : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) J]
  have hpos : (0 : ℝ) < 2 ^ J := by positivity
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  refine (h.mono fun ω => le_of_eq ?_).of_le (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (div_nonneg hB₀.le hr0.le)) h2κ.le) ?_ le_rfl
  · simp only [fluxBoxY, sqSum]
    congr 1
    rw [tsum_eq_sum (s := S) (fun u hu => by rw [if_neg hu, mul_zero])]
    exact Finset.sum_congr rfl fun u hu => by rw [if_pos hu, mul_one]
  · have h1 : B₀ / Real.sqrt (2 * 4 ^ J) ≤ B₀ / 2 ^ J :=
      div_le_div_of_nonneg_left hB₀.le hpos h2J
    calc Real.sqrt S.card * (B₀ / Real.sqrt (2 * 4 ^ J)) * 2 ^ κ
        ≤ Real.sqrt S.card * (B₀ / 2 ^ J) * 2 ^ κ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)) h2κ.le
      _ = B₀ * 2 ^ κ * Real.sqrt S.card / 2 ^ J := by ring

theorem growthMoments_fluxBoxR_mul {k i : Fin d} {abar B₀ κ CH : ℝ} (hB₀ : 0 < B₀) (hκ : 0 ≤ κ)
    (hCH : 0 < CH)
    (hHeat : ∀ t : ℝ, 0 < t → ∀ j : Fin d, ∑' v : Vertex d, ENNReal.ofReal
      |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| ≤
        ENNReal.ofReal (CH / Real.sqrt t))
    (hobs : ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex d, GrowthMomentsD p (fun ω => ENNReal.ofReal
      |fluxObsD hG hGv k i r x ω - if i = k then abar else 0|) (B₀ / r) κ)
    (T : Finset (Vertex d)) (j : ℕ) :
    GrowthMomentsD p (fun ω => fluxBoxR hG hGv k i abar T j ω *
      ENNReal.ofReal (6 * CH * 2 ^ j) ^ (1 / 2 : ℝ)) (6 * d * CH * B₀ * 2 ^ κ * Real.sqrt T.card) κ := by
  have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  have hr : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hK : ∀ i' : Fin d, ∑' v, heatGradKernelD i' (4 ^ j) (7 * 4 ^ j) v ≤
      ENNReal.ofReal (6 * CH * 2 ^ j) := by
    intro i'
    refine (tsum_heatGradKernelD_le hCH.le hHeat (by positivity) i').trans (le_of_eq ?_)
    have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    rw [sqrt_four_pow, h4]
    congr 1
    field_simp
    ring
  have hM : (0 : ℝ) ≤ d * T.card * (6 * CH * 2 ^ j) := by positivity
  have hm : ∑' u, dyadicWeight T (4 ^ j) (7 * 4 ^ j) u ≤
      ENNReal.ofReal (d * T.card * (6 * CH * 2 ^ j)) := by
    refine (tsum_dyadicWeight_le T hK).trans (le_of_eq ?_)
    symm
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast]
    norm_num
  have h := growthMoments_sqrt_weighted_tsum
    (X := fun u ω => fluxObsD hG hGv k i (2 ^ j) u ω - if i = k then abar else 0)
    (fun u => (measurable_fluxObsD hG hGv k i _ u).sub_const _) (div_nonneg hB₀.le hpos.le) hκ
    (fun u => hobs _ hr u) hM hm
  have hBj : 0 ≤ Real.sqrt (d * T.card * (6 * CH * 2 ^ j)) * (B₀ / 2 ^ j) * 2 ^ κ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hB₀.le hpos.le)) h2κ.le
  have h' := h.const_mul (c := Real.sqrt (6 * CH * 2 ^ j)) (Real.sqrt_nonneg _) hBj
  refine (h'.mono fun ω => le_of_eq ?_).of_le (mul_nonneg (Real.sqrt_nonneg _) hBj) ?_ le_rfl
  · simp only [fluxBoxR]
    rw [ofReal_rpow_half _ (by positivity)]
    exact mul_comm _ _
  · have hsq : Real.sqrt (6 * CH * 2 ^ j) * Real.sqrt (d * T.card * (6 * CH * 2 ^ j)) ≤
        6 * d * CH * 2 ^ j * Real.sqrt T.card := by
      refine sqrt_mul_sqrt_le (by positivity) (by positivity) ?_
      rw [mul_pow, Real.sq_sqrt hTc]
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
      have hdd : (d : ℝ) ≤ d ^ 2 := by nlinarith
      have h0 : 0 ≤ 36 * CH ^ 2 * (2 ^ j) ^ 2 * (T.card : ℝ) := by positivity
      calc 6 * CH * 2 ^ j * (d * T.card * (6 * CH * 2 ^ j))
          = 36 * CH ^ 2 * (2 ^ j) ^ 2 * (T.card : ℝ) * d := by ring
        _ ≤ 36 * CH ^ 2 * (2 ^ j) ^ 2 * (T.card : ℝ) * d ^ 2 :=
            mul_le_mul_of_nonneg_left hdd h0
        _ = (6 * d * CH * 2 ^ j) ^ 2 * T.card := by ring
    calc Real.sqrt (6 * CH * 2 ^ j) *
          (Real.sqrt (d * T.card * (6 * CH * 2 ^ j)) * (B₀ / 2 ^ j) * 2 ^ κ)
        = (Real.sqrt (6 * CH * 2 ^ j) * Real.sqrt (d * T.card * (6 * CH * 2 ^ j))) *
            (B₀ / 2 ^ j * 2 ^ κ) := by ring
      _ ≤ (6 * d * CH * 2 ^ j * Real.sqrt T.card) * (B₀ / 2 ^ j * 2 ^ κ) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 6 * d * CH * B₀ * 2 ^ κ * Real.sqrt T.card * (2 ^ j / 2 ^ j) := by ring
      _ = 6 * d * CH * B₀ * 2 ^ κ * Real.sqrt T.card := by rw [div_self hpos.ne', mul_one]

theorem growthMoments_fluxBoxR0_mul {k i : Fin d} {abar BΛ κ : ℝ} (hBΛ : 0 < BΛ) (hκ : 0 ≤ κ)
    (hflux : ∀ u : Vertex d, GrowthMomentsD p (fun ω =>
      ENNReal.ofReal |fluxValD hG hGv k ω u i - if i = k then abar else 0|) BΛ κ)
    (T : Finset (Vertex d)) :
    GrowthMomentsD p (fun ω => fluxBoxR0 hG hGv k i abar T ω * ENNReal.ofReal 4 ^ (1 / 2 : ℝ))
      (4 * d * BΛ * 2 ^ κ * Real.sqrt T.card) κ := by
  have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  have hK : ∀ i' : Fin d, ∑' v, heatGradKernelD i' 0 2 v ≤ ENNReal.ofReal 4 := by
    intro i'
    refine (tsum_heatGradKernelD_le_two le_rfl i').trans (le_of_eq ?_)
    norm_num
  have hm : ∑' u, dyadicWeight T 0 2 u ≤ ENNReal.ofReal (d * T.card * 4) := by
    refine (tsum_dyadicWeight_le T hK).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast]
    norm_num
  have h := growthMoments_sqrt_weighted_tsum
    (X := fun u ω => fluxValD hG hGv k ω u i - if i = k then abar else 0)
    (fun u => (measurable_fluxValD hG hGv k u i).sub_const _) hBΛ.le hκ hflux (by positivity) hm
  have hB : 0 ≤ Real.sqrt (d * T.card * 4) * BΛ * 2 ^ κ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hBΛ.le) h2κ.le
  have h' := h.const_mul (c := 2) (by norm_num) hB
  refine (h'.mono fun ω => le_of_eq ?_).of_le (by positivity) ?_ le_rfl
  · simp only [fluxBoxR0]
    rw [ofReal_rpow_half _ (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact mul_comm _ _
  · have hsq : Real.sqrt (d * T.card * 4) ≤ 2 * d * Real.sqrt T.card := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast NeZero.pos d
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt hTc]
      have hdd : (d : ℝ) ≤ d ^ 2 := by nlinarith
      nlinarith
    calc 2 * (Real.sqrt (d * T.card * 4) * BΛ * 2 ^ κ)
        ≤ 2 * (2 * d * Real.sqrt T.card * BΛ * 2 ^ κ) := by gcongr
      _ = 4 * d * BΛ * 2 ^ κ * Real.sqrt T.card := by ring

/-- **Dario–Gu, (eq.gsmallH-1), on finite sets of `ℤ^d`.** -/
theorem exists_fluxWeakNormBoxD (hd : 2 ≤ d) (hpc : criticalProbability d < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) (hV : FluxVarianceBoundD d p) :
    ∃ abar A κ : ℝ, 0 < abar ∧ 0 < A ∧ 0 < κ ∧ ∀ (k i : Fin d) (J : ℕ) (S T : Finset (Vertex d)),
      ∃ Y Z : Configuration d → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMomentsD p Y (A * Real.sqrt S.card / 2 ^ J) κ ∧
        GrowthMomentsD p Z (A * (J + 1) * Real.sqrt T.card) κ ∧
        ∀ᵐ ω ∂latticeBondLaw d p, ∀ w : Vertex d → ℝ, (∀ y ∉ S, w y = 0) →
          (∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x) →
          ENNReal.ofReal |∑ x ∈ S, (fluxValD hG hGv k ω x i - if i = k then abar else 0) * w x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ) := by
  obtain ⟨abar, s, C, habar, hs, hC, hA3⟩ := exists_fluxSpatialAverageD_inv hG hGv hd hpc hp1 hGae hV
  obtain ⟨CH, hCH, hHeat⟩ := exists_tsum_ofReal_abs_zdHeat_grad_le (d := d)
  obtain ⟨BΛ, κΛ, hBΛ, hκΛ, hflux⟩ := exists_growthMomentsD_flux hG hGv hd hpc hp1 hGae habar.le
  obtain ⟨κ, hκ0, hκs, hκΛ'⟩ : ∃ κ : ℝ, 0 < κ ∧ 1 / s ≤ κ ∧ κΛ ≤ κ :=
    ⟨max (1 / s) κΛ, lt_max_of_lt_right hκΛ, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨B₀, hB₀0, hB₀⟩ : ∃ B₀ : ℝ, 0 < B₀ ∧ B₀ = 2 * C * (1 / s) ^ (1 / s) :=
    ⟨_, by positivity, rfl⟩
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  obtain ⟨A, hA0, hA1, hA2, hA3'⟩ : ∃ A : ℝ, 0 < A ∧ 2 * (B₀ * 2 ^ κ) ≤ A ∧
      2 * (6 * d * CH * B₀ * 2 ^ κ) ≤ A ∧ 2 * (4 * d * BΛ * 2 ^ κ) ≤ A :=
    by
      refine ⟨2 * (B₀ * 2 ^ κ) + 2 * (6 * d * CH * B₀ * 2 ^ κ) + 2 * (4 * d * BΛ * 2 ^ κ),
        by positivity, ?_, ?_, ?_⟩ <;>
      · have h1 : 0 ≤ 2 * (B₀ * 2 ^ κ) := by positivity
        have h2 : 0 ≤ 2 * (6 * (d : ℝ) * CH * B₀ * 2 ^ κ) := by positivity
        have h3 : 0 ≤ 2 * (4 * (d : ℝ) * BΛ * 2 ^ κ) := by positivity
        linarith
  refine ⟨abar, A, κ, habar, hA0, hκ0, fun k i J S T => ?_⟩
  have hobs : ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex d, GrowthMomentsD p (fun ω => ENNReal.ofReal
      |fluxObsD hG hGv k i r x ω - if i = k then abar else 0|) (B₀ / r) κ := by
    intro r hr x
    have hr0 : (0 : ℝ) < r := by linarith
    have h := growthMomentsD_of_isOsBond (fun ω => abs_nonneg _) hs (div_pos hC hr0)
      (hA3 k i r hr x)
    refine h.of_le (by have := div_pos hC hr0; positivity) (le_of_eq ?_) hκs
    rw [hB₀]
    ring
  have hTc : (0 : ℝ) ≤ Real.sqrt T.card := Real.sqrt_nonneg _
  refine ⟨fluxBoxY hG hGv k i abar J S, fluxBoxZ hG hGv CH k i abar J T,
    measurable_fluxBoxY hG hGv k i abar J S, measurable_fluxBoxZ hG hGv CH k i abar J T, ?_, ?_,
    ?_⟩
  · refine (growthMoments_fluxBoxY hG hGv hB₀0 hκ0.le hobs J S).of_le (by positivity) ?_ le_rfl
    have hpos : (0 : ℝ) < 2 ^ J := by positivity
    rw [div_le_div_iff_of_pos_right hpos]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  · set D := (J + 1) * (A / 2) * Real.sqrt T.card with hD
    have hD0 : 0 ≤ D := by positivity
    have hJ1 : (1 : ℝ) ≤ J + 1 := by linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
    have hsum := (GrowthMomentsD.finsetSum (Finset.range J)
      (fun j => (measurable_fluxBoxR hG hGv k i abar T j).mul_const
        (ENNReal.ofReal (6 * CH * 2 ^ j) ^ (1 / 2 : ℝ))) (by positivity)
      (fun j _ => growthMoments_fluxBoxR_mul hG hGv hB₀0 hκ0.le hCH hHeat hobs T j)).of_le
        (by positivity) (show ((Finset.range J).card : ℝ) *
          (6 * d * CH * B₀ * 2 ^ κ * Real.sqrt T.card) ≤ D by
        rw [Finset.card_range, hD]
        have h1 : 6 * d * CH * B₀ * 2 ^ κ ≤ A / 2 := by linarith
        have h2 : (J : ℝ) ≤ J + 1 := by linarith
        calc (J : ℝ) * (6 * d * CH * B₀ * 2 ^ κ * Real.sqrt T.card)
            ≤ (J + 1) * (A / 2 * Real.sqrt T.card) := by gcongr
          _ = (J + 1) * (A / 2) * Real.sqrt T.card := by ring) le_rfl
    have hinit := (growthMoments_fluxBoxR0_mul hG hGv hBΛ hκ0.le
      (fun u => (hflux k i u).of_le hBΛ.le le_rfl hκΛ') T).of_le (by positivity)
        (show 4 * d * BΛ * 2 ^ κ * Real.sqrt T.card ≤ D by
          rw [hD]
          have h1 : 4 * d * BΛ * 2 ^ κ ≤ A / 2 := by linarith
          calc 4 * d * BΛ * 2 ^ κ * Real.sqrt T.card ≤ A / 2 * Real.sqrt T.card := by gcongr
            _ ≤ (J + 1) * (A / 2 * Real.sqrt T.card) :=
                le_mul_of_one_le_left (by positivity) hJ1
            _ = (J + 1) * (A / 2) * Real.sqrt T.card := by ring) le_rfl
    have hadd := GrowthMomentsD.add (Finset.measurable_sum _ fun j _ =>
      (measurable_fluxBoxR hG hGv k i abar T j).mul_const _).aemeasurable hsum hinit hD0
    refine hadd.of_le (by positivity) (le_of_eq ?_) le_rfl
    rw [hD]
    ring
  · filter_upwards [hGae] with ω hω w hw hT
    exact ofReal_abs_sum_flux_mul_le hG hGv hCH.le hHeat abar J hω hw hT

end Flux

end Rigidity.Green.GeneralFlux
