import Rigidity.Proofs.Green.DarioGuFluxDyadic
import Rigidity.Proofs.Green.DarioGuFluxSpatialAverage
import Rigidity.Proofs.Corrector.PlanarCoarseningError

/-!
# The weak norm of the centered flux on boxes of `ℤ²`

The estimate (eq.gsmallH-1) of Dario–Gu, Appendix B, in dimension two and in the lattice form of
`DarioGuFluxDyadic`: for the centered flux `g = a(Dχ_{e_k} + e_k) - ā e_k` on `ℤ²` (component `i`,
zero off the infinite cluster), every finite set `S`, every `J` and every `w` vanishing off `S`
with gradient supported in `T`,

`|Σ_S g w| ≤ Y ‖w‖_{ℓ²(S)} + Z ‖∇w‖_{ℓ²(T)}`

almost surely (`exists_fluxWeakNormBox`), where the random variables `Y` and `Z` do not depend
on `w` and have moments `E[Y^q] ≤ (A √|S| 2^{-J} q^κ)^q` and `E[Z^q] ≤ (A (J + 1) √|T| q^κ)^q`.
With `S` a box of side `R` and `2^J ≈ R`, this is `‖g‖_{H̲^{-1}} ≤ O_s(C log R)` in the normalization
of the source, the bound (mainstep1propb1) for `d = 2`.

The source proves (eq.gsmallH-1) from the continuous multiscale Poincaré inequality (D.28) of
Armstrong, Kuusi and Mourrat with the heat averages of Gu's Proposition 1.1 at every time
`t ∈ (0, 1]`; here the heat averages are those of `ℤ²` at the dyadic times `4^j ≥ 1`
(`exists_fluxSpatialAverage_two`), and the times below `2` are handled by the moments of the flux
itself (the Lipschitz bound of the corrector, `stepOne_lipschitz_data`), which is (fluxbounded.est).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare Rigidity.Corrector
  Rigidity.Percolation Rigidity.External
open scoped ENNReal Classical

namespace Rigidity.Green

variable {p : unitInterval}

/-! ### Moments -/

theorem growthMoments_of_isOsBond {X : Configuration 2 → ℝ} (hX0 : ∀ ω, 0 ≤ X ω) {s θ : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (h : IsOsBond 2 p X s θ) :
    GrowthMoments p (fun ω => ENNReal.ofReal (X ω)) (2 * θ * (1 / s) ^ (1 / s)) (1 / s) := by
  have e : (fun ω => Real.exp (Real.rpow (max (X ω / θ) 0) s)) =
      fun ω => Real.exp ((X ω / θ) ^ s) := by
    funext ω
    rw [max_eq_left (div_nonneg (hX0 ω) hθ.le)]
    rfl
  obtain ⟨h1, h2⟩ := h
  rw [e] at h1 h2
  exact growthMoments_of_exp_moment hX0 hθ hs h1 h2

theorem GrowthMoments.mono_ae {X Y : Configuration 2 → ℝ≥0∞} {B κ : ℝ}
    (h : GrowthMoments p Y B κ) (hle : ∀ᵐ ω ∂latticeBondLaw 2 p, X ω ≤ Y ω) :
    GrowthMoments p X B κ := fun q hq =>
  (lintegral_mono_ae (hle.mono fun _ h => ENNReal.rpow_le_rpow h (by linarith))).trans (h q hq)

theorem sqrt_mul_sqrt_le {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : a * b ≤ c ^ 2) :
    Real.sqrt a * Real.sqrt b ≤ c := by
  rw [← Real.sqrt_mul ha, ← Real.sqrt_sq hc]
  exact Real.sqrt_le_sqrt h

theorem ofReal_rpow_half (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]

section Flux

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- On `G`, the centered flux is summable against every heat kernel and its heat average at time
`r²` is the heat average `fluxObs` of the flux minus the constant. -/
theorem heatAvg_flux_eq {k i : Fin 2} {ω : Configuration 2} (hω : ω ∈ G) (c : ℝ) :
    HeatSummableAll (fun z => fluxVal hG hGv k ω (z, i) - c) ∧ ∀ r : ℝ, 0 < r → ∀ u : Vertex 2,
      heatAvg (r ^ 2) (fun z => fluxVal hG hGv k ω (z, i) - c) u =
        fluxObs hG hGv k i r u ω - c := by
  obtain ⟨h, -⟩ := hGv hω
  obtain ⟨ℓ, hℓ⟩ := exists_correctedPlane_of_valid (hGv hω) (uniqueInfiniteComponent_infinite h)
    (Pi.single k 1)
  obtain ⟨A, hA⟩ := exists_abs_planeFlux_le hℓ i
  have hflux : ∀ z, fluxVal hG hGv k ω (z, i) = planeFlux (uniqueInfiniteComponent h) ℓ (z, i) :=
    fun z => fluxVal_eq_planeFlux hG hGv hω h hℓ (z, i)
  have hgrow : ∀ z, |fluxVal hG hGv k ω (z, i)| ≤ |A| * (1 + ‖latticeEuclideanEmbedding z‖) :=
    fun z => by
      rw [hflux]
      exact (hA z).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
  have hsum : HeatSummableAll (fun z => fluxVal hG hGv k ω (z, i)) :=
    heatSummableAll_of_abs_le hgrow
  refine ⟨heatSummableAll_of_abs_le (A := |A| + |c|) fun z => ?_, fun r hr u => ?_⟩
  · have h1 := hgrow z
    have h2 : 0 ≤ ‖latticeEuclideanEmbedding z‖ := norm_nonneg _
    calc |fluxVal hG hGv k ω (z, i) - c| ≤ |fluxVal hG hGv k ω (z, i)| + |c| := abs_sub _ _
      _ ≤ (|A| + |c|) * (1 + ‖latticeEuclideanEmbedding z‖) := by
          nlinarith [abs_nonneg c, abs_nonneg A]
  · have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have hs1 := hsum.summable hr2 u
    have hs2 := (hasSum_openHeat (allOpen 2) hr2 u).summable
    unfold heatAvg
    rw [show (fun z => openHeat (allOpen 2) (r ^ 2) u z * (fluxVal hG hGv k ω (z, i) - c)) =
        fun z => openHeat (allOpen 2) (r ^ 2) u z * fluxVal hG hGv k ω (z, i) -
          openHeat (allOpen 2) (r ^ 2) u z * c from funext fun z => mul_sub _ _ _,
      hs1.tsum_sub (hs2.mul_right c), tsum_mul_right,
      (hasSum_openHeat (allOpen 2) hr2 u).tsum_eq, one_mul]
    rfl

/-- The moments of the centered flux at a point, from the Lipschitz bound of the corrector. -/
theorem exists_growthMoments_flux {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {abar : ℝ} (habar : 0 ≤ abar) :
    ∃ B κ : ℝ, 0 < B ∧ 0 < κ ∧ ∀ (k i : Fin 2) (u : Vertex 2),
      GrowthMoments p (fun ω =>
        ENNReal.ofReal |fluxVal hG hGv k ω (u, i) - if i = k then abar else 0|) B κ := by
  obtain ⟨Λ, BΛ, κΛ, hBΛ, hκΛ, hΛm, hΛ0, hlip, hΛmom⟩ := stepOne_lipschitz_data hG hGv
    Rigidity.Proofs.Regularity.armstrongDarioOrderZeroTwo_holds hpc hp1 hGae
  refine ⟨(1 + abar) * BΛ, κΛ, by positivity, hκΛ, fun k i u => ?_⟩
  have hY : GrowthMoments p (fun ω => ENNReal.ofReal (1 + abar) * ENNReal.ofReal (1 + Λ k u ω))
      ((1 + abar) * BΛ) κΛ :=
    GrowthMoments.const_mul (fun q hq => hΛmom k u q hq) (by positivity) hBΛ.le
  refine GrowthMoments.mono_ae hY ?_
  filter_upwards [hlip k, hGae] with ω hl hω
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hΛu := hΛ0 k u ω
  have hδ : |(if i = k then abar else 0)| ≤ abar := by
    split_ifs
    · exact (abs_of_nonneg habar).le
    · rw [abs_zero]; exact habar
  simp only [fluxVal]
  by_cases hc : EdgeOpen ω (u, i) ∧ ω ∈ infiniteComponentEvent u
  · rw [if_pos hc]
    have hhead : ω ∈ infiniteComponentEvent (edgeHead ((u, i) : LatticeEdge)) :=
      mem_infiniteComponentEvent_of_adj hc.1 hc.2
    have hsw := correctorDiff_swap' hG hGv (q := Pi.single k 1) hω hc.2 hhead
    have hb := hl u hc.2 (edgeHead (u, i)) hc.1
    have hone : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    rw [hsw]
    have h1 := abs_sub (-correctorDiff hG hGv (Pi.single k 1) ω u (edgeHead (u, i)) +
      (if i = k then (1 : ℝ) else 0)) (if i = k then abar else 0)
    have h2 := abs_add_le (-correctorDiff hG hGv (Pi.single k 1) ω u (edgeHead (u, i)))
      (if i = k then (1 : ℝ) else 0)
    rw [abs_neg] at h2
    nlinarith
  · rw [if_neg hc, zero_sub, abs_neg]
    nlinarith

/-! ### The random variables of the bound -/

/-- `‖Φ_{t_J} g‖_{ℓ²(S)}`, `t_J = 2·4^J`. -/
noncomputable def fluxBoxY (k i : Fin 2) (abar : ℝ) (J : ℕ) (S : Finset (Vertex 2))
    (ω : Configuration 2) : ℝ≥0∞ :=
  sqSum S (fun x => fluxObs hG hGv k i (Real.sqrt (2 * 4 ^ J)) x ω -
    if i = k then abar else 0) ^ (1 / 2 : ℝ)

/-- The weighted `ℓ²` norm of `Φ_{4^j} g` at the dyadic step `j`. -/
noncomputable def fluxBoxR (k i : Fin 2) (abar : ℝ) (T : Finset (Vertex 2)) (j : ℕ)
    (ω : Configuration 2) : ℝ≥0∞ :=
  (∑' u, ENNReal.ofReal ((fluxObs hG hGv k i (2 ^ j) u ω - if i = k then abar else 0) ^ 2) *
    dyadicWeight T (4 ^ j) (7 * 4 ^ j) u) ^ (1 / 2 : ℝ)

/-- The weighted `ℓ²` norm of `g` for the first step. -/
noncomputable def fluxBoxR0 (k i : Fin 2) (abar : ℝ) (T : Finset (Vertex 2))
    (ω : Configuration 2) : ℝ≥0∞ :=
  (∑' u, ENNReal.ofReal ((fluxVal hG hGv k ω (u, i) - if i = k then abar else 0) ^ 2) *
    dyadicWeight T 0 2 u) ^ (1 / 2 : ℝ)

/-- The coefficient of `‖∇w‖`. -/
noncomputable def fluxBoxZ (CH : ℝ) (k i : Fin 2) (abar : ℝ) (J : ℕ) (T : Finset (Vertex 2))
    (ω : Configuration 2) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range J, fluxBoxR hG hGv k i abar T j ω * ENNReal.ofReal (6 * CH * 2 ^ j) ^ (1 / 2 : ℝ) +
    fluxBoxR0 hG hGv k i abar T ω * ENNReal.ofReal 4 ^ (1 / 2 : ℝ)

theorem measurable_fluxBoxY (k i : Fin 2) (abar : ℝ) (J : ℕ) (S : Finset (Vertex 2)) :
    Measurable (fluxBoxY hG hGv k i abar J S) :=
  (Finset.measurable_sum _ fun x _ =>
    (((measurable_fluxObs hG hGv k i _ x).sub_const _).pow_const 2).ennreal_ofReal).pow_const _

theorem measurable_fluxBoxR (k i : Fin 2) (abar : ℝ) (T : Finset (Vertex 2)) (j : ℕ) :
    Measurable (fluxBoxR hG hGv k i abar T j) :=
  (Measurable.tsum fun u => ((((measurable_fluxObs hG hGv k i _ u).sub_const _).pow_const
    2).ennreal_ofReal).mul_const _).pow_const _

theorem measurable_fluxBoxR0 (k i : Fin 2) (abar : ℝ) (T : Finset (Vertex 2)) :
    Measurable (fluxBoxR0 hG hGv k i abar T) :=
  (Measurable.tsum fun u => ((((measurable_fluxVal hG hGv k (u, i)).sub_const _).pow_const
    2).ennreal_ofReal).mul_const _).pow_const _

theorem measurable_fluxBoxZ (CH : ℝ) (k i : Fin 2) (abar : ℝ) (J : ℕ) (T : Finset (Vertex 2)) :
    Measurable (fluxBoxZ hG hGv CH k i abar J T) :=
  (Finset.measurable_sum _ fun j _ => (measurable_fluxBoxR hG hGv k i abar T j).mul_const _).add
    ((measurable_fluxBoxR0 hG hGv k i abar T).mul_const _)

/-- **The deterministic bound** on `G`. -/
theorem ofReal_abs_sum_flux_mul_le {CH : ℝ} (hCH : 0 ≤ CH)
    (hHeat : ∀ t : ℝ, 0 < t → ∀ j : Fin 2, ∑' v : Vertex 2, ENNReal.ofReal
      |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| ≤
        ENNReal.ofReal (CH / Real.sqrt t))
    {k i : Fin 2} (abar : ℝ) (J : ℕ) {S T : Finset (Vertex 2)} {ω : Configuration 2} (hω : ω ∈ G)
    {w : Vertex 2 → ℝ} (hw : ∀ y ∉ S, w y = 0) (hT : ∀ x ∉ T, ∀ j : Fin 2, w (x + unit j) = w x) :
    ENNReal.ofReal |∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x| ≤
      fluxBoxY hG hGv k i abar J S ω * sqSum S w ^ (1 / 2 : ℝ) +
        fluxBoxZ hG hGv CH k i abar J T ω * gradSqSum T w ^ (1 / 2 : ℝ) := by
  obtain ⟨hf, heq⟩ := heatAvg_flux_eq hG hGv (k := k) (i := i) hω (if i = k then abar else 0)
  have key := ofReal_abs_sum_mul_le_dyadic hCH hHeat hf hw hT J
  refine key.trans (le_of_eq ?_)
  have e1 : heatAvg (2 * 4 ^ J) (fun z => fluxVal hG hGv k ω (z, i) - if i = k then abar else 0) =
      fun x => fluxObs hG hGv k i (Real.sqrt (2 * 4 ^ J)) x ω - if i = k then abar else 0 := by
    funext x
    have h := heq (Real.sqrt (2 * 4 ^ J)) (Real.sqrt_pos.2 (by positivity)) x
    rw [Real.sq_sqrt (by positivity)] at h
    exact h
  have e2 : ∀ j : ℕ,
      heatAvg (4 ^ j) (fun z => fluxVal hG hGv k ω (z, i) - if i = k then abar else 0) =
        fun u => fluxObs hG hGv k i (2 ^ j) u ω - if i = k then abar else 0 := by
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

theorem growthMoments_fluxBoxY {k i : Fin 2} {abar B₀ κ : ℝ} (hB₀ : 0 < B₀) (hκ : 0 ≤ κ)
    (hobs : ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex 2, GrowthMoments p (fun ω => ENNReal.ofReal
      |fluxObs hG hGv k i r x ω - if i = k then abar else 0|) (B₀ / r) κ)
    (J : ℕ) (S : Finset (Vertex 2)) :
    GrowthMoments p (fluxBoxY hG hGv k i abar J S) (B₀ * 2 ^ κ * Real.sqrt S.card / 2 ^ J) κ := by
  have hr : 1 ≤ Real.sqrt (2 * 4 ^ J) := Real.one_le_sqrt.2 (by
    have : (1 : ℝ) ≤ 4 ^ J := one_le_pow₀ (by norm_num)
    linarith)
  have hm : ∑' u : Vertex 2, (if u ∈ S then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal S.card := by
    refine le_of_eq ?_
    rw [tsum_eq_sum (s := S) (fun u hu => if_neg hu), Finset.sum_ite_mem, Finset.inter_self,
      Finset.sum_const, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
  have hr0 : 0 < Real.sqrt (2 * 4 ^ J) := by linarith
  have h := growthMoments_sqrt_weighted_tsum
    (X := fun u ω => fluxObs hG hGv k i (Real.sqrt (2 * 4 ^ J)) u ω - if i = k then abar else 0)
    (fun u => (measurable_fluxObs hG hGv k i _ u).sub_const _) (div_nonneg hB₀.le hr0.le) hκ
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

theorem growthMoments_fluxBoxR_mul {k i : Fin 2} {abar B₀ κ CH : ℝ} (hB₀ : 0 < B₀) (hκ : 0 ≤ κ)
    (hCH : 0 < CH)
    (hHeat : ∀ t : ℝ, 0 < t → ∀ j : Fin 2, ∑' v : Vertex 2, ENNReal.ofReal
      |openHeat (allOpen 2) t 0 (v + unit j) - openHeat (allOpen 2) t 0 v| ≤
        ENNReal.ofReal (CH / Real.sqrt t))
    (hobs : ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex 2, GrowthMoments p (fun ω => ENNReal.ofReal
      |fluxObs hG hGv k i r x ω - if i = k then abar else 0|) (B₀ / r) κ)
    (T : Finset (Vertex 2)) (j : ℕ) :
    GrowthMoments p (fun ω => fluxBoxR hG hGv k i abar T j ω *
      ENNReal.ofReal (6 * CH * 2 ^ j) ^ (1 / 2 : ℝ)) (9 * CH * B₀ * 2 ^ κ * Real.sqrt T.card) κ := by
  have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  have hr : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hK : ∀ i' : Fin 2, ∑' v, heatGradKernel i' (4 ^ j) (7 * 4 ^ j) v ≤
      ENNReal.ofReal (6 * CH * 2 ^ j) := by
    intro i'
    refine (tsum_heatGradKernel_le hCH.le hHeat (by positivity) i').trans (le_of_eq ?_)
    have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    rw [sqrt_four_pow, h4]
    congr 1
    field_simp
    ring
  have hM : (0 : ℝ) ≤ 2 * T.card * (6 * CH * 2 ^ j) := by positivity
  have hm : ∑' u, dyadicWeight T (4 ^ j) (7 * 4 ^ j) u ≤
      ENNReal.ofReal (2 * T.card * (6 * CH * 2 ^ j)) := by
    refine (tsum_dyadicWeight_le T hK).trans (le_of_eq ?_)
    symm
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast]
    norm_num
  have h := growthMoments_sqrt_weighted_tsum
    (X := fun u ω => fluxObs hG hGv k i (2 ^ j) u ω - if i = k then abar else 0)
    (fun u => (measurable_fluxObs hG hGv k i _ u).sub_const _) (div_nonneg hB₀.le hpos.le) hκ
    (fun u => hobs _ hr u) hM hm
  have hBj : 0 ≤ Real.sqrt (2 * T.card * (6 * CH * 2 ^ j)) * (B₀ / 2 ^ j) * 2 ^ κ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hB₀.le hpos.le)) h2κ.le
  have h' := h.const_mul (c := Real.sqrt (6 * CH * 2 ^ j)) (Real.sqrt_nonneg _) hBj
  refine (h'.mono fun ω => le_of_eq ?_).of_le (mul_nonneg (Real.sqrt_nonneg _) hBj) ?_ le_rfl
  · simp only [fluxBoxR]
    rw [ofReal_rpow_half _ (by positivity)]
    exact mul_comm _ _
  · have hsq : Real.sqrt (6 * CH * 2 ^ j) * Real.sqrt (2 * T.card * (6 * CH * 2 ^ j)) ≤
        9 * CH * 2 ^ j * Real.sqrt T.card := by
      refine sqrt_mul_sqrt_le (by positivity) (by positivity) ?_
      rw [mul_pow, mul_pow, Real.sq_sqrt hTc]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg CH) (sq_nonneg ((2 : ℝ) ^ j))) hTc]
    calc Real.sqrt (6 * CH * 2 ^ j) *
          (Real.sqrt (2 * T.card * (6 * CH * 2 ^ j)) * (B₀ / 2 ^ j) * 2 ^ κ)
        = (Real.sqrt (6 * CH * 2 ^ j) * Real.sqrt (2 * T.card * (6 * CH * 2 ^ j))) *
            (B₀ / 2 ^ j * 2 ^ κ) := by ring
      _ ≤ (9 * CH * 2 ^ j * Real.sqrt T.card) * (B₀ / 2 ^ j * 2 ^ κ) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = 9 * CH * B₀ * 2 ^ κ * Real.sqrt T.card * (2 ^ j / 2 ^ j) := by ring
      _ = 9 * CH * B₀ * 2 ^ κ * Real.sqrt T.card := by rw [div_self hpos.ne', mul_one]

theorem growthMoments_fluxBoxR0_mul {k i : Fin 2} {abar BΛ κ : ℝ} (hBΛ : 0 < BΛ) (hκ : 0 ≤ κ)
    (hflux : ∀ u : Vertex 2, GrowthMoments p (fun ω =>
      ENNReal.ofReal |fluxVal hG hGv k ω (u, i) - if i = k then abar else 0|) BΛ κ)
    (T : Finset (Vertex 2)) :
    GrowthMoments p (fun ω => fluxBoxR0 hG hGv k i abar T ω * ENNReal.ofReal 4 ^ (1 / 2 : ℝ))
      (6 * BΛ * 2 ^ κ * Real.sqrt T.card) κ := by
  have hTc : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  have hK : ∀ i' : Fin 2, ∑' v, heatGradKernel i' 0 2 v ≤ ENNReal.ofReal 4 := by
    intro i'
    refine (tsum_heatGradKernel_le_two le_rfl i').trans (le_of_eq ?_)
    norm_num
  have hm : ∑' u, dyadicWeight T 0 2 u ≤ ENNReal.ofReal (2 * T.card * 4) := by
    refine (tsum_dyadicWeight_le T hK).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast]
    norm_num
  have h := growthMoments_sqrt_weighted_tsum
    (X := fun u ω => fluxVal hG hGv k ω (u, i) - if i = k then abar else 0)
    (fun u => (measurable_fluxVal hG hGv k (u, i)).sub_const _) hBΛ.le hκ hflux (by positivity) hm
  have hB : 0 ≤ Real.sqrt (2 * T.card * 4) * BΛ * 2 ^ κ :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hBΛ.le) h2κ.le
  have h' := h.const_mul (c := 2) (by norm_num) hB
  refine (h'.mono fun ω => le_of_eq ?_).of_le (by positivity) ?_ le_rfl
  · simp only [fluxBoxR0]
    rw [ofReal_rpow_half _ (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact mul_comm _ _
  · have hsq : Real.sqrt (2 * T.card * 4) ≤ 3 * Real.sqrt T.card := by
      rw [show (2 * T.card * 4 : ℝ) = 8 * T.card by ring, Real.sqrt_mul (by norm_num)]
      have h8 : Real.sqrt 8 ≤ 3 := by
        rw [show (3 : ℝ) = Real.sqrt 9 by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      exact mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg _)
    calc 2 * (Real.sqrt (2 * T.card * 4) * BΛ * 2 ^ κ)
        ≤ 2 * (3 * Real.sqrt T.card * BΛ * 2 ^ κ) := by gcongr
      _ = 6 * BΛ * 2 ^ κ * Real.sqrt T.card := by ring

/-- **Dario–Gu, (eq.gsmallH-1), in dimension two, on finite sets of `ℤ²`.** -/
theorem exists_fluxWeakNormBox (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) :
    ∃ abar A κ : ℝ, 0 < abar ∧ 0 < A ∧ 0 < κ ∧ ∀ (k i : Fin 2) (J : ℕ) (S T : Finset (Vertex 2)),
      ∃ Y Z : Configuration 2 → ℝ≥0∞, Measurable Y ∧ Measurable Z ∧
        GrowthMoments p Y (A * Real.sqrt S.card / 2 ^ J) κ ∧
        GrowthMoments p Z (A * (J + 1) * Real.sqrt T.card) κ ∧
        ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ w : Vertex 2 → ℝ, (∀ y ∉ S, w y = 0) →
          (∀ x ∉ T, ∀ j : Fin 2, w (x + unit j) = w x) →
          ENNReal.ofReal |∑ x ∈ S, (fluxVal hG hGv k ω (x, i) - if i = k then abar else 0) * w x| ≤
            Y ω * sqSum S w ^ (1 / 2 : ℝ) + Z ω * gradSqSum T w ^ (1 / 2 : ℝ) := by
  obtain ⟨abar, s, C, habar, hs, hC, hA3⟩ := exists_fluxSpatialAverage_two hG hGv hpc hp1 hGae
  obtain ⟨CH, hCH, hHeat⟩ := exists_tsum_ofReal_abs_openHeat_grad_le
  obtain ⟨BΛ, κΛ, hBΛ, hκΛ, hflux⟩ := exists_growthMoments_flux hG hGv hpc hp1 hGae habar.le
  obtain ⟨κ, hκ0, hκs, hκΛ'⟩ : ∃ κ : ℝ, 0 < κ ∧ 1 / s ≤ κ ∧ κΛ ≤ κ :=
    ⟨max (1 / s) κΛ, lt_max_of_lt_right hκΛ, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨B₀, hB₀0, hB₀⟩ : ∃ B₀ : ℝ, 0 < B₀ ∧ B₀ = 2 * C * (1 / s) ^ (1 / s) :=
    ⟨_, by positivity, rfl⟩
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  obtain ⟨A, hA0, hA1, hA2, hA3'⟩ : ∃ A : ℝ, 0 < A ∧ 2 * (B₀ * 2 ^ κ) ≤ A ∧
      2 * (9 * CH * B₀ * 2 ^ κ) ≤ A ∧ 2 * (6 * BΛ * 2 ^ κ) ≤ A :=
    ⟨2 * (B₀ * 2 ^ κ) + 2 * (9 * CH * B₀ * 2 ^ κ) + 2 * (6 * BΛ * 2 ^ κ), by positivity,
      by nlinarith [mul_pos (mul_pos hCH hB₀0) h2κ, mul_pos hBΛ h2κ],
      by nlinarith [mul_pos hB₀0 h2κ, mul_pos hBΛ h2κ],
      by nlinarith [mul_pos hB₀0 h2κ, mul_pos (mul_pos hCH hB₀0) h2κ]⟩
  refine ⟨abar, A, κ, habar, hA0, hκ0, fun k i J S T => ?_⟩
  have hobs : ∀ r : ℝ, 1 ≤ r → ∀ x : Vertex 2, GrowthMoments p (fun ω => ENNReal.ofReal
      |fluxObs hG hGv k i r x ω - if i = k then abar else 0|) (B₀ / r) κ := by
    intro r hr x
    have hr0 : (0 : ℝ) < r := by linarith
    have h := growthMoments_of_isOsBond (fun ω => abs_nonneg _) hs (div_pos hC hr0)
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
    have hsum := (GrowthMoments.finsetSum (Finset.range J)
      (fun j => (measurable_fluxBoxR hG hGv k i abar T j).mul_const
        (ENNReal.ofReal (6 * CH * 2 ^ j) ^ (1 / 2 : ℝ))) (by positivity)
      (fun j _ => growthMoments_fluxBoxR_mul hG hGv hB₀0 hκ0.le hCH hHeat hobs T j)).of_le
        (by positivity) (show ((Finset.range J).card : ℝ) *
          (9 * CH * B₀ * 2 ^ κ * Real.sqrt T.card) ≤ D by
        rw [Finset.card_range, hD]
        have h1 : 9 * CH * B₀ * 2 ^ κ ≤ A / 2 := by linarith
        have h2 : (J : ℝ) ≤ J + 1 := by linarith
        calc (J : ℝ) * (9 * CH * B₀ * 2 ^ κ * Real.sqrt T.card)
            ≤ (J + 1) * (A / 2 * Real.sqrt T.card) := by gcongr
          _ = (J + 1) * (A / 2) * Real.sqrt T.card := by ring) le_rfl
    have hinit := (growthMoments_fluxBoxR0_mul hG hGv hBΛ hκ0.le
      (fun u => (hflux k i u).of_le hBΛ.le le_rfl hκΛ') T).of_le (by positivity)
        (show 6 * BΛ * 2 ^ κ * Real.sqrt T.card ≤ D by
          rw [hD]
          have h1 : 6 * BΛ * 2 ^ κ ≤ A / 2 := by linarith
          calc 6 * BΛ * 2 ^ κ * Real.sqrt T.card ≤ A / 2 * Real.sqrt T.card := by gcongr
            _ ≤ (J + 1) * (A / 2 * Real.sqrt T.card) :=
                le_mul_of_one_le_left (by positivity) hJ1
            _ = (J + 1) * (A / 2) * Real.sqrt T.card := by ring) le_rfl
    have hadd := GrowthMoments.add (Finset.measurable_sum _ fun j _ =>
      (measurable_fluxBoxR hG hGv k i abar T j).mul_const _).aemeasurable hsum hinit hD0
    refine hadd.of_le (by positivity) (le_of_eq ?_) le_rfl
    rw [hD]
    ring
  · filter_upwards [hGae] with ω hω w hw hT
    exact ofReal_abs_sum_flux_mul_le hG hGv hCH.le hHeat abar J hω hw hT

end Flux

end Rigidity.Green
