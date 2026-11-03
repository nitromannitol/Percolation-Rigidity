import Rigidity.Steps.Section5.MeanZeroRepresentation
import Rigidity.Steps.S2.GreenGradientHomogenization

/-! # Proposition 5.8: the two-scale expansion of a neutral potential

Proposition 5.8 (`TwoScaleExpansionStmt`; corrected draft L1657-1667, proof L1703-1727; arXiv source
L1629-1640, L1674-1700): on `Σ f = 0`, beyond a minimal scale `M_f ≤ O_s(C)`,
`|u_f(x) - L + Σᵢ Mᵢ ∂ᵢḠ(x)| ≤ C |x|^{-5/4}` with `Mᵢ = Σ_y f(y) ℓ_{eᵢ}(y)` [C18].

The printed proof applies Proposition 2.6 to `∇_y G(x, e)`, the gradient in the *source* variable,
which Proposition 2.6 (a statement on `∇ₓG(x, y)` for a fixed pole `y`) does not cover. As in
[C18], the pole is moved to `x`:

* the normalized Green function `H(x, y) = G(x, y) - K(y)` is symmetric
  (`NormalizedGreenSymmetryStep`, C13/C14), so with `L = Σ_y f(y) K(y)`,
  `u_f(x) - L = Σ_y f(y) H(x, y) = Σ_y f(y) G(y, x) - K(x) Σ_y f(y)`;
* summation by parts against the flow `F` of Lemma 5.6 (`div F = f`, carried by the edges of a
  connected set `V ⊇ supp f ∩ 𝒞_∞` with `|V| ≤ R ≤ O_s` and `|F| ≤ |V| Σ |f|`): the steps of Lemma 5.6
  are used rather than its statement, which records neither `div F = f` nor where `F` lives;
  `u_f(x) - L = ½ Σ_{(a, b)} F(a, b) (G(a, x) - G(b, x))` and
  `Mᵢ = ½ Σ_{(a, b)} F(a, b) (ℓ_{eᵢ}(a) - ℓ_{eᵢ}(b))` (step:5.8-ibp, `SummationByPartsStep`);
* on each edge `(a, b)` of `V`, Proposition 2.6 with pole `x` (`ForwardDiffEdgeStep` reads the
  forward differences on the edge) gives `G(a, x) - G(b, x) = Σᵢ (ℓᵢ(a) - ℓᵢ(b)) ∂ᵢḠ(z - x)` up to
  `O(|x|^{-11/8})` (`δ = 1/8`), `z ∈ {a, b}`, as soon as the scale `M(x)` of the pole `x` is below
  `|x|/2`; the union bound over the poles gives one random scale for all `x` (`MinimalScaleStep`
  of Section 2, with `TailOfOsStep`; this is the minimal scale of step:5.8-ibp);
* `∂ᵢḠ(z - x) = -∂ᵢḠ(x) + O(|z| |x|^{-2})` (step:5.8-taylor, `GreenTaylorStep`; oddness of `∇Ḡ`
  gives the sign of C18), with `|ℓᵢ(a) - ℓᵢ(b)| ≤ Λ (1 + |a|)` (`CorrectedPlaneGradientStep`, from
  Theorem 2.5, the scale `M_corr(0)` of the printed `M_f`) and `|a| ≤ Σ_{supp f} |y| + |V|` on `V`
  (`ConnectedSetRadiusStep`, the box `□_f` of the printed `M_f`).

With `t = |x|`, `τ = t^{1/24}`, `n = |V| < τ` and `Λ < τ`, the sum of the errors over the `n²`
pairs is `O(n³ (τ^{-33} + Λ n² τ^{-48})) = O(τ^{-30}) = O(t^{-5/4})`. The minimal scale is the one
of `MinimalScaleStep` for the scales `M(x)` of Proposition 2.6, `R` and `Λ`, with exponent `24`. -/

open MeasureTheory LatticeProb.Percolation Classical Filter Topology

namespace Rigidity.Steps.Section5

open Rigidity.Section2 Rigidity.Section5 Rigidity.Steps.S2

/-- step:5.8-symmetry (corrections C13, C14; Dario-Gu Thm 2 and Sec. 5): almost surely,
for every Green family `G` of the infinite cluster there is a normalization `K` such that
`H(x, y) = G(x, y) - K(y)` is symmetric. (Proof route: `K(y)` is the limit of
`G(·, y) - Ḡ(· - y)` of `SupercriticalBondGreenQuantitative`; Green's second identity for `G(·, x)`
and `G(·, y)` on `𝒞_∞ ∩ B_r` gives `G(y, x) - G(x, y) = K(x) - K(y) + o(1)` along a sequence of
radii on which the boundary flux `Σ_{∂B_r} |∇G|` stays bounded, by Caccioppoli on the annuli.) -/
def NormalizedGreenSymmetryStep : Prop :=
  LatticeProb.External.SupercriticalBondGreenQuantitative → ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
      ∀ G, IsGreenFamily (uniqueInfiniteComponent h) G →
        ∃ K : uniqueInfiniteComponent h → ℝ, ∀ x y, G x y - K y = G y x - K x

/-- step:5.8-support (deterministic; the support of `F` lies in the box `□_f`): a finite set `V`
of an open component, connected through its own edges, has `ℓ¹` diameter at most `|V|`. -/
def ConnectedSetRadiusStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (V : Finset C),
    ((componentGraph C).induce (V : Set C)).Preconnected →
    ∀ a ∈ V, ∀ b ∈ V, l1 a.val ≤ l1 b.val + V.card

/-- step:5.8-corrector (Theorem 2.5 with `α = 1` at the origin, the scale `M_corr(0)` of the
printed `M_f`): the gradients of the corrected planes `ℓ_{eᵢ}` grow at most linearly,
`|ℓ_{eᵢ}(a) - ℓ_{eᵢ}(b)| ≤ Λ (1 + |a|)` on the open edges `(a, b)`, with `Λ ≤ O_s(θ)`. -/
def CorrectedPlaneGradientStep : Prop :=
  Rigidity.External.CorrectorQuantitativeInput → ∀ p : unitInterval,
    criticalProbability 2 < (p : ℝ) → (p : ℝ) < 1 →
    ∃ s θ : ℝ, 0 < s ∧ 0 < θ ∧ ∃ Λ : Configuration 2 → ℝ, Measurable Λ ∧ IsOs 2 p Λ s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ (i : Fin 2) (ℓ : uniqueInfiniteComponent h → ℝ),
          IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single i 1) ℓ →
          ∀ a b, (componentGraph (uniqueInfiniteComponent h)).Adj a b →
            |ℓ a - ℓ b| ≤ Λ ω * (1 + l1 a.val)

/-- step:5.8-edge (deterministic; Proposition 2.6 read on an edge): an open edge `(a, b)` is
`(z, z + eⱼ)` or `(z + eⱼ, z)` with `z ∈ {a, b}`, so for any slopes `D z i`,
`|g(a) - g(b) - Σᵢ (ℓᵢ(a) - ℓᵢ(b)) D z i|` is the `j`-th term of the left side of eq.
`green-gradient-homogenization` at `z` (`∂ⱼḠ = Σᵢ δᵢⱼ ∂ᵢḠ`), hence at most their sum. -/
def ForwardDiffEdgeStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (g : C → ℝ) (ℓ : Fin 2 → C → ℝ)
    (D : C → Fin 2 → ℝ) (a b : C), (componentGraph C).Adj a b →
    ∃ z, (z = a ∨ z = b) ∧
      |g a - g b - ∑ i, (ℓ i a - ℓ i b) * D z i| ≤
        ∑ j, |forwardDiff C g z j - D z j -
          ∑ i, (forwardDiff C (ℓ i) z j - if i = j then 1 else 0) * D z i|

/-- step:5.8-taylor (eq. `gradient-green-taylor`, with the oddness of `∇Ḡ` [C18]): `Ḡ` is smooth
away from its pole and `∇Ḡ` is odd and homogeneous of degree `-1`, so for `4 |z| ≤ |x|`,
`|∂ᵢḠ(z - x) + ∂ᵢḠ(x)| ≤ C |z| |x|^{-2}`. -/
def GreenTaylorStep : Prop :=
  ∀ κ : {a : ℝ // 0 < a}, ∃ CT : ℝ, 0 < CT ∧ ∀ x z : Vertex 2, x ≠ 0 → 4 * l1 z ≤ l1 x →
    ∀ i : Fin 2,
      |fderiv ℝ (greenBar 2 le_rfl κ) (toReal z - toReal x) (EuclideanSpace.single i 1) +
          fderiv ℝ (greenBar 2 le_rfl κ) (toReal x) (EuclideanSpace.single i 1)| ≤
        CT * l1 z / l1 x ^ 2

/-! ### Elementary estimates -/

theorem l1_nonneg (x : Vertex 2) : 0 ≤ l1 x := Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The triangle inequality `|x| ≤ |z - x| + |z|` for the `ℓ¹` norm. -/
theorem l1_le_dist_add (x z : Vertex 2) : l1 x ≤ ∑ i, |((z i - x i : ℤ) : ℝ)| + l1 z := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  push_cast
  linarith [abs_sub_abs_le_abs_sub (x i : ℝ) (z i : ℝ), abs_sub_comm (x i : ℝ) (z i : ℝ)]

theorem latticeL1Dist_zero (x : Vertex 2) : S2.latticeL1Dist x 0 = l1 x := by
  simp [S2.latticeL1Dist, l1]

theorem rpow_pow_twentyFour {τ : ℝ} (hτ : 0 ≤ τ) (a : ℝ) (k : ℕ) (h : 24 * a = k) :
    (τ ^ 24) ^ a = τ ^ k := by
  rw [← Real.rpow_natCast τ 24, ← Real.rpow_mul hτ, ← Real.rpow_natCast τ k]
  congr 1

/-- The error of Proposition 2.6 with `δ = 1/8` at distance `D ≥ τ²⁴/2`:
`C D^{-3/8} D^{-1} ≤ 4 C τ^{-33}`. -/
theorem green_error_le {C6 D τ : ℝ} (hC6 : 0 ≤ C6) (hτ : 0 < τ) (hD : τ ^ 24 / 2 ≤ D) :
    C6 * Real.rpow D (-1 / 2 + 1 / 8) * Real.rpow D (1 - ((2 : ℕ) : ℝ)) ≤ 4 * C6 / τ ^ 33 := by
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  simp only [Real.rpow_eq_pow]
  rw [show (1 - ((2 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
    show (-1 / 2 + 1 / 8 : ℝ) = -(3 / 8) by norm_num, Real.rpow_neg hD0.le]
  have h38 : τ ^ 9 / 2 ≤ D ^ (3 / 8 : ℝ) := by
    have h1 : (τ ^ 24 / 2) ^ (3 / 8 : ℝ) ≤ D ^ (3 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hD (by norm_num)
    have h2 : (τ ^ 24 / 2) ^ (3 / 8 : ℝ) = τ ^ 9 / 2 ^ (3 / 8 : ℝ) := by
      rw [Real.div_rpow (by positivity) (by norm_num), rpow_pow_twentyFour hτ.le (3 / 8) 9 (by norm_num)]
    have h3 : (2 : ℝ) ^ (3 / 8 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 8 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : 0 < (2 : ℝ) ^ (3 / 8 : ℝ) := by positivity
    calc τ ^ 9 / 2 ≤ τ ^ 9 / 2 ^ (3 / 8 : ℝ) := div_le_div_of_nonneg_left (by positivity) h4 h3
      _ = _ := h2.symm
      _ ≤ _ := h1
  have i1 : (D ^ (3 / 8 : ℝ))⁻¹ ≤ 2 / τ ^ 9 := by
    rw [inv_le_comm₀ (lt_of_lt_of_le (by positivity) h38) (by positivity), inv_div]
    exact h38
  have i2 : D⁻¹ ≤ 2 / τ ^ 24 := by
    rw [inv_le_comm₀ hD0 (by positivity), inv_div]
    exact hD
  calc C6 * (D ^ (3 / 8 : ℝ))⁻¹ * D⁻¹ ≤ C6 * (2 / τ ^ 9) * (2 / τ ^ 24) := by gcongr
    _ = 4 * C6 / τ ^ 33 := by field_simp; ring

/-- The final count: with `n ≤ r ≤ τ` and `λ ≤ τ`, the errors summed over the `n²` pairs of the
connecting set, with flux at most `n m_f`, are at most `A τ^{-30} = A |x|^{-5/4}`. -/
theorem two_scale_numeric {τ n r lam mf C6 CT ρf A : ℝ} (hτ1 : 1 ≤ τ) (hn0 : 0 ≤ n) (hnr : n ≤ r)
    (hrτ : r ≤ τ) (hlamτ : lam ≤ τ) (hmf : 0 ≤ mf) (hC6 : 0 ≤ C6)
    (hCT : 0 ≤ CT) (hρf : 0 ≤ ρf) (hA : 2 * mf * C6 + mf * CT * (2 + ρf) ^ 2 ≤ A) :
    1 / 2 * n ^ 2 * (n * mf) *
        (4 * C6 / τ ^ 33 + 2 * lam * (1 + (ρf + n)) * CT * (ρf + n) / τ ^ 48) ≤ A / τ ^ 30 := by
  have hτ0 : 0 < τ := by linarith
  have hnτ : n ≤ τ := hnr.trans hrτ
  have hn3 : n ^ 3 ≤ τ ^ 3 := pow_le_pow_left₀ hn0 hnτ 3
  have hρ1 : 1 + (ρf + n) ≤ (2 + ρf) * τ := by nlinarith
  have hρ2 : ρf + n ≤ (2 + ρf) * τ := by nlinarith
  have h6 : τ ^ 6 ≤ τ ^ 18 := pow_le_pow_right₀ hτ1 (by norm_num)
  have e : 1 / 2 * n ^ 2 * (n * mf) *
        (4 * C6 / τ ^ 33 + 2 * lam * (1 + (ρf + n)) * CT * (ρf + n) / τ ^ 48) =
      (2 * mf * C6 * n ^ 3 * τ ^ 15 + mf * CT * lam * (1 + (ρf + n)) * (ρf + n) * n ^ 3) /
        τ ^ 48 := by
    field_simp; ring
  have e' : A / τ ^ 30 = A * τ ^ 18 / τ ^ 48 := by field_simp
  rw [e, e']
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : 2 * mf * C6 * n ^ 3 * τ ^ 15 ≤ 2 * mf * C6 * τ ^ 18 := by
    calc 2 * mf * C6 * n ^ 3 * τ ^ 15 ≤ 2 * mf * C6 * τ ^ 3 * τ ^ 15 := by gcongr
      _ = 2 * mf * C6 * τ ^ 18 := by ring
  have h2 : mf * CT * lam * (1 + (ρf + n)) * (ρf + n) * n ^ 3 ≤
      mf * CT * (2 + ρf) ^ 2 * τ ^ 18 := by
    calc mf * CT * lam * (1 + (ρf + n)) * (ρf + n) * n ^ 3
        ≤ mf * CT * τ * ((2 + ρf) * τ) * ((2 + ρf) * τ) * τ ^ 3 := by gcongr
      _ = mf * CT * (2 + ρf) ^ 2 * τ ^ 6 := by ring
      _ ≤ mf * CT * (2 + ρf) ^ 2 * τ ^ 18 := by gcongr
  have h3 : (2 * mf * C6 + mf * CT * (2 + ρf) ^ 2) * τ ^ 18 ≤ A * τ ^ 18 := by gcongr
  nlinarith

/-! ### Proposition 5.8 -/

/-- Proposition 5.8 follows from Proposition 2.6, the steps of Lemma 5.6, the symmetry of the
normalized Green function, the edge reading of Proposition 2.6, the Taylor expansion of `∇Ḡ`, the
linear growth of `∇ℓ_{eᵢ}` and the union bound over the poles. -/
theorem twoScaleExpansion_of_steps {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hW : Rigidity.External.WellConnectedInput)
    (hGQ : LatticeProb.External.SupercriticalBondGreenQuantitative)
    (hCQ : Rigidity.External.CorrectorQuantitativeInput) (hU : UniqueClusterAe p)
    (h26 : GreenGradientHomogenizationStmt 2 le_rfl p)
    (hC : ConnectingSetStep) (hF : FlowOnConnectedSetStep) (hS : SummationByPartsStep)
    (hrad : ConnectedSetRadiusStep) (hsym : NormalizedGreenSymmetryStep)
    (hgrad : CorrectedPlaneGradientStep) (hedge : ForwardDiffEdgeStep) (htay : GreenTaylorStep)
    (htail : TailOfOsStep 2 p) (hmin : MinimalScaleStep 2 p)
    (f : Vertex 2 → ℤ) : TwoScaleExpansionStmt p f := by
  intro hf
  obtain ⟨κ, h26'⟩ := h26
  obtain ⟨s6, C6, hs6, hC6, h26δ⟩ := h26' (1 / 8) (by norm_num)
  choose M6 hM6m _ hM6os hM6ae using h26δ
  obtain ⟨θR, sR, hθR, hsR, R, hRm, hRos, hRae⟩ := hC hW p hpc hp1 f hf
  obtain ⟨sΛ, θΛ, hsΛ, hθΛ, Λ, hΛm, hΛos, hΛae⟩ := hgrad hCQ p hpc hp1
  obtain ⟨CT, hCT, hT⟩ := htay κ
  obtain ⟨c6, hc6, ht6⟩ := htail s6 C6 hs6 hC6
  obtain ⟨cR, hcR, htR⟩ := htail sR θR hsR hθR
  obtain ⟨cΛ, hcΛ, htΛ⟩ := htail sΛ θΛ hsΛ hθΛ
  obtain ⟨mf, hmf⟩ : ∃ m : ℝ, m = ∑ y ∈ hf.toFinset, |(f y : ℝ)| := ⟨_, rfl⟩
  obtain ⟨ρf, hρf⟩ : ∃ m : ℝ, m = ∑ y ∈ hf.toFinset, l1 y := ⟨_, rfl⟩
  have hmf0 : 0 ≤ mf := hmf ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρf0 : 0 ≤ ρf := hρf ▸ Finset.sum_nonneg fun y _ => l1_nonneg y
  have hfm : ∀ y, |(f y : ℝ)| ≤ mf := by
    intro y
    by_cases hy : f y = 0
    · simp only [hy, Int.cast_zero, abs_zero]
      exact hmf0
    · rw [hmf]
      exact Finset.single_le_sum (f := fun y => |(f y : ℝ)|) (fun _ _ => abs_nonneg _)
        (hf.mem_toFinset.mpr hy)
  have hfl : ∀ y, f y ≠ 0 → l1 y ≤ ρf := fun y hy => hρf ▸
    Finset.single_le_sum (f := l1) (fun y _ => l1_nonneg y) (hf.mem_toFinset.mpr hy)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 + 4 * (ρf + 1) + (2 * mf * C6 + mf * CT * (2 + ρf) ^ 2) :=
    ⟨_, rfl⟩
  have hB0 : 0 ≤ 2 * mf * C6 + mf * CT * (2 + ρf) ^ 2 := by positivity
  have hA4 : 4 ≤ A := by linarith
  obtain ⟨s', C', hs', hAC', hM⟩ := hmin 3 ![s6, sR, sΛ] ![c6, cR, cΛ] A 24
    (by intro i; fin_cases i <;> simp [hs6, hsR, hsΛ])
    (by intro i; fin_cases i <;> simp [hc6, hcR, hcΛ]) (by linarith)
  obtain ⟨M, hMm, -, hMos, hMae⟩ := hM 0 ![fun y => M6 y, fun _ => R, fun _ => Λ]
    (by intro i y; fin_cases i <;> simp [hM6m, hRm, hΛm])
    (by
      intro i y
      fin_cases i
      · exact ht6 _ (hM6m y) (hM6os y)
      · exact htR _ hRm hRos
      · exact htΛ _ hΛm hΛos)
  refine ⟨C', s', by linarith, hs', κ, M, hMm, hMos, ?_⟩
  filter_upwards [hU, hRae, hΛae, hMae, ae_all_iff.2 hM6ae, hsym hGQ p hpc hp1]
    with ω hω hV hΛω hMω h6ω hsymω
  refine ⟨hω, fun hmass G hG ℓ hℓ => ?_⟩
  -- the flow of Lemma 5.6 on the connecting set `V`
  obtain ⟨V, hVc, hVf, hVR⟩ := hV hω
  have hsum : ∑ y ∈ V, (f y.val : ℝ) = 0 := by
    have h1 : mass (uniqueInfiniteComponent hω) f = ∑ y ∈ V, f y.val :=
      finsum_eq_sum_of_support_subset _ fun y hy => Finset.mem_coe.mpr (hVf y hy)
    have h2 : ∑ y ∈ V, f y.val = 0 := h1 ▸ hmass
    exact_mod_cast h2
  obtain ⟨F, hanti, hsupp, hdiv, hbd⟩ := hF (componentGraph (uniqueInfiniteComponent hω)) V
    (fun y => (f y.val : ℝ)) hVc (fun y hy => hVf y (Int.cast_ne_zero.mp hy)) hsum
  have hSF : ∀ a b, F a b ≠ 0 → (a, b) ∈ V ×ˢ V := fun a b h =>
    Finset.mem_product.mpr ⟨(hsupp a b h).2.1, (hsupp a b h).2.2⟩
  have hSb : ∀ k : (uniqueInfiniteComponent hω) → ℝ, ∑ᶠ a, (f a.val : ℝ) * k a =
      (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (k e.1 - k e.2) := hS F _ (V ×ˢ V) hanti hSF hdiv
  -- the normalization of the Green function
  obtain ⟨K, hK⟩ := hsymω hω G hG
  refine ⟨∑ᶠ y : (uniqueInfiniteComponent hω), (f y.val : ℝ) * K y, fun x hx => ?_⟩
  set Dx : Fin 2 → ℝ := fun i =>
    fderiv ℝ (greenBar 2 le_rfl κ) (toReal x.val) (EuclideanSpace.single i 1) with hDx
  set Tm : (uniqueInfiniteComponent hω) × (uniqueInfiniteComponent hω) → ℝ := fun e =>
    G e.1 x - G e.2 x + ∑ i, (ℓ i e.1 - ℓ i e.2) * Dx i with hTm
  have hid : potential (uniqueInfiniteComponent hω) G f x - ∑ᶠ y : (uniqueInfiniteComponent hω), (f y.val : ℝ) * K y +
      ∑ i, pairing (uniqueInfiniteComponent hω) f (ℓ i) * Dx i = (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * Tm e := by
    have h1 : potential (uniqueInfiniteComponent hω) G f x = (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (G x e.1 - G x e.2) :=
      hSb (fun y => G x y)
    have h3 : ∀ i, pairing (uniqueInfiniteComponent hω) f (ℓ i) =
        (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (ℓ i e.1 - ℓ i e.2) := fun i => hSb (ℓ i)
    have h4 : ∑ i, pairing (uniqueInfiniteComponent hω) f (ℓ i) * Dx i =
        (1 / 2) * ∑ e ∈ V ×ˢ V, F e.1 e.2 * ∑ i, (ℓ i e.1 - ℓ i e.2) * Dx i := by
      simp only [h3]
      calc ∑ i, (1 / 2 * ∑ e ∈ V ×ˢ V, F e.1 e.2 * (ℓ i e.1 - ℓ i e.2)) * Dx i
          = ∑ i, ∑ e ∈ V ×ˢ V, 1 / 2 * (F e.1 e.2 * ((ℓ i e.1 - ℓ i e.2) * Dx i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun e _ => by ring
        _ = ∑ e ∈ V ×ˢ V, ∑ i, 1 / 2 * (F e.1 e.2 * ((ℓ i e.1 - ℓ i e.2) * Dx i)) :=
            Finset.sum_comm
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
    rw [h1, hSb K, h4, ← mul_sub, ← Finset.sum_sub_distrib, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hTm]
    linear_combination F e.1 e.2 * (hK x e.1 - hK x e.2)
  rw [hid]
  -- the minimal scale at `x`
  have hcond := hMω x.val (by rwa [latticeL1Dist_zero])
  rw [latticeL1Dist_zero] at hcond
  have c0 := hcond 0
  have c1 := hcond 1
  have c2 := hcond 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at c0 c1 c2
  obtain ⟨r, hr2, hRr, hrt⟩ : ∃ r : ℝ, 2 ≤ r ∧ R ω ≤ r ∧ A * r ^ 24 < l1 x.val :=
    ⟨_, le_max_right _ _, le_max_left _ _, c1⟩
  obtain ⟨lam, hlam2, hΛlam, hlamt⟩ : ∃ r : ℝ, 2 ≤ r ∧ Λ ω ≤ r ∧ A * r ^ 24 < l1 x.val :=
    ⟨_, le_max_right _ _, le_max_left _ _, c2⟩
  obtain ⟨m, hm2, hMm6, hmt⟩ : ∃ r : ℝ, 2 ≤ r ∧ M6 x.val ω ≤ r ∧ A * r ^ 24 < l1 x.val :=
    ⟨_, le_max_right _ _, le_max_left _ _, c0⟩
  have ht0 : 0 < l1 x.val := lt_of_le_of_lt (by positivity) hrt
  obtain ⟨τ, hτ24, hτ0⟩ : ∃ τ : ℝ, τ ^ 24 = l1 x.val ∧ 0 < τ :=
    ⟨l1 x.val ^ (((24 : ℕ) : ℝ)⁻¹), Real.rpow_inv_natCast_pow ht0.le (by norm_num),
      Real.rpow_pos_of_pos ht0 _⟩
  have hle : ∀ {u : ℝ}, 0 ≤ u → A * u ^ 24 < l1 x.val → u < τ := fun hu h => by
    rw [← hτ24] at h
    exact lt_of_pow_lt_pow_left₀ 24 hτ0.le
      (lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) (by linarith)) h)
  have hrτ := hle (by linarith) hrt
  have hlamτ := hle (by linarith) hlamt
  have hτ1 : 1 ≤ τ := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℝ, (V.card : ℝ) = n := ⟨_, rfl⟩
  have hn0 : 0 ≤ n := hn ▸ Nat.cast_nonneg _
  have hnr : n ≤ r := hn ▸ hVR.trans hRr
  have hx0 : x.val ≠ 0 := by
    intro h
    rw [h] at ht0
    simp [l1] at ht0
  have h4ρ : 4 * (ρf + n) < l1 x.val := by
    have h1 : ρf * 1 ≤ ρf * r := mul_le_mul_of_nonneg_left (by linarith) hρf0
    have h2 : r ≤ r ^ 24 := le_self_pow₀ (by linarith) (by norm_num)
    have h3 : 4 * (ρf + 1) * r ^ 24 ≤ A * r ^ 24 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : 4 * (ρf + 1) * r ≤ 4 * (ρf + 1) * r ^ 24 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hM6x : 4 * M6 x.val ω < l1 x.val := by
    have : m ≤ m ^ 24 := le_self_pow₀ (by linarith) (by norm_num)
    have h3 : 4 * m ^ 24 ≤ A * m ^ 24 := mul_le_mul_of_nonneg_right hA4 (by positivity)
    linarith
  obtain ⟨Err, hErr⟩ : ∃ E : ℝ,
      E = 4 * C6 / τ ^ 33 + 2 * lam * (1 + (ρf + n)) * CT * (ρf + n) / τ ^ 48 := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by linarith
  have hErr0 : 0 ≤ Err := by
    have hρn : 0 ≤ ρf + n := by linarith
    have h1 : 0 ≤ 2 * lam * (1 + (ρf + n)) * CT * (ρf + n) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlam0) (by linarith))
        hCT.le) hρn
    rw [hErr]
    exact add_nonneg (div_nonneg (by linarith) (pow_nonneg hτ0.le _))
      (div_nonneg h1 (pow_nonneg hτ0.le _))
  -- the bound on each edge
  have hedgeb : ∀ e ∈ V ×ˢ V, |F e.1 e.2| * |Tm e| ≤ n * mf * Err := by
    intro e _
    by_cases hFe : F e.1 e.2 = 0
    · rw [hFe, abs_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hn0 hmf0) hErr0
    obtain ⟨hadj, he1, he2⟩ := hsupp e.1 e.2 hFe
    have hFb : |F e.1 e.2| ≤ n * mf :=
      (hbd _ _).trans <| (Finset.sum_le_sum fun c _ => hfm c.val).trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, hn]))
    obtain ⟨y0, hy0V, hy0f⟩ : ∃ y0 ∈ V, f y0.val ≠ 0 := by
      by_contra hno
      simp only [not_exists, not_and, not_not] at hno
      apply hFe
      have h0 : ∑ c ∈ V, |(f c.val : ℝ)| = 0 :=
        Finset.sum_eq_zero fun c hc => by simp [hno c hc]
      have := hbd e.1 e.2
      rw [h0] at this
      exact abs_nonpos_iff.mp this
    have hlV : ∀ a ∈ V, l1 a.val ≤ ρf + n := fun a ha => by
      have := hrad ω _ V hVc a ha y0 hy0V
      linarith [hfl _ hy0f]
    obtain ⟨z, hz, hez⟩ := hedge ω _ (fun w => G w x) ℓ
      (fun z i => fderiv ℝ (greenBar 2 le_rfl κ) (toReal z.val - toReal x.val)
        (EuclideanSpace.single i 1)) e.1 e.2 hadj
    have hzV : z ∈ V := by rcases hz with rfl | rfl <;> assumption
    have hlz := hlV z hzV
    have hD : l1 x.val / 2 ≤ ∑ i, |((z.val i - x.val i : ℤ) : ℝ)| := by
      have := l1_le_dist_add x.val z.val
      linarith
    have hP := h6ω x.val hω x.prop (fun w => G w x) (hG x) ℓ hℓ z (by linarith)
    have hP' := green_error_le (D := ∑ i, |((z.val i - x.val i : ℤ) : ℝ)|) hC6.le hτ0
      (by rw [hτ24]; exact hD)
    have hfirst := hez.trans (hP.trans hP')
    beta_reduce at hfirst
    have hTz : ∀ i, |fderiv ℝ (greenBar 2 le_rfl κ) (toReal z.val - toReal x.val)
        (EuclideanSpace.single i 1) + Dx i| ≤ CT * (ρf + n) / τ ^ 48 := by
      intro i
      refine (hT x.val z.val hx0 (by linarith) i).trans ?_
      rw [show τ ^ 48 = l1 x.val ^ 2 by rw [← hτ24]; ring]
      gcongr
    have hli : ∀ i, |ℓ i e.1 - ℓ i e.2| ≤ lam * (1 + (ρf + n)) := fun i =>
      (hΛω hω i (ℓ i) (hℓ i) e.1 e.2 hadj).trans
        (mul_le_mul hΛlam (by linarith [hlV _ he1]) (by linarith [l1_nonneg e.1.val])
          (by linarith))
    have hsplit : Tm e = (G e.1 x - G e.2 x - ∑ i, (ℓ i e.1 - ℓ i e.2) *
          fderiv ℝ (greenBar 2 le_rfl κ) (toReal z.val - toReal x.val)
            (EuclideanSpace.single i 1)) +
        ∑ i, (ℓ i e.1 - ℓ i e.2) * (fderiv ℝ (greenBar 2 le_rfl κ)
          (toReal z.val - toReal x.val) (EuclideanSpace.single i 1) + Dx i) := by
      simp only [hTm, mul_add, Finset.sum_add_distrib]
      ring
    have hsum2 : |∑ i, (ℓ i e.1 - ℓ i e.2) * (fderiv ℝ (greenBar 2 le_rfl κ)
        (toReal z.val - toReal x.val) (EuclideanSpace.single i 1) + Dx i)| ≤
        2 * lam * (1 + (ρf + n)) * CT * (ρf + n) / τ ^ 48 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |(ℓ i e.1 - ℓ i e.2) * (fderiv ℝ (greenBar 2 le_rfl κ)
            (toReal z.val - toReal x.val) (EuclideanSpace.single i 1) + Dx i)|
          ≤ ∑ _i : Fin 2, lam * (1 + (ρf + n)) * (CT * (ρf + n) / τ ^ 48) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul]
            exact mul_le_mul (hli i) (hTz i) (abs_nonneg _) (by positivity)
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have hTb : |Tm e| ≤ Err := by
      rw [hsplit, hErr]
      exact (abs_add_le _ _).trans (add_le_add hfirst hsum2)
    exact mul_le_mul hFb hTb (abs_nonneg _) (mul_nonneg hn0 hmf0)
  have hcard : ((V ×ˢ V).card : ℝ) = n ^ 2 := by
    rw [Finset.card_product, ← hn]
    push_cast
    ring
  have hrpow : (l1 x.val).rpow (-5 / 4) = 1 / τ ^ 30 := by
    rw [Real.rpow_eq_pow, ← hτ24, show (-5 / 4 : ℝ) = -(5 / 4) by norm_num,
      Real.rpow_neg (by positivity), rpow_pow_twentyFour hτ0.le (5 / 4) 30 (by norm_num),
      one_div]
  calc |1 / 2 * ∑ e ∈ V ×ˢ V, F e.1 e.2 * Tm e|
      ≤ 1 / 2 * ∑ e ∈ V ×ˢ V, |F e.1 e.2| * |Tm e| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ ≤ 1 / 2 * ∑ _e ∈ V ×ˢ V, n * mf * Err :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hedgeb) (by norm_num)
    _ = 1 / 2 * n ^ 2 * (n * mf) * Err := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ A / τ ^ 30 := by
        rw [hErr]
        exact two_scale_numeric hτ1 hn0 hnr hrτ.le hlamτ.le hmf0 hC6.le hCT.le hρf0
          (by linarith)
    _ ≤ C' / τ ^ 30 := by gcongr
    _ = C' * (l1 x.val).rpow (-5 / 4) := by rw [hrpow]; ring

end Rigidity.Steps.Section5
