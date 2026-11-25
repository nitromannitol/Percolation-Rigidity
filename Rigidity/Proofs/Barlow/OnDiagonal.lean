import Rigidity.Proofs.Barlow.HeatEnergy
import Rigidity.Proofs.Green.DarioGuApproxInputs

/-!
# The on-diagonal upper bound in a very good ball

This file proves Proposition 3.1 and Corollary 3.2 of Barlow (*Random walks on supercritical
percolation clusters*, Ann. Probab. 32 (2004)) for the variable speed random walk on the open graph
of a planar bond configuration, with Euclidean balls of a component `K` in place of the chemical
balls of the source.

A ball `B(z, r)` is good (`IsGoodBall`, Definition 1.7 of the source) if `|K ∩ B(z, r)| ≥ C_V r²`
and the weak Poincaré inequality (1.16) holds with the gradient on `K ∩ B(z, L r)`. If every ball
`B(z, r)` with `|z - x₀| ≤ R` and `N ≤ r ≤ R/18` is good, and the heat kernel from `x₁` is at most
`ε` at distance `R/18` up to time `R`, then for `|x₁ - x₀| ≤ 8R/9`

  `p_{2t}(x₁, x₁) ≤ C / t`   for `2 C_P L² C_V N⁴ ≤ t ≤ R`

(`openHeat_diag_le_of_good`), and `p_{2t}(x₁, y) ≤ C / t` for every `y` if `|x₁ - x₀| ≤ 7R/9`
and `t ≤ R/2` (`openHeat_le_of_good`).

The proof is the one of the source: the Poincaré inequality on the balls of radius `r` centred at
the lattice points near `x₀` (`sum_sq_clusterBall_le`, the source's (3.4)) bounds the energy
`-ψ'(t)` of `ψ(t) = p_{2t}(x₁, x₁)` from below by `r^{-2}(ψ - ε - β r^{-2})`, and the choice
`r² = 4β/ψ` gives `ψ' ≤ -c ψ²`. Two departures: all lattice points near `x₀` serve as centres (the
overlap of the balls is then counted exactly), and the initial phase, where `r(t)` of the source
would be below `N`, is handled with `r = N`, which gives exponential decay of `ψ` until
`ψ ≤ 4β/N²` (the source uses the bound `ψ(t) ≤ c t^{-1/2}` of its (1.7) instead). The time range
is `t ≤ R` rather than `t ≤ c R²/log R`.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green

namespace Rigidity.Barlow

variable {ω : Configuration 2}

/-! ### Balls, energies and good balls -/

/-- The lattice points at Euclidean distance `< r` from `y`. -/
noncomputable def latticeBall (y : Vertex 2) (r : ℝ) : Finset (Vertex 2) :=
  (indexBox y (⌈r⌉₊ : ℤ)).filter (fun x => latticeDist x y < r)

theorem mem_latticeBall {y x : Vertex 2} {r : ℝ} : x ∈ latticeBall y r ↔ latticeDist x y < r := by
  unfold latticeBall
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_indexBox.2 fun i => ?_, h⟩
    have h1 := (latticeDist_ge_abs x y i).trans_lt h
    have h2 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h3 : |((x i - y i : ℤ) : ℝ)| < ((⌈r⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3.le

theorem card_latticeBall_le (y : Vertex 2) {r : ℝ} (hr : 1 ≤ r) :
    ((latticeBall y r).card : ℝ) ≤ 25 * r ^ 2 := by
  have h1 : (latticeBall y r).card ≤ (indexBox y (⌈r⌉₊ : ℤ)).card := Finset.card_filter_le _ _
  rw [card_indexBox] at h1
  have h2 : ((latticeBall y r).card : ℝ) ≤ ((2 * ⌈r⌉₊ + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  push_cast at h2
  have h3 : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
  have h4 : (0 : ℝ) ≤ ⌈r⌉₊ := Nat.cast_nonneg _
  nlinarith

/-- The energy `Σ_{x ∈ U} Σ_{z ∈ U, z ∼ x} (u(z) - u(x))²` of `u` on the open edges inside `U`. -/
noncomputable def nbrEnergy (ω : Configuration 2) (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) : ℝ :=
  ∑ x ∈ U, ∑ z ∈ U.filter (fun z => (openGraph ω).Adj x z), (u z - u x) ^ 2

/-- **Barlow 2004, Definition 1.7** (good ball), for the Euclidean ball `K ∩ B(z, r)` of a
component `K`: the volume bound (1.15) `C_V r² ≤ |K ∩ B(z, r)|` and the weak Poincaré inequality
(1.16) with the gradient on the open edges inside `K ∩ B(z, L r)`. -/
def IsGoodBall (ω : Configuration 2) (K : OpenComponent ω) (CV CP L : ℝ) (z : Vertex 2)
    (r : ℝ) : Prop :=
  CV * r ^ 2 ≤ (clusterBall K z r).card ∧
    ∀ u : Vertex 2 → ℝ, ∑ x ∈ clusterBall K z r, (u x - finAvg (clusterBall K z r) u) ^ 2 ≤
      CP * r ^ 2 * nbrEnergy ω (clusterBall K z (L * r)) u

/-- `Σ_U u² = Σ_U (u - (u)_U)² + (Σ_U u)² / |U|`. -/
theorem sum_sq_eq_add_sq_div (U : Finset (Vertex 2)) (u : Vertex 2 → ℝ) (hU : U.Nonempty) :
    ∑ x ∈ U, u x ^ 2 = ∑ x ∈ U, (u x - finAvg U u) ^ 2 + (∑ x ∈ U, u x) ^ 2 / U.card := by
  have hc : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.card_pos.ne'
  set a := finAvg U u with ha
  have hsum : ∑ x ∈ U, u x = U.card * a := by
    rw [ha, finAvg]
    field_simp
  have hexp : ∀ x, (u x - a) ^ 2 = u x ^ 2 - 2 * a * u x + a ^ 2 := fun x => by ring
  rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hsum]
  field_simp
  ring

/-- Double counting: `Σ_{c ∈ Λ} Σ_{x ∈ B(c)} g(x) = Σ_{x ∈ W} g(x) |{c ∈ Λ : x ∈ B(c)}|`. -/
theorem sum_sum_eq_sum_mul_card (Λ W : Finset (Vertex 2)) (B : Vertex 2 → Finset (Vertex 2))
    (hB : ∀ c ∈ Λ, B c ⊆ W) (g : Vertex 2 → ℝ) :
    ∑ c ∈ Λ, ∑ x ∈ B c, g x = ∑ x ∈ W, g x * (Λ.filter (fun c => x ∈ B c)).card := by
  have h1 : ∀ c ∈ Λ, ∑ x ∈ B c, g x = ∑ x ∈ W, if x ∈ B c then g x else 0 := by
    intro c hc
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hB c hc h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Barlow 2004, (3.4)**: if every ball of radius `r` centred within `ρ + r` of `x₀` is good,
then for a nonnegative `f` of total mass at most one,
`Σ_{K ∩ B(x₀, ρ)} f² ≤ 25 C_P L² C_V^{-1} r² E(f) + 25 C_V^{-2} r^{-2}`, with `E(f)` the energy of
`f` on the open graph. -/
theorem sum_sq_clusterBall_le {K : OpenComponent ω} {CV CP L ρ r : ℝ} {x0 : Vertex 2}
    {f : Vertex 2 → ℝ} (hCV : 0 < CV) (hCP : 0 ≤ CP) (hL : 1 ≤ L) (hr : 1 ≤ r)
    (hgood : ∀ z, latticeDist z x0 < ρ + r → IsGoodBall ω K CV CP L z r)
    (hf0 : ∀ x, 0 ≤ f x) (hfs : Summable f) (hf1 : ∑' x, f x ≤ 1)
    (he : Summable fun x => ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) :
    ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 ≤
      25 * CP * L ^ 2 / CV * r ^ 2 *
          (∑' x, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) +
        25 / (CV ^ 2 * r ^ 2) := by
  set E := ∑' x, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 with hE
  have he0 : ∀ x, 0 ≤ ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 :=
    fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Λ := latticeBall x0 (ρ + r) with hΛ
  set Bc : Vertex 2 → Finset (Vertex 2) := fun c => clusterBall K c r with hBc_def
  set Bs : Vertex 2 → Finset (Vertex 2) := fun c => clusterBall K c (L * r) with hBs_def
  set W := Λ.biUnion Bs with hW
  have hrLr : r ≤ L * r := le_mul_of_one_le_left (by linarith) hL
  have hLr1 : 1 ≤ L * r := by nlinarith
  have hBs : ∀ c ∈ Λ, Bs c ⊆ W := fun c hc => Finset.subset_biUnion_of_mem Bs hc
  have hBc : ∀ c ∈ Λ, Bc c ⊆ W := fun c hc => (clusterBall_mono hrLr).trans (hBs c hc)
  have hgoodΛ : ∀ c ∈ Λ, IsGoodBall ω K CV CP L c r := fun c hc => hgood c (mem_latticeBall.1 hc)
  have hr2 : 0 < r ^ 2 := by positivity
  have hsumle : ∀ S : Finset (Vertex 2), ∑ x ∈ S, f x ≤ 1 := fun S =>
    (hfs.sum_le_tsum S fun x _ => hf0 x).trans hf1
  -- the Poincaré inequality on each ball
  have hA : ∀ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2 ≤
      CP * r ^ 2 * nbrEnergy ω (Bs c) f + (∑ x ∈ Bc c, f x) / (CV * r ^ 2) := by
    intro c hc
    obtain ⟨hvol, hP⟩ := hgoodΛ c hc
    have hpos : (0 : ℝ) < (Bc c).card := lt_of_lt_of_le (by positivity) hvol
    have hne : (Bc c).Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos)
    rw [sum_sq_eq_add_sq_div (Bc c) f hne]
    have hS0 : 0 ≤ ∑ x ∈ Bc c, f x := Finset.sum_nonneg fun x _ => hf0 x
    have hS1 := hsumle (Bc c)
    have h2 : (∑ x ∈ Bc c, f x) ^ 2 / (Bc c).card ≤ (∑ x ∈ Bc c, f x) / (CV * r ^ 2) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      calc (∑ x ∈ Bc c, f x) ^ 2 * (CV * r ^ 2) ≤ (∑ x ∈ Bc c, f x) * (CV * r ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
        _ ≤ (∑ x ∈ Bc c, f x) * (Bc c).card := mul_le_mul_of_nonneg_left hvol hS0
    exact add_le_add (hP f) h2
  -- the multiplicity of the covering
  have hcount : ∀ x (ρ' : ℝ), 1 ≤ ρ' →
      ((Λ.filter (fun c => x ∈ clusterBall K c ρ')).card : ℝ) ≤ 25 * ρ' ^ 2 := by
    intro x ρ' hρ'
    have hsub : Λ.filter (fun c => x ∈ clusterBall K c ρ') ⊆ latticeBall x ρ' := by
      intro c hc
      rw [Finset.mem_filter, mem_clusterBall] at hc
      rw [mem_latticeBall, latticeDist_comm]
      exact hc.2.2
    have h := Finset.card_le_card hsub
    have h' : ((Λ.filter (fun c => x ∈ clusterBall K c ρ')).card : ℝ) ≤
        (latticeBall x ρ').card := by exact_mod_cast h
    exact h'.trans (card_latticeBall_le x hρ')
  have hB : ∑ c ∈ Λ, nbrEnergy ω (Bs c) f ≤ 25 * (L * r) ^ 2 * E := by
    have h1 : ∀ c ∈ Λ, nbrEnergy ω (Bs c) f ≤
        ∑ x ∈ Bs c, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 := by
      intro c _
      unfold nbrEnergy
      refine Finset.sum_le_sum fun x _ => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
      intro z hz
      rw [Finset.mem_filter] at hz
      exact ((openGraph ω).mem_neighborFinset x z).2 hz.2
    calc ∑ c ∈ Λ, nbrEnergy ω (Bs c) f
        ≤ ∑ c ∈ Λ, ∑ x ∈ Bs c, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 :=
          Finset.sum_le_sum h1
      _ = ∑ x ∈ W, (∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) *
            (Λ.filter (fun c => x ∈ Bs c)).card :=
          sum_sum_eq_sum_mul_card Λ W Bs hBs
            (fun x => ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2)
      _ ≤ ∑ x ∈ W, (∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) *
            (25 * (L * r) ^ 2) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcount x (L * r) hLr1) (he0 x)
      _ = 25 * (L * r) ^ 2 *
            ∑ x ∈ W, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ 25 * (L * r) ^ 2 * E :=
          mul_le_mul_of_nonneg_left (he.sum_le_tsum W fun x _ => he0 x) (by positivity)
  have hC : ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ≤ 25 * r ^ 2 := by
    calc ∑ c ∈ Λ, ∑ x ∈ Bc c, f x
        = ∑ x ∈ W, f x * (Λ.filter (fun c => x ∈ Bc c)).card := sum_sum_eq_sum_mul_card Λ W Bc hBc f
      _ ≤ ∑ x ∈ W, f x * (25 * r ^ 2) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcount x r hr) (hf0 x)
      _ = 25 * r ^ 2 * ∑ x ∈ W, f x := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ 25 * r ^ 2 * 1 := mul_le_mul_of_nonneg_left (hsumle W) (by positivity)
      _ = 25 * r ^ 2 := mul_one _
  -- every point of `K ∩ B(x₀, ρ)` is covered by at least `C_V r²` balls
  have hsub : clusterBall K x0 ρ ⊆ W := by
    intro x hx
    have hx' := mem_clusterBall.1 hx
    have hxΛ : x ∈ Λ := by
      rw [hΛ, mem_latticeBall]
      linarith
    refine Finset.mem_biUnion.2 ⟨x, hxΛ, ?_⟩
    rw [hBs_def, mem_clusterBall]
    refine ⟨hx'.1, ?_⟩
    have : latticeDist x x = 0 := by simp [latticeDist]
    rw [this]
    positivity
  have hD : CV * r ^ 2 * ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 ≤ ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2 := by
    rw [sum_sum_eq_sum_mul_card Λ W Bc hBc (fun x => f x ^ 2)]
    calc CV * r ^ 2 * ∑ x ∈ clusterBall K x0 ρ, f x ^ 2
        = ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 * (CV * r ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => mul_comm _ _
      _ ≤ ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 * (Λ.filter (fun c => x ∈ Bc c)).card := by
          refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hx' := mem_clusterBall.1 hx
          obtain ⟨hvol, -⟩ := hgood x (by linarith [hx'.2])
          refine hvol.trans ?_
          have hinc : clusterBall K x r ⊆ Λ.filter (fun c => x ∈ Bc c) := by
            intro c hc
            have hc' := mem_clusterBall.1 hc
            rw [Finset.mem_filter, hΛ, mem_latticeBall, hBc_def, mem_clusterBall]
            have htri := latticeDist_triangle c x x0
            rw [latticeDist_comm x c] at htri
            refine ⟨by linarith [hx'.2, hc'.2], hx'.1, ?_⟩
            rw [latticeDist_comm]
            exact hc'.2
          exact_mod_cast Finset.card_le_card hinc
      _ ≤ ∑ x ∈ W, f x ^ 2 * (Λ.filter (fun c => x ∈ Bc c)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by positivity
  -- combination
  have hsumA : ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2 ≤
      CP * r ^ 2 * (25 * (L * r) ^ 2 * E) + 25 * r ^ 2 / (CV * r ^ 2) := by
    calc ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2
        ≤ ∑ c ∈ Λ, (CP * r ^ 2 * nbrEnergy ω (Bs c) f + (∑ x ∈ Bc c, f x) / (CV * r ^ 2)) :=
          Finset.sum_le_sum hA
      _ = CP * r ^ 2 * ∑ c ∈ Λ, nbrEnergy ω (Bs c) f +
            (∑ c ∈ Λ, ∑ x ∈ Bc c, f x) / (CV * r ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hB (by positivity))
          (div_le_div_of_nonneg_right hC (by positivity))
  have hkey : CV * r ^ 2 * ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 ≤
      CV * r ^ 2 * (25 * CP * L ^ 2 / CV * r ^ 2 * E + 25 / (CV ^ 2 * r ^ 2)) := by
    refine hD.trans (hsumA.trans (le_of_eq ?_))
    field_simp
  exact le_of_mul_le_mul_left hkey (by positivity)

/-! ### Two comparison lemmas for differential inequalities -/

/-- If `ψ' ≤ 0` and `ψ' ≤ -κ ψ` wherever `ψ ≥ m`, then `ψ(b) ≤ max(m, ψ(a) e^{-κ(b - a)})`. -/
theorem le_max_exp_of_hasDerivAt {ψ ψ' : ℝ → ℝ} {a b κ m : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn ψ (Set.Icc a b)) (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt ψ (ψ' s) s)
    (hneg : ∀ s ∈ Set.Ioo a b, ψ' s ≤ 0)
    (hdec : ∀ s ∈ Set.Ioo a b, m ≤ ψ s → ψ' s ≤ -κ * ψ s) :
    ψ b ≤ max m (ψ a * Real.exp (-κ * (b - a))) := by
  have hanti : AntitoneOn ψ (Set.Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := ψ') (convex_Icc a b) hcont
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact (hd s hs).hasDerivWithinAt
    · rw [interior_Icc] at hs
      exact hneg s hs
  by_cases h : ∃ s ∈ Set.Icc a b, ψ s < m
  · obtain ⟨s, hs, hlt⟩ := h
    exact le_max_of_le_left ((hanti hs ⟨hab, le_rfl⟩ hs.2).trans hlt.le)
  · simp only [not_exists, not_and, not_lt] at h
    refine le_max_of_le_right ?_
    have hganti : AntitoneOn (fun s => ψ s * Real.exp (κ * s)) (Set.Icc a b) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := fun s => (ψ' s + κ * ψ s) * Real.exp (κ * s)) (convex_Icc a b) ?_
        (fun s hs => ?_) (fun s hs => ?_)
      · exact hcont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
      · rw [interior_Icc] at hs
        have h1 := (hd s hs).mul ((hasDerivAt_id' s).const_mul κ).exp
        exact (h1.congr_deriv (by ring)).hasDerivWithinAt
      · rw [interior_Icc] at hs
        have := hdec s hs (h s (Set.Ioo_subset_Icc_self hs))
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
    have hg := hganti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    refine le_of_mul_le_mul_right ?_ (Real.exp_pos (κ * b))
    calc ψ b * Real.exp (κ * b) ≤ ψ a * Real.exp (κ * a) := hg
      _ = ψ a * Real.exp (-κ * (b - a)) * Real.exp (κ * b) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf

/-- If `ψ > 0`, `ψ' ≤ 0` and `ψ' ≤ -c ψ²` wherever `ψ ≥ m`, then
`ψ(b) ≤ max(m, (ψ(a)^{-1} + c (b - a))^{-1})`. -/
theorem le_max_inv_of_hasDerivAt {ψ ψ' : ℝ → ℝ} {a b c m : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hcont : ContinuousOn ψ (Set.Icc a b)) (hd : ∀ s ∈ Set.Ioo a b, HasDerivAt ψ (ψ' s) s)
    (hneg : ∀ s ∈ Set.Ioo a b, ψ' s ≤ 0) (hpos : ∀ s ∈ Set.Icc a b, 0 < ψ s)
    (hdec : ∀ s ∈ Set.Ioo a b, m ≤ ψ s → ψ' s ≤ -c * ψ s ^ 2) :
    ψ b ≤ max m ((ψ a)⁻¹ + c * (b - a))⁻¹ := by
  have hanti : AntitoneOn ψ (Set.Icc a b) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := ψ') (convex_Icc a b) hcont
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact (hd s hs).hasDerivWithinAt
    · rw [interior_Icc] at hs
      exact hneg s hs
  by_cases h : ∃ s ∈ Set.Icc a b, ψ s < m
  · obtain ⟨s, hs, hlt⟩ := h
    exact le_max_of_le_left ((hanti hs ⟨hab, le_rfl⟩ hs.2).trans hlt.le)
  · simp only [not_exists, not_and, not_lt] at h
    refine le_max_of_le_right ?_
    have hgmono : MonotoneOn (fun s => (ψ s)⁻¹ - c * s) (Set.Icc a b) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun s => -ψ' s / ψ s ^ 2 - c * 1) (convex_Icc a b) ?_ (fun s hs => ?_)
        (fun s hs => ?_)
      · refine (hcont.inv₀ fun s hs => (hpos s hs).ne').sub ?_
        exact (continuous_const.mul continuous_id).continuousOn
      · rw [interior_Icc] at hs
        have h1 := ((hd s hs).inv (hpos s (Set.Ioo_subset_Icc_self hs)).ne').sub
          ((hasDerivAt_id' s).const_mul c)
        exact h1.hasDerivWithinAt
      · rw [interior_Icc] at hs
        have hψ := hpos s (Set.Ioo_subset_Icc_self hs)
        have := hdec s hs (h s (Set.Ioo_subset_Icc_self hs))
        rw [mul_one, sub_nonneg, le_div_iff₀ (by positivity)]
        linarith
    have hg := hgmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    have hpa := hpos a ⟨le_rfl, hab⟩
    have hpb := hpos b ⟨hab, le_rfl⟩
    have hD : 0 < (ψ a)⁻¹ + c * (b - a) := by
      have : 0 ≤ c * (b - a) := mul_nonneg hc (by linarith)
      have : 0 < (ψ a)⁻¹ := inv_pos.2 hpa
      linarith
    have hle : (ψ a)⁻¹ + c * (b - a) ≤ (ψ b)⁻¹ := by
      simp only at hg
      linarith
    calc ψ b = ((ψ b)⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ ((ψ a)⁻¹ + c * (b - a))⁻¹ := inv_anti₀ hD hle

/-! ### Proposition 3.1 and Corollary 3.2 -/

theorem openHeat_eq_zero_of_mem_of_notMem {K : OpenComponent ω} {x y : Vertex 2}
    (hx : x ∈ K.supp) (hy : y ∉ K.supp) (t : ℝ) : openHeat ω t x y = 0 := by
  refine openHeat_eq_zero_of_not_reachable ω (fun h => hy ?_) t
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact (SimpleGraph.ConnectedComponent.sound h).symm

theorem exp_neg_le_openHeat_self {t : ℝ} (ht : 0 ≤ t) (x : Vertex 2) :
    Real.exp (-4 * t) ≤ openHeat ω t x x := by
  have hs := summable_vsrwHeat (G := openGraph ω) (D := 4) (by norm_num)
    (openGraph_degree_le_four ω) t x x
  have h := hs.le_tsum 0 (fun n _ => mul_nonneg (poissonWeight_nonneg ht n)
    (lazyPow_mem_Icc (by norm_num) (openGraph_degree_le_four ω) n x x).1)
  have h0 : poissonWeight 4 t 0 * lazyPow (openGraph ω) 4 0 x x = Real.exp (-4 * t) := by
    simp [poissonWeight, lazyPow_zero]
  rw [h0] at h
  exact h

/-- `Σ_y f(y)² ≤ Σ_{y ∈ S} f(y)² + ε` if `f ≥ 0`, `Σ f ≤ 1` and `f ≤ ε` off `S`. -/
theorem tsum_sq_le_sum_sq_add {f : Vertex 2 → ℝ} {S : Finset (Vertex 2)} {ε : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfs : Summable f) (hf1 : ∑' x, f x ≤ 1) (hε0 : 0 ≤ ε)
    (hout : ∀ x ∉ S, f x ≤ ε) : ∑' x, f x ^ 2 ≤ ∑ x ∈ S, f x ^ 2 + ε := by
  have hg : Summable fun x => if x ∈ S then f x ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := S) fun x hx => if_neg hx
  have hpt : ∀ x, f x ^ 2 ≤ (if x ∈ S then f x ^ 2 else 0) + ε * f x := by
    intro x
    by_cases hx : x ∈ S
    · rw [if_pos hx]
      nlinarith [hf0 x]
    · rw [if_neg hx, zero_add, sq]
      exact mul_le_mul_of_nonneg_right (hout x hx) (hf0 x)
  have hsum := hg.add (hfs.mul_left ε)
  have hsq : Summable fun x => f x ^ 2 :=
    hsum.of_nonneg_of_le (fun x => sq_nonneg _) hpt
  calc ∑' x, f x ^ 2 ≤ ∑' x, ((if x ∈ S then f x ^ 2 else 0) + ε * f x) :=
        Summable.tsum_le_tsum hpt hsq hsum
    _ = ∑ x ∈ S, f x ^ 2 + ε * ∑' x, f x := by
        rw [hg.tsum_add (hfs.mul_left ε), tsum_mul_left,
          tsum_eq_sum (s := S) (fun x hx => if_neg hx)]
        congr 1
        exact Finset.sum_congr rfl fun x hx => if_pos hx
    _ ≤ ∑ x ∈ S, f x ^ 2 + ε * 1 := by gcongr
    _ = _ := by ring

theorem phase_one_step {ψ ε E α β N : ℝ} (hα : 0 < α) (hN : 0 < N)
    (hkey : ψ - ε ≤ α * N ^ 2 * E + β / N ^ 2) (hm : 4 * β / N ^ 2 ≤ ψ)
    (hε : ε ≤ β / N ^ 2) : -E ≤ -(1 / (2 * α * N ^ 2)) * ψ := by
  have h4 : 4 * β / N ^ 2 = 4 * (β / N ^ 2) := by ring
  have h1 : ψ / 2 ≤ α * N ^ 2 * E := by linarith
  rw [neg_mul, neg_le_neg_iff, one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  linarith

theorem phase_two_step {ψ ε E α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hψ : 0 < ψ)
    (hkey : ψ - ε ≤ α * (4 * β / ψ) * E + ψ / 4) (hε : 4 * ε ≤ ψ) :
    -E ≤ -(1 / (8 * α * β)) * ψ ^ 2 := by
  have h1 : ψ / 2 ≤ α * (4 * β / ψ) * E := by linarith
  have h2 : α * (4 * β / ψ) * E = 4 * α * β * E / ψ := by
    field_simp
  rw [h2, le_div_iff₀ hψ] at h1
  rw [neg_mul, neg_le_neg_iff, one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- The constant of Proposition 3.1. -/
noncomputable def diagConst (CV CP L : ℝ) : ℝ :=
  max (10000 * CP * L ^ 2 / CV ^ 3) (max 1 (32400 / CV ^ 2))

theorem one_le_diagConst (CV CP L : ℝ) : 1 ≤ diagConst CV CP L :=
  le_max_of_le_right (le_max_left _ _)

/-- **Barlow 2004, Proposition 3.1** (on-diagonal upper bound in a very good ball), for the
variable speed walk and Euclidean balls: `p_{2t}(x₁, x₁) ≤ C / t` for
`2 C_P L² C_V N⁴ ≤ t ≤ R`. -/
theorem openHeat_diag_le_of_good {K : OpenComponent ω} {CV CP L R N ε : ℝ} {x0 x1 : Vertex 2}
    (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N) (hNR : N ≤ R / 18)
    (hgood : ∀ z, latticeDist z x0 ≤ R → ∀ r, N ≤ r → r ≤ R / 18 → IsGoodBall ω K CV CP L z r)
    (hx1 : x1 ∈ K.supp) (hx10 : latticeDist x1 x0 ≤ 8 * R / 9) (hε0 : 0 ≤ ε)
    (hε : ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x1 → openHeat ω s x1 y ≤ ε)
    (hεN : ε * N ^ 2 * CV ^ 2 ≤ 25) (hεR : 4 * ε * R ≤ 1) {t : ℝ}
    (ht0 : 2 * (CP * L ^ 2 * CV * N ^ 4) ≤ t) (htR : t ≤ R) :
    openHeat ω (2 * t) x1 x1 ≤ diagConst CV CP L / t := by
  set α := 25 * CP * L ^ 2 / CV with hα
  set β := 25 / CV ^ 2 with hβ
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 < β := by positivity
  have hN0 : 0 < N := by linarith
  have hR18 : 18 ≤ R := by linarith
  set T0 := CP * L ^ 2 * CV * N ^ 4 with hT0
  have hT00 : 0 < T0 := by positivity
  have ht : 0 < t := by linarith
  set ψ : ℝ → ℝ := fun s => openHeat ω (2 * s) x1 x1 with hψ
  set E : ℝ → ℝ := fun s => ∑' y, ∑ z ∈ (openGraph ω).neighborFinset y,
    (openHeat ω s x1 z - openHeat ω s x1 y) ^ 2 with hE
  have hE0 : ∀ s, 0 ≤ E s := fun s => tsum_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : ∀ s, 0 ≤ s → HasDerivAt ψ (-E s) s := fun s hs => hasDerivAt_openHeat_two_mul hs x1
  have hcont : Continuous ψ :=
    (continuous_openHeat ω x1 x1).comp (continuous_const.mul continuous_id)
  -- the key inequality (3.5) at time `s` and radius `r`
  have hkey : ∀ s, 0 ≤ s → s ≤ R → ∀ r, N ≤ r → r ≤ R / 18 →
      ψ s - ε ≤ α * r ^ 2 * E s + β / r ^ 2 := by
    intro s hs hsR r hNr hrR
    have hr1 : 1 ≤ r := hN.trans hNr
    have hf0 : ∀ y, 0 ≤ openHeat ω s x1 y := fun y => openHeat_nonneg ω hs x1 y
    have hfs := (hasSum_openHeat ω hs x1).summable
    have hf1 : ∑' y, openHeat ω s x1 y ≤ 1 := (hasSum_openHeat ω hs x1).tsum_eq.le
    have hout : ∀ y ∉ clusterBall K x0 (17 * R / 18), openHeat ω s x1 y ≤ ε := by
      intro y hy
      by_cases hyK : y ∈ K.supp
      · have hy' : 17 * R / 18 ≤ latticeDist y x0 := by
          by_contra hlt
          exact hy (mem_clusterBall.2 ⟨hyK, lt_of_not_ge hlt⟩)
        have htri := latticeDist_triangle y x1 x0
        rw [latticeDist_comm x1 y] at htri
        exact hε s hs hsR y (by linarith)
      · rw [openHeat_eq_zero_of_mem_of_notMem hx1 hyK]
        exact hε0
    have h1 := tsum_sq_le_sum_sq_add hf0 hfs hf1 hε0 hout
    have h2 := sum_sq_clusterBall_le (K := K) (x0 := x0) (ρ := 17 * R / 18) (r := r) hCV hCP.le
      hL hr1 (fun z hz => hgood z (by linarith) r hNr hrR) hf0 hfs hf1
      (summable_openHeat_energy hs x1)
    have hψs : ψ s = ∑' y, openHeat ω s x1 y ^ 2 := (hasSum_openHeat_sq hs x1).tsum_eq.symm
    rw [hψs]
    have : 25 / (CV ^ 2 * r ^ 2) = β / r ^ 2 := by rw [hβ]; field_simp
    rw [this] at h2
    linarith
  -- phase one: `ψ(T₀) ≤ 4β/N²`
  have hψ0 : ψ 0 = 1 := by
    simp only [hψ, mul_zero]
    rw [openHeat_zero]
    simp
  have hphase1 : ψ T0 ≤ 4 * β / N ^ 2 := by
    have h := le_max_exp_of_hasDerivAt (ψ := ψ) (ψ' := fun s => -E s) (a := 0) (b := T0)
      (κ := 1 / (2 * α * N ^ 2)) (m := 4 * β / N ^ 2) hT00.le hcont.continuousOn
      (fun s hs => hd s hs.1.le) (fun s _ => neg_nonpos.2 (hE0 s)) (fun s hs hm => by
        refine phase_one_step hα0 hN0 (hkey s hs.1.le (by linarith [hs.2]) N le_rfl hNR) hm ?_
        rw [le_div_iff₀ (by positivity), hβ]
        rw [le_div_iff₀ (by positivity)]
        nlinarith)
    refine h.trans (max_le le_rfl ?_)
    rw [hψ0, one_mul, sub_zero]
    have hκT : 1 / (2 * α * N ^ 2) * T0 = CV ^ 2 * N ^ 2 / 50 := by
      rw [hα, hT0]
      field_simp
      ring
    have hexp : Real.exp (-(1 / (2 * α * N ^ 2)) * T0) ≤ 50 / (CV ^ 2 * N ^ 2) := by
      rw [neg_mul, hκT, Real.exp_neg]
      have hx : CV ^ 2 * N ^ 2 / 50 ≤ Real.exp (CV ^ 2 * N ^ 2 / 50) := by
        linarith [Real.add_one_le_exp (CV ^ 2 * N ^ 2 / 50)]
      have hxpos : 0 < CV ^ 2 * N ^ 2 / 50 := by positivity
      calc (Real.exp (CV ^ 2 * N ^ 2 / 50))⁻¹ ≤ (CV ^ 2 * N ^ 2 / 50)⁻¹ := inv_anti₀ hxpos hx
        _ = 50 / (CV ^ 2 * N ^ 2) := by field_simp
    refine hexp.trans ?_
    have h4 : 4 * β / N ^ 2 = 100 / (CV ^ 2 * N ^ 2) := by
      rw [hβ]
      field_simp
      ring
    rw [h4]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  -- antitone
  have hanti : AntitoneOn ψ (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => -E s) (convex_Ici 0)
      hcont.continuousOn (fun s hs => ?_) (fun s _ => neg_nonpos.2 (hE0 s))
    rw [interior_Ici] at hs
    exact (hd s (le_of_lt hs)).hasDerivWithinAt
  -- phase two
  have hT0t : T0 ≤ t := by linarith
  have hψpos : ∀ s, 0 ≤ s → 0 < ψ s := fun s hs =>
    lt_of_lt_of_le (Real.exp_pos _) (exp_neg_le_openHeat_self (by linarith) x1)
  have hphase2 := le_max_inv_of_hasDerivAt (ψ := ψ) (ψ' := fun s => -E s) (a := T0) (b := t)
    (c := 1 / (8 * α * β)) (m := max (4 * ε) (4 * β * 324 / R ^ 2)) hT0t (by positivity)
    hcont.continuousOn (fun s hs => hd s (by linarith [hs.1])) (fun s _ => neg_nonpos.2 (hE0 s))
    (fun s hs => hψpos s (by linarith [hs.1])) (fun s hs hm => by
      have hs0 : 0 ≤ s := by linarith [hs.1]
      have hψs := hψpos s hs0
      have hψT : ψ s ≤ 4 * β / N ^ 2 :=
        (hanti (Set.mem_Ici.2 hT00.le) (Set.mem_Ici.2 hs0) hs.1.le).trans hphase1
      have hm1 : 4 * ε ≤ ψ s := (le_max_left _ _).trans hm
      have hm2 : 4 * β * 324 / R ^ 2 ≤ ψ s := (le_max_right _ _).trans hm
      set r := Real.sqrt (4 * β / ψ s) with hr
      have hr2 : r ^ 2 = 4 * β / ψ s := Real.sq_sqrt (by positivity)
      have hNr : N ≤ r := by
        rw [hr, ← Real.sqrt_sq hN0.le]
        refine Real.sqrt_le_sqrt ?_
        rw [le_div_iff₀ hψs]
        rw [le_div_iff₀ (by positivity)] at hψT
        linarith
      have hrR : r ≤ R / 18 := by
        rw [hr, ← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ R / 18)]
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_iff₀ hψs]
        rw [div_le_iff₀ (by positivity)] at hm2
        nlinarith
      have hk := hkey s hs0 (by linarith [hs.2]) r hNr hrR
      rw [hr2] at hk
      have hβr : β / (4 * β / ψ s) = ψ s / 4 := by field_simp
      rw [hβr] at hk
      exact phase_two_step hα0 hβ0 hψs hk hm1)
  -- conclusion
  have hpos0 : 0 < (ψ T0)⁻¹ := inv_pos.2 (hψpos T0 hT00.le)
  have hc : 0 < 1 / (8 * α * β) := by positivity
  have hfin : ((ψ T0)⁻¹ + 1 / (8 * α * β) * (t - T0))⁻¹ ≤ 16 * α * β / t := by
    have hlow : 1 / (8 * α * β) * (t / 2) ≤ (ψ T0)⁻¹ + 1 / (8 * α * β) * (t - T0) := by
      have : t / 2 ≤ t - T0 := by linarith
      nlinarith
    have hlowpos : 0 < 1 / (8 * α * β) * (t / 2) := by positivity
    calc ((ψ T0)⁻¹ + 1 / (8 * α * β) * (t - T0))⁻¹ ≤ (1 / (8 * α * β) * (t / 2))⁻¹ :=
          inv_anti₀ hlowpos hlow
      _ = 16 * α * β / t := by field_simp; ring
  have hm2t : max (4 * ε) (4 * β * 324 / R ^ 2) ≤ max 1 (32400 / CV ^ 2) / t := by
    refine max_le ?_ ?_
    · have h1 : 4 * ε ≤ 1 / t := by
        rw [le_div_iff₀ ht]
        nlinarith
      exact h1.trans (div_le_div_of_nonneg_right (le_max_left _ _) ht.le)
    · have h1 : 4 * β * 324 / R ^ 2 ≤ 32400 / CV ^ 2 / t := by
        rw [div_le_div_iff₀ (by positivity) ht, hβ]
        have hRt : t ≤ R ^ 2 := by nlinarith
        have : 4 * (25 / CV ^ 2) * 324 = 32400 / CV ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hRt (by positivity)
      exact h1.trans (div_le_div_of_nonneg_right (le_max_right _ _) ht.le)
  have h16 : 16 * α * β / t = 10000 * CP * L ^ 2 / CV ^ 3 / t := by
    rw [hα, hβ]
    field_simp
    ring
  calc openHeat ω (2 * t) x1 x1 = ψ t := rfl
    _ ≤ max (max (4 * ε) (4 * β * 324 / R ^ 2)) ((ψ T0)⁻¹ + 1 / (8 * α * β) * (t - T0))⁻¹ :=
        hphase2
    _ ≤ max (max 1 (32400 / CV ^ 2) / t) (10000 * CP * L ^ 2 / CV ^ 3 / t) :=
        max_le_max hm2t (hfin.trans (le_of_eq h16))
    _ = diagConst CV CP L / t := by
        rw [diagConst, max_div_div_right ht.le, max_comm]

/-- **Barlow 2004, Corollary 3.2**: under the hypotheses of Proposition 3.1, if
`|x₁ - x₀| ≤ 7R/9` then `p_{2t}(x₁, y) ≤ C / t` for every `y` and `2 C_P L² C_V N⁴ ≤ t ≤ R/2`. -/
theorem openHeat_le_of_good {K : OpenComponent ω} {CV CP L R N ε : ℝ} {x0 x1 : Vertex 2}
    (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N) (hNR : N ≤ R / 18)
    (hgood : ∀ z, latticeDist z x0 ≤ R → ∀ r, N ≤ r → r ≤ R / 18 → IsGoodBall ω K CV CP L z r)
    (hx1 : x1 ∈ K.supp) (hx10 : latticeDist x1 x0 ≤ 7 * R / 9) (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ K.supp, ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x →
      openHeat ω s x y ≤ ε)
    (hεN : ε * N ^ 2 * CV ^ 2 ≤ 25) (hεR : 4 * ε * R ≤ 1) (y : Vertex 2) {t : ℝ}
    (ht0 : 2 * (CP * L ^ 2 * CV * N ^ 4) ≤ t) (htR : t ≤ R / 2) :
    openHeat ω (2 * t) x1 y ≤ diagConst CV CP L / t := by
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht0
  have htR' : t ≤ R := by linarith
  by_cases hyK : y ∈ K.supp
  · by_cases hy0 : latticeDist y x0 ≤ 8 * R / 9
    · have h1 := openHeat_diag_le_of_good hCV hCP hL hN hNR hgood hx1 (by linarith) hε0
        (hε x1 hx1) hεN hεR ht0 htR'
      have h2 := openHeat_diag_le_of_good hCV hCP hL hN hNR hgood hyK hy0 hε0
        (hε y hyK) hεN hεR ht0 htR'
      calc openHeat ω (2 * t) x1 y
          ≤ (openHeat ω (2 * t) x1 x1 + openHeat ω (2 * t) y y) / 2 :=
            openHeat_two_mul_le_half_add ht.le x1 y
        _ ≤ (diagConst CV CP L / t + diagConst CV CP L / t) / 2 := by gcongr
        _ = diagConst CV CP L / t := by ring
    · have htri := latticeDist_triangle y x1 x0
      rw [latticeDist_comm x1 y] at htri
      have h1 := hε x1 hx1 (2 * t) (by linarith) (by linarith) y (by linarith)
      refine h1.trans ?_
      have hR : 0 < R := by linarith
      have h2 : ε ≤ 1 / (4 * R) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      refine h2.trans ?_
      calc 1 / (4 * R) ≤ 1 / t := by
            rw [div_le_div_iff₀ (by positivity) ht]
            linarith
        _ ≤ diagConst CV CP L / t := div_le_div_of_nonneg_right (one_le_diagConst _ _ _) ht.le
  · rw [openHeat_eq_zero_of_mem_of_notMem hx1 hyK]
    exact div_nonneg (zero_le_one.trans (one_le_diagConst _ _ _)) ht.le

end Rigidity.Barlow
