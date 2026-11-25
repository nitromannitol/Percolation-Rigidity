import Rigidity.Proofs.BarlowLattice.HeatEnergy
import Rigidity.Proofs.WeakPoincare.Balls
import Rigidity.Proofs.Barlow.OnDiagonal

/-!
# The on-diagonal upper bound in a very good ball, in every dimension

This file proves Proposition 3.1 and Corollary 3.2 of Barlow (*Random walks on supercritical
percolation clusters*, Ann. Probab. 32 (2004)) for the variable speed random walk on the open graph
of a bond configuration of `ℤ^d`, with Euclidean balls of a component `K` in place of the chemical
balls of the source; it is the `d`-dimensional form of `Rigidity.Barlow.openHeat_diag_le_of_good`.

A ball `B(z, r)` is good (`Rigidity.WeakPoincare.IsGoodBall`, Definition 1.7 of the source) if
`|K ∩ B(z, r)| ≥ C_V r^d` and the weak Poincaré inequality (1.16) holds with the gradient on
`K ∩ B(z, L r)`. If every ball `B(z, r)` with `|z - x₀| ≤ R` and `N ≤ r ≤ R/18` is good, and the
heat kernel from `x₁` is at most `ε` at distance `R/18` up to time `R`, then for
`|x₁ - x₀| ≤ 8R/9`

  `p_{2t}(x₁, x₁) ≤ C t^{-d/2}`   for `2 C_P L^d C_V N^{d+2} ≤ t ≤ R`

(`bondHeat_diag_le_of_good`; `t^{-d/2}` is written `(√t)^{-d}`), and `p_{2t}(x₁, y) ≤ C t^{-d/2}` for
every `y` if `|x₁ - x₀| ≤ 7R/9` and `t ≤ R/2` (`bondHeat_le_of_good`).

The proof is the one of the source: the Poincaré inequality on the balls of radius `r` centred at
the lattice points near `x₀` (`sum_sq_clusterBall_le`, the source's (3.4)) bounds the energy
`-ψ'(t)` of `ψ(t) = p_{2t}(x₁, x₁)` from below by `r^{-2}(ψ - ε - β r^{-d})`, and the choice
`r^d = 4β/ψ` gives `ψ' ≤ -c ψ^{1+2/d}`, that is `(ψ^{2/d})' ≤ -(2c/d) (ψ^{2/d})²`. Two departures:
all lattice points near `x₀` serve as centres (the overlap of the balls is then counted exactly), and
the initial phase, where `r(t)` of the source would be below `N`, is handled with `r = N`, which
gives exponential decay of `ψ` until `ψ ≤ 4β/N^d` (the source uses the bound `ψ(t) ≤ c t^{-1/2}`
of its (1.7) instead). The time range is `t ≤ R` rather than `t ≤ c R²/log R`.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green Rigidity.WeakPoincare Rigidity.Proofs.Cluster

namespace Rigidity.BarlowLattice

variable {d : ℕ}

variable [NeZero d] {ω : Configuration d}

/-! ### Balls -/

/-- The lattice points at Euclidean distance `< r` from `y`. -/
noncomputable def latticeBall (y : Vertex d) (r : ℝ) : Finset (Vertex d) :=
  (box y (⌈r⌉₊ : ℤ)).filter (fun x => latticeDist x y < r)

omit [NeZero d] in
theorem mem_latticeBall {y x : Vertex d} {r : ℝ} : x ∈ latticeBall y r ↔ latticeDist x y < r := by
  unfold latticeBall
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_box.2 fun i => ?_, h⟩
    have h1 := (abs_sub_le_latticeDist x y i).trans_lt h
    have h2 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h3 : |((x i - y i : ℤ) : ℝ)| < ((⌈r⌉₊ : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3.le

omit [NeZero d] in
/-- `|B(y, r) ∩ ℤ^d| ≤ (5 r)^d` for `r ≥ 1`. -/
theorem card_latticeBall_le (y : Vertex d) {r : ℝ} (hr : 1 ≤ r) :
    ((latticeBall y r).card : ℝ) ≤ (5 * r) ^ d := by
  have h1 : (latticeBall y r).card ≤ (box y (⌈r⌉₊ : ℤ)).card := Finset.card_filter_le _ _
  have h2 : ((latticeBall y r).card : ℝ) ≤ (box y (⌈r⌉₊ : ℤ)).card := by exact_mod_cast h1
  rw [card_box y (by positivity)] at h2
  refine h2.trans (pow_le_pow_left₀ (by positivity) ?_ d)
  have h3 : (⌈r⌉₊ : ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
  push_cast
  linarith

omit [NeZero d] in
/-- `Σ_U u² = Σ_U (u - (u)_U)² + (Σ_U u)² / |U|`. -/
theorem sum_sq_eq_add_sq_div (U : Finset (Vertex d)) (u : Vertex d → ℝ) (hU : U.Nonempty) :
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

omit [NeZero d] in
/-- Double counting: `Σ_{c ∈ Λ} Σ_{x ∈ B(c)} g(x) = Σ_{x ∈ W} g(x) |{c ∈ Λ : x ∈ B(c)}|`. -/
theorem sum_sum_eq_sum_mul_card (Λ W : Finset (Vertex d)) (B : Vertex d → Finset (Vertex d))
    (hB : ∀ c ∈ Λ, B c ⊆ W) (g : Vertex d → ℝ) :
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

omit [NeZero d] in
/-- **Barlow 2004, (3.4)**: if every ball of radius `r` centred within `ρ + r` of `x₀` is good,
then for a nonnegative `f` of total mass at most one,
`Σ_{K ∩ B(x₀, ρ)} f² ≤ 5^d C_P L^d C_V^{-1} r² E(f) + 5^d C_V^{-2} r^{-d}`, with `E(f)` the energy of
`f` on the open graph. -/
theorem sum_sq_clusterBall_le {K : OpenComponent ω} {CV CP L ρ r : ℝ} {x0 : Vertex d}
    {f : Vertex d → ℝ} (hCV : 0 < CV) (hCP : 0 ≤ CP) (hL : 1 ≤ L) (hr : 1 ≤ r)
    (hgood : ∀ z, latticeDist z x0 < ρ + r → IsGoodBall ω K CV CP L z r)
    (hf0 : ∀ x, 0 ≤ f x) (hfs : Summable f) (hf1 : ∑' x, f x ≤ 1)
    (he : Summable fun x => ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) :
    ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 ≤
      5 ^ d * CP * L ^ d / CV * r ^ 2 *
          (∑' x, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2) +
        5 ^ d / (CV ^ 2 * r ^ d) := by
  set E := ∑' x, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 with hE
  have he0 : ∀ x, 0 ≤ ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 :=
    fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Λ := latticeBall x0 (ρ + r) with hΛ
  set Bc : Vertex d → Finset (Vertex d) := fun c => clusterBall K c r with hBc_def
  set Bs : Vertex d → Finset (Vertex d) := fun c => clusterBall K c (L * r) with hBs_def
  set W := Λ.biUnion Bs with hW
  have hrLr : r ≤ L * r := le_mul_of_one_le_left (by linarith) hL
  have hLr1 : 1 ≤ L * r := by nlinarith
  have hBs : ∀ c ∈ Λ, Bs c ⊆ W := fun c hc => Finset.subset_biUnion_of_mem Bs hc
  have hBc : ∀ c ∈ Λ, Bc c ⊆ W := fun c hc => (clusterBall_mono hrLr).trans (hBs c hc)
  have hgoodΛ : ∀ c ∈ Λ, IsGoodBall ω K CV CP L c r := fun c hc => hgood c (mem_latticeBall.1 hc)
  have hr2 : 0 < r ^ 2 := by positivity
  have hsumle : ∀ S : Finset (Vertex d), ∑ x ∈ S, f x ≤ 1 := fun S =>
    (hfs.sum_le_tsum S fun x _ => hf0 x).trans hf1
  -- the Poincaré inequality on each ball
  have hA : ∀ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2 ≤
      CP * r ^ 2 * nbrEnergy ω (Bs c) f + (∑ x ∈ Bc c, f x) / (CV * r ^ d) := by
    intro c hc
    obtain ⟨hvol, hP⟩ := hgoodΛ c hc
    have hpos : (0 : ℝ) < (Bc c).card := lt_of_lt_of_le (by positivity) hvol
    have hne : (Bc c).Nonempty := Finset.card_pos.1 (by exact_mod_cast hpos)
    rw [sum_sq_eq_add_sq_div (Bc c) f hne]
    have hS0 : 0 ≤ ∑ x ∈ Bc c, f x := Finset.sum_nonneg fun x _ => hf0 x
    have hS1 := hsumle (Bc c)
    have h2 : (∑ x ∈ Bc c, f x) ^ 2 / (Bc c).card ≤ (∑ x ∈ Bc c, f x) / (CV * r ^ d) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      calc (∑ x ∈ Bc c, f x) ^ 2 * (CV * r ^ d) ≤ (∑ x ∈ Bc c, f x) * (CV * r ^ d) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
        _ ≤ (∑ x ∈ Bc c, f x) * (Bc c).card := mul_le_mul_of_nonneg_left hvol hS0
    exact add_le_add (hP f) h2
  -- the multiplicity of the covering
  have hcount : ∀ x (ρ' : ℝ), 1 ≤ ρ' →
      ((Λ.filter (fun c => x ∈ clusterBall K c ρ')).card : ℝ) ≤ (5 * ρ') ^ d := by
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
  have hB : ∑ c ∈ Λ, nbrEnergy ω (Bs c) f ≤ (5 * (L * r)) ^ d * E := by
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
            ((5 * (L * r)) ^ d) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcount x (L * r) hLr1) (he0 x)
      _ = (5 * (L * r)) ^ d *
            ∑ x ∈ W, ∑ z ∈ (openGraph ω).neighborFinset x, (f z - f x) ^ 2 := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (5 * (L * r)) ^ d * E :=
          mul_le_mul_of_nonneg_left (he.sum_le_tsum W fun x _ => he0 x) (by positivity)
  have hC : ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ≤ (5 * r) ^ d := by
    calc ∑ c ∈ Λ, ∑ x ∈ Bc c, f x
        = ∑ x ∈ W, f x * (Λ.filter (fun c => x ∈ Bc c)).card := sum_sum_eq_sum_mul_card Λ W Bc hBc f
      _ ≤ ∑ x ∈ W, f x * ((5 * r) ^ d) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hcount x r hr) (hf0 x)
      _ = (5 * r) ^ d * ∑ x ∈ W, f x := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ (5 * r) ^ d * 1 := mul_le_mul_of_nonneg_left (hsumle W) (by positivity)
      _ = (5 * r) ^ d := mul_one _
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
  have hD : CV * r ^ d * ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 ≤ ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2 := by
    rw [sum_sum_eq_sum_mul_card Λ W Bc hBc (fun x => f x ^ 2)]
    calc CV * r ^ d * ∑ x ∈ clusterBall K x0 ρ, f x ^ 2
        = ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 * (CV * r ^ d) := by
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
            refine ⟨by linarith [hx'.2, hc'.2], hx'.1, ?_⟩
            rw [latticeDist_comm]
            exact hc'.2
          exact_mod_cast Finset.card_le_card hinc
      _ ≤ ∑ x ∈ W, f x ^ 2 * (Λ.filter (fun c => x ∈ Bc c)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => by positivity
  -- combination
  have hsumA : ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2 ≤
      CP * r ^ 2 * ((5 * (L * r)) ^ d * E) + (5 * r) ^ d / (CV * r ^ d) := by
    calc ∑ c ∈ Λ, ∑ x ∈ Bc c, f x ^ 2
        ≤ ∑ c ∈ Λ, (CP * r ^ 2 * nbrEnergy ω (Bs c) f + (∑ x ∈ Bc c, f x) / (CV * r ^ d)) :=
          Finset.sum_le_sum hA
      _ = CP * r ^ 2 * ∑ c ∈ Λ, nbrEnergy ω (Bs c) f +
            (∑ c ∈ Λ, ∑ x ∈ Bc c, f x) / (CV * r ^ d) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hB (by positivity))
          (div_le_div_of_nonneg_right hC (by positivity))
  have hkey : CV * r ^ d * ∑ x ∈ clusterBall K x0 ρ, f x ^ 2 ≤
      CV * r ^ d * (5 ^ d * CP * L ^ d / CV * r ^ 2 * E + 5 ^ d / (CV ^ 2 * r ^ d)) := by
    refine hD.trans (hsumA.trans (le_of_eq ?_))
    simp only [mul_pow]
    field_simp
  exact le_of_mul_le_mul_left hkey (by positivity)

/-! ### Proposition 3.1 and Corollary 3.2 -/

omit [NeZero d] in
theorem bondHeat_eq_zero_of_mem_of_notMem {K : OpenComponent ω} {x y : Vertex d}
    (hx : x ∈ K.supp) (hy : y ∉ K.supp) (t : ℝ) : bondHeat ω t x y = 0 := by
  refine bondHeat_eq_zero_of_not_reachable ω (fun h => hy ?_) t
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact (SimpleGraph.ConnectedComponent.sound h).symm

theorem exp_neg_le_bondHeat_self {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    Real.exp (-(2 * d) * t) ≤ bondHeat ω t x x := by
  have hs := summable_bondHeat ω t x x
  have h := hs.le_tsum 0 (fun n _ => mul_nonneg (poissonWeight_nonneg ht n)
    (lazyPow_mem_Icc two_mul_dim_pos (openGraph_degree_le_two_mul ω) n x x).1)
  have h0 : poissonWeight (2 * d) t 0 * lazyPow (openGraph ω) (2 * d) 0 x x =
      Real.exp (-(2 * d) * t) := by
    simp [poissonWeight, lazyPow_zero]
  rw [h0] at h
  exact h

omit [NeZero d] in
/-- `Σ_y f(y)² ≤ Σ_{y ∈ S} f(y)² + ε` if `f ≥ 0`, `Σ f ≤ 1` and `f ≤ ε` off `S`. -/
theorem tsum_sq_le_sum_sq_add {f : Vertex d → ℝ} {S : Finset (Vertex d)} {ε : ℝ}
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

omit [NeZero d] in
/-- `(√t)^d = t^{d/2}` for `t ≥ 0`. -/
theorem sqrt_pow_eq_rpow {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t ^ d = t ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  ring

/-- If `ψ φ ≤ A E`, then `-E q (φ/ψ) ≤ -(q/A) φ²` (the step `ψ' ≤ -c ψ^{1+2/d}` of
Proposition 3.1, for `φ = ψ^{2/d}`). -/
theorem neg_mul_le_of_mul_le {E q φ ψ A : ℝ} (hq : 0 < q) (hφ : 0 < φ) (hψ : 0 < ψ) (hA : 0 < A)
    (h : ψ * φ ≤ A * E) : -E * q * (φ / ψ) ≤ -(q / A) * φ ^ 2 := by
  simp only [neg_mul, neg_le_neg_iff]
  rw [div_mul_eq_mul_div, div_le_iff₀ hA]
  have e : E * q * (φ / ψ) * A = q * φ * (A * E) / ψ := by field_simp
  rw [e, le_div_iff₀ hψ]
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ q * φ)]

/-- The constant `α = 5^d C_P L^d / C_V` of the energy term of (3.4). -/
noncomputable def diagAlpha (d : ℕ) (CV CP L : ℝ) : ℝ := 5 ^ d * CP * L ^ d / CV

/-- The constant `β = 5^d / C_V²` of the mass term of (3.4). -/
noncomputable def diagBeta (d : ℕ) (CV : ℝ) : ℝ := 5 ^ d / CV ^ 2

/-- The constant of Proposition 3.1 in dimension `d`. -/
noncomputable def diagConst (d : ℕ) (CV CP L : ℝ) : ℝ :=
  max ((2 * d * diagAlpha d CV CP L * (4 * diagBeta d CV) ^ ((2 : ℝ) / d)) ^ ((d : ℝ) / 2))
    (max 1 (4 * diagBeta d CV * 18 ^ d))

theorem one_le_diagConst (d : ℕ) (CV CP L : ℝ) : 1 ≤ diagConst d CV CP L :=
  le_max_of_le_right (le_max_left _ _)

/-- **Barlow 2004, Proposition 3.1** (on-diagonal upper bound in a very good ball), for the
variable speed walk on `ℤ^d` and Euclidean balls: `p_{2t}(x₁, x₁) ≤ C t^{-d/2}` for
`2 C_P L^d C_V N^{d+2} ≤ t ≤ R`. -/
theorem bondHeat_diag_le_of_good {K : OpenComponent ω} {CV CP L R N ε : ℝ} {x0 x1 : Vertex d}
    (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N) (hNR : N ≤ R / 18)
    (hgood : ∀ z, latticeDist z x0 ≤ R → ∀ r, N ≤ r → r ≤ R / 18 → IsGoodBall ω K CV CP L z r)
    (hx1 : x1 ∈ K.supp) (hx10 : latticeDist x1 x0 ≤ 8 * R / 9) (hε0 : 0 ≤ ε)
    (hε : ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x1 → bondHeat ω s x1 y ≤ ε)
    (hεN : ε * N ^ d * CV ^ 2 ≤ 5 ^ d) (hεR : 4 * ε * Real.sqrt R ^ d ≤ 1) {t : ℝ}
    (ht0 : 2 * (CP * L ^ d * CV * N ^ (d + 2)) ≤ t) (htR : t ≤ R) :
    bondHeat ω (2 * t) x1 x1 ≤ diagConst d CV CP L / Real.sqrt t ^ d := by
  set α := diagAlpha d CV CP L with hα
  set β := diagBeta d CV with hβ
  have hα0 : 0 < α := by rw [hα, diagAlpha]; positivity
  have hβ0 : 0 < β := by rw [hβ, diagBeta]; positivity
  have hN0 : 0 < N := by linarith
  have hR18 : 18 ≤ R := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  set T0 := CP * L ^ d * CV * N ^ (d + 2) with hT0
  have hT00 : 0 < T0 := by positivity
  have ht : 0 < t := by linarith
  set ψ : ℝ → ℝ := fun s => bondHeat ω (2 * s) x1 x1 with hψ
  set E : ℝ → ℝ := fun s => ∑' y, ∑ z ∈ (openGraph ω).neighborFinset y,
    (bondHeat ω s x1 z - bondHeat ω s x1 y) ^ 2 with hE
  have hE0 : ∀ s, 0 ≤ E s := fun s => tsum_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : ∀ s, 0 ≤ s → HasDerivAt ψ (-E s) s := fun s hs => hasDerivAt_bondHeat_two_mul hs x1
  have hcont : Continuous ψ :=
    (continuous_bondHeat ω x1 x1).comp (continuous_const.mul continuous_id)
  -- the key inequality (3.5) at time `s` and radius `r`
  have hkey : ∀ s, 0 ≤ s → s ≤ R → ∀ r, N ≤ r → r ≤ R / 18 →
      ψ s - ε ≤ α * r ^ 2 * E s + β / r ^ d := by
    intro s hs hsR r hNr hrR
    have hr1 : 1 ≤ r := hN.trans hNr
    have hf0 : ∀ y, 0 ≤ bondHeat ω s x1 y := fun y => bondHeat_nonneg ω hs x1 y
    have hfs := (hasSum_bondHeat ω hs x1).summable
    have hf1 : ∑' y, bondHeat ω s x1 y ≤ 1 := (hasSum_bondHeat ω hs x1).tsum_eq.le
    have hout : ∀ y ∉ clusterBall K x0 (17 * R / 18), bondHeat ω s x1 y ≤ ε := by
      intro y hy
      by_cases hyK : y ∈ K.supp
      · have hy' : 17 * R / 18 ≤ latticeDist y x0 := by
          by_contra hlt
          exact hy (mem_clusterBall.2 ⟨hyK, lt_of_not_ge hlt⟩)
        have htri := latticeDist_triangle y x1 x0
        exact hε s hs hsR y (by linarith)
      · rw [bondHeat_eq_zero_of_mem_of_notMem hx1 hyK]
        exact hε0
    have h1 := tsum_sq_le_sum_sq_add hf0 hfs hf1 hε0 hout
    have h2 := sum_sq_clusterBall_le (K := K) (x0 := x0) (ρ := 17 * R / 18) (r := r) hCV hCP.le
      hL hr1 (fun z hz => hgood z (by linarith) r hNr hrR) hf0 hfs hf1
      (summable_bondHeat_energy hs x1)
    have hψs : ψ s = ∑' y, bondHeat ω s x1 y ^ 2 := (hasSum_bondHeat_sq hs x1).tsum_eq.symm
    rw [hψs]
    have e1 : 5 ^ d / (CV ^ 2 * r ^ d) = β / r ^ d := by rw [hβ, diagBeta]; field_simp
    have e2 : 5 ^ d * CP * L ^ d / CV * r ^ 2 = α * r ^ 2 := by rw [hα, diagAlpha]
    rw [e1, e2] at h2
    linarith
  -- phase one: `ψ(T₀) ≤ 4β/N^d`
  have hψ0 : ψ 0 = 1 := by
    simp only [hψ, mul_zero]
    rw [bondHeat_zero]
    simp
  have hphase1 : ψ T0 ≤ 4 * β / N ^ d := by
    have h := Barlow.le_max_exp_of_hasDerivAt (ψ := ψ) (ψ' := fun s => -E s) (a := 0) (b := T0)
      (κ := 1 / (2 * α * N ^ 2)) (m := 4 * β / N ^ d) hT00.le hcont.continuousOn
      (fun s hs => hd s hs.1.le) (fun s _ => neg_nonpos.2 (hE0 s)) (fun s hs hm => by
        have hk := hkey s hs.1.le (by linarith [hs.2]) N le_rfl hNR
        have hεb : ε ≤ β / N ^ d := by
          rw [le_div_iff₀ (by positivity), hβ, diagBeta, le_div_iff₀ (by positivity)]
          linarith
        have h4 : 4 * β / N ^ d = 4 * (β / N ^ d) := by ring
        have h1 : ψ s / 2 ≤ α * N ^ 2 * E s := by linarith
        show -E s ≤ -(1 / (2 * α * N ^ 2)) * ψ s
        rw [neg_mul, neg_le_neg_iff, one_div, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
        linarith)
    refine h.trans (max_le le_rfl ?_)
    rw [hψ0, one_mul, sub_zero]
    have hκT : 1 / (2 * α * N ^ 2) * T0 = N ^ d / (2 * β) := by
      rw [hα, hβ, hT0, diagAlpha, diagBeta]
      field_simp
      ring
    have hexp : Real.exp (-(1 / (2 * α * N ^ 2)) * T0) ≤ 2 * β / N ^ d := by
      rw [neg_mul, hκT, Real.exp_neg]
      have hxpos : 0 < N ^ d / (2 * β) := by positivity
      have hx : N ^ d / (2 * β) ≤ Real.exp (N ^ d / (2 * β)) := by
        linarith [Real.add_one_le_exp (N ^ d / (2 * β))]
      calc (Real.exp (N ^ d / (2 * β)))⁻¹ ≤ (N ^ d / (2 * β))⁻¹ := inv_anti₀ hxpos hx
        _ = 2 * β / N ^ d := by rw [inv_div]
    refine hexp.trans ?_
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  -- antitone
  have hanti : AntitoneOn ψ (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => -E s) (convex_Ici 0)
      hcont.continuousOn (fun s hs => ?_) (fun s _ => neg_nonpos.2 (hE0 s))
    rw [interior_Ici] at hs
    exact (hd s (le_of_lt hs)).hasDerivWithinAt
  -- phase two, for `φ = ψ^{2/d}`
  have hT0t : T0 ≤ t := by linarith
  have hψpos : ∀ s, 0 ≤ s → 0 < ψ s := fun s hs =>
    lt_of_lt_of_le (Real.exp_pos _) (exp_neg_le_bondHeat_self (by linarith) x1)
  set q : ℝ := 2 / d with hq
  have hq0 : 0 < q := by positivity
  set m := max (4 * ε) (4 * β / (R / 18) ^ d) with hm_def
  have hm0 : 0 ≤ m := le_max_of_le_left (by positivity)
  have hB : 0 < (4 * β) ^ q := Real.rpow_pos_of_pos (by positivity) q
  set c := q / (2 * α * (4 * β) ^ q) with hc_def
  have hc0 : 0 < c := by positivity
  have hcontφ : ContinuousOn (fun s => ψ s ^ q) (Set.Icc T0 t) :=
    hcont.continuousOn.rpow_const fun s _ => Or.inr hq0.le
  have hphase2 : ψ t ^ q ≤ max (m ^ q) ((ψ T0 ^ q)⁻¹ + c * (t - T0))⁻¹ :=
    Barlow.le_max_inv_of_hasDerivAt (ψ := fun s => ψ s ^ q)
    (ψ' := fun s => -E s * q * ψ s ^ (q - 1)) (a := T0) (b := t) (c := c) (m := m ^ q)
    hT0t hc0.le hcontφ
    (fun s hs => (hd s (by linarith [hs.1])).rpow_const
      (Or.inl (hψpos s (by linarith [hs.1])).ne'))
    (fun s hs => by
      have h1 : 0 ≤ ψ s ^ (q - 1) := Real.rpow_nonneg (hψpos s (by linarith [hs.1])).le _
      have h2 := hE0 s
      show -E s * q * ψ s ^ (q - 1) ≤ 0
      have : 0 ≤ E s * q * ψ s ^ (q - 1) := by positivity
      linarith)
    (fun s hs => Real.rpow_pos_of_pos (hψpos s (by linarith [hs.1])) _)
    (fun s hs hmφ => by
      have hs0 : 0 ≤ s := by linarith [hs.1]
      have hψs := hψpos s hs0
      have hmψ : m ≤ ψ s := (Real.rpow_le_rpow_iff hm0 hψs.le hq0).1 hmφ
      have hψT : ψ s ≤ 4 * β / N ^ d :=
        (hanti (Set.mem_Ici.2 hT00.le) (Set.mem_Ici.2 hs0) hs.1.le).trans hphase1
      have hm1 : 4 * ε ≤ ψ s := (le_max_left _ _).trans hmψ
      have hm2 : 4 * β / (R / 18) ^ d ≤ ψ s := (le_max_right _ _).trans hmψ
      set r := (4 * β / ψ s) ^ ((d : ℝ)⁻¹) with hr
      have hrd : r ^ d = 4 * β / ψ s :=
        Real.rpow_inv_natCast_pow (by positivity) (NeZero.ne d)
      have hNr : N ≤ r := by
        rw [hr, ← Real.pow_rpow_inv_natCast hN0.le (NeZero.ne d)]
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        rw [le_div_iff₀ hψs]
        rw [le_div_iff₀ (by positivity)] at hψT
        linarith
      have hrR : r ≤ R / 18 := by
        rw [hr, ← Real.pow_rpow_inv_natCast (by linarith : (0 : ℝ) ≤ R / 18) (NeZero.ne d)]
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        rw [div_le_iff₀ hψs]
        rw [div_le_iff₀ (by positivity)] at hm2
        linarith
      have hk := hkey s hs0 (by linarith [hs.2]) r hNr hrR
      rw [hrd] at hk
      have hβr : β / (4 * β / ψ s) = ψ s / 4 := by field_simp
      rw [hβr] at hk
      have hφ : 0 < ψ s ^ q := Real.rpow_pos_of_pos hψs q
      have hr2 : r ^ 2 = (4 * β) ^ q / ψ s ^ q := by
        have he : (d : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = q := by rw [hq]; push_cast; ring
        rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), he,
          Real.div_rpow (by positivity) hψs.le]
      have h1 : ψ s / 2 ≤ α * r ^ 2 * E s := by linarith
      rw [hr2] at h1
      have e : α * ((4 * β) ^ q / ψ s ^ q) * E s = α * (4 * β) ^ q * E s / ψ s ^ q := by ring
      rw [e, le_div_iff₀ hφ] at h1
      have h2 : ψ s * ψ s ^ q ≤ 2 * α * (4 * β) ^ q * E s := by linarith
      have hψq : ψ s ^ (q - 1) = ψ s ^ q / ψ s := Real.rpow_sub_one hψs.ne' q
      show -E s * q * ψ s ^ (q - 1) ≤ -c * (ψ s ^ q) ^ 2
      rw [hψq, hc_def]
      exact neg_mul_le_of_mul_le hq0 hφ hψs (by positivity) h2)
  -- conclusion
  have hfin : ((ψ T0 ^ q)⁻¹ + c * (t - T0))⁻¹ ≤ 2 / (c * t) := by
    have hp0 : 0 < (ψ T0 ^ q)⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos (hψpos T0 hT00.le) q)
    have hlow : c * (t / 2) ≤ (ψ T0 ^ q)⁻¹ + c * (t - T0) := by
      have : t / 2 ≤ t - T0 := by linarith
      nlinarith
    have hlowpos : 0 < c * (t / 2) := by positivity
    calc ((ψ T0 ^ q)⁻¹ + c * (t - T0))⁻¹ ≤ (c * (t / 2))⁻¹ := inv_anti₀ hlowpos hlow
      _ = 2 / (c * t) := by field_simp
  have hst : 0 < Real.sqrt t ^ d := by positivity
  have hD1 : 1 ≤ diagConst d CV CP L := one_le_diagConst d CV CP L
  have hD2 : 4 * β * 18 ^ d ≤ diagConst d CV CP L := le_max_of_le_right (le_max_right _ _)
  have hψt := hψpos t ht.le
  rcases le_max_iff.1 (hphase2.trans (max_le_max le_rfl hfin)) with h1 | h1
  · have hψm : ψ t ≤ m := (Real.rpow_le_rpow_iff hψt.le hm0 hq0).1 h1
    refine hψm.trans (max_le ?_ ?_)
    · have hsR : Real.sqrt t ^ d ≤ Real.sqrt R ^ d :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt htR) d
      rw [le_div_iff₀ hst]
      have : 4 * ε * Real.sqrt t ^ d ≤ 4 * ε * Real.sqrt R ^ d :=
        mul_le_mul_of_nonneg_left hsR (by positivity)
      linarith
    · have hsR : Real.sqrt t ^ d ≤ R ^ d := by
        refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ d
        refine (Real.sqrt_le_sqrt htR).trans ?_
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      have e : 4 * β / (R / 18) ^ d = 4 * β * 18 ^ d / R ^ d := by
        rw [div_pow]
        field_simp
      rw [e]
      calc 4 * β * 18 ^ d / R ^ d ≤ 4 * β * 18 ^ d / Real.sqrt t ^ d :=
            div_le_div_of_nonneg_left (by positivity) hst hsR
        _ ≤ diagConst d CV CP L / Real.sqrt t ^ d := div_le_div_of_nonneg_right hD2 hst.le
  · have hψt' : ψ t = (ψ t ^ q) ^ q⁻¹ := (Real.rpow_rpow_inv hψt.le hq0.ne').symm
    have h3 : ψ t ≤ (2 / (c * t)) ^ q⁻¹ := by
      rw [hψt']
      exact Real.rpow_le_rpow (by positivity) h1 (by positivity)
    have hqinv : q⁻¹ = (d : ℝ) / 2 := by rw [hq, inv_div]
    have h2c : 2 / c = 2 * d * α * (4 * β) ^ q := by
      rw [hc_def, hq]
      field_simp
    have e : (2 / (c * t)) ^ q⁻¹ = (2 * d * α * (4 * β) ^ q) ^ ((d : ℝ) / 2) / Real.sqrt t ^ d := by
      rw [div_mul_eq_div_div, Real.div_rpow (by positivity) ht.le, h2c, hqinv,
        sqrt_pow_eq_rpow ht.le]
    rw [e] at h3
    refine h3.trans (div_le_div_of_nonneg_right ?_ hst.le)
    exact le_max_left _ _

/-- **Barlow 2004, Corollary 3.2**: under the hypotheses of Proposition 3.1, if
`|x₁ - x₀| ≤ 7R/9` then `p_{2t}(x₁, y) ≤ C t^{-d/2}` for every `y` and
`2 C_P L^d C_V N^{d+2} ≤ t ≤ R/2`. -/
theorem bondHeat_le_of_good {K : OpenComponent ω} {CV CP L R N ε : ℝ} {x0 x1 : Vertex d}
    (hCV : 0 < CV) (hCP : 0 < CP) (hL : 1 ≤ L) (hN : 1 ≤ N) (hNR : N ≤ R / 18)
    (hgood : ∀ z, latticeDist z x0 ≤ R → ∀ r, N ≤ r → r ≤ R / 18 → IsGoodBall ω K CV CP L z r)
    (hx1 : x1 ∈ K.supp) (hx10 : latticeDist x1 x0 ≤ 7 * R / 9) (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ K.supp, ∀ s, 0 ≤ s → s ≤ R → ∀ y, R / 18 ≤ latticeDist y x →
      bondHeat ω s x y ≤ ε)
    (hεN : ε * N ^ d * CV ^ 2 ≤ 5 ^ d) (hεR : 4 * ε * Real.sqrt R ^ d ≤ 1) (y : Vertex d) {t : ℝ}
    (ht0 : 2 * (CP * L ^ d * CV * N ^ (d + 2)) ≤ t) (htR : t ≤ R / 2) :
    bondHeat ω (2 * t) x1 y ≤ diagConst d CV CP L / Real.sqrt t ^ d := by
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht0
  have htR' : t ≤ R := by linarith
  have hst : 0 < Real.sqrt t ^ d := by positivity
  by_cases hyK : y ∈ K.supp
  · by_cases hy0 : latticeDist y x0 ≤ 8 * R / 9
    · have h1 := bondHeat_diag_le_of_good hCV hCP hL hN hNR hgood hx1 (by linarith) hε0
        (hε x1 hx1) hεN hεR ht0 htR'
      have h2 := bondHeat_diag_le_of_good hCV hCP hL hN hNR hgood hyK hy0 hε0
        (hε y hyK) hεN hεR ht0 htR'
      calc bondHeat ω (2 * t) x1 y
          ≤ (bondHeat ω (2 * t) x1 x1 + bondHeat ω (2 * t) y y) / 2 :=
            bondHeat_two_mul_le_half_add ht.le x1 y
        _ ≤ (diagConst d CV CP L / Real.sqrt t ^ d + diagConst d CV CP L / Real.sqrt t ^ d) / 2 := by
            gcongr
        _ = diagConst d CV CP L / Real.sqrt t ^ d := by ring
    · have htri := latticeDist_triangle y x1 x0
      have h1 := hε x1 hx1 (2 * t) (by linarith) (by linarith) y (by linarith)
      refine h1.trans ?_
      have hsR : Real.sqrt t ^ d ≤ Real.sqrt R ^ d :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt htR') d
      have h2 : ε ≤ 1 / Real.sqrt t ^ d := by
        rw [le_div_iff₀ hst]
        have : 4 * ε * Real.sqrt t ^ d ≤ 4 * ε * Real.sqrt R ^ d :=
          mul_le_mul_of_nonneg_left hsR (by positivity)
        have : 0 ≤ ε * Real.sqrt t ^ d := by positivity
        linarith
      exact h2.trans (div_le_div_of_nonneg_right (one_le_diagConst _ _ _ _) hst.le)
  · rw [bondHeat_eq_zero_of_mem_of_notMem hx1 hyK]
    exact div_nonneg (zero_le_one.trans (one_le_diagConst _ _ _ _)) hst.le

end Rigidity.BarlowLattice
