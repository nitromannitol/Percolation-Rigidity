import Rigidity.Proofs.Green.HeatDomination
import LatticeProb.Graph.CarneVaropoulos

/-!
# Polynomial upper bounds on the Green function

Let `G` be an infinite connected graph with degrees at most `Δ`, and `y` a vertex such that the
transition probabilities into `y` satisfy `p_n(x, y) ≤ K n^{-γ}` for `n ≥ N₀` and `n` at least the
graph distance `r = dist(x, y)`, with `γ > 1`. Then the Green function
`g(x) = ∑_n p_n(x, y) / deg y` satisfies, for every `δ > 0`,

  `g(x) ≤ C r^{2 - 2γ + δ}`  whenever `r ≥ max N₀ 1`.

The sum over times is cut at `T = ⌈r^{2-θ}⌉ + 1` with `θ = min 1 (δ/(γ - 1))`. Before `T`, the
Carne-Varopoulos bound `p_n(x, y) ≤ 2 √(deg y / deg x) e^{-r²/(2n)}` gives at most
`2 √Δ T e^{-r^θ/6}`, which decays faster than any power of `r`. After `T`, the comparison of
`∑_{n ≥ T} n^{-γ}` with `∫_{T-1}^∞ t^{-γ} dt` gives `K (T-1)^{1-γ}/(γ-1) ≤ K r^{(2-θ)(1-γ)}/(γ-1)`.

With the transition bound `p_n(x, y) ≤ K n^{-(D/2)(1-η)}` that follows from Faber-Krahn
inequalities of dimension `D` with constants `a₀ R^{-η}` on the balls around `y`
(`HeatDomination.lean`), the exponent is `2 - D(1 - η) + δ`. For the lattice dimension `D = d`
and `η = 0` this is the Green function bound `g(x) ≤ C |x - y|^{2-d}` of Barlow and of Dario-Gu
(1.10) up to the loss `r^δ`; the loss comes from using the Carne-Varopoulos bound, which carries
no on-diagonal factor, in place of a Gaussian upper bound.
-/

open scoped Classical

namespace Rigidity.Green

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Integral comparison for the tail of a `p`-series:
`∑_{k ≥ 0} (k + m + 1)^{-γ} ≤ m^{1-γ} / (γ - 1)` for `γ > 1` and `m ≥ 1`. -/
theorem tsum_rpow_neg_add_le {γ : ℝ} (hγ : 1 < γ) {m : ℕ} (hm : 1 ≤ m) :
    ∑' k : ℕ, ((k + (m + 1) : ℕ) : ℝ) ^ (-γ) ≤ (m : ℝ) ^ (1 - γ) / (γ - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine Real.tsum_le_of_sum_range_le (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    fun N => ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-γ)) (Set.Icc (m : ℝ) (m + N)) := by
    intro a ha b _ hab
    exact Real.rpow_le_rpow_of_nonpos (hm0.trans_le ha.1) hab (by linarith)
  have hsum := hanti.sum_le_integral
  have hnot : (0 : ℝ) ∉ Set.uIcc (m : ℝ) (m + N) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩)] at hsum
  have hcast : ∀ i : ℕ, ((i + (m + 1) : ℕ) : ℝ) = (m : ℝ) + ((i + 1 : ℕ) : ℝ) := by
    intro i
    push_cast
    ring
  simp_rw [hcast]
  refine hsum.trans ?_
  have hb : 0 ≤ ((m : ℝ) + N) ^ (-γ + 1) := Real.rpow_nonneg (by positivity) _
  rw [show -γ + 1 = 1 - γ by ring] at hb ⊢
  rw [show (((m : ℝ) + N) ^ (1 - γ) - (m : ℝ) ^ (1 - γ)) / (1 - γ) =
      ((m : ℝ) ^ (1 - γ) - ((m : ℝ) + N) ^ (1 - γ)) / (γ - 1) by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring]
  exact (div_le_div_iff_of_pos_right (by linarith)).2 (by linarith)

/-- Stretched-exponential decay beats every power: for `θ, c > 0` and any `a` there is `C` with
`e^{-r^θ / c} ≤ C r^{-a}` for all `r ≥ 1`. -/
theorem exists_exp_neg_rpow_div_le {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → Real.exp (-(r ^ θ / c)) ≤ C * r ^ (-a) := by
  set k := ⌈max a 0 / θ⌉₊
  have hC0 : 0 ≤ (k.factorial : ℝ) * c ^ k := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc.le _)
  refine ⟨k.factorial * c ^ k, hC0, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have ht : 0 < r ^ θ / c := div_pos (Real.rpow_pos_of_pos hr0 θ) hc
  have h1 := Real.pow_div_factorial_le_exp (r ^ θ / c) ht.le k
  have hpos : 0 < (r ^ θ / c) ^ k / k.factorial :=
    div_pos (pow_pos ht k) (by exact_mod_cast Nat.factorial_pos k)
  have h2 : Real.exp (-(r ^ θ / c)) ≤ k.factorial / (r ^ θ / c) ^ k := by
    rw [Real.exp_neg, ← inv_div ((r ^ θ / c) ^ k) (k.factorial : ℝ)]
    exact inv_anti₀ hpos h1
  have hrk : r ^ (θ * k) ≠ 0 := (Real.rpow_pos_of_pos hr0 _).ne'
  have hck : c ^ k ≠ 0 := pow_ne_zero _ hc.ne'
  have h3 : (k.factorial : ℝ) / (r ^ θ / c) ^ k = k.factorial * c ^ k * r ^ (-(θ * k)) := by
    rw [div_pow, ← Real.rpow_natCast (r ^ θ) k, ← Real.rpow_mul hr0.le, Real.rpow_neg hr0.le]
    field_simp
  have h4 : r ^ (-(θ * k)) ≤ r ^ (-a) := by
    refine Real.rpow_le_rpow_of_exponent_le hr ?_
    have h5 : max a 0 / θ ≤ k := Nat.le_ceil _
    rw [div_le_iff₀ hθ] at h5
    linarith [le_max_left a 0]
  calc Real.exp (-(r ^ θ / c)) ≤ k.factorial / (r ^ θ / c) ^ k := h2
    _ = k.factorial * c ^ k * r ^ (-(θ * k)) := h3
    _ ≤ k.factorial * c ^ k * r ^ (-a) := mul_le_mul_of_nonneg_left h4 hC0

/-- The Carne-Varopoulos bound on a graph of degree at most `Δ`, uniformly over the times below
`T`: `p_n(x, y) ≤ 2 √Δ e^{-r²/(2T)}` for `n < T`, when `x ≠ y`. -/
theorem heat_le_two_sqrt_mul_exp_of_lt [Infinite V] (hG : G.Connected) {Δ : ℕ} (hΔ : BoundedDegree G Δ)
    {x y : V} (hxy : 1 ≤ G.dist x y) {n T : ℕ} (hnT : n < T) :
    heat G n x y ≤
      2 * Real.sqrt Δ * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * T)) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hR : 0 ≤ 2 * Real.sqrt Δ * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * T)) := by positivity
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [heat_eq_zero_of_lt_dist (by omega)]
    exact hR
  have hcv := heat_le_carneVaropoulos G hdeg x y n hn
  have hdx : (1 : ℝ) ≤ G.degree x := by exact_mod_cast hdeg x
  have hdy : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
  have hsq : Real.sqrt ((G.degree y : ℝ) / G.degree x) ≤ Real.sqrt Δ :=
    Real.sqrt_le_sqrt ((div_le_self (Nat.cast_nonneg _) hdx).trans hdy)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnT' : (n : ℝ) ≤ T := by exact_mod_cast hnT.le
  have hexp : Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) ≤
      Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * T)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  calc heat G n x y
      ≤ 2 * Real.sqrt ((G.degree y : ℝ) / G.degree x) *
          Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)) := hcv
    _ ≤ 2 * Real.sqrt Δ * Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * T)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) hexp (Real.exp_nonneg _)
          (by positivity)

/-- **Green function bound, cut-off form.** If `p_n(x, y) ≤ K n^{-γ}` for `n ≥ N₀` at least the
distance, with `γ > 1`, then for every `θ ∈ (0, 1]` the Green function with pole `y` satisfies
`g(x) ≤ C r^{(2-θ)(1-γ)}` at distance `r ≥ max N₀ 1`. -/
theorem heatGreen_le_rpow_of_heatDominated_cutoff [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {y : V} {N₀ : ℕ} {K γ : ℝ} (hγ : 1 < γ)
    (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, N₀ ≤ G.dist x y → 1 ≤ G.dist x y →
      heatGreen G y x ≤ C * (G.dist x y : ℝ) ^ ((2 - θ) * (1 - γ)) := by
  have hK : 0 ≤ K := by
    have h1 := h y (N₀ + 1) (by omega) (by rw [SimpleGraph.dist_self]; omega)
    have h2 : (0 : ℝ) < ((N₀ + 1 : ℕ) : ℝ) ^ (-γ) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have : K * ((N₀ + 1 : ℕ) : ℝ) ^ (-γ) < 0 := mul_neg_of_neg_of_pos (by linarith) h2
    linarith [heat_nonneg (G := G) (N₀ + 1) y y]
  obtain ⟨C₁, hC₁, hC₁b⟩ := exists_exp_neg_rpow_div_le hθ0 (by norm_num : (0 : ℝ) < 6)
    ((2 - θ) * γ)
  have hγ1 : 0 < γ - 1 := by linarith
  have hC0 : 0 ≤ 6 * Real.sqrt Δ * C₁ + K / (γ - 1) :=
    add_nonneg (mul_nonneg (by positivity) hC₁) (div_nonneg hK hγ1.le)
  refine ⟨6 * Real.sqrt Δ * C₁ + K / (γ - 1), hC0, fun x hN hx1 => ?_⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = G.dist x y := ⟨_, rfl⟩
  rw [← hρ]
  have hρ1 : 1 ≤ ρ := by
    rw [hρ]
    exact_mod_cast hx1
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈ρ ^ (2 - θ)⌉₊ := ⟨_, rfl⟩
  have hpow1 : 1 ≤ ρ ^ (2 - θ) := Real.one_le_rpow hρ1 (by linarith)
  have hpowpos : 0 < ρ ^ (2 - θ) := by linarith
  have hρpow : ρ ≤ ρ ^ (2 - θ) := by
    have := Real.rpow_le_rpow_of_exponent_le hρ1 (by linarith : (1 : ℝ) ≤ 2 - θ)
    rwa [Real.rpow_one] at this
  have hmge : ρ ^ (2 - θ) ≤ m := by
    rw [hm]
    exact Nat.le_ceil _
  have hmlt : (m : ℝ) < ρ ^ (2 - θ) + 1 := by
    rw [hm]
    exact Nat.ceil_lt_add_one hpowpos.le
  have hm1 : 1 ≤ m := by exact_mod_cast hpow1.trans hmge
  have hrm : G.dist x y ≤ m := by
    have hle : (G.dist x y : ℝ) ≤ m := by
      rw [← hρ]
      exact hρpow.trans hmge
    exact_mod_cast hle
  have hT3 : ((m + 1 : ℕ) : ℝ) ≤ 3 * ρ ^ (2 - θ) := by
    push_cast
    linarith
  have hT0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hb : Summable fun n : ℕ => K * (n : ℝ) ^ (-γ) := summable_rpow_mul K hγ
  have hs : Summable fun n => heat G n x y := summable_heat_of_heatDominated hb h x
  have hsplit : ∑ n ∈ Finset.range (m + 1), heat G n x y + ∑' k, heat G (k + (m + 1)) x y =
      ∑' n, heat G n x y := hs.sum_add_tsum_nat_add (m + 1)
  have hhead : ∑ n ∈ Finset.range (m + 1), heat G n x y ≤
      ((m + 1 : ℕ) : ℝ) *
        (2 * Real.sqrt Δ * Real.exp (-(ρ ^ 2) / (2 * ((m + 1 : ℕ) : ℝ)))) := by
    have hsum := Finset.sum_le_sum fun n (hn : n ∈ Finset.range (m + 1)) =>
      heat_le_two_sqrt_mul_exp_of_lt hG hΔ hx1 (Finset.mem_range.1 hn)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hρ] at hsum
    exact hsum
  have hexp : Real.exp (-(ρ ^ 2) / (2 * ((m + 1 : ℕ) : ℝ))) ≤ Real.exp (-(ρ ^ θ / 6)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (mul_pos two_pos hT0)]
    have hsplitρ : ρ ^ (2 : ℝ) = ρ ^ θ * ρ ^ (2 - θ) := by
      rw [← Real.rpow_add hρ0]
      congr 1
      ring
    rw [← Real.rpow_natCast ρ 2, Nat.cast_ofNat, hsplitρ]
    have hθnn : 0 ≤ ρ ^ θ := Real.rpow_nonneg hρ0.le _
    nlinarith [mul_le_mul_of_nonneg_left hT3 hθnn]
  have hhead' : ∑ n ∈ Finset.range (m + 1), heat G n x y ≤
      6 * Real.sqrt Δ * C₁ * ρ ^ ((2 - θ) * (1 - γ)) := by
    have hC := hC₁b ρ hρ1
    have hpe : ρ ^ (2 - θ) * ρ ^ (-((2 - θ) * γ)) = ρ ^ ((2 - θ) * (1 - γ)) := by
      rw [← Real.rpow_add hρ0]
      congr 1
      ring
    have hsqrt : 0 ≤ 2 * Real.sqrt Δ := by positivity
    calc ∑ n ∈ Finset.range (m + 1), heat G n x y
        ≤ ((m + 1 : ℕ) : ℝ) *
            (2 * Real.sqrt Δ * Real.exp (-(ρ ^ 2) / (2 * ((m + 1 : ℕ) : ℝ)))) := hhead
      _ ≤ (3 * ρ ^ (2 - θ)) * (2 * Real.sqrt Δ * (C₁ * ρ ^ (-((2 - θ) * γ)))) :=
          mul_le_mul hT3 (mul_le_mul_of_nonneg_left (hexp.trans hC) hsqrt)
            (mul_nonneg hsqrt (Real.exp_nonneg _)) (by linarith)
      _ = 6 * Real.sqrt Δ * C₁ * (ρ ^ (2 - θ) * ρ ^ (-((2 - θ) * γ))) := by ring
      _ = 6 * Real.sqrt Δ * C₁ * ρ ^ ((2 - θ) * (1 - γ)) := by rw [hpe]
  have htail : ∑' k, heat G (k + (m + 1)) x y ≤ K / (γ - 1) * ρ ^ ((2 - θ) * (1 - γ)) := by
    have hle : ∀ k : ℕ, heat G (k + (m + 1)) x y ≤ K * ((k + (m + 1) : ℕ) : ℝ) ^ (-γ) :=
      fun k => h x (k + (m + 1)) (by omega) (by omega)
    have hgs : Summable fun k : ℕ => K * ((k + (m + 1) : ℕ) : ℝ) ^ (-γ) :=
      (summable_nat_add_iff (f := fun n : ℕ => K * (n : ℝ) ^ (-γ)) (m + 1)).2 hb
    have hts : Summable fun k : ℕ => heat G (k + (m + 1)) x y :=
      (summable_nat_add_iff (f := fun n : ℕ => heat G n x y) (m + 1)).2 hs
    have h1 := Summable.tsum_le_tsum hle hts hgs
    rw [tsum_mul_left] at h1
    have h2 := tsum_rpow_neg_add_le hγ hm1
    have h3 : (m : ℝ) ^ (1 - γ) ≤ ρ ^ ((2 - θ) * (1 - γ)) := by
      rw [Real.rpow_mul hρ0.le]
      exact Real.rpow_le_rpow_of_nonpos hpowpos hmge (by linarith)
    calc ∑' k, heat G (k + (m + 1)) x y
        ≤ K * ∑' k : ℕ, ((k + (m + 1) : ℕ) : ℝ) ^ (-γ) := h1
      _ ≤ K * ((m : ℝ) ^ (1 - γ) / (γ - 1)) := mul_le_mul_of_nonneg_left h2 hK
      _ ≤ K * (ρ ^ ((2 - θ) * (1 - γ)) / (γ - 1)) :=
          mul_le_mul_of_nonneg_left ((div_le_div_iff_of_pos_right hγ1).2 h3) hK
      _ = K / (γ - 1) * ρ ^ ((2 - θ) * (1 - γ)) := by ring
  have hdy : (1 : ℝ) ≤ G.degree y := by exact_mod_cast degree_pos hG y
  calc heatGreen G y x ≤ ∑' n, heat G n x y :=
        div_le_self (tsum_nonneg fun n => heat_nonneg n x y) hdy
    _ = ∑ n ∈ Finset.range (m + 1), heat G n x y + ∑' k, heat G (k + (m + 1)) x y :=
        hsplit.symm
    _ ≤ 6 * Real.sqrt Δ * C₁ * ρ ^ ((2 - θ) * (1 - γ)) +
          K / (γ - 1) * ρ ^ ((2 - θ) * (1 - γ)) := add_le_add hhead' htail
    _ = (6 * Real.sqrt Δ * C₁ + K / (γ - 1)) * ρ ^ ((2 - θ) * (1 - γ)) := by ring

/-- **Green function bound.** If `p_n(x, y) ≤ K n^{-γ}` for `n ≥ N₀` at least the distance, with
`γ > 1`, then for every `δ > 0` the Green function with pole `y` satisfies
`g(x) ≤ C r^{2 - 2γ + δ}` at distance `r ≥ max N₀ 1`. -/
theorem heatGreen_le_rpow_of_heatDominated [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {y : V} {N₀ : ℕ} {K γ : ℝ} (hγ : 1 < γ)
    (h : HeatDominated G y N₀ fun n => K * (n : ℝ) ^ (-γ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, N₀ ≤ G.dist x y → 1 ≤ G.dist x y →
      heatGreen G y x ≤ C * (G.dist x y : ℝ) ^ (2 - 2 * γ + δ) := by
  set θ := min 1 (δ / (γ - 1))
  have hγ1 : 0 < γ - 1 := by linarith
  have hθ0 : 0 < θ := lt_min one_pos (div_pos hδ hγ1)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθδ : θ * (γ - 1) ≤ δ := by
    have := mul_le_mul_of_nonneg_right (min_le_right 1 (δ / (γ - 1))) hγ1.le
    rwa [div_mul_cancel₀ _ hγ1.ne'] at this
  obtain ⟨C, hC, hCb⟩ := heatGreen_le_rpow_of_heatDominated_cutoff hG hΔ hγ h hθ0 hθ1
  refine ⟨C, hC, fun x hN hx1 => (hCb x hN hx1).trans ?_⟩
  have hρ1 : (1 : ℝ) ≤ G.dist x y := by exact_mod_cast hx1
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hρ1 ?_) hC
  linarith

/-- **Green function bound from Faber-Krahn inequalities on growing balls.** If the balls of
radius `R ≥ R₀` around `y` satisfy the Faber-Krahn inequality of dimension `D` with constant
`a₀ R^{-η}`, and `(D/2)(1 - η) > 1`, then for every `δ > 0` the Green function with pole `y`
satisfies `g(x) ≤ C r^{2 - D(1-η) + δ}` at distance `r ≥ max R₀ 2`. -/
theorem heatGreen_le_rpow_of_faberKrahn_balls [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {D a₀ η : ℝ} (hD : 0 < D) (ha₀ : 0 < a₀) {R₀ : ℕ} (y : V)
    (hFK : ∀ R : ℕ, R₀ ≤ R → FaberKrahnOn G {v | G.dist y v ≤ R} D (a₀ * (R : ℝ) ^ (-η)))
    (hγ : 1 < D / 2 * (1 - η)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, max R₀ 2 ≤ G.dist x y →
      heatGreen G y x ≤ C * (G.dist x y : ℝ) ^ (2 - D * (1 - η) + δ) := by
  obtain ⟨K, hK⟩ := heatDominated_of_faberKrahn_balls hG hΔ hD ha₀ y hFK
  obtain ⟨C, hC, hCb⟩ := heatGreen_le_rpow_of_heatDominated hG hΔ hγ hK hδ
  refine ⟨C, hC, fun x hx => ?_⟩
  have h := hCb x hx (le_trans (by omega) hx)
  rwa [show 2 - 2 * (D / 2 * (1 - η)) + δ = 2 - D * (1 - η) + δ by ring] at h

end Rigidity.Green
