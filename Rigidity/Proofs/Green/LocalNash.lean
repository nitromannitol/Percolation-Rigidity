/-
The heat-step computation `heat_step_of_faberKrahnOn` is adapted from Lattice-Probability
(https://github.com/nitromannitol/Lattice-Probability), commit
7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069, file `LatticeProb/Graph/OnDiagonal.lean`, theorem
`heat_step`, Copyright 2026 Ahmed Bou-Rabee, Apache License 2.0.
Changes: the Nash inequality of dimension one (`nash_ineq`) is replaced by the Nash inequality
`nash_of_faberKrahnOn` of a local Faber-Krahn inequality, with the support hypothesis that the
ball of radius `n + 1` lies in the Faber-Krahn domain; the conclusion is the step inequality of
exponent `1 + 2/D`; the final `nlinarith` is replaced by the corresponding real-power estimate.
-/
import LatticeProb.Graph.OnDiagonal
import LatticeProb.Graph.Odometer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# On-diagonal heat kernel bounds from a local Faber-Krahn inequality

On a locally finite graph `G`, a vertex set `B` satisfies the Faber-Krahn inequality of dimension
`D` with constant `a` (`FaberKrahnOn G B D a`) if every function `g` supported in a finite set
`Ω ⊆ B` has

  `a ∑_Ω g² ≤ |Ω|^{2/D} ∑_y ∑_{v ∼ y} (g y - g v)²`,

that is, the first Dirichlet eigenvalue of `Ω` is at least `a |Ω|^{-2/D} / 2`. The standard
truncation argument turns this into a Nash inequality for nonnegative functions supported in `B`
(`nash_of_faberKrahnOn`), with the degree measure:

  `‖f‖₂^{2 (1 + 2/D)} ≤ (4Δ/a) (4 ‖f‖₁²)^{2/D} E(f)`,

where `Δ` bounds the degrees. Applied, as in the dimension-one bound of Lattice-Probability, to
`u_n + u_{n+1}` with `u_n = p_n(x, ·)/deg`, it gives the decrease
`s_n - s_{n+1} ≥ c s_n^{1 + 2/D}` of `s_n = p_{2n}(x, x)/deg(x)` as long as the ball of radius
`n + 1` around `x` lies in `B`, and the reciprocal-power iteration gives

  `p_{2N}(x, x) ≤ deg(x) (c (2/D) N)^{-D/2}`

whenever the ball of radius `N` around `x` lies in `B` (`heat_even_le_of_faberKrahnOn`). Only
the walk's first `2N` steps enter, so the inequality is needed on a ball only.
-/

open scoped Classical

namespace Rigidity.Green

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The Faber-Krahn inequality of dimension `D` with constant `a` for functions supported in
finite subsets of `B`. The Dirichlet sum is taken over any finite set containing the support and
its neighbours. -/
def FaberKrahnOn (G : SimpleGraph V) [G.LocallyFinite] (B : Set V) (D a : ℝ) : Prop :=
  ∀ (Ω T : Finset V) (g : V → ℝ), (↑Ω : Set V) ⊆ B → (∀ y, g y ≠ 0 → y ∈ Ω) → Ω ⊆ T →
    (∀ y ∈ Ω, ∀ v, G.Adj y v → v ∈ T) →
      a * ∑ y ∈ Ω, g y ^ 2 ≤
        (Ω.card : ℝ) ^ (2 / D) * ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2

/-- The Faber-Krahn inequality passes to subsets. -/
theorem FaberKrahnOn.mono {B B' : Set V} {D a : ℝ} (h : FaberKrahnOn G B D a) (hB : B' ⊆ B) :
    FaberKrahnOn G B' D a :=
  fun Ω T g hΩ hg hΩT hN => h Ω T g (hΩ.trans hB) hg hΩT hN

/-- A transition probability vanishes beyond its time. -/
theorem dist_le_of_heat_ne_zero {m : ℕ} {x y : V} (h : heat G m x y ≠ 0) : G.dist x y ≤ m := by
  by_contra hlt
  exact h (heat_eq_zero_of_lt_dist (by omega))

/-- **Nash inequality from the Faber-Krahn inequality.** For a nonnegative `f` supported in `B`,
with the degree-weighted norms `A = ∑ deg f²`, `M = ∑ deg f` and the Dirichlet form
`A - ∑ deg f Pf`, one has `A^{1 + 2/D} ≤ (4Δ/a) (4M²)^{2/D} (A - ∑ deg f Pf)`. -/
theorem nash_of_faberKrahnOn {Δ : ℕ} (hΔ : BoundedDegree G Δ) (hdeg : ∀ v : V, 0 < G.degree v)
    {B : Set V} {D a : ℝ} (hD : 0 < D) (ha : 0 < a) (hFK : FaberKrahnOn G B D a)
    (f : V → ℝ) (hf : ∀ y, 0 ≤ f y) (hB : ∀ y, f y ≠ 0 → y ∈ B) (T : Finset V)
    (hT : ∀ y, f y ≠ 0 → y ∈ T) (hTN : ∀ y v : V, f y ≠ 0 → G.Adj y v → v ∈ T) :
    (∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2) ^ (1 + 2 / D)
      ≤ 4 * Δ / a * (4 * (∑ y ∈ T, (G.degree y : ℝ) * f y) ^ 2) ^ (2 / D)
        * ((∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2)
            - ∑ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y) := by
  set A := ∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2 with hAdef
  set M := ∑ y ∈ T, (G.degree y : ℝ) * f y with hMdef
  set W := ∑ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y with hWdef
  have hW : W = ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, f y * f v := sum_degree_mul_walkOp hdeg f T
  have hD2 : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (f y - f v) ^ 2 = 2 * A - 2 * W := by
    rw [hW]; exact sum_sq_sub_eq f T hT hTN
  have hEnn : 0 ≤ A - W := by
    have : (0 : ℝ) ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (f y - f v) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun y _ => by positivity
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun y _ => mul_nonneg (Nat.cast_nonneg _) (hf y)
  have hΔnn : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  have hRHSnn : 0 ≤ 4 * Δ / a * (4 * M ^ 2) ^ (2 / D) * (A - W) := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * M ^ 2) (2 / D)
    positivity
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · calc A ^ (1 + 2 / D) = 0 := by rw [← hA0, Real.zero_rpow (by positivity)]
      _ ≤ _ := hRHSnn
  have hMpos : 0 < M := by
    rcases eq_or_lt_of_le hMnn with hM0 | hM
    · exfalso
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => mul_nonneg (Nat.cast_nonneg _) (hf y))).1 hM0.symm
      have hA0 : A = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hy0 := hzero y hy
        have hd : (G.degree y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg y).ne'
        have hfy : f y = 0 := by
          rcases mul_eq_zero.1 hy0 with h | h
          · exact absurd h hd
          · exact h
        rw [hfy]; ring
      linarith
    · exact hM
  set lam := A / (4 * M) with hlam
  have hlampos : 0 < lam := by positivity
  set Ω := T.filter (fun y => lam < f y) with hΩdef
  set g : V → ℝ := fun y => max (f y - lam) 0 with hgdef
  have hgsupp : ∀ y, g y ≠ 0 → y ∈ Ω := by
    intro y hy
    have hlt : lam < f y := by
      by_contra hle
      exact hy (max_eq_right (by linarith))
    exact Finset.mem_filter.2 ⟨hT y (by linarith), hlt⟩
  have hΩB : (↑Ω : Set V) ⊆ B := by
    intro y hy
    have hy := (Finset.mem_filter.1 hy).2
    exact hB y (by linarith)
  have hΩT : Ω ⊆ T := Finset.filter_subset _ _
  have hΩN : ∀ y ∈ Ω, ∀ v, G.Adj y v → v ∈ T := by
    intro y hy v hv
    have hy := (Finset.mem_filter.1 hy).2
    exact hTN y v (by linarith) hv
  have hFKg := hFK Ω T g hΩB hgsupp hΩT hΩN
  have hgrad : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2
      ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (f y - f v) ^ 2 := by
    refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun v _ => ?_
    have h := abs_max_sub_max_le_abs (f y - lam) (f v - lam) 0
    rw [show f y - lam - (f v - lam) = f y - f v by ring] at h
    rw [← sq_abs, ← sq_abs (f y - f v)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hcard : (Ω.card : ℝ) * lam ≤ M := by
    have h1 : (Ω.card : ℝ) * lam = ∑ y ∈ Ω, lam := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ y ∈ Ω, lam ≤ ∑ y ∈ Ω, (G.degree y : ℝ) * f y := by
      refine Finset.sum_le_sum fun y hy => ?_
      have hy := (Finset.mem_filter.1 hy).2
      have hd : (1 : ℝ) ≤ G.degree y := by exact_mod_cast hdeg y
      nlinarith
    have h3 : ∑ y ∈ Ω, (G.degree y : ℝ) * f y ≤ M :=
      Finset.sum_le_sum_of_subset_of_nonneg hΩT
        (fun y _ _ => mul_nonneg (Nat.cast_nonneg _) (hf y))
    linarith
  have hsplit : A ≤ Δ * ∑ y ∈ Ω, g y ^ 2 + 2 * lam * M := by
    have hpt : ∀ y ∈ T, (G.degree y : ℝ) * f y ^ 2
        ≤ (G.degree y : ℝ) * g y ^ 2 + 2 * lam * ((G.degree y : ℝ) * f y) := by
      intro y _
      have hd : (0 : ℝ) ≤ G.degree y := Nat.cast_nonneg _
      have hfy := hf y
      have hle : f y ^ 2 ≤ g y ^ 2 + 2 * lam * f y := by
        rcases le_or_gt (f y) lam with h | h
        · have hg0 : g y = 0 := max_eq_right (by linarith)
          rw [hg0]
          nlinarith
        · have hg1 : g y = f y - lam := max_eq_left (by linarith)
          rw [hg1]
          nlinarith
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have hsub : ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 = ∑ y ∈ Ω, (G.degree y : ℝ) * g y ^ 2 := by
      refine (Finset.sum_subset hΩT fun y _ hy => ?_).symm
      have hg0 : g y = 0 := by
        by_contra hne
        exact hy (hgsupp y hne)
      rw [hg0]; ring
    have hdeg_le : ∑ y ∈ Ω, (G.degree y : ℝ) * g y ^ 2 ≤ Δ * ∑ y ∈ Ω, g y ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      have : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
      nlinarith [sq_nonneg (g y)]
    linarith
  have h2lam : 2 * lam * M = A / 2 := by
    rw [hlam]; field_simp; ring
  have hcardle : (Ω.card : ℝ) ≤ 4 * M ^ 2 / A := by
    rw [le_div_iff₀ hApos]
    have : (Ω.card : ℝ) * lam * (4 * M) ≤ M * (4 * M) := by
      have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ 4 * M)
      linarith
    have hl : lam * (4 * M) = A := by rw [hlam]; field_simp
    nlinarith
  have hpow : (Ω.card : ℝ) ^ (2 / D) ≤ (4 * M ^ 2 / A) ^ (2 / D) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcardle (by positivity)
  have hmain : a * (A / 2) ≤ Δ * ((4 * M ^ 2 / A) ^ (2 / D) * (2 * A - 2 * W)) := by
    have h1 : a * (A / 2) ≤ a * (Δ * ∑ y ∈ Ω, g y ^ 2) := by
      have := hsplit; rw [h2lam] at this
      exact mul_le_mul_of_nonneg_left (by linarith) ha.le
    have h2 : a * (Δ * ∑ y ∈ Ω, g y ^ 2) = Δ * (a * ∑ y ∈ Ω, g y ^ 2) := by ring
    have h3 : a * ∑ y ∈ Ω, g y ^ 2 ≤ (4 * M ^ 2 / A) ^ (2 / D) * (2 * A - 2 * W) := by
      calc a * ∑ y ∈ Ω, g y ^ 2
          ≤ (Ω.card : ℝ) ^ (2 / D) * ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2 := hFKg
        _ ≤ (4 * M ^ 2 / A) ^ (2 / D) * (2 * A - 2 * W) := by
          rw [← hD2]
          exact mul_le_mul hpow hgrad
            (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Real.rpow_nonneg (by positivity) _)
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hΔnn)
  have hdiv : (4 * M ^ 2 / A) ^ (2 / D) = (4 * M ^ 2) ^ (2 / D) / A ^ (2 / D) :=
    Real.div_rpow (by positivity) hApos.le _
  have hApow : A ^ (1 + 2 / D) = A * A ^ (2 / D) := by
    rw [Real.rpow_add hApos, Real.rpow_one]
  have hAD : 0 < A ^ (2 / D) := Real.rpow_pos_of_pos hApos _
  rw [hdiv] at hmain
  rw [hApow]
  have hkey : a * A * A ^ (2 / D) ≤ 4 * Δ * (4 * M ^ 2) ^ (2 / D) * (A - W) := by
    have := mul_le_mul_of_nonneg_right hmain hAD.le
    rw [show Δ * ((4 * M ^ 2) ^ (2 / D) / A ^ (2 / D) * (2 * A - 2 * W)) * A ^ (2 / D)
        = 2 * Δ * (4 * M ^ 2) ^ (2 / D) * (A - W) * (A ^ (2 / D) / A ^ (2 / D)) by ring,
      div_self hAD.ne', mul_one] at this
    linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha]
  linarith

/-- **The heat step from a local Faber-Krahn inequality.** If the ball of radius `n + 1` around
`x` lies in `B`, the return densities `s_n = p_{2n}(x, x)/deg(x)` satisfy
`s_n^{1 + 2/D} ≤ (8Δ/a) 16^{2/D} (s_n - s_{n+1})`. -/
theorem heat_step_of_faberKrahnOn [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {B : Set V} {D a : ℝ} (hD : 0 < D) (ha : 0 < a)
    (hFK : FaberKrahnOn G B D a) (x : V) (n : ℕ) (hB : ∀ v, G.dist x v ≤ n + 1 → v ∈ B) :
    (heat G (n + n) x x / (G.degree x : ℝ)) ^ (1 + 2 / D)
      ≤ 8 * Δ / a * (16 : ℝ) ^ (2 / D) *
        (heat G (n + n) x x / (G.degree x : ℝ)
          - heat G (n + 1 + (n + 1)) x x / (G.degree x : ℝ)) := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  set T := window G n x with hTdef
  set u : ℕ → V → ℝ := fun m y => heat G m x y / (G.degree y : ℝ) with hudef
  set f : V → ℝ := fun y => u n y + u (n + 1) y with hfdef
  set g : V → ℝ := fun y => u n y - u (n + 1) y with hgdef
  have hunn : ∀ (m : ℕ) (y : V), 0 ≤ u m y := fun m y =>
    div_nonneg (heat_nonneg m x y) (Nat.cast_nonneg _)
  have hfnn : ∀ y, 0 ≤ f y := fun y => by rw [hfdef]; exact add_nonneg (hunn n y) (hunn (n+1) y)
  have hf_heat : ∀ y, f y ≠ 0 → heat G n x y ≠ 0 ∨ heat G (n + 1) x y ≠ 0 := by
    intro y hy
    by_cases h1 : heat G n x y = 0
    · by_cases h2 : heat G (n + 1) x y = 0
      · exact absurd (by simp [hfdef, hudef, h1, h2] : f y = 0) hy
      · exact Or.inr h2
    · exact Or.inl h1
  have hg_heat : ∀ y, g y ≠ 0 → heat G n x y ≠ 0 ∨ heat G (n + 1) x y ≠ 0 := by
    intro y hy
    by_cases h1 : heat G n x y = 0
    · by_cases h2 : heat G (n + 1) x y = 0
      · exact absurd (by simp [hgdef, hudef, h1, h2] : g y = 0) hy
      · exact Or.inr h2
    · exact Or.inl h1
  have hTf : ∀ y, f y ≠ 0 → y ∈ T := fun y hy => mem_window_of_heat (hf_heat y hy)
  have hTNf : ∀ y v : V, f y ≠ 0 → G.Adj y v → v ∈ T :=
    fun y v hy hadj => mem_window_of_adj (hf_heat y hy) hadj
  have hTg : ∀ y, g y ≠ 0 → y ∈ T := fun y hy => mem_window_of_heat (hg_heat y hy)
  have hTNg : ∀ y v : V, g y ≠ 0 → G.Adj y v → v ∈ T :=
    fun y v hy hadj => mem_window_of_adj (hg_heat y hy) hadj
  have hBf : ∀ y, f y ≠ 0 → y ∈ B := by
    intro y hy
    refine hB y ?_
    rcases hf_heat y hy with h | h
    · exact (dist_le_of_heat_ne_zero h).trans (by omega)
    · exact dist_le_of_heat_ne_zero h
  have hF : ∀ (m k : ℕ), (m = n ∨ m = n + 1) →
      ∑ y ∈ T, (G.degree y : ℝ) * u m y * u k y = heat G (m + k) x x / (G.degree x : ℝ) := by
    intro m k hm
    exact sum_degree_heat_mul hdeg m k x x T (reach_subset_window x hm)
  have e1 : n + (n + 1) = n + n + 1 := by omega
  have e2 : n + 1 + n = n + n + 1 := by omega
  have e3 : n + 1 + (n + 1) = n + n + 2 := by omega
  have e4 : n + (n + 2) = n + n + 2 := by omega
  have e5 : n + 1 + (n + 2) = n + n + 3 := by omega
  set a0 := heat G (n + n) x x / (G.degree x : ℝ) with ha0
  set a1 := heat G (n + n + 1) x x / (G.degree x : ℝ) with ha1
  set a2 := heat G (n + n + 2) x x / (G.degree x : ℝ) with ha2
  set a3 := heat G (n + n + 3) x x / (G.degree x : ℝ) with ha3
  have hA : ∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2 = a0 + 2 * a1 + a2 := by
    have expand : ∀ y ∈ T, (G.degree y : ℝ) * f y ^ 2
        = (G.degree y : ℝ) * u n y * u n y + (G.degree y : ℝ) * u n y * u (n + 1) y
          + ((G.degree y : ℝ) * u (n + 1) y * u n y
            + (G.degree y : ℝ) * u (n + 1) y * u (n + 1) y) := by
      intro y _; rw [hfdef]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hF n n (Or.inl rfl), hF n (n + 1) (Or.inl rfl),
      hF (n + 1) n (Or.inr rfl), hF (n + 1) (n + 1) (Or.inr rfl), e1, e2, e3]
    ring
  have hwf : ∀ y, walkOp G f y = u (n + 1) y + u (n + 2) y := by
    intro y
    rw [hfdef, walkOp_add, walkOp_heat_div, walkOp_heat_div]
  have hWf : ∑ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y = a1 + 2 * a2 + a3 := by
    have expand : ∀ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y
        = (G.degree y : ℝ) * u n y * u (n + 1) y + (G.degree y : ℝ) * u n y * u (n + 2) y
          + ((G.degree y : ℝ) * u (n + 1) y * u (n + 1) y
            + (G.degree y : ℝ) * u (n + 1) y * u (n + 2) y) := by
      intro y _; rw [hwf y, hfdef]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hF n (n + 1) (Or.inl rfl), hF n (n + 2) (Or.inl rfl),
      hF (n + 1) (n + 1) (Or.inr rfl), hF (n + 1) (n + 2) (Or.inr rfl), e1, e3, e4, e5]
    ring
  have hM : ∑ y ∈ T, (G.degree y : ℝ) * f y = 2 := by
    have hone : ∀ m : ℕ, (m = n ∨ m = n + 1) → ∑ y ∈ T, (G.degree y : ℝ) * u m y = 1 := by
      intro m hm
      have hcast : ∀ y ∈ T, (G.degree y : ℝ) * u m y = heat G m x y := by
        intro y _
        have hy : (G.degree y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg y).ne'
        rw [hudef]
        field_simp
      rw [Finset.sum_congr rfl hcast, ← sum_heat_eq_one hdeg m x]
      exact (Finset.sum_subset (reach_subset_window x hm)
        (fun y _ hy => heat_eq_zero_of_notMem_reach m x y hy)).symm
    have expand : ∀ y ∈ T, (G.degree y : ℝ) * f y
        = (G.degree y : ℝ) * u n y + (G.degree y : ℝ) * u (n + 1) y := by
      intro y _; rw [hfdef]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, hone n (Or.inl rfl),
      hone (n + 1) (Or.inr rfl)]
    norm_num
  have hanti : 0 ≤ a0 - a1 - a2 + a3 := by
    have h0 : (0:ℝ) ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2 :=
      Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun v _ => sq_nonneg _
    rw [sum_sq_add_eq g T hTg hTNg, ← sum_degree_mul_walkOp hdeg g T] at h0
    have hAg : ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 = a0 - 2 * a1 + a2 := by
      have expand : ∀ y ∈ T, (G.degree y : ℝ) * g y ^ 2
          = (G.degree y : ℝ) * u n y * u n y - (G.degree y : ℝ) * u n y * u (n + 1) y
            - ((G.degree y : ℝ) * u (n + 1) y * u n y
              - (G.degree y : ℝ) * u (n + 1) y * u (n + 1) y) := by
        intro y _; rw [hgdef]; ring
      rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, hF n n (Or.inl rfl), hF n (n + 1) (Or.inl rfl),
        hF (n + 1) n (Or.inr rfl), hF (n + 1) (n + 1) (Or.inr rfl), e1, e2, e3]
      ring
    have hwg : ∀ y, walkOp G g y = u (n + 1) y - u (n + 2) y := by
      intro y
      rw [hgdef, walkOp_sub, walkOp_heat_div, walkOp_heat_div]
    have hWg : ∑ y ∈ T, (G.degree y : ℝ) * g y * walkOp G g y = a1 - 2 * a2 + a3 := by
      have expand : ∀ y ∈ T, (G.degree y : ℝ) * g y * walkOp G g y
          = (G.degree y : ℝ) * u n y * u (n + 1) y - (G.degree y : ℝ) * u n y * u (n + 2) y
            - ((G.degree y : ℝ) * u (n + 1) y * u (n + 1) y
              - (G.degree y : ℝ) * u (n + 1) y * u (n + 2) y) := by
        intro y _; rw [hwg y, hgdef]; ring
      rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, hF n (n + 1) (Or.inl rfl), hF n (n + 2) (Or.inl rfl),
        hF (n + 1) (n + 1) (Or.inr rfl), hF (n + 1) (n + 2) (Or.inr rfl), e1, e3, e4, e5]
      ring
    rw [hAg, hWg] at h0
    linarith
  have hnash := nash_of_faberKrahnOn hΔ hdeg hD ha hFK f hfnn hBf T hTf hTNf
  rw [hA, hM, hWf] at hnash
  have ha0nn : 0 ≤ a0 := div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have ha1nn : 0 ≤ a1 := div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have ha2nn : 0 ≤ a2 := div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have hmono : a0 ^ (1 + 2 / D) ≤ (a0 + 2 * a1 + a2) ^ (1 + 2 / D) :=
    Real.rpow_le_rpow ha0nn (by linarith) (by positivity)
  have h16 : (4 * (2 : ℝ) ^ 2) ^ (2 / D) = (16 : ℝ) ^ (2 / D) := by norm_num
  rw [h16] at hnash
  have hcoef : 0 ≤ 4 * (Δ : ℝ) / a * (16 : ℝ) ^ (2 / D) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 16) (2 / D)
    positivity
  have hE : (a0 + 2 * a1 + a2) - (a1 + 2 * a2 + a3) ≤ 2 * (a0 - a2) := by linarith
  rw [e3]
  calc a0 ^ (1 + 2 / D) ≤ (a0 + 2 * a1 + a2) ^ (1 + 2 / D) := hmono
    _ ≤ 4 * Δ / a * (16 : ℝ) ^ (2 / D) * ((a0 + 2 * a1 + a2) - (a1 + 2 * a2 + a3)) := hnash
    _ ≤ 4 * Δ / a * (16 : ℝ) ^ (2 / D) * (2 * (a0 - a2)) :=
        mul_le_mul_of_nonneg_left hE hcoef
    _ = 8 * Δ / a * (16 : ℝ) ^ (2 / D) * (a0 - a2) := by ring

/-- The tangent-line inequality of `t ↦ t^{-β}` at `s`, for `0 < t ≤ s`. -/
theorem rpow_neg_add_le {s t β : ℝ} (ht : 0 < t) (hts : t ≤ s) (hβ : 0 < β) :
    s ^ (-β) + β * s ^ (-β - 1) * (s - t) ≤ t ^ (-β) := by
  have hs : 0 < s := ht.trans_le hts
  set r := t / s with hr
  have hrpos : 0 < r := div_pos ht hs
  have hbern : 1 + β * (1 - r) ≤ r ^ (-β) := by
    rw [Real.rpow_def_of_pos hrpos]
    have h1 := Real.add_one_le_exp (Real.log r * -β)
    have h2 := Real.log_le_sub_one_of_pos hrpos
    nlinarith
  have htr : t = r * s := by rw [hr]; field_simp
  have hts' : t ^ (-β) = r ^ (-β) * s ^ (-β) := by
    rw [htr, Real.mul_rpow hrpos.le hs.le]
  have hsub : s ^ (-β - 1) = s ^ (-β) / s := Real.rpow_sub_one hs.ne' _
  have hspos : 0 < s ^ (-β) := Real.rpow_pos_of_pos hs _
  rw [hts', hsub]
  have hrs : (s - t) / s = 1 - r := by rw [hr]; field_simp
  calc s ^ (-β) + β * (s ^ (-β) / s) * (s - t)
      = s ^ (-β) * (1 + β * ((s - t) / s)) := by field_simp
    _ = s ^ (-β) * (1 + β * (1 - r)) := by rw [hrs]
    _ ≤ s ^ (-β) * r ^ (-β) := mul_le_mul_of_nonneg_left hbern hspos.le
    _ = r ^ (-β) * s ^ (-β) := by ring

/-- **Reciprocal-power iteration.** A nonnegative sequence with
`c s_n^{1+β} ≤ s_n - s_{n+1}` for `n < N` satisfies `s_N ≤ (c β N)^{-1/β}`. -/
theorem le_rpow_of_rpow_step {s : ℕ → ℝ} {c β : ℝ} (hc : 0 < c) (hβ : 0 < β)
    (hs : ∀ n, 0 ≤ s n) {N : ℕ} (hN : 1 ≤ N)
    (hstep : ∀ n < N, c * s n ^ (1 + β) ≤ s n - s (n + 1)) :
    s N ≤ (c * β * N) ^ (-1 / β) := by
  rcases eq_or_lt_of_le (hs N) with h0 | hpos
  · rw [← h0]; exact Real.rpow_nonneg (by positivity) _
  have hmono : ∀ n < N, s (n + 1) ≤ s n := by
    intro n hn
    have := hstep n hn
    have : 0 ≤ c * s n ^ (1 + β) := mul_nonneg hc.le (Real.rpow_nonneg (hs n) _)
    linarith
  have hge' : ∀ k, k ≤ N → s N ≤ s (N - k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 := hmono (N - (k + 1)) (by omega)
        have he : N - (k + 1) + 1 = N - k := by omega
        rw [he] at h2
        linarith
  have hge : ∀ n ≤ N, s N ≤ s n := by
    intro n hn
    have := hge' (N - n) (by omega)
    rwa [Nat.sub_sub_self hn] at this
  have hind : ∀ n ≤ N, c * β * n ≤ s n ^ (-β) := by
    intro n
    induction n with
    | zero =>
        intro _
        rw [Nat.cast_zero, mul_zero]
        exact Real.rpow_nonneg (hs 0) _
    | succ n ih =>
        intro hn
        have ih := ih (by omega)
        have ht : 0 < s (n + 1) := hpos.trans_le (hge _ hn)
        have hsn : 0 < s n := ht.trans_le (hmono n (by omega))
        have htan := rpow_neg_add_le ht (hmono n (by omega)) hβ
        have hstepn := hstep n (by omega)
        have hprod : s n ^ (-β - 1) * s n ^ (1 + β) = 1 := by
          rw [← Real.rpow_add hsn, show -β - 1 + (1 + β) = 0 by ring, Real.rpow_zero]
        have hgain : c * β ≤ β * s n ^ (-β - 1) * (s n - s (n + 1)) := by
          have hnn : 0 ≤ β * s n ^ (-β - 1) := mul_nonneg hβ.le (Real.rpow_nonneg hsn.le _)
          calc c * β = β * s n ^ (-β - 1) * (c * s n ^ (1 + β)) := by
                rw [show β * s n ^ (-β - 1) * (c * s n ^ (1 + β))
                  = c * β * (s n ^ (-β - 1) * s n ^ (1 + β)) by ring, hprod, mul_one]
            _ ≤ β * s n ^ (-β - 1) * (s n - s (n + 1)) := mul_le_mul_of_nonneg_left hstepn hnn
        push_cast
        linarith
  have hfin := hind N le_rfl
  have hbase : 0 < c * β * N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hp := Real.rpow_le_rpow_of_nonpos hbase hfin
    (show -1 / β ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hβ.le)
  rw [← Real.rpow_mul (hs N)] at hp
  have he : (-β) * (-1 / β) = 1 := by field_simp
  simpa only [he, Real.rpow_one] using hp

/-- **On-diagonal bound from a local Faber-Krahn inequality.** If the ball of radius `N ≥ 1`
around `x` lies in a set with the Faber-Krahn inequality of dimension `D` and constant `a`, and
the degrees are at most `Δ`, then `p_{2N}(x, x) ≤ deg(x) (c (2/D) N)^{-D/2}` with
`c = a / (8 Δ 16^{2/D})`. -/
theorem heat_even_le_of_faberKrahnOn [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {B : Set V} {D a : ℝ} (hD : 0 < D) (ha : 0 < a)
    (hFK : FaberKrahnOn G B D a) (x : V) {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ v, G.dist x v ≤ N → v ∈ B) :
    heat G (N + N) x x ≤
      (G.degree x : ℝ) * (a / (8 * Δ * (16 : ℝ) ^ (2 / D)) * (2 / D) * N) ^ (-(D / 2)) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hdx : (0 : ℝ) < G.degree x := by exact_mod_cast hdeg x
  have hΔpos : (0 : ℝ) < Δ := by
    have := (hdeg x).trans_le (hΔ x)
    exact_mod_cast this
  have h16 : (0 : ℝ) < (16 : ℝ) ^ (2 / D) := Real.rpow_pos_of_pos (by norm_num) _
  set c := a / (8 * Δ * (16 : ℝ) ^ (2 / D)) with hc
  have hcpos : 0 < c := by positivity
  set s : ℕ → ℝ := fun k => heat G (k + k) x x / (G.degree x : ℝ) with hsdef
  have hsnn : ∀ k, 0 ≤ s k := fun k => div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have hstep : ∀ n < N, c * s n ^ (1 + 2 / D) ≤ s n - s (n + 1) := by
    intro n hn
    have h := heat_step_of_faberKrahnOn hG hΔ hD ha hFK x n
      (fun v hv => hB v (hv.trans (by omega)))
    have hK : 0 < 8 * (Δ : ℝ) / a * (16 : ℝ) ^ (2 / D) := by positivity
    have hcK : c * (8 * (Δ : ℝ) / a * (16 : ℝ) ^ (2 / D)) = 1 := by
      rw [hc]; field_simp
    calc c * s n ^ (1 + 2 / D)
        ≤ c * (8 * Δ / a * (16 : ℝ) ^ (2 / D) * (s n - s (n + 1))) :=
          mul_le_mul_of_nonneg_left h hcpos.le
      _ = s n - s (n + 1) := by rw [← mul_assoc, hcK, one_mul]
  have hmain := le_rpow_of_rpow_step hcpos (by positivity : (0 : ℝ) < 2 / D) hsnn hN hstep
  have hexp : -1 / (2 / D) = -(D / 2) := by field_simp
  rw [hexp] at hmain
  have hval : heat G (N + N) x x = (G.degree x : ℝ) * s N := by
    rw [hsdef]; field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_left hmain hdx.le

end Rigidity.Green
