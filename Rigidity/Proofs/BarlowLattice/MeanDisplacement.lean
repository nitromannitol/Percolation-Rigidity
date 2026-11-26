import Rigidity.Proofs.BarlowLattice.HeatDecay
import Rigidity.Proofs.Barlow.MeanDisplacement

/-!
# The mean displacement bound of Nash and Bass

This file proves Lemma 3.3 and Proposition 3.4 of Barlow (*Random walks on supercritical
percolation clusters*, Ann. Probab. 32 (2004)) for the variable speed random walk on the open
graph of a configuration of `ℤ^d`: if the entropy satisfies `Q(s) ≥ c₁ + (d/2) log s` on `[T₀, t]`
with `T₀² ≤ t`, and `M(t) ≥ 1/2`, then the mean displacement satisfies `M(t) ≤ K √t`
(`meanDist_le_of_entropy`), with `K` depending only on `d` and `c₁`.

The ingredients are the derivatives (3.8) and (3.10) of the source as sums over directed edges
(from the Gauss–Green formula `tsum_mul_openLaplacian_eq`), the inequality
`M'(t) ≤ 2dλ + Q'(t)/(4λ)` for every `λ > 0` (`deriv_meanDist_le`, the source's `M'² ≤ c Q'` in
the form of the arithmetic–geometric mean), the bound `M(t) ≤ 2dt`, Lemma 3.3(a)
(`neg_log_le_heatEntropy`) and Lemma 3.3(b) (`heatEntropy_le_log_meanDist`). The integral
argument of the source after (3.10) is replaced by the monotonicity of
`H(s) = M(s) - 2d√s - √s (Q(s) - c₁ - (d/2) log s)` on `[T₀, t]`.
-/

open scoped Classical
open Finset LatticeProb.Percolation Rigidity.Green Rigidity.WeakPoincare

namespace Rigidity.BarlowLattice

variable {d : ℕ}

variable [NeZero d] {ω : Configuration d}

omit [NeZero d] in
/-- **The Gauss–Green formula with a weight** (Barlow 2004, Lemma 1.6): if the directed-edge
family `g(a) (f(b) - f(a))` is summable, then
`Σ_x g(x) Δf(x) = -½ Σ_{(a, b)} (g(b) - g(a)) (f(b) - f(a))`. -/
theorem tsum_mul_openLaplacian_eq {f g : Vertex d → ℝ}
    (hP : Summable fun e : OpenDart ω => g e.1 * (f e.2.1 - f e.1)) :
    Summable (fun e : OpenDart ω => (g e.2.1 - g e.1) * (f e.2.1 - f e.1)) ∧
      ∑' x, g x * openLaplacian ω f x =
        -(1 / 2) * ∑' e : OpenDart ω, (g e.2.1 - g e.1) * (f e.2.1 - f e.1) := by
  have hQ : Summable fun e : OpenDart ω => g e.2.1 * (f e.1 - f e.2.1) :=
    summable_openDart_swap (F := fun a b => g a * (f b - f a)) hP
  have hS : Summable fun e : OpenDart ω => (g e.2.1 - g e.1) * (f e.2.1 - f e.1) := by
    refine ((hP.add hQ).neg).congr fun e => ?_
    ring
  have hswap : ∑' e : OpenDart ω, g e.2.1 * (f e.1 - f e.2.1) =
      ∑' e : OpenDart ω, g e.1 * (f e.2.1 - f e.1) :=
    (tsum_openDart_swap (fun a b => g a * (f b - f a))).symm
  have hSsum : ∑' e : OpenDart ω, (g e.2.1 - g e.1) * (f e.2.1 - f e.1) =
      -(2 * ∑' e : OpenDart ω, g e.1 * (f e.2.1 - f e.1)) := by
    have : (fun e : OpenDart ω => (g e.2.1 - g e.1) * (f e.2.1 - f e.1)) =
        fun e => -(g e.1 * (f e.2.1 - f e.1) + g e.2.1 * (f e.1 - f e.2.1)) := by
      funext e
      ring
    rw [this, tsum_neg, hP.tsum_add hQ, hswap]
    ring
  refine ⟨hS, ?_⟩
  have hL : ∑' x, g x * openLaplacian ω f x = ∑' e : OpenDart ω, g e.1 * (f e.2.1 - f e.1) := by
    rw [tsum_openDart (F := fun a b => g a * (f b - f a)) hP]
    refine tsum_congr fun x => ?_
    rw [openLaplacian, Finset.mul_sum]
  rw [hL, hSsum]
  ring

/-- The directed-edge family `g(a) (p_t(x, b) - p_t(x, a))` is summable if `|g(a)|` grows at most
like the square of the graph distance from `x`. -/
theorem summable_openDart_heat {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) {g : Vertex d → ℝ} {G : ℝ}
    (hG : 0 ≤ G)
    (hg : ∀ a, (openGraph ω).Reachable x a → |g a| ≤ G * (1 + ((openGraph ω).dist x a : ℝ)) ^ 2) :
    Summable fun e : OpenDart ω => g e.1 * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) := by
  refine summable_openDart_of_abs_le (g := decayMajorant x (G * 260 * Real.exp (126 * d * t)))
    (summable_decayMajorant x _) (fun y => by unfold decayMajorant; positivity) fun e => ?_
  by_cases h : (openGraph ω).Reachable x e.1
  · have hb := bondHeat_nbr_le ht h e.2.2
    have ha := bondHeat_le_exp_mul_pow_dist (ω := ω) ht x e.1
    have hbn := bondHeat_nonneg ω ht x e.2.1
    have han := bondHeat_nonneg ω ht x e.1
    have hpoly := one_add_sq_mul_pow_dist_le h
    set k := ((openGraph ω).dist x e.1 : ℝ)
    have hdiff : |bondHeat ω t x e.2.1 - bondHeat ω t x e.1| ≤
        65 * Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x e.1 := by
      rw [abs_le]
      constructor <;> nlinarith [Real.exp_pos (126 * d * t),
        pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 64) ((openGraph ω).dist x e.1)]
    rw [abs_mul, decayMajorant]
    calc |g e.1| * |bondHeat ω t x e.2.1 - bondHeat ω t x e.1|
        ≤ (G * (1 + k) ^ 2) * (65 * Real.exp (126 * d * t) * (1 / 64 : ℝ) ^ (openGraph ω).dist x e.1) :=
          mul_le_mul (hg _ h) hdiff (abs_nonneg _) (by positivity)
      _ = G * 65 * Real.exp (126 * d * t) * ((1 + k) ^ 2 * (1 / 64 : ℝ) ^ (openGraph ω).dist x e.1) := by
          ring
      _ ≤ G * 65 * Real.exp (126 * d * t) * (4 * (1 / 16 : ℝ) ^ l1Dist x e.1) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · have hb : ¬ (openGraph ω).Reachable x e.2.1 := fun hxb =>
      h (hxb.trans (((openGraph ω).mem_neighborFinset _ _).1 e.2.2).symm.reachable)
    rw [bondHeat_eq_zero_of_not_reachable' h, bondHeat_eq_zero_of_not_reachable' hb, sub_zero,
      mul_zero, abs_zero, decayMajorant]
    positivity

omit [NeZero d] in
theorem abs_latticeDist_le_sq (x a : Vertex d) (h : (openGraph ω).Reachable x a) :
    |latticeDist x a| ≤ 1 * (1 + ((openGraph ω).dist x a : ℝ)) ^ 2 := by
  rw [abs_of_nonneg (latticeDist_nonneg x a), one_mul]
  have := latticeDist_le_dist h
  nlinarith

theorem abs_neg_log_sub_one_le_sq {t : ℝ} (ht : 0 < t) (x a : Vertex d)
    (h : (openGraph ω).Reachable x a) :
    |-Real.log (bondHeat ω t x a) - 1| ≤
      (2 + 2 * d * t + |Real.log t|) * (1 + ((openGraph ω).dist x a : ℝ)) ^ 2 := by
  have hlog := abs_log_bondHeat_le ht le_rfl le_rfl h
  set k := ((openGraph ω).dist x a : ℝ)
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have h1 : |-Real.log (bondHeat ω t x a) - 1| ≤ |Real.log (bondHeat ω t x a)| + 1 := by
    calc |-Real.log (bondHeat ω t x a) - 1| ≤ |-Real.log (bondHeat ω t x a)| + |(1 : ℝ)| :=
          abs_sub _ _
      _ = _ := by rw [abs_neg, abs_one]
  have hdt : 0 ≤ 2 * d * t := by positivity
  nlinarith [abs_nonneg (Real.log t), mul_nonneg hdt hk0, mul_nonneg hdt (sq_nonneg k),
    mul_nonneg (abs_nonneg (Real.log t)) hk0, mul_nonneg (abs_nonneg (Real.log t)) (sq_nonneg k)]

/-- **Barlow 2004, (3.8)**: `M'(t) = -½ Σ_{(a, b)} (|b - x| - |a - x|)(p_t(x, b) - p_t(x, a))`. -/
theorem hasDerivAt_meanDist_dart {t : ℝ} (ht : 0 < t) (x : Vertex d) :
    HasDerivAt (meanDist ω x)
      (-(1 / 2) * ∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)) t := by
  have hP := summable_openDart_heat (ω := ω) ht.le x (g := fun a => latticeDist x a) zero_le_one
    (fun a h => abs_latticeDist_le_sq x a h)
  have hGG := (tsum_mul_openLaplacian_eq (f := fun z => bondHeat ω t x z)
    (g := fun a => latticeDist x a) hP).2
  rw [← hGG]
  exact hasDerivAt_meanDist ht x

/-- **Barlow 2004, (3.10)**:
`Q'(t) = ½ Σ_{(a, b)} (log p_t(x, b) - log p_t(x, a))(p_t(x, b) - p_t(x, a))`. -/
theorem hasDerivAt_heatEntropy_dart {t : ℝ} (ht : 0 < t) (x : Vertex d) :
    HasDerivAt (heatEntropy ω x)
      ((1 / 2) * ∑' e : OpenDart ω, (Real.log (bondHeat ω t x e.2.1) -
        Real.log (bondHeat ω t x e.1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)) t := by
  have hP := summable_openDart_heat (ω := ω) ht.le x
    (g := fun a => -Real.log (bondHeat ω t x a) - 1) (by positivity)
    (fun a h => abs_neg_log_sub_one_le_sq ht x a h)
  have hGG : ∑' y, (-Real.log (bondHeat ω t x y) - 1) *
      openLaplacian ω (fun z => bondHeat ω t x z) y =
      -(1 / 2) * ∑' e : OpenDart ω, ((-Real.log (bondHeat ω t x e.2.1) - 1) -
        (-Real.log (bondHeat ω t x e.1) - 1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) :=
    (tsum_mul_openLaplacian_eq (f := fun z => bondHeat ω t x z)
      (g := fun a => -Real.log (bondHeat ω t x a) - 1) hP).2
  have h := hasDerivAt_heatEntropy (ω := ω) ht x
  rw [hGG] at h
  refine h.congr_deriv ?_
  have e : ∀ e : OpenDart ω, ((-Real.log (bondHeat ω t x e.2.1) - 1) -
      (-Real.log (bondHeat ω t x e.1) - 1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) =
      -((Real.log (bondHeat ω t x e.2.1) - Real.log (bondHeat ω t x e.1)) *
        (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)) := fun e => by ring
  rw [tsum_congr e, tsum_neg]
  ring

omit [NeZero d] in
theorem latticeDist_le_one_of_mem_neighborFinset {a b : Vertex d}
    (hb : b ∈ (openGraph ω).neighborFinset a) : latticeDist a b ≤ 1 := by
  have hadj := ((openGraph ω).mem_neighborFinset a b).1 hb
  have h := latticeDist_le_length (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
  simpa using h

theorem summable_openDart_heat_fst {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    Summable fun e : OpenDart ω => bondHeat ω t x e.1 :=
  summable_openDart_of_abs_le (g := fun y => bondHeat ω t x y) (hasSum_bondHeat ω ht x).summable
    (fun y => bondHeat_nonneg ω ht x y) fun e => by
      rw [abs_of_nonneg (bondHeat_nonneg ω ht x e.1)]

theorem tsum_openDart_heat_fst_le {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    ∑' e : OpenDart ω, bondHeat ω t x e.1 ≤ 2 * d := by
  rw [tsum_openDart (F := fun a _ => bondHeat ω t x a) (summable_openDart_heat_fst ht x)]
  have h1 : ∀ y, ∑ _z ∈ (openGraph ω).neighborFinset y, bondHeat ω t x y ≤
      2 * d * bondHeat ω t x y :=
    fun y => by
      rw [Finset.sum_const, (openGraph ω).card_neighborFinset_eq_degree, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast openGraph_degree_le_two_mul ω y)
        (bondHeat_nonneg ω ht x y)
  have hs := (hasSum_bondHeat ω ht x)
  have hsum : Summable fun y => ∑ _z ∈ (openGraph ω).neighborFinset y, bondHeat ω t x y :=
    summable_neighbor_sum_of_openDart (F := fun a _ => bondHeat ω t x a)
      (summable_openDart_heat_fst ht x)
  calc ∑' y, ∑ _z ∈ (openGraph ω).neighborFinset y, bondHeat ω t x y
      ≤ ∑' y, 2 * d * bondHeat ω t x y :=
        Summable.tsum_le_tsum h1 hsum (hs.summable.mul_left (2 * (d : ℝ)))
    _ = 2 * d := by rw [tsum_mul_left, hs.tsum_eq, mul_one]

/-- `Σ_{(a, b)} |p_t(x, b) - p_t(x, a)| ≤ 8λ + Q'(t)/(2λ)`-type bound in its basic form:
the directed-edge sum of `p_t(x, a) + p_t(x, b)` is at most `4d`. -/
theorem summable_openDart_heat_add {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    Summable fun e : OpenDart ω => bondHeat ω t x e.1 + bondHeat ω t x e.2.1 :=
  (summable_openDart_heat_fst ht x).add
    (summable_openDart_swap (F := fun a _ => bondHeat ω t x a) (summable_openDart_heat_fst ht x))

theorem tsum_openDart_heat_add_le {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) :
    ∑' e : OpenDart ω, (bondHeat ω t x e.1 + bondHeat ω t x e.2.1) ≤ 4 * d := by
  rw [(summable_openDart_heat_fst ht x).tsum_add
    (summable_openDart_swap (F := fun a _ => bondHeat ω t x a) (summable_openDart_heat_fst ht x)),
    ← tsum_openDart_swap (fun a _ => bondHeat ω t x a)]
  linarith [tsum_openDart_heat_fst_le (ω := ω) ht x]

/-- **The inequality `M'² ≤ c Q'` of Barlow 2004, (3.9)–(3.10)**, in the arithmetic–geometric form:
`M'(t) ≤ 2dλ + Q'(t)/(4λ)` for every `λ > 0`. -/
theorem deriv_meanDist_le {t l : ℝ} (ht : 0 < t) (hl : 0 < l) (x : Vertex d) :
    -(1 / 2) * ∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) ≤
      2 * d * l + ((1 / 2) * ∑' e : OpenDart ω, (Real.log (bondHeat ω t x e.2.1) -
        Real.log (bondHeat ω t x e.1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)) / (4 * l) := by
  have hPd := summable_openDart_heat (ω := ω) ht.le x (g := fun a => latticeDist x a) zero_le_one
    (fun a h => abs_latticeDist_le_sq x a h)
  have hSd : Summable fun e : OpenDart ω => (latticeDist x e.2.1 - latticeDist x e.1) *
      (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) :=
    (tsum_mul_openLaplacian_eq (f := fun z => bondHeat ω t x z)
      (g := fun a => latticeDist x a) hPd).1
  have hPl := summable_openDart_heat (ω := ω) ht.le x
    (g := fun a => -Real.log (bondHeat ω t x a) - 1) (by positivity)
    (fun a h => abs_neg_log_sub_one_le_sq ht x a h)
  have hSl' : Summable fun e : OpenDart ω => ((-Real.log (bondHeat ω t x e.2.1) - 1) -
      (-Real.log (bondHeat ω t x e.1) - 1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) :=
    (tsum_mul_openLaplacian_eq (f := fun z => bondHeat ω t x z)
      (g := fun a => -Real.log (bondHeat ω t x a) - 1) hPl).1
  have hSl : Summable fun e : OpenDart ω => (Real.log (bondHeat ω t x e.2.1) -
      Real.log (bondHeat ω t x e.1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) := by
    refine hSl'.neg.congr fun e => ?_
    ring
  have hA := summable_openDart_heat_add (ω := ω) ht.le x
  -- the pointwise inequality on each directed edge
  have hpt : ∀ e : OpenDart ω, -(latticeDist x e.2.1 - latticeDist x e.1) *
      (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) ≤
      l * (bondHeat ω t x e.1 + bondHeat ω t x e.2.1) +
        (Real.log (bondHeat ω t x e.2.1) - Real.log (bondHeat ω t x e.1)) *
          (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) / (4 * l) := by
    intro e
    have hd : |latticeDist x e.2.1 - latticeDist x e.1| ≤ 1 := by
      have h1 := latticeDist_triangle e.2.1 e.1 x
      have h2 := latticeDist_triangle e.1 e.2.1 x
      have h3 := latticeDist_le_one_of_mem_neighborFinset (ω := ω) e.2.2
      rw [latticeDist_comm x e.2.1, latticeDist_comm x e.1] at *
      rw [abs_le]
      constructor
      · have := latticeDist_comm e.1 e.2.1
        linarith
      · have := latticeDist_comm e.1 e.2.1
        linarith
    have h1 : -(latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) ≤
        |bondHeat ω t x e.2.1 - bondHeat ω t x e.1| := by
      calc -(latticeDist x e.2.1 - latticeDist x e.1) *
            (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)
          ≤ |-(latticeDist x e.2.1 - latticeDist x e.1) *
            (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)| := le_abs_self _
        _ = |latticeDist x e.2.1 - latticeDist x e.1| *
            |bondHeat ω t x e.2.1 - bondHeat ω t x e.1| := by rw [abs_mul, abs_neg]
        _ ≤ 1 * |bondHeat ω t x e.2.1 - bondHeat ω t x e.1| :=
            mul_le_mul_of_nonneg_right hd (abs_nonneg _)
        _ = _ := one_mul _
    by_cases h : (openGraph ω).Reachable x e.1
    · have hb : (openGraph ω).Reachable x e.2.1 :=
        h.trans (((openGraph ω).mem_neighborFinset _ _).1 e.2.2).reachable
      have hmono : 0 ≤ (Real.log (bondHeat ω t x e.2.1) - Real.log (bondHeat ω t x e.1)) *
          (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) := by
        rcases le_total (bondHeat ω t x e.1) (bondHeat ω t x e.2.1) with hab | hab
        · exact mul_nonneg (sub_nonneg.2 (Real.log_le_log (bondHeat_pos ht h) hab))
            (sub_nonneg.2 hab)
        · exact mul_nonneg_of_nonpos_of_nonpos
            (sub_nonpos.2 (Real.log_le_log (bondHeat_pos ht hb) hab)) (sub_nonpos.2 hab)
      have h2 := Barlow.abs_sub_le_of_log (bondHeat_pos ht h) (bondHeat_pos ht hb) hl
      rw [mul_comm (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)] at h2
      linarith
    · have hb : ¬ (openGraph ω).Reachable x e.2.1 := fun hxb =>
        h (hxb.trans (((openGraph ω).mem_neighborFinset _ _).1 e.2.2).symm.reachable)
      rw [bondHeat_eq_zero_of_not_reachable' h, bondHeat_eq_zero_of_not_reachable' hb]
      simp
  have hsum1 : Summable fun e : OpenDart ω => l * (bondHeat ω t x e.1 + bondHeat ω t x e.2.1) +
      (Real.log (bondHeat ω t x e.2.1) - Real.log (bondHeat ω t x e.1)) *
        (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) / (4 * l) :=
    (hA.mul_left _).add (hSl.div_const _)
  have hle := Summable.tsum_le_tsum hpt (hSd.neg.congr fun e => by ring) hsum1
  rw [(hA.mul_left _).tsum_add (hSl.div_const _), tsum_mul_left, tsum_div_const] at hle
  have h8 := tsum_openDart_heat_add_le (ω := ω) ht.le x
  have hneg : ∑' e : OpenDart ω, -(latticeDist x e.2.1 - latticeDist x e.1) *
      (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) =
      -∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω t x e.2.1 - bondHeat ω t x e.1) := by
    rw [← tsum_neg]
    exact tsum_congr fun e => by ring
  rw [hneg] at hle
  have hl2 : l * ∑' e : OpenDart ω, (bondHeat ω t x e.1 + bondHeat ω t x e.2.1) ≤ 4 * d * l := by
    have := mul_le_mul_of_nonneg_left h8 hl.le
    linarith
  have e1 : ((1 / 2) * ∑' e : OpenDart ω, (Real.log (bondHeat ω t x e.2.1) -
      Real.log (bondHeat ω t x e.1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)) / (4 * l) =
      (∑' e : OpenDart ω, (Real.log (bondHeat ω t x e.2.1) -
      Real.log (bondHeat ω t x e.1)) * (bondHeat ω t x e.2.1 - bondHeat ω t x e.1)) / (4 * l) / 2 := by
    field_simp
  rw [e1]
  linarith

omit [NeZero d] in
/-- `M(0) = 0`. -/
theorem meanDist_zero (x : Vertex d) : meanDist ω x 0 = 0 := by
  unfold meanDist
  refine (tsum_congr fun y => ?_).trans tsum_zero
  rw [bondHeat_zero]
  split_ifs with h
  · subst h
    simp [latticeDist]
  · rw [mul_zero]

/-- `M(t) ≤ 2dt`: the walk moves at most at unit rate per open edge. -/
theorem meanDist_le {t : ℝ} (ht : 0 ≤ t) (x : Vertex d) : meanDist ω x t ≤ 2 * d * t := by
  have hanti : AntitoneOn (fun s => meanDist ω x s - 2 * d * s) (Set.Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => -(1 / 2) *
      ∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω s x e.2.1 - bondHeat ω s x e.1) - 2 * d * 1) (convex_Icc 0 t)
      ((continuousOn_meanDist x t).sub (continuous_const.mul continuous_id).continuousOn)
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact ((hasDerivAt_meanDist_dart hs.1 x).sub
        ((hasDerivAt_id' s).const_mul (2 * (d : ℝ)))).hasDerivWithinAt
    · rw [interior_Icc] at hs
      have hs0 := hs.1
      -- `M'(s) ≤ ½ Σ |Δp| ≤ ½ Σ (p(a) + p(b)) ≤ 2d`
      have hPd := summable_openDart_heat (ω := ω) hs0.le x (g := fun a => latticeDist x a)
        zero_le_one (fun a h => abs_latticeDist_le_sq x a h)
      have hSd := (tsum_mul_openLaplacian_eq (f := fun z => bondHeat ω s x z)
        (g := fun a => latticeDist x a) hPd).1
      have hA := summable_openDart_heat_add (ω := ω) hs0.le x
      have hpt : ∀ e : OpenDart ω, -(latticeDist x e.2.1 - latticeDist x e.1) *
          (bondHeat ω s x e.2.1 - bondHeat ω s x e.1) ≤
          bondHeat ω s x e.1 + bondHeat ω s x e.2.1 := by
        intro e
        have hd : |latticeDist x e.2.1 - latticeDist x e.1| ≤ 1 := by
          have h1 := latticeDist_triangle e.2.1 e.1 x
          have h2 := latticeDist_triangle e.1 e.2.1 x
          have h3 := latticeDist_le_one_of_mem_neighborFinset (ω := ω) e.2.2
          have h4 := latticeDist_comm e.1 e.2.1
          rw [latticeDist_comm x e.2.1, latticeDist_comm x e.1]
          rw [abs_le]
          constructor <;> linarith
        have hna := bondHeat_nonneg ω hs0.le x e.1
        have hnb := bondHeat_nonneg ω hs0.le x e.2.1
        have hab : |bondHeat ω s x e.2.1 - bondHeat ω s x e.1| ≤
            bondHeat ω s x e.1 + bondHeat ω s x e.2.1 := by
          rw [abs_le]
          constructor <;> linarith
        calc -(latticeDist x e.2.1 - latticeDist x e.1) *
              (bondHeat ω s x e.2.1 - bondHeat ω s x e.1)
            ≤ |(latticeDist x e.2.1 - latticeDist x e.1) *
                (bondHeat ω s x e.2.1 - bondHeat ω s x e.1)| := by
              rw [neg_mul]
              exact neg_le_abs _
          _ = |latticeDist x e.2.1 - latticeDist x e.1| *
                |bondHeat ω s x e.2.1 - bondHeat ω s x e.1| := abs_mul _ _
          _ ≤ 1 * (bondHeat ω s x e.1 + bondHeat ω s x e.2.1) :=
              mul_le_mul hd hab (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      have hle := Summable.tsum_le_tsum hpt (hSd.neg.congr fun e => by ring) hA
      have h8 := tsum_openDart_heat_add_le (ω := ω) hs0.le x
      have hneg : ∑' e : OpenDart ω, -(latticeDist x e.2.1 - latticeDist x e.1) *
          (bondHeat ω s x e.2.1 - bondHeat ω s x e.1) =
          -∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
            (bondHeat ω s x e.2.1 - bondHeat ω s x e.1) := by
        rw [← tsum_neg]
        exact tsum_congr fun e => by ring
      rw [hneg] at hle
      show -(1 / 2) * ∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω s x e.2.1 - bondHeat ω s x e.1) - 2 * d * 1 ≤ 0
      linarith
  have h := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only at h
  rw [meanDist_zero, mul_zero, sub_zero] at h
  linarith

/-- **Barlow 2004, Lemma 3.3(a)**: if `p_t(x, ·) ≤ B` then `Q(t) ≥ -log B`. -/
theorem neg_log_le_heatEntropy {t B : ℝ} (ht : 0 < t) (x : Vertex d)
    (hle : ∀ y, bondHeat ω t x y ≤ B) : -Real.log B ≤ heatEntropy ω x t := by
  have hs := hasSum_bondHeat ω ht.le x
  have hpt : ∀ y, bondHeat ω t x y * (-Real.log B) ≤ Real.negMulLog (bondHeat ω t x y) := by
    intro y
    rw [Real.negMulLog]
    by_cases h0 : bondHeat ω t x y = 0
    · rw [h0]; simp
    · have hp : 0 < bondHeat ω t x y := lt_of_le_of_ne (bondHeat_nonneg ω ht.le x y) (Ne.symm h0)
      have := Real.log_le_log hp (hle y)
      nlinarith
  calc -Real.log B = ∑' y, bondHeat ω t x y * (-Real.log B) := by
        rw [tsum_mul_right, hs.tsum_eq, one_mul]
    _ ≤ heatEntropy ω x t :=
        Summable.tsum_le_tsum hpt (hs.summable.mul_right _) (summable_negMulLog_bondHeat ht x)

/-- `Σ_y e^{-|y - x|/M} ≤ (6d)^d M^d` for `M ≥ 1/2`. -/
theorem tsum_exp_neg_latticeDist_le {M : ℝ} (hM : 1 / 2 ≤ M) (x : Vertex d) :
    Summable (fun y => Real.exp (-(latticeDist x y / M))) ∧
      ∑' y, Real.exp (-(latticeDist x y / M)) ≤ (6 * d) ^ d * M ^ d := by
  have hM0 : 0 < M := by linarith
  have hd1 : (1 : ℝ) ≤ d := one_le_dim_real
  have hdM : 0 < (d : ℝ) * M := by positivity
  set q := Real.exp (-(1 / (d * M))) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by rw [neg_lt_zero]; positivity)
  have hpt : ∀ y, Real.exp (-(latticeDist x y / M)) ≤ q ^ l1Dist x y := by
    intro y
    have hl : (l1Dist x y : ℝ) ≤ d * latticeDist x y := by
      have e : (l1Dist x y : ℝ) = ∑ i, |(x i : ℝ) - y i| := by
        simp only [l1Dist]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, abs_sub_comm]
      rw [e]
      calc ∑ i, |(x i : ℝ) - y i| ≤ ∑ _i : Fin d, latticeDist x y :=
            Finset.sum_le_sum fun i _ => abs_sub_le_latticeDist x y i
        _ = d * latticeDist x y := by simp
    rw [hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have e : (l1Dist x y : ℝ) * -(1 / (d * M)) = -((l1Dist x y : ℝ) / (d * M)) := by ring
    rw [e, neg_le_neg_iff, div_le_div_iff₀ hdM hM0]
    nlinarith [latticeDist_nonneg x y]
  have hsum := hasSum_pow_l1Dist x hq0 hq1
  have hs : Summable fun y => Real.exp (-(latticeDist x y / M)) :=
    hsum.summable.of_nonneg_of_le (fun y => (Real.exp_pos _).le) hpt
  refine ⟨hs, ?_⟩
  have h1 : ∑' y, Real.exp (-(latticeDist x y / M)) ≤ ((1 - q)⁻¹ + q * (1 - q)⁻¹) ^ d := by
    rw [← hsum.tsum_eq]
    exact Summable.tsum_le_tsum hpt hs hsum.summable
  refine h1.trans ?_
  -- `1 - q ≥ 1/(3dM)`
  have hq' : 1 / (3 * (d * M)) ≤ 1 - q := by
    have hexp : q ≤ 1 / (1 + 1 / (d * M)) := by
      rw [hq, le_div_iff₀ (by positivity)]
      have h2 := Real.add_one_le_exp (1 / (d * M))
      have h3 : Real.exp (-(1 / (d * M))) * Real.exp (1 / (d * M)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(1 / (d * M)))]
    have hfin : 1 - 1 / (1 + 1 / (d * M)) = 1 / (d * M + 1) := by
      field_simp
      ring
    have h4 : 1 / (3 * (d * M)) ≤ 1 / (d * M + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hpos : 0 < 1 - q := by
    have : 0 < 1 / (3 * (d * M)) := by positivity
    linarith
  have hratio : (1 - q)⁻¹ + q * (1 - q)⁻¹ ≤ 6 * d * M := by
    have e : (1 - q)⁻¹ + q * (1 - q)⁻¹ = (1 + q) / (1 - q) := by
      rw [div_eq_mul_inv]
      ring
    rw [e, div_le_iff₀ hpos]
    have : 1 ≤ 3 * (d * M) * (1 - q) := by
      rw [div_le_iff₀ (by positivity)] at hq'
      linarith
    nlinarith
  have hr0 : 0 ≤ (1 - q)⁻¹ + q * (1 - q)⁻¹ := by
    have : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 hpos.le
    positivity
  calc ((1 - q)⁻¹ + q * (1 - q)⁻¹) ^ d ≤ (6 * d * M) ^ d := pow_le_pow_left₀ hr0 hratio d
    _ = (6 * d) ^ d * M ^ d := by rw [mul_pow]

/-- The constant `K_d = 1 + (6d)^d` of Lemma 3.3(b). -/
noncomputable def entropyConst (d : ℕ) : ℝ := 1 + (6 * d) ^ d

/-- **Barlow 2004, Lemma 3.3(b)**: if `M(t) ≥ 1/2` then `Q(t) ≤ K_d + d log M(t)`. -/
theorem heatEntropy_le_log_meanDist {t : ℝ} (ht : 0 < t) (x : Vertex d)
    (hM : 1 / 2 ≤ meanDist ω x t) :
    heatEntropy ω x t ≤ entropyConst d + d * Real.log (meanDist ω x t) := by
  set M := meanDist ω x t with hMdef
  have hM0 : 0 < M := by linarith
  obtain ⟨hes, hel⟩ := tsum_exp_neg_latticeDist_le hM x
  have hs := hasSum_bondHeat ω ht.le x
  have hds := summable_latticeDist_mul_bondHeat (ω := ω) ht.le x
  set b := d * Real.log M with hb
  have hpt : ∀ y, Real.negMulLog (bondHeat ω t x y) ≤
      (1 / M) * (latticeDist x y * bondHeat ω t x y) + b * bondHeat ω t x y +
        Real.exp (-1 - b) * Real.exp (-(latticeDist x y / M)) := by
    intro y
    have h := Barlow.negMulLog_le_mul_add_exp (bondHeat ω t x y) ((1 / M) * latticeDist x y + b)
      (bondHeat_nonneg ω ht.le x y)
    have he : Real.exp (-1 - ((1 / M) * latticeDist x y + b)) =
        Real.exp (-1 - b) * Real.exp (-(latticeDist x y / M)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at h
    linarith
  have hsumR : Summable fun y => (1 / M) * (latticeDist x y * bondHeat ω t x y) +
      b * bondHeat ω t x y + Real.exp (-1 - b) * Real.exp (-(latticeDist x y / M)) :=
    ((hds.mul_left _).add (hs.summable.mul_left _)).add (hes.mul_left _)
  have hle := Summable.tsum_le_tsum hpt (summable_negMulLog_bondHeat ht x) hsumR
  rw [((hds.mul_left _).add (hs.summable.mul_left _)).tsum_add (hes.mul_left _),
    (hds.mul_left _).tsum_add (hs.summable.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, hs.tsum_eq] at hle
  have hMd : ∑' y, latticeDist x y * bondHeat ω t x y = M := rfl
  rw [hMd] at hle
  have h1 : (1 / M) * M = 1 := by field_simp
  have h2 : Real.exp (-1 - b) = Real.exp (-1) / M ^ d := by
    have e : Real.exp (d * Real.log M) = M ^ d := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [hb, sub_eq_add_neg, Real.exp_add, Real.exp_neg (d * Real.log M), e, div_eq_mul_inv]
  have h3 : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  have h4 : Real.exp (-1 - b) * ∑' y, Real.exp (-(latticeDist x y / M)) ≤ (6 * d) ^ d := by
    rw [h2]
    calc Real.exp (-1) / M ^ d * ∑' y, Real.exp (-(latticeDist x y / M))
        ≤ Real.exp (-1) / M ^ d * ((6 * d) ^ d * M ^ d) :=
          mul_le_mul_of_nonneg_left hel (by positivity)
      _ = Real.exp (-1) * (6 * d) ^ d := by field_simp
      _ ≤ 1 * (6 * d) ^ d := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (6 * d) ^ d := one_mul _
  unfold heatEntropy
  rw [h1] at hle
  rw [entropyConst]
  linarith

/-- **Barlow 2004, Proposition 3.4** (upper half), in dimension `d`: if
`Q(s) ≥ c₁ + (d/2) log s` on `[T₀, t]`, `T₀² ≤ t` and `M(t) ≥ 1/2`, then
`M(t) ≤ 2 (3d + K_d - c₁ + d log(2d)) √t`. -/
theorem meanDist_le_of_entropy {x : Vertex d} {T0 t c1 : ℝ} (hT0 : 1 ≤ T0) (hT0t : T0 ^ 2 ≤ t)
    (hQ : ∀ s, T0 ≤ s → s ≤ t → c1 + d / 2 * Real.log s ≤ heatEntropy ω x s)
    (hM : 1 / 2 ≤ meanDist ω x t) :
    meanDist ω x t ≤
      2 * (3 * d + entropyConst d - c1 + d * Real.log (2 * d)) * Real.sqrt t := by
  have hT0' : 0 < T0 := by linarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hT0t
  have hd1 : (1 : ℝ) ≤ d := one_le_dim_real
  have hT0le : T0 ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq hT0'.le]
    exact Real.sqrt_le_sqrt hT0t
  have hT0t' : T0 ≤ t := by nlinarith
  set H : ℝ → ℝ := fun s => meanDist ω x s - 2 * d * Real.sqrt s -
    Real.sqrt s * (heatEntropy ω x s - c1 - d / 2 * Real.log s) with hH
  have hanti : AntitoneOn H (Set.Icc T0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s =>
      (-(1 / 2) * ∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω s x e.2.1 - bondHeat ω s x e.1)) - 2 * d * (1 / (2 * Real.sqrt s)) -
      ((1 / (2 * Real.sqrt s)) * (heatEntropy ω x s - c1 - d / 2 * Real.log s) +
        Real.sqrt s * ((1 / 2) * ∑' e : OpenDart ω, (Real.log (bondHeat ω s x e.2.1) -
          Real.log (bondHeat ω s x e.1)) * (bondHeat ω s x e.2.1 - bondHeat ω s x e.1) - 0 -
          d / 2 * s⁻¹))) (convex_Icc T0 t) ?_ (fun s hs => ?_) (fun s hs => ?_)
    · have hpos : ∀ s ∈ Set.Icc T0 t, 0 < s := fun s hs => lt_of_lt_of_le hT0' hs.1
      refine (((continuousOn_meanDist x t).mono fun s hs => ⟨(hpos s hs).le, hs.2⟩).sub
        (continuous_const.mul Real.continuous_sqrt).continuousOn).sub
        (Real.continuous_sqrt.continuousOn.mul (((continuousOn_heatEntropy x hT0').sub
          continuousOn_const).sub (continuousOn_const.mul
            (Real.continuousOn_log.mono fun s hs => (hpos s hs).ne'))))
    · rw [interior_Icc] at hs
      have hs0 : 0 < s := lt_trans hT0' hs.1
      have hsq := Real.hasDerivAt_sqrt hs0.ne'
      have hd := ((hasDerivAt_meanDist_dart (ω := ω) hs0 x).sub (hsq.const_mul (2 * (d : ℝ)))).sub
        (hsq.mul (((hasDerivAt_heatEntropy_dart (ω := ω) hs0 x).sub (hasDerivAt_const s c1)).sub
          ((Real.hasDerivAt_log hs0.ne').const_mul (d / 2 : ℝ))))
      exact hd.hasDerivWithinAt
    · rw [interior_Icc] at hs
      have hs0 : 0 < s := lt_trans hT0' hs.1
      have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
      have hR : 0 ≤ heatEntropy ω x s - c1 - d / 2 * Real.log s := by
        have := hQ s hs.1.le hs.2.le
        linarith
      have hMQ := deriv_meanDist_le (ω := ω) hs0 (l := 1 / (4 * Real.sqrt s)) (by positivity) x
      set Qd := (1 / 2) * ∑' e : OpenDart ω, (Real.log (bondHeat ω s x e.2.1) -
          Real.log (bondHeat ω s x e.1)) * (bondHeat ω s x e.2.1 - bondHeat ω s x e.1)
      set Md := -(1 / 2) * ∑' e : OpenDart ω, (latticeDist x e.2.1 - latticeDist x e.1) *
        (bondHeat ω s x e.2.1 - bondHeat ω s x e.1)
      have e1 : 2 * d * (1 / (4 * Real.sqrt s)) = d / 2 * (1 / Real.sqrt s) := by
        field_simp
        ring
      have e2 : Qd / (4 * (1 / (4 * Real.sqrt s))) = Real.sqrt s * Qd := by field_simp
      rw [e2, e1] at hMQ
      have e3 : Real.sqrt s * s⁻¹ = 1 / Real.sqrt s := by
        have := Real.sq_sqrt hs0.le
        field_simp
        nlinarith
      have e4 : 2 * d * (1 / (2 * Real.sqrt s)) = d * (1 / Real.sqrt s) := by field_simp
      have hRn : 0 ≤ (1 / (2 * Real.sqrt s)) * (heatEntropy ω x s - c1 - d / 2 * Real.log s) := by
        positivity
      show Md - 2 * d * (1 / (2 * Real.sqrt s)) -
        ((1 / (2 * Real.sqrt s)) * (heatEntropy ω x s - c1 - d / 2 * Real.log s) +
          Real.sqrt s * (Qd - 0 - d / 2 * s⁻¹)) ≤ 0
      have e5 : Real.sqrt s * (Qd - 0 - d / 2 * s⁻¹) =
          Real.sqrt s * Qd - d / 2 * (1 / Real.sqrt s) := by
        rw [sub_zero, mul_sub, ← e3]
        ring
      rw [e4, e5]
      linarith
  have hHt := hanti ⟨le_rfl, hT0t'⟩ ⟨hT0t', le_rfl⟩ hT0t'
  simp only [hH] at hHt
  have hRT0 : 0 ≤ heatEntropy ω x T0 - c1 - d / 2 * Real.log T0 := by
    have := hQ T0 le_rfl hT0t'
    linarith
  have hMT0 := meanDist_le (ω := ω) hT0'.le x
  have hsqT0 : 0 ≤ Real.sqrt T0 := Real.sqrt_nonneg _
  -- `M(t) ≤ 4d √t + √t · R(t)`, `R(t) = Q(t) - c₁ - (d/2) log t`
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hdT0 : 2 * d * T0 ≤ 2 * d * Real.sqrt t := mul_le_mul_of_nonneg_left hT0le (by positivity)
  have hMt : meanDist ω x t ≤
      Real.sqrt t * (4 * d + (heatEntropy ω x t - c1 - d / 2 * Real.log t)) := by
    nlinarith [mul_nonneg hsqT0 hRT0, mul_nonneg hsqT0 (by positivity : (0 : ℝ) ≤ 2 * d)]
  -- Lemma 3.3(b)
  have hQt := heatEntropy_le_log_meanDist (ω := ω) ht x hM
  set M := meanDist ω x t with hMdef
  have hM0 : 0 < M := by linarith
  set ρ := M / Real.sqrt t with hρ
  have hρ0 : 0 < ρ := by positivity
  have hlogρ : Real.log ρ = Real.log M - Real.log t / 2 := by
    rw [hρ, Real.log_div hM0.ne' hsqt.ne', Real.log_sqrt ht.le]
  have hρle : ρ ≤ 4 * d + (entropyConst d - c1 + d * Real.log ρ) := by
    have h1 : ρ ≤ 4 * d + (heatEntropy ω x t - c1 - d / 2 * Real.log t) := by
      rw [hρ, div_le_iff₀ hsqt]
      linarith
    rw [hlogρ]
    have e : d * (Real.log M - Real.log t / 2) = d * Real.log M - d / 2 * Real.log t := by ring
    rw [e]
    linarith
  have hlog2d : Real.log ρ ≤ ρ / (2 * d) + Real.log (2 * d) - 1 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < ρ / (2 * d))
    rw [Real.log_div hρ0.ne' (by positivity)] at h
    linarith
  have hdlog : d * Real.log ρ ≤ ρ / 2 + d * Real.log (2 * d) - d := by
    have h := mul_le_mul_of_nonneg_left hlog2d (by positivity : (0 : ℝ) ≤ d)
    have e : (d : ℝ) * (ρ / (2 * d) + Real.log (2 * d) - 1) =
        ρ / 2 + d * Real.log (2 * d) - d := by
      field_simp
    linarith
  have hρb : ρ ≤ 2 * (3 * d + entropyConst d - c1 + d * Real.log (2 * d)) := by linarith
  calc M = ρ * Real.sqrt t := by rw [hρ]; field_simp
    _ ≤ 2 * (3 * d + entropyConst d - c1 + d * Real.log (2 * d)) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right hρb hsqt.le

end Rigidity.BarlowLattice
