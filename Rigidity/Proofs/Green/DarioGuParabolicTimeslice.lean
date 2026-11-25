import Rigidity.Proofs.Green.DarioGuParabolicCaccioppoli

/-!
# The `L^∞ L²` gradient estimate in time slices on the planar cluster

**Dario–Gu, Lemma 2.10** (lines 1023-1036 of the source): *There exists a positive constant
`C < ∞` such that for any radius `R ≥ 1`, any point `y ∈ ℤ^d` and any function
`u : I_R × (𝒞_∞ ∩ B_R(y)) → ℝ` which satisfies `∂_t u - ∇·a∇u = 0` in `I_R × (𝒞_∞ ∩ B_R(y))`, one has
`sup_{t ∈ I_{R/2}} ‖∇u(t, ·)‖_{L̲²(𝒞_∞ ∩ B_{R/2}(y))} ≤ C ‖∇u‖_{L̲²(I_R × (𝒞_∞ ∩ B_R(y)))}`.*
The source refers to Armstrong–Kuusi–Mourrat, Lemma 8.2 ("the extension to the percolation cluster
makes no difference in the proof").

With the normalized norms and a constant independent of the configuration the printed inequality
fails: if `𝒞_∞ ∩ B_{R/2}(y)` is a path of length of order `R` joining two large clusters of the
annulus, a time-independent `u`, harmonic at the interior vertices, close to `0` on one of them and
to `1` on the other, has `‖∇u(t)‖²_{L̲²(𝒞_∞ ∩ B_{R/2})}` of order `R^{-2}` and
`‖∇u‖²_{L̲²(I_R × (𝒞_∞ ∩ B_R))}` of order `R^{-3}`. The statement proved here is the unnormalized one,
`sup_{t ∈ I_{R/2}} ‖∇u(t, ·)‖²_{L²(𝒞_∞ ∩ B_{R/2}(y))} ≤ C R^{-2} ‖∇u‖²_{L²(I_R × (𝒞_∞ ∩ B_R(y)))}`,
which gives the printed one whenever `|𝒞_∞ ∩ B_R(y)| ≤ C' |𝒞_∞ ∩ B_{R/2}(y)|`; the gradient on the
left is over the open edges inside `𝒞_∞ ∩ B_{R/2}(y)`, on the right over the open edges from
`𝒞_∞ ∩ B_R(y)` into itself.

The proof is that of the source: with a cutoff `η` and `F(t) = Σ_{x ∼ z} η(x) η(z) (u(t,z) - u(t,x))²`,
testing the equation with `η² ∂_t u` gives `F'(t) ≤ 4 ℓ² Σ_{x ∼ z} (u(t,z) - u(t,x))²`
(`timesliceDeriv_le`); integrating from `s` to `t` and averaging over `s` gives the estimate
(`timeslice_of_cutoff`).
-/

open MeasureTheory Finset LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open scoped Classical

namespace Rigidity.Green

variable {ω : Configuration 2}

/-- **Dario–Gu, Lemma 2.10**, in dimension two, in the unnormalized form, for every open
component. -/
def DarioGuTimesliceTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (ω : Configuration 2) (K : OpenComponent ω) (y : Vertex 2) (R : ℝ), 1 ≤ R →
    ∀ u : ℝ → Vertex 2 → ℝ, IsClusterCaloric ω (clusterBall K y R) (-R ^ 2) 0 u →
      ∀ t ∈ Set.Ioc (-(R / 2) ^ 2) 0,
        gradEnergy ω (clusterBall K y (R / 2)) (u t) ≤
          C / R ^ 2 * ∫ τ in Set.Ioc (-R ^ 2) 0, ∑ x ∈ clusterBall K y R,
            clusterGradAt ω (clusterBall K y R) (u τ) x ^ 2

/-! ### The derivative of the weighted energy -/

/-- `F'(t) ≤ 4 ℓ² G(t)` at a fixed time: with `w` the restricted Laplacian of `v`,
`2 Σ_{x ∼ z} η_x η_z (v_z - v_x)(w_z - w_x) ≤ 4 ℓ² Σ_{x ∼ z} (v_z - v_x)²`. -/
theorem timesliceDeriv_le (V : Finset (Vertex 2)) (v η : Vertex 2 → ℝ) {ℓ : ℝ}
    (hηlip : ∀ x z, (openGraph ω).Adj x z → |η x - η z| ≤ ℓ) :
    2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then
        η x * η z * ((v z - v x) * (restrictLap ω V v z - restrictLap ω V v x)) else 0) ≤
      4 * ℓ ^ 2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) := by
  set w : Vertex 2 → ℝ := restrictLap ω V v with hw
  set f : Vertex 2 → ℝ := fun x => η x ^ 2 * w x with hf
  set P : ℝ := ∑ x ∈ V, η x ^ 2 * w x ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun x _ => by positivity
  -- summation by parts: `2P = -Σ (f_z - f_x)(v_z - v_x)`
  have hsbp := two_mul_sum_restrict (ω := ω) V f v
  have e1 : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then f x * (v z - v x) else 0) = P := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ∑ z ∈ V, (if (openGraph ω).Adj x z then f x * (v z - v x) else 0) =
        f x * w x := by
      simp only [hw, restrictLap, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    rw [this, hf]
    ring
  rw [e1] at hsbp
  -- the decomposition of `f_z - f_x`
  set X : ℝ := ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then
    (η z - η x) * (η z * w z + η x * w x) * (v z - v x) else 0) with hX
  have hdec : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (f z - f x) * (v z - v x) else 0) =
      ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then
        η x * η z * ((v z - v x) * (w z - w x)) else 0) + X := by
    rw [hX, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs
    · simp only [hf]
      ring
    · ring
  -- the bound `-2X ≤ 4P + 4ℓ²G`
  have hpt : ∀ x ∈ V, ∀ z ∈ V, (if (openGraph ω).Adj x z then
      -(2 * ((η z - η x) * (η z * w z + η x * w x) * (v z - v x))) else 0) ≤
      (if (openGraph ω).Adj x z then
        (η z ^ 2 * w z ^ 2 + η x ^ 2 * w x ^ 2) / 2 + 4 * ℓ ^ 2 * (v z - v x) ^ 2 else 0) := by
    intro x _ z _
    split_ifs with hxz
    · have hl := hηlip x z hxz
      have hl0 : 0 ≤ ℓ := (abs_nonneg _).trans hl
      have hB : ((η z - η x) * (v z - v x)) ^ 2 ≤ ℓ ^ 2 * (v z - v x) ^ 2 := by
        rw [mul_pow]
        have : (η z - η x) ^ 2 ≤ ℓ ^ 2 := by
          rw [← sq_abs, abs_sub_comm]
          exact pow_le_pow_left₀ (abs_nonneg _) hl 2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
      have hA : (η z * w z + η x * w x) ^ 2 ≤ 2 * (η z ^ 2 * w z ^ 2 + η x ^ 2 * w x ^ 2) := by
        nlinarith [sq_nonneg (η z * w z - η x * w x)]
      nlinarith [sq_nonneg ((η z * w z + η x * w x) / 2 + 2 * ((η z - η x) * (v z - v x)))]
    · exact le_refl _
  have hsum := Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz => hpt x hx z hz
  have hL : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then
      -(2 * ((η z - η x) * (η z * w z + η x * w x) * (v z - v x))) else 0) = -(2 * X) := by
    rw [hX, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  have hR : ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then
      (η z ^ 2 * w z ^ 2 + η x ^ 2 * w x ^ 2) / 2 + 4 * ℓ ^ 2 * (v z - v x) ^ 2 else 0) =
      (∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then η z ^ 2 * w z ^ 2 else 0) +
        ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then η x ^ 2 * w x ^ 2 else 0)) / 2 +
      4 * ℓ ^ 2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) := by
    rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  rw [hL, hR, sum_restrict_swap (ω := ω) V (fun z => η z ^ 2 * w z ^ 2)] at hsum
  have h4 := sum_restrict_le_four (ω := ω) V (g := fun x => η x ^ 2 * w x ^ 2)
    (fun x => by positivity)
  rw [hdec] at hsbp
  linarith

/-! ### Integration in time -/

/-- **The time-slice estimate with a cutoff.** For `u` caloric at the vertices of `V` whose open
neighbours lie in `V`, `η ∈ [0, 1]` vanishing off these vertices and varying by at most `ℓ` along
open edges, and `t ∈ [c, b]`,
`Σ_{x ∼ z} η_x η_z (u(t,z) - u(t,x))² ≤ (1/(c - a) + 4ℓ²) ∫_a^b Σ_{x ∼ z} (u(τ,z) - u(τ,x))² dτ`. -/
theorem timeslice_of_cutoff {V : Finset (Vertex 2)} {a c b : ℝ} (hac : a < c) (hcb : c ≤ b)
    {u : ℝ → Vertex 2 → ℝ} (hu : IsClusterCaloric ω V a b u) {η : Vertex 2 → ℝ} {ℓ : ℝ}
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hηint : ∀ x, η x ≠ 0 → x ∈ V ∧ ∀ z, (openGraph ω).Adj x z → z ∈ V)
    (hηlip : ∀ x z, (openGraph ω).Adj x z → |η x - η z| ≤ ℓ) {t : ℝ} (ht : t ∈ Set.Icc c b) :
    ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then η x * η z * (u t z - u t x) ^ 2 else 0) ≤
      (1 / (c - a) + 4 * ℓ ^ 2) *
        ∫ τ in a..b, ∑ x ∈ V, ∑ z ∈ V,
          (if (openGraph ω).Adj x z then (u τ z - u τ x) ^ 2 else 0) := by
  have hab : a < b := lt_of_lt_of_le hac hcb
  have hca : 0 < c - a := by linarith
  set F : ℝ → ℝ := fun τ => ∑ x ∈ V, ∑ z ∈ V,
    (if (openGraph ω).Adj x z then η x * η z * (u τ z - u τ x) ^ 2 else 0) with hF
  set F' : ℝ → ℝ := fun τ => 2 * ∑ x ∈ V, ∑ z ∈ V, (if (openGraph ω).Adj x z then
    η x * η z * ((u τ z - u τ x) * (restrictLap ω V (u τ) z - restrictLap ω V (u τ) x)) else 0)
    with hF'
  set G : ℝ → ℝ := fun τ => ∑ x ∈ V, ∑ z ∈ V,
    (if (openGraph ω).Adj x z then (u τ z - u τ x) ^ 2 else 0) with hG
  have hcu : ∀ x ∈ V, ContinuousOn (fun τ => u τ x) (Set.Icc a b) := hu.1
  have hG0 : ∀ τ, 0 ≤ G τ := fun τ => Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
  have hFG : ∀ τ, F τ ≤ G τ := fun τ => Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => by
    split_ifs
    · have h1 : η x * η z ≤ 1 := by nlinarith [hη0 x, hη0 z, hη1 x, hη1 z]
      have h2 : 0 ≤ (u τ z - u τ x) ^ 2 := sq_nonneg _
      nlinarith
    · exact le_refl _
  have hlap : ∀ x ∈ V, ContinuousOn (fun τ => restrictLap ω V (u τ) x) (Set.Icc a b) := by
    intro x hx
    unfold restrictLap
    refine continuousOn_finsetSum _ fun z hz => ?_
    by_cases h : (openGraph ω).Adj x z
    · simp only [h, if_true]
      exact (hcu z hz).sub (hcu x hx)
    · simp only [h, if_false]
      exact continuousOn_const
  have hFc : ContinuousOn F (Set.Icc a b) := continuousOn_sum_restrict fun x hx z hz =>
    continuousOn_const.mul (((hcu z hz).sub (hcu x hx)).pow 2)
  have hF'c : ContinuousOn F' (Set.Icc a b) := continuousOn_const.mul
    (continuousOn_sum_restrict fun x hx z hz => continuousOn_const.mul
      (((hcu z hz).sub (hcu x hx)).mul ((hlap z hz).sub (hlap x hx))))
  have hGc : ContinuousOn G (Set.Icc a b) := continuousOn_sum_restrict fun x hx z hz =>
    ((hcu z hz).sub (hcu x hx)).pow 2
  -- the derivative of `F`
  have hFd : ∀ s ∈ Set.Ioo a b, HasDerivAt F (F' s) s := by
    intro s hs
    have hterm : ∀ x ∈ V, ∀ z ∈ V, HasDerivAt
        (fun τ => if (openGraph ω).Adj x z then η x * η z * (u τ z - u τ x) ^ 2 else 0)
        (if (openGraph ω).Adj x z then η x * η z *
          (2 * ((u s z - u s x) * (restrictLap ω V (u s) z - restrictLap ω V (u s) x)))
          else 0) s := by
      intro x _ z _
      by_cases hxz : (openGraph ω).Adj x z
      · simp only [hxz, if_true]
        by_cases h0 : η x * η z = 0
        · rw [h0]
          simpa using hasDerivAt_const s (0 : ℝ)
        · have hx : η x ≠ 0 := fun h => h0 (by rw [h, zero_mul])
          have hz : η z ≠ 0 := fun h => h0 (by rw [h, mul_zero])
          obtain ⟨hxV, hxnb⟩ := hηint x hx
          obtain ⟨hzV, hznb⟩ := hηint z hz
          have dx := hu.2 x hxV hxnb s hs
          have dz := hu.2 z hzV hznb s hs
          rw [openLaplacian_eq_restrict hxnb] at dx
          rw [openLaplacian_eq_restrict hznb] at dz
          refine (((dz.sub dx).pow 2).const_mul (η x * η z)).congr_deriv ?_
          simp only [restrictLap, Pi.sub_apply]
          rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
          push_cast
          ring
      · simp only [hxz, if_false]
        exact hasDerivAt_const s (0 : ℝ)
    have hsum := HasDerivAt.fun_sum fun x hx => HasDerivAt.fun_sum fun z hz => hterm x hx z hz
    refine hsum.congr_deriv ?_
    simp only [hF', Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> ring
  -- `F' ≤ 4ℓ² G`
  have hF'G : ∀ τ, F' τ ≤ 4 * ℓ ^ 2 * G τ := fun τ =>
    timesliceDeriv_le (ω := ω) V (u τ) η hηlip
  have huIcc : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → ∀ {H : ℝ → ℝ},
      ContinuousOn H (Set.Icc a b) → IntervalIntegrable H volume p q := by
    intro p q hp hpq hq H hH
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hpq]
    exact hH.mono (Set.Icc_subset_Icc hp hq)
  -- `F(t) ≤ F(s) + 4ℓ² ∫_a^b G` for `s ∈ [a, c]`
  have hGab : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b →
      ∫ τ in p..q, G τ ≤ ∫ τ in a..b, G τ := by
    intro p q hp hpq hq
    have h1 := intervalIntegral.integral_add_adjacent_intervals (huIcc le_rfl hp (hpq.trans hq) hGc)
      (huIcc hp hpq hq hGc)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (huIcc le_rfl (hp.trans hpq) hq hGc) (huIcc (hp.trans hpq) hq le_rfl hGc)
    have h3 : 0 ≤ ∫ τ in a..p, G τ := intervalIntegral.integral_nonneg hp fun τ _ => hG0 τ
    have h4 : 0 ≤ ∫ τ in q..b, G τ := intervalIntegral.integral_nonneg hq fun τ _ => hG0 τ
    linarith
  have hstep : ∀ s ∈ Set.Icc a c, F t ≤ F s + 4 * ℓ ^ 2 * ∫ τ in a..b, G τ := by
    intro s hs
    have hst : s ≤ t := hs.2.trans ht.1
    have hFTC : ∫ τ in s..t, F' τ = F t - F s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
        (hFc.mono (Set.Icc_subset_Icc hs.1 ht.2))
        (fun τ hτ => hFd τ ⟨lt_of_le_of_lt hs.1 hτ.1, lt_of_lt_of_le hτ.2 ht.2⟩)
        (huIcc hs.1 hst ht.2 hF'c)
    have hmono : ∫ τ in s..t, F' τ ≤ ∫ τ in s..t, 4 * ℓ ^ 2 * G τ :=
      intervalIntegral.integral_mono_on hst (huIcc hs.1 hst ht.2 hF'c)
        ((huIcc hs.1 hst ht.2 hGc).const_mul _) fun τ _ => hF'G τ
    have hmono' : ∫ τ in s..t, 4 * ℓ ^ 2 * G τ = 4 * ℓ ^ 2 * ∫ τ in s..t, G τ :=
      intervalIntegral.integral_const_mul _ _
    have h1 := hGab hs.1 hst ht.2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * ℓ ^ 2)
    linarith
  -- averaging over `s ∈ [a, c]`
  have havg : ∫ s in a..c, F t ≤ ∫ s in a..c, (F s + 4 * ℓ ^ 2 * ∫ τ in a..b, G τ) :=
    intervalIntegral.integral_mono_on hac.le intervalIntegrable_const
      ((huIcc le_rfl hac.le hcb hFc).add intervalIntegrable_const) hstep
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (huIcc le_rfl hac.le hcb hFc)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at havg
  have hFc' : ∫ s in a..c, F s ≤ ∫ s in a..c, G s :=
    intervalIntegral.integral_mono_on hac.le (huIcc le_rfl hac.le hcb hFc)
      (huIcc le_rfl hac.le hcb hGc) fun s _ => hFG s
  have h1 := hGab le_rfl hac.le hcb
  have hint0 : 0 ≤ ∫ τ in a..b, G τ := intervalIntegral.integral_nonneg hab.le fun τ _ => hG0 τ
  have hca' : c - a ≠ 0 := hca.ne'
  have h2 : (c - a) * F t ≤ (c - a) * ((1 / (c - a) + 4 * ℓ ^ 2) * ∫ τ in a..b, G τ) := by
    have e : (c - a) * ((1 / (c - a) + 4 * ℓ ^ 2) * ∫ τ in a..b, G τ) =
        (∫ τ in a..b, G τ) + (c - a) * (4 * ℓ ^ 2 * ∫ τ in a..b, G τ) := by
      rw [add_mul, mul_add, ← mul_assoc, mul_one_div_cancel hca', one_mul]
    rw [e]
    linarith
  exact le_of_mul_le_mul_left h2 hca

/-! ### The estimate on balls -/

theorem latticeDist_le_one_of_adj {x z : Vertex 2} (h : (openGraph ω).Adj x z) :
    latticeDist x z ≤ 1 := by
  have h1 := LatticeProb.Percolation.lattice_adj_iff_l1Dist.mp (openGraph_le ω h)
  unfold LatticeProb.Percolation.latticeL1Dist at h1
  rw [Fin.sum_univ_two] at h1
  have h2 : |((x 0 - z 0 : ℤ) : ℝ)| + |((x 1 - z 1 : ℤ) : ℝ)| = 1 := by exact_mod_cast h1
  push_cast at h2
  have hsq := latticeDist_sq x z
  have hd := latticeDist_nonneg x z
  have ha := abs_nonneg ((x 0 : ℝ) - z 0)
  have hb := abs_nonneg ((x 1 : ℝ) - z 1)
  have e1 := sq_abs ((x 0 : ℝ) - z 0)
  have e2 := sq_abs ((x 1 : ℝ) - z 1)
  have hab2 : |(x 0 : ℝ) - z 0| ^ 2 + |(x 1 : ℝ) - z 1| ^ 2 ≤ 1 := by
    have h3 : (|(x 0 : ℝ) - z 0| + |(x 1 : ℝ) - z 1|) ^ 2 = 1 := by rw [h2]; norm_num
    nlinarith [mul_nonneg ha hb]
  have hd2 : latticeDist x z ^ 2 ≤ 1 := by
    rw [hsq, ← e1, ← e2]
    exact hab2
  nlinarith

theorem eq_of_latticeDist_lt_one {x y : Vertex 2} (h : latticeDist x y < 1) : x = y := by
  have hsq := latticeDist_sq x y
  have hd := latticeDist_nonneg x y
  have h1 : ((x 0 : ℝ) - y 0) ^ 2 + ((x 1 : ℝ) - y 1) ^ 2 < 1 := by nlinarith
  have a0 : |(x 0 : ℝ) - y 0| < 1 := by
    nlinarith [abs_nonneg ((x 0 : ℝ) - y 0), sq_abs ((x 0 : ℝ) - y 0),
      sq_nonneg ((x 1 : ℝ) - y 1)]
  have a1 : |(x 1 : ℝ) - y 1| < 1 := by
    nlinarith [abs_nonneg ((x 1 : ℝ) - y 1), sq_abs ((x 1 : ℝ) - y 1),
      sq_nonneg ((x 0 : ℝ) - y 0)]
  have k0 : x 0 - y 0 = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast a0)
  have k1 : x 1 - y 1 = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast a1)
  funext i
  fin_cases i
  · exact sub_eq_zero.1 k0
  · exact sub_eq_zero.1 k1

/-- `Σ_z b_z² ≤ (Σ_z b_z)²` for the open edges from `x` into `V`. -/
theorem sum_sq_le_clusterGradAt_sq (V : Finset (Vertex 2)) (v : Vertex 2 → ℝ) (x : Vertex 2) :
    ∑ z ∈ V, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) ≤
      clusterGradAt ω V v x ^ 2 := by
  unfold clusterGradAt
  set b : Vertex 2 → ℝ := fun z => if (openGraph ω).Adj x z then |v z - v x| else 0 with hb
  have hb0 : ∀ z, 0 ≤ b z := fun z => by simp only [hb]; split_ifs <;> positivity
  have e : ∀ z, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) = b z ^ 2 := fun z => by
    simp only [hb]
    split_ifs <;> simp [sq_abs]
  simp only [e]
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun z hz => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => hb0 i) hz) (hb0 z)

/-- The gradient energy inside `W` is at most four times the weighted energy on `V ⊇ W` when the
weight is `1` on `W`. -/
theorem gradEnergy_le_four_mul {V W : Finset (Vertex 2)} (hWV : W ⊆ V) (v η : Vertex 2 → ℝ)
    (hη0 : ∀ x, 0 ≤ η x) (hηW : ∀ x ∈ W, η x = 1) :
    gradEnergy ω W v ≤ 4 * ∑ x ∈ V, ∑ z ∈ V,
      (if (openGraph ω).Adj x z then η x * η z * (v z - v x) ^ 2 else 0) := by
  have h1 : gradEnergy ω W v ≤ ∑ x ∈ W, 4 * ∑ z ∈ W,
      (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0) := by
    unfold gradEnergy
    refine Finset.sum_le_sum fun x _ => ?_
    have := clusterGradAt_sq_le (ω := ω) W v x
    unfold clusterGradAt at this
    rw [← Finset.sum_filter] at this
    convert this using 2
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ x ∈ W, ∑ z ∈ W, (if (openGraph ω).Adj x z then (v z - v x) ^ 2 else 0)
      = ∑ x ∈ W, ∑ z ∈ W,
          (if (openGraph ω).Adj x z then η x * η z * (v z - v x) ^ 2 else 0) :=
        Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun z hz => by
          rw [hηW x hx, hηW z hz, one_mul, one_mul]
    _ ≤ ∑ x ∈ W, ∑ z ∈ V,
          (if (openGraph ω).Adj x z then η x * η z * (v z - v x) ^ 2 else 0) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg hWV fun z _ _ => by
          split_ifs
          · exact mul_nonneg (mul_nonneg (hη0 x) (hη0 z)) (sq_nonneg _)
          · exact le_refl _
    _ ≤ ∑ x ∈ V, ∑ z ∈ V,
          (if (openGraph ω).Adj x z then η x * η z * (v z - v x) ^ 2 else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hWV fun x _ _ => Finset.sum_nonneg fun z _ => by
          split_ifs
          · exact mul_nonneg (mul_nonneg (hη0 x) (hη0 z)) (sq_nonneg _)
          · exact le_refl _

/-- **Dario–Gu, Lemma 2.10** holds in the unnormalized form, with `C = 4096`. -/
theorem darioGuTimesliceTwo_holds : DarioGuTimesliceTwo := by
  refine ⟨4096, by norm_num, fun ω K y R hR u hu t ht => ?_⟩
  set V := clusterBall K y R with hV
  set W := clusterBall K y (R / 2) with hW
  have hR0 : 0 < R := by linarith
  have hWV : W ⊆ V := clusterBall_mono (by linarith)
  have hcu : ∀ x ∈ V, ContinuousOn (fun τ => u τ x) (Set.Icc (-R ^ 2) 0) := hu.1
  set I : ℝ := ∫ τ in Set.Ioc (-R ^ 2) 0, ∑ x ∈ V, clusterGradAt ω V (u τ) x ^ 2 with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioc fun τ _ =>
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hab : -R ^ 2 < -R ^ 2 / 4 := by nlinarith
  have htI : t ∈ Set.Icc (-R ^ 2 / 4) 0 := ⟨by
    have := ht.1
    have e : -(R / 2) ^ 2 = -R ^ 2 / 4 := by ring
    linarith, ht.2⟩
  -- `∫ G ≤ I`
  have hGI : ∫ τ in (-R ^ 2)..0, ∑ x ∈ V, ∑ z ∈ V,
      (if (openGraph ω).Adj x z then (u τ z - u τ x) ^ 2 else 0) ≤ I := by
    rw [intervalIntegral.integral_of_le (show -R ^ 2 ≤ (0 : ℝ) by nlinarith)]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun τ _ =>
      Finset.sum_le_sum fun x _ => sum_sq_le_clusterGradAt_sq (ω := ω) V (u τ) x
    · refine integrableOn_of_continuousOn (continuousOn_sum_restrict fun x hx z hz => ?_)
      exact ((hcu z hz).sub (hcu x hx)).pow 2
    · refine integrableOn_of_continuousOn (continuousOn_finsetSum _ fun x hx => ?_)
      refine ContinuousOn.pow ?_ 2
      unfold clusterGradAt
      refine continuousOn_finsetSum _ fun z hz => ?_
      by_cases h : (openGraph ω).Adj x z
      · simp only [h, if_true]
        exact ((hcu z hz).sub (hcu x hx)).abs
      · simp only [h, if_false]
        exact continuousOn_const
  have hC : (0 : ℝ) ≤ 4096 / R ^ 2 := by positivity
  rcases le_or_gt R 2 with hR2 | hR2
  · -- `B_{R/2}(y)` has at most one vertex
    have h0 : gradEnergy ω W (u t) = 0 := by
      unfold gradEnergy
      refine Finset.sum_eq_zero fun x hx => ?_
      have hxy : x = y := eq_of_latticeDist_lt_one ((mem_clusterBall.1 hx).2.trans_le
        (by linarith))
      have hempty : W.filter (fun z => (openGraph ω).Adj x z) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun z hz hadj => by
          have hzy : z = y := eq_of_latticeDist_lt_one ((mem_clusterBall.1 hz).2.trans_le
            (by linarith))
          rw [hxy, hzy] at hadj
          exact (openGraph ω).irrefl hadj
      rw [hempty]
      simp
    rw [h0]
    exact mul_nonneg hC hI0
  rcases lt_or_ge R 8 with hR8 | hR8
  · -- small radii: the indicator of `B_{R/2}(y)`
    set η : Vertex 2 → ℝ := fun x => if x ∈ W then 1 else 0 with hη
    have hη0 : ∀ x, 0 ≤ η x := fun x => by simp only [hη]; split_ifs <;> norm_num
    have hη1 : ∀ x, η x ≤ 1 := fun x => by simp only [hη]; split_ifs <;> norm_num
    have hηW : ∀ x ∈ W, η x = 1 := fun x hx => by simp only [hη, if_pos hx]
    have hηint : ∀ x, η x ≠ 0 → x ∈ V ∧ ∀ z, (openGraph ω).Adj x z → z ∈ V := by
      intro x hx
      have hxW : x ∈ W := by
        by_contra h
        exact hx (by simp only [hη, if_neg h])
      obtain ⟨hxK, hxd⟩ := mem_clusterBall.1 hxW
      refine ⟨hWV hxW, fun z hz => mem_clusterBall.2 ⟨(mem_supp_iff_of_adj hz).1 hxK, ?_⟩⟩
      have h1 := latticeDist_triangle z x y
      have h2 := latticeDist_le_one_of_adj hz
      linarith
    have hηlip : ∀ x z, (openGraph ω).Adj x z → |η x - η z| ≤ 1 := fun x z _ => by
      simp only [hη]
      split_ifs <;> norm_num
    have hmain := timeslice_of_cutoff (ω := ω) hab (by nlinarith) hu hη0 hη1 hηint hηlip htI
    have hL := gradEnergy_le_four_mul (ω := ω) hWV (u t) η hη0 hηW
    have hR2pos : 0 < R ^ 2 := by positivity
    have hconst : 4 * (1 / (-R ^ 2 / 4 - -R ^ 2) + 4 * 1 ^ 2) ≤ 4096 / R ^ 2 := by
      have e : 1 / (-R ^ 2 / 4 - -R ^ 2) = 4 / (3 * R ^ 2) := by
        rw [show -R ^ 2 / 4 - -R ^ 2 = 3 * R ^ 2 / 4 by ring, one_div_div]
      rw [e]
      have h1 : 4 / (3 * R ^ 2) ≤ 4 / R ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) hR2pos (by linarith)
      have h2 : (4 : ℝ) ≤ 256 / R ^ 2 := by
        rw [le_div_iff₀ hR2pos]
        nlinarith
      have h3 : 4 * (4 / R ^ 2 + 256 / R ^ 2) = 1040 / R ^ 2 := by ring
      have h4 : (1040 : ℝ) / R ^ 2 ≤ 4096 / R ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num) hR2pos.le
      linarith
    have hpos : 0 ≤ 1 / (-R ^ 2 / 4 - -R ^ 2) + 4 * (1 : ℝ) ^ 2 := by
      have : 0 < -R ^ 2 / 4 - -R ^ 2 := by nlinarith
      exact add_nonneg (div_nonneg zero_le_one this.le) (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hGI hpos
    have h2 := mul_le_mul_of_nonneg_right hconst hI0
    linarith
  · -- large radii: the cutoff of the Caccioppoli inequality
    set η := caccCutoff (ω := ω) K y R with hη
    have hden : 0 < R / 2 - 2 := by linarith
    have hmain := timeslice_of_cutoff (ω := ω) hab (by nlinarith) hu (caccCutoff_nonneg K y R)
      (caccCutoff_le_one K y R) (caccCutoff_interior K y hden) (caccCutoff_lip K y hden) htI
    have hL := gradEnergy_le_four_mul (ω := ω) hWV (u t) η (caccCutoff_nonneg K y R)
      (caccCutoff_eq_one K y hden)
    set ℓ : ℝ := 2 / (R / 2 - 2) with hℓ
    have hℓ2 : ℓ ^ 2 ≤ 64 / R ^ 2 := by
      have h1 : ℓ ≤ 8 / R := by
        simp only [hℓ]
        rw [div_le_div_iff₀ hden hR0]
        linarith
      have h0 : 0 ≤ ℓ := by simp only [hℓ]; positivity
      calc ℓ ^ 2 ≤ (8 / R) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = 64 / R ^ 2 := by ring
    have hR2pos : 0 < R ^ 2 := by positivity
    have hconst : 4 * (1 / (-R ^ 2 / 4 - -R ^ 2) + 4 * ℓ ^ 2) ≤ 4096 / R ^ 2 := by
      have e : 1 / (-R ^ 2 / 4 - -R ^ 2) = 4 / (3 * R ^ 2) := by
        rw [show -R ^ 2 / 4 - -R ^ 2 = 3 * R ^ 2 / 4 by ring, one_div_div]
      rw [e]
      have h1 : 4 / (3 * R ^ 2) ≤ 4 / R ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) hR2pos (by linarith)
      have h3 : 4 * (4 / R ^ 2 + 4 * (64 / R ^ 2)) = 1040 / R ^ 2 := by ring
      have h4 : (1040 : ℝ) / R ^ 2 ≤ 4096 / R ^ 2 :=
        div_le_div_of_nonneg_right (by norm_num) hR2pos.le
      linarith
    have hpos : 0 ≤ 1 / (-R ^ 2 / 4 - -R ^ 2) + 4 * ℓ ^ 2 := by
      have : 0 < -R ^ 2 / 4 - -R ^ 2 := by nlinarith
      exact add_nonneg (div_nonneg zero_le_one this.le) (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hGI hpos
    have h2 := mul_le_mul_of_nonneg_right hconst hI0
    linarith

end Rigidity.Green
