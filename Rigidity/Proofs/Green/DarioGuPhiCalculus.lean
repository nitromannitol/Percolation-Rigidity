import Rigidity.Proofs.Green.DarioGuHeatKernelInputs

/-!
# The function `Φ_C` of Dario–Gu in dimension two

`Φ_C(t, x) = C t^{-1} exp(-g(t, |x|) / C)` with the shape `g(t, r) = r²/t` for `r ≤ t` and
`g(t, r) = r (1 + ln(r/t))` for `r > t` (`dgShape`). The shape is nonnegative, nondecreasing in
`r`, homogeneous (`g(λt, λr) = λ g(t, r)`), and `min(r²/t, r) ≤ g(t, r) ≤ r²/t`. Hence
`g(s, a) + g(s, b) ≥ g(2s, r)/2` whenever `r ≤ a + b` (`dgShape_add_ge`), which is the form of
the semigroup property (3.2) of `Φ_C` used in the proof of Theorem 1 (§4.3).

The lattice sums `Σ_x exp(-g(t, |x - z|)/c) ≤ L t` (`sum_exp_neg_dgShape_le`, `t ≥ 1`) give the
weighted `L²` norms of functions bounded by `Φ_C` (`weightedL2Le_of_abs_le`) and the bound of the
second factor of the term (4.48)-a1 (`sum_sq_dgPhi_mul_exp_le`).
-/

open Finset LatticeProb.Percolation

namespace Rigidity.Green

/-- The shape of the exponent of `Φ_C`. -/
noncomputable def dgShape (t r : ℝ) : ℝ :=
  if r ≤ t then r ^ 2 / t else r * (1 + Real.log (r / t))

theorem dgExponent_eq (C t r : ℝ) : dgExponent C t r = dgShape t r / C := by
  unfold dgExponent dgShape
  split_ifs <;> ring

theorem dgPhi_eq (C t r : ℝ) : dgPhi C t r = C * t⁻¹ * Real.exp (-(dgShape t r / C)) := by
  rw [dgPhi, dgExponent_eq]

theorem dgShape_of_le {t r : ℝ} (ht : 0 < t) (h : t ≤ r) :
    dgShape t r = r * (1 + Real.log (r / t)) := by
  unfold dgShape
  split_ifs with h'
  · have hr : r = t := le_antisymm h' h
    subst hr
    rw [div_self ht.ne', Real.log_one]
    field_simp
    ring
  · rfl

theorem dgShape_nonneg {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) : 0 ≤ dgShape t r := by
  unfold dgShape
  split_ifs with h
  · positivity
  · push Not at h
    have : 0 ≤ Real.log (r / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    exact mul_nonneg hr (by linarith)

theorem dgShape_le_sq {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) : dgShape t r ≤ r ^ 2 / t := by
  unfold dgShape
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have hrt : 0 < r / t := div_pos (by linarith) ht
    have hl := Real.log_le_sub_one_of_pos hrt
    calc r * (1 + Real.log (r / t)) ≤ r * (r / t) :=
          mul_le_mul_of_nonneg_left (by linarith) hr
      _ = r ^ 2 / t := by ring

theorem min_le_dgShape {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) : min (r ^ 2 / t) r ≤ dgShape t r := by
  unfold dgShape
  split_ifs with h
  · exact min_le_left _ _
  · push Not at h
    have : 0 ≤ Real.log (r / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    calc min (r ^ 2 / t) r ≤ r := min_le_right _ _
      _ ≤ r * (1 + Real.log (r / t)) := le_mul_of_one_le_right hr (by linarith)

theorem dgShape_mono {t a b : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hab : a ≤ b) :
    dgShape t a ≤ dgShape t b := by
  unfold dgShape
  split_ifs with h1 h2 h2
  · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab 2) ht.le
  · push Not at h2
    have hb : 0 ≤ Real.log (b / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    have h3 : a ^ 2 / t ≤ t := by
      rw [div_le_iff₀ ht]
      nlinarith
    nlinarith
  · exact absurd (hab.trans h2) h1
  · push Not at h1 h2
    have hla : Real.log (a / t) ≤ Real.log (b / t) :=
      Real.log_le_log (div_pos (by linarith) ht) (div_le_div_of_nonneg_right hab ht.le)
    have ha' : 0 ≤ Real.log (a / t) := Real.log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    exact mul_le_mul hab (by linarith) (by linarith) (by linarith)

theorem dgShape_homog {l t r : ℝ} (hl : 0 < l) (ht : 0 < t) :
    dgShape (l * t) (l * r) = l * dgShape t r := by
  unfold dgShape
  by_cases h : r ≤ t
  · have h' : l * r ≤ l * t := mul_le_mul_of_nonneg_left h hl.le
    rw [if_pos h', if_pos h]
    field_simp
  · have h' : ¬ l * r ≤ l * t := fun h' => h (le_of_mul_le_mul_left h' hl)
    rw [if_neg h', if_neg h, mul_div_mul_left r t hl.ne']
    ring

/-- `g(s, a) + g(s, b) ≥ g(2s, r)/2` for `r ≤ a + b`. -/
theorem dgShape_add_ge {s a b r : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hrab : r ≤ a + b) : dgShape (2 * s) r / 2 ≤ dgShape s a + dgShape s b := by
  have h1 : dgShape (2 * s) r / 2 = dgShape s (r / 2) := by
    have := dgShape_homog (l := 1 / 2) (t := 2 * s) (r := r) (by norm_num) (by positivity)
    rw [show 1 / 2 * (2 * s) = s by ring, show 1 / 2 * r = r / 2 by ring] at this
    rw [this]
    ring
  rw [h1]
  rcases le_total b a with hba | hab
  · have : dgShape s (r / 2) ≤ dgShape s a := dgShape_mono hs (by linarith) (by linarith)
    linarith [dgShape_nonneg hs hb]
  · have : dgShape s (r / 2) ≤ dgShape s b := dgShape_mono hs (by linarith) (by linarith)
    linarith [dgShape_nonneg hs ha]

theorem dgPhi_nonneg {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t) (r : ℝ) : 0 ≤ dgPhi C t r := by
  unfold dgPhi
  positivity

theorem dgPhi_mono {C C' t r : ℝ} (hC : 0 < C) (hCC : C ≤ C') (ht : 0 < t) (hr : 0 ≤ r) :
    dgPhi C t r ≤ dgPhi C' t r := by
  rw [dgPhi_eq, dgPhi_eq]
  have hg := dgShape_nonneg ht hr
  have he : Real.exp (-(dgShape t r / C)) ≤ Real.exp (-(dgShape t r / C')) :=
    Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_left hg hC hCC))
  have : C * t⁻¹ ≤ C' * t⁻¹ := mul_le_mul_of_nonneg_right hCC (by positivity)
  have hC' : 0 < C' := lt_of_lt_of_le hC hCC
  exact mul_le_mul this he (by positivity) (by positivity)

/-! ### Lattice sums -/

theorem latticeDist_nonneg (x z : Vertex 2) : 0 ≤ latticeDist x z := norm_nonneg _

theorem latticeDist_comm (x z : Vertex 2) : latticeDist x z = latticeDist z x := by
  unfold latticeDist
  rw [norm_sub_rev]

theorem latticeDist_triangle (x y z : Vertex 2) :
    latticeDist x z ≤ latticeDist y z + latticeDist y x := by
  unfold latticeDist
  calc ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding z‖
      = ‖(latticeEuclideanEmbedding y - latticeEuclideanEmbedding z) -
          (latticeEuclideanEmbedding y - latticeEuclideanEmbedding x)‖ := by
        congr 1
        abel
    _ ≤ _ := norm_sub_le _ _

theorem latticeDist_sq (x z : Vertex 2) :
    latticeDist x z ^ 2 = ((x 0 : ℝ) - z 0) ^ 2 + ((x 1 : ℝ) - z 1) ^ 2 := by
  rw [latticeDist, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_two]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  rfl

theorem abs_add_abs_le_latticeDist (x z : Vertex 2) :
    (|(x 0 : ℝ) - z 0| + |(x 1 : ℝ) - z 1|) / 2 ≤ latticeDist x z := by
  have h := latticeDist_sq x z
  have h0 := latticeDist_nonneg x z
  have ha := sq_abs ((x 0 : ℝ) - z 0)
  have hb := sq_abs ((x 1 : ℝ) - z 1)
  nlinarith [abs_nonneg ((x 0 : ℝ) - z 0), abs_nonneg ((x 1 : ℝ) - z 1),
    sq_nonneg (|(x 0 : ℝ) - z 0| - |(x 1 : ℝ) - z 1|),
    sq_nonneg (latticeDist x z - (|(x 0 : ℝ) - z 0| + |(x 1 : ℝ) - z 1|) / 2)]

/-- `Σ_{n ∈ T} q^{|n - a|} ≤ 2/(1 - q)`. -/
theorem sum_pow_natAbs_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℤ) (T : Finset ℤ) :
    ∑ n ∈ T, q ^ (n - a).natAbs ≤ 2 / (1 - q) := by
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hg1 : Summable fun n : ℕ => q ^ (n + 1) := (summable_nat_add_iff 1).2 hg
  have hs : Summable fun n : ℤ => q ^ n.natAbs := by
    apply Summable.of_nat_of_neg_add_one
    · simpa using hg
    · have : (fun n : ℕ => q ^ (-((n : ℤ) + 1)).natAbs) = fun n : ℕ => q ^ (n + 1) := by
        funext n
        congr 1
      rw [this]
      exact hg1
  have hinj : Set.InjOn (fun n : ℤ => n - a) T := fun m _ n _ h => by simpa using h
  calc ∑ n ∈ T, q ^ (n - a).natAbs = ∑ m ∈ T.image (fun n => n - a), q ^ m.natAbs :=
        (Finset.sum_image (f := fun m : ℤ => q ^ m.natAbs) hinj).symm
    _ ≤ ∑' m : ℤ, q ^ m.natAbs :=
        hs.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
    _ = (∑' n : ℕ, q ^ n) + ∑' n : ℕ, q ^ (n + 1) := by
        rw [tsum_of_nat_of_neg_add_one (by simpa using hg)]
        · congr 1
        · have : (fun n : ℕ => q ^ (-((n : ℤ) + 1)).natAbs) = fun n : ℕ => q ^ (n + 1) := by
            funext n
            congr 1
          rw [this]
          exact hg1
    _ ≤ 2 / (1 - q) := by
        rw [tsum_geometric_of_lt_one hq0 hq1]
        have h2 : ∑' n : ℕ, q ^ (n + 1) = q * (1 - q)⁻¹ := by
          simp_rw [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
          ring
        rw [h2]
        have h1q : 0 < 1 - q := by linarith
        rw [div_eq_mul_inv]
        nlinarith [inv_pos.2 h1q]

theorem one_div_one_sub_exp_neg_le {u : ℝ} (hu : 0 < u) : 1 / (1 - Real.exp (-u)) ≤ 1 + 1 / u := by
  have he : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp u])
  have h1 : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    have : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp; ring
    linarith
  calc 1 / (1 - Real.exp (-u)) ≤ 1 / (u / (1 + u)) :=
        one_div_le_one_div_of_le (by positivity) h1
    _ = 1 + 1 / u := by field_simp; ring

/-- `Σ_{x ∈ S} F(x₀) G(x₁) ≤ (Σ F)(Σ G)` over the coordinate projections. -/
theorem sum_mul_coord_le (F G : ℤ → ℝ) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n)
    (S : Finset (Vertex 2)) :
    ∑ x ∈ S, F (x 0) * G (x 1) ≤
      (∑ m ∈ S.image (fun x => x 0), F m) * ∑ m ∈ S.image (fun x => x 1), G m := by
  have hinj : Set.InjOn (fun x : Vertex 2 => (x 0, x 1)) S := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  calc ∑ x ∈ S, F (x 0) * G (x 1)
      = ∑ p ∈ S.image (fun x : Vertex 2 => (x 0, x 1)), F p.1 * G p.2 :=
        (Finset.sum_image (f := fun p : ℤ × ℤ => F p.1 * G p.2) hinj).symm
    _ ≤ ∑ p ∈ S.image (fun x => x 0) ×ˢ S.image (fun x => x 1), F p.1 * G p.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => mul_nonneg (hF _) (hG _))
        intro p hp
        simp only [Finset.mem_image] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
    _ = _ := rfl

theorem sum_exp_neg_sq_div_le {c t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) (z : Vertex 2)
    (S : Finset (Vertex 2)) :
    ∑ x ∈ S, Real.exp (-(c * latticeDist x z ^ 2 / t)) ≤
      4 * Real.exp (c / 2) * (1 + 1 / c) ^ 2 * t := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  set q := Real.exp (-(c / Real.sqrt t)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by have := div_pos hc hst; linarith)
  -- `exp(-c n²/t) ≤ e^{c/4} q^{|n|}`
  have h1d : ∀ m : ℤ, Real.exp (-(c * (m : ℝ) ^ 2 / t)) ≤
      Real.exp (c / 4) * q ^ m.natAbs := by
    intro m
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hm : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hm]
    have hsq : (m : ℝ) ^ 2 = |(m : ℝ)| ^ 2 := (sq_abs _).symm
    rw [hsq]
    set u := |(m : ℝ)| / Real.sqrt t with hu
    have hut : |(m : ℝ)| ^ 2 / t = u ^ 2 := by
      rw [hu, div_pow, Real.sq_sqrt ht0.le]
    have : c * |(m : ℝ)| ^ 2 / t = c * u ^ 2 := by rw [mul_div_assoc, hut]
    rw [this]
    have : |(m : ℝ)| * -(c / Real.sqrt t) = -(c * u) := by rw [hu]; ring
    rw [this]
    nlinarith [sq_nonneg (u - 1 / 2)]
  have hsum : ∀ (a : ℤ) (T : Finset ℤ),
      ∑ n ∈ T, Real.exp (-(c * ((n : ℝ) - a) ^ 2 / t)) ≤ Real.exp (c / 4) * (2 / (1 - q)) := by
    intro a T
    calc ∑ n ∈ T, Real.exp (-(c * ((n : ℝ) - a) ^ 2 / t))
        ≤ ∑ n ∈ T, Real.exp (c / 4) * q ^ (n - a).natAbs := by
          refine Finset.sum_le_sum fun n _ => ?_
          have := h1d (n - a)
          push_cast at this
          exact this
      _ = Real.exp (c / 4) * ∑ n ∈ T, q ^ (n - a).natAbs := by rw [Finset.mul_sum]
      _ ≤ Real.exp (c / 4) * (2 / (1 - q)) :=
          mul_le_mul_of_nonneg_left (sum_pow_natAbs_sub_le hq0 hq1 a T) (Real.exp_pos _).le
  have hfac : ∀ x : Vertex 2, Real.exp (-(c * latticeDist x z ^ 2 / t)) =
      Real.exp (-(c * ((x 0 : ℝ) - z 0) ^ 2 / t)) * Real.exp (-(c * ((x 1 : ℝ) - z 1) ^ 2 / t)) := by
    intro x
    rw [← Real.exp_add, latticeDist_sq]
    congr 1
    ring
  have hgeo : 2 / (1 - q) ≤ 2 * ((1 + 1 / c) * Real.sqrt t) := by
    have := one_div_one_sub_exp_neg_le (div_pos hc hst)
    rw [← hq] at this
    have h1 : 1 + 1 / (c / Real.sqrt t) ≤ (1 + 1 / c) * Real.sqrt t := by
      have hs1 : 1 ≤ Real.sqrt t := by rw [Real.one_le_sqrt]; exact ht
      rw [one_div_div]
      have : Real.sqrt t / c = 1 / c * Real.sqrt t := by ring
      rw [this]
      nlinarith [one_div_pos.2 hc]
    calc 2 / (1 - q) = 2 * (1 / (1 - q)) := by ring
      _ ≤ 2 * ((1 + 1 / c) * Real.sqrt t) := by linarith
  calc ∑ x ∈ S, Real.exp (-(c * latticeDist x z ^ 2 / t))
      = ∑ x ∈ S, (fun n : ℤ => Real.exp (-(c * ((n : ℝ) - z 0) ^ 2 / t))) (x 0) *
          (fun n : ℤ => Real.exp (-(c * ((n : ℝ) - z 1) ^ 2 / t))) (x 1) :=
        Finset.sum_congr rfl fun x _ => hfac x
    _ ≤ (∑ m ∈ S.image (fun x => x 0), Real.exp (-(c * (((m : ℤ) : ℝ) - z 0) ^ 2 / t))) *
          ∑ m ∈ S.image (fun x => x 1), Real.exp (-(c * (((m : ℤ) : ℝ) - z 1) ^ 2 / t)) :=
        sum_mul_coord_le (fun n : ℤ => Real.exp (-(c * ((n : ℝ) - z 0) ^ 2 / t)))
          (fun n : ℤ => Real.exp (-(c * ((n : ℝ) - z 1) ^ 2 / t)))
          (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) S
    _ ≤ (Real.exp (c / 4) * (2 / (1 - q))) * (Real.exp (c / 4) * (2 / (1 - q))) :=
        mul_le_mul (hsum _ _) (hsum _ _) (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
          (by have : 0 < 1 - q := by linarith
              positivity)
    _ ≤ (Real.exp (c / 4) * (2 * ((1 + 1 / c) * Real.sqrt t))) *
          (Real.exp (c / 4) * (2 * ((1 + 1 / c) * Real.sqrt t))) := by
        have h0 : 0 ≤ Real.exp (c / 4) * (2 / (1 - q)) := by
          have : 0 < 1 - q := by linarith
          positivity
        have h2 := mul_le_mul_of_nonneg_left hgeo (Real.exp_pos (c / 4)).le
        exact mul_le_mul h2 h2 h0 (h0.trans h2)
    _ = 4 * Real.exp (c / 2) * (1 + 1 / c) ^ 2 * t := by
        have : Real.exp (c / 4) * Real.exp (c / 4) = Real.exp (c / 2) := by
          rw [← Real.exp_add]; ring_nf
        have hs := Real.mul_self_sqrt ht0.le
        calc Real.exp (c / 4) * (2 * ((1 + 1 / c) * Real.sqrt t)) *
              (Real.exp (c / 4) * (2 * ((1 + 1 / c) * Real.sqrt t)))
            = 4 * (Real.exp (c / 4) * Real.exp (c / 4)) * (1 + 1 / c) ^ 2 *
                (Real.sqrt t * Real.sqrt t) := by ring
          _ = _ := by rw [this, hs]

theorem sum_exp_neg_mul_le {c : ℝ} (hc : 0 < c) (z : Vertex 2) (S : Finset (Vertex 2)) :
    ∑ x ∈ S, Real.exp (-(c * latticeDist x z)) ≤ 4 * (1 + 2 / c) ^ 2 := by
  set q := Real.exp (-(c / 2)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have h1d : ∀ m : ℤ, Real.exp (-(c / 2 * |(m : ℝ)|)) = q ^ m.natAbs := by
    intro m
    rw [hq, ← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
    ring_nf
  have hle : ∀ x : Vertex 2, Real.exp (-(c * latticeDist x z)) ≤
      q ^ (x 0 - z 0).natAbs * q ^ (x 1 - z 1).natAbs := by
    intro x
    rw [← h1d, ← h1d, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have := abs_add_abs_le_latticeDist x z
    push_cast
    nlinarith
  have hgeo : 2 / (1 - q) ≤ 2 * (1 + 2 / c) := by
    have := one_div_one_sub_exp_neg_le (u := c / 2) (by positivity)
    rw [← hq, one_div_div] at this
    calc 2 / (1 - q) = 2 * (1 / (1 - q)) := by ring
      _ ≤ 2 * (1 + 2 / c) := by linarith
  have h0 : 0 ≤ 2 / (1 - q) := by have : 0 < 1 - q := by linarith
                                  positivity
  calc ∑ x ∈ S, Real.exp (-(c * latticeDist x z))
      ≤ ∑ x ∈ S, (fun n : ℤ => q ^ (n - z 0).natAbs) (x 0) *
          (fun n : ℤ => q ^ (n - z 1).natAbs) (x 1) := Finset.sum_le_sum fun x _ => hle x
    _ ≤ (∑ m ∈ S.image (fun x => x 0), q ^ (m - z 0).natAbs) *
          ∑ m ∈ S.image (fun x => x 1), q ^ (m - z 1).natAbs :=
        sum_mul_coord_le (fun n : ℤ => q ^ (n - z 0).natAbs) (fun n : ℤ => q ^ (n - z 1).natAbs)
          (fun _ => pow_nonneg hq0 _) (fun _ => pow_nonneg hq0 _) S
    _ ≤ (2 / (1 - q)) * (2 / (1 - q)) :=
        mul_le_mul (sum_pow_natAbs_sub_le hq0 hq1 _ _) (sum_pow_natAbs_sub_le hq0 hq1 _ _)
          (Finset.sum_nonneg fun _ _ => pow_nonneg hq0 _) h0
    _ ≤ (2 * (1 + 2 / c)) * (2 * (1 + 2 / c)) := mul_le_mul hgeo hgeo h0 (h0.trans hgeo)
    _ = 4 * (1 + 2 / c) ^ 2 := by ring

/-- `Σ_{x ∈ S} exp(-g(t, |x - z|)/c) ≤ L t` for `t ≥ 1`. -/
theorem sum_exp_neg_dgShape_le {c : ℝ} (hc : 0 < c) : ∃ L : ℝ, 0 < L ∧ ∀ t : ℝ, 1 ≤ t →
    ∀ (z : Vertex 2) (S : Finset (Vertex 2)),
      ∑ x ∈ S, Real.exp (-(dgShape t (latticeDist x z) / c)) ≤ L * t := by
  refine ⟨4 * Real.exp (1 / c / 2) * (1 + 1 / (1 / c)) ^ 2 + 4 * (1 + 2 / (1 / c)) ^ 2,
    by positivity, fun t ht z S => ?_⟩
  have ht0 : 0 < t := by linarith
  have hc' : 0 < 1 / c := one_div_pos.2 hc
  have hpt : ∀ x : Vertex 2, Real.exp (-(dgShape t (latticeDist x z) / c)) ≤
      Real.exp (-(1 / c * latticeDist x z ^ 2 / t)) + Real.exp (-(1 / c * latticeDist x z)) := by
    intro x
    have hm := min_le_dgShape ht0 (latticeDist_nonneg x z)
    rcases min_choice (latticeDist x z ^ 2 / t) (latticeDist x z) with h | h
    · rw [h] at hm
      have : Real.exp (-(dgShape t (latticeDist x z) / c)) ≤
          Real.exp (-(1 / c * latticeDist x z ^ 2 / t)) := by
        apply Real.exp_le_exp.2
        rw [neg_le_neg_iff, mul_div_assoc, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right hm hc.le
      linarith [Real.exp_pos (-(1 / c * latticeDist x z))]
    · rw [h] at hm
      have : Real.exp (-(dgShape t (latticeDist x z) / c)) ≤
          Real.exp (-(1 / c * latticeDist x z)) := by
        apply Real.exp_le_exp.2
        rw [neg_le_neg_iff, one_div_mul_eq_div]
        exact div_le_div_of_nonneg_right hm hc.le
      linarith [Real.exp_pos (-(1 / c * latticeDist x z ^ 2 / t))]
  calc ∑ x ∈ S, Real.exp (-(dgShape t (latticeDist x z) / c))
      ≤ ∑ x ∈ S, (Real.exp (-(1 / c * latticeDist x z ^ 2 / t)) +
          Real.exp (-(1 / c * latticeDist x z))) := Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x ∈ S, Real.exp (-(1 / c * latticeDist x z ^ 2 / t)) +
          ∑ x ∈ S, Real.exp (-(1 / c * latticeDist x z)) := Finset.sum_add_distrib
    _ ≤ 4 * Real.exp (1 / c / 2) * (1 + 1 / (1 / c)) ^ 2 * t + 4 * (1 + 2 / (1 / c)) ^ 2 * t := by
        have h1 := sum_exp_neg_sq_div_le hc' ht z S
        have h2 := sum_exp_neg_mul_le hc' z S
        have h3 : 4 * (1 + 2 / (1 / c)) ^ 2 ≤ 4 * (1 + 2 / (1 / c)) ^ 2 * t :=
          le_mul_of_one_le_right (by positivity) ht
        linarith
    _ = _ := by ring

end Rigidity.Green
