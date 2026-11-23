import Rigidity.Proofs.Green.DarioGuTail

/-!
# The minimal time of a lattice family of minimal times

`latticeSup T y ω = sup_w {T w ω : |w - y| ≤ T w ω + 1}`: for `t ≥ latticeSup T y ω` (and a
bounded family) every `w` with `|w - y| ≤ t + 1` has `T w ω ≤ t` (`le_of_latticeSup_le`). This is
the construction of `T'_NA` in (3.52) and of `T¹_par` in (4.44) of Dario–Gu. If the `T w` have a
uniform tail `C exp(-u^s/C)`, a union bound over `w`, with `Σ_w exp(-(|w - y| - 1)_+^s / (2C)) < ∞`,
gives `latticeSup T y` a tail of the same form, and the family is almost surely bounded
(`hasTail_latticeSup`).
-/

open MeasureTheory Finset LatticeProb.Percolation
open scoped ENNReal

namespace Rigidity.Green

variable {p : unitInterval}

theorem sum_natAbs_sub_le (f : ℕ → ℝ) (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f) (a : ℤ)
    (T : Finset ℤ) : ∑ n ∈ T, f (n - a).natAbs ≤ 2 * ∑' k, f k := by
  have hf1 : Summable fun n : ℕ => f (n + 1) := (summable_nat_add_iff 1).2 hf
  have hneg : (fun n : ℕ => f (-((n : ℤ) + 1)).natAbs) = fun n : ℕ => f (n + 1) := by
    funext n
    congr 1
  have hs : Summable fun n : ℤ => f n.natAbs := by
    apply Summable.of_nat_of_neg_add_one
    · simpa using hf
    · rw [hneg]; exact hf1
  have hinj : Set.InjOn (fun n : ℤ => n - a) T := fun m _ n _ h => by simpa using h
  calc ∑ n ∈ T, f (n - a).natAbs = ∑ m ∈ T.image (fun n => n - a), f m.natAbs :=
        (Finset.sum_image (f := fun m : ℤ => f m.natAbs) hinj).symm
    _ ≤ ∑' m : ℤ, f m.natAbs := hs.sum_le_tsum _ (fun _ _ => hf0 _)
    _ = (∑' n : ℕ, f n) + ∑' n : ℕ, f (n + 1) := by
        rw [tsum_of_nat_of_neg_add_one (by simpa using hf) (by rw [hneg]; exact hf1), hneg]
        rfl
    _ ≤ 2 * ∑' k, f k := by
        have : ∑' n : ℕ, f (n + 1) ≤ ∑' k, f k := by
          rw [hf.tsum_eq_zero_add]
          linarith [hf0 0]
        linarith

theorem summable_inv_add_one_sq : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  simpa using this

/-- `Σ_{w ∈ S} (1 + |w - y|)^{-4} ≤ Z`. -/
theorem sum_inv_one_add_pow_four_le (y : Vertex 2) (S : Finset (Vertex 2)) :
    ∑ w ∈ S, ((1 + latticeDist w y) ^ 4)⁻¹ ≤ (2 * ∑' k : ℕ, (((k : ℝ) + 1) ^ 2)⁻¹) ^ 2 := by
  set f := fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  have hpt : ∀ w : Vertex 2, ((1 + latticeDist w y) ^ 4)⁻¹ ≤
      f (w 0 - y 0).natAbs * f (w 1 - y 1).natAbs := by
    intro w
    have hd := latticeDist_sq w y
    have hd0 := latticeDist_nonneg w y
    have h0 : (((w 0 - y 0).natAbs : ℕ) : ℝ) = |(w 0 : ℝ) - y 0| := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    have h1 : (((w 1 - y 1).natAbs : ℕ) : ℝ) = |(w 1 : ℝ) - y 1| := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    simp only [f, h0, h1]
    have ha : |(w 0 : ℝ) - y 0| ≤ latticeDist w y := by
      rw [← Real.sqrt_sq (abs_nonneg ((w 0 : ℝ) - y 0)), ← Real.sqrt_sq hd0, sq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((w 1 : ℝ) - y 1)])
    have hb : |(w 1 : ℝ) - y 1| ≤ latticeDist w y := by
      rw [← Real.sqrt_sq (abs_nonneg ((w 1 : ℝ) - y 1)), ← Real.sqrt_sq hd0, sq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((w 0 : ℝ) - y 0)])
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    have hA : 0 ≤ |(w 0 : ℝ) - y 0| := abs_nonneg _
    have hB : 0 ≤ |(w 1 : ℝ) - y 1| := abs_nonneg _
    have h2 : (|(w 0 : ℝ) - y 0| + 1) * (|(w 1 : ℝ) - y 1| + 1) ≤ (1 + latticeDist w y) ^ 2 := by
      nlinarith
    calc (|(w 0 : ℝ) - y 0| + 1) ^ 2 * (|(w 1 : ℝ) - y 1| + 1) ^ 2
        = ((|(w 0 : ℝ) - y 0| + 1) * (|(w 1 : ℝ) - y 1| + 1)) ^ 2 := by ring
      _ ≤ ((1 + latticeDist w y) ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = (1 + latticeDist w y) ^ 4 := by ring
  calc ∑ w ∈ S, ((1 + latticeDist w y) ^ 4)⁻¹
      ≤ ∑ w ∈ S, (fun n : ℤ => f (n - y 0).natAbs) (w 0) * (fun n : ℤ => f (n - y 1).natAbs) (w 1) :=
        Finset.sum_le_sum fun w _ => hpt w
    _ ≤ (∑ m ∈ S.image (fun x => x 0), f (m - y 0).natAbs) *
          ∑ m ∈ S.image (fun x => x 1), f (m - y 1).natAbs :=
        sum_mul_coord_le (fun n : ℤ => f (n - y 0).natAbs) (fun n : ℤ => f (n - y 1).natAbs)
          (fun _ => hf0 _) (fun _ => hf0 _) S
    _ ≤ (2 * ∑' k, f k) * (2 * ∑' k, f k) := by
        have h1 := sum_natAbs_sub_le f hf0 summable_inv_add_one_sq (y 0) (S.image (fun x => x 0))
        have h2 := sum_natAbs_sub_le f hf0 summable_inv_add_one_sq (y 1) (S.image (fun x => x 1))
        exact mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => hf0 _)
          (by have h0 : 0 ≤ ∑' k, f k := tsum_nonneg hf0
              linarith)
    _ = _ := by ring

/-- `exp(-v^s / c) ≤ K (1 + v)^{-4}` for `v ≥ 0`. -/
theorem exp_neg_rpow_le_inv_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) : ∃ K : ℝ, 0 < K ∧
    ∀ v : ℝ, 0 ≤ v → Real.exp (-Real.rpow v s / c) ≤ K * ((1 + v) ^ 4)⁻¹ := by
  set m := ⌈4 / s⌉₊
  have hm : 4 ≤ s * m := by
    have := Nat.le_ceil (4 / s)
    rw [div_le_iff₀ hs] at this
    linarith
  refine ⟨16 * max 1 (m.factorial * c ^ m), by positivity, fun v hv => ?_⟩
  have hK1 : 1 ≤ max 1 ((m.factorial : ℝ) * c ^ m) := le_max_left _ _
  rcases le_or_gt v 1 with h1 | h1
  · have he : Real.exp (-Real.rpow v s / c) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      exact div_nonneg (Real.rpow_nonneg hv s) hc.le
    have hp : ((1 + v) ^ 4)⁻¹ ≥ 1 / 16 := by
      rw [ge_iff_le, one_div]
      apply inv_anti₀ (by positivity)
      have : (1 + v) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      linarith
    nlinarith
  · set x := Real.rpow v s / c
    have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg hv s) hc.le
    have hexp := Real.pow_div_factorial_le_exp x hx0 m
    have hxm : x ^ m = Real.rpow v (s * m) / c ^ m := by
      show (v ^ s / c) ^ m = v ^ (s * (m : ℝ)) / c ^ m
      rw [div_pow, Real.rpow_mul hv, Real.rpow_natCast]
    have hv4 : v ^ 4 ≤ Real.rpow v (s * m) := by
      have := Real.rpow_le_rpow_of_exponent_le h1.le hm
      rwa [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h16 : (1 + v) ^ 4 ≤ 16 * v ^ 4 := by
      have : 1 + v ≤ 2 * v := by linarith
      calc (1 + v) ^ 4 ≤ (2 * v) ^ 4 := pow_le_pow_left₀ (by linarith) this 4
        _ = 16 * v ^ 4 := by ring
    have hxpos : 0 < x ^ m := by
      rw [hxm]; exact div_pos (lt_of_lt_of_le (pow_pos (by linarith) 4) hv4) (by positivity)
    have hexp' : Real.exp (-x) ≤ m.factorial / x ^ m := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos x) (div_pos (by positivity) hxpos), inv_div]
      calc x ^ m / m.factorial ≤ Real.exp x := hexp
        _ = Real.exp x := rfl
    have hvpos : 0 < v ^ 4 := pow_pos (by linarith) 4
    calc Real.exp (-Real.rpow v s / c) = Real.exp (-x) := by rw [neg_div]
      _ ≤ m.factorial / x ^ m := hexp'
      _ = m.factorial * c ^ m / Real.rpow v (s * m) := by
          rw [hxm]; field_simp
      _ ≤ m.factorial * c ^ m / v ^ 4 := div_le_div_of_nonneg_left (by positivity) hvpos hv4
      _ ≤ 16 * (m.factorial * c ^ m) * ((1 + v) ^ 4)⁻¹ := by
          rw [div_eq_mul_inv]
          have : (v ^ 4)⁻¹ ≤ 16 * ((1 + v) ^ 4)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hvpos]
            linarith
          nlinarith [this, (by positivity : (0 : ℝ) ≤ m.factorial * c ^ m)]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [le_max_right (1 : ℝ) ((m.factorial : ℝ) * c ^ m)]

/-- The lattice minimal time. -/
noncomputable def latticeSup (T : Vertex 2 → Configuration 2 → ℝ) (y : Vertex 2)
    (ω : Configuration 2) : ℝ :=
  ⨆ w : Vertex 2, if latticeDist w y ≤ T w ω + 1 then T w ω else 0

theorem latticeSup_nonneg {T : Vertex 2 → Configuration 2 → ℝ} (hT : ∀ w ω, 0 ≤ T w ω)
    (y : Vertex 2) (ω : Configuration 2) : 0 ≤ latticeSup T y ω :=
  Real.iSup_nonneg fun w => by split_ifs <;> [exact hT w ω; exact le_rfl]

theorem measurable_latticeSup {T : Vertex 2 → Configuration 2 → ℝ} (hT : ∀ w, Measurable (T w))
    (y : Vertex 2) : Measurable (latticeSup T y) :=
  Measurable.iSup fun w => Measurable.ite (measurableSet_le measurable_const ((hT w).add_const 1))
    (hT w) measurable_const

theorem le_of_latticeSup_le {T : Vertex 2 → Configuration 2 → ℝ} {y : Vertex 2}
    {ω : Configuration 2}
    (hb : BddAbove (Set.range fun w => if latticeDist w y ≤ T w ω + 1 then T w ω else 0))
    {t : ℝ} (ht : latticeSup T y ω ≤ t) {w : Vertex 2} (hw : latticeDist w y ≤ t + 1) :
    T w ω ≤ t := by
  by_contra h
  push Not at h
  have hinc : latticeDist w y ≤ T w ω + 1 := by linarith
  have := le_ciSup hb w
  rw [if_pos hinc] at this
  exact absurd (this.trans ht) (not_le.2 h)

theorem exists_le_of_lt_latticeSup {T : Vertex 2 → Configuration 2 → ℝ} {y : Vertex 2}
    {ω : Configuration 2} {a : ℝ} (ha : 0 < a)
    (h : ¬ BddAbove (Set.range fun w => if latticeDist w y ≤ T w ω + 1 then T w ω else 0) ∨
      2 * a ≤ latticeSup T y ω) :
    ∃ w, max a (latticeDist w y - 1) ≤ T w ω := by
  have hex : ∃ w, a < (if latticeDist w y ≤ T w ω + 1 then T w ω else 0) := by
    rcases h with h | h
    · rw [not_bddAbove_iff] at h
      obtain ⟨_, ⟨w, rfl⟩, hw⟩ := h a
      exact ⟨w, hw⟩
    · exact exists_lt_of_lt_ciSup (lt_of_lt_of_le (by linarith) h)
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, ?_⟩
  split_ifs at hw with hc
  · exact max_le hw.le (by linarith)
  · exact absurd hw (not_lt.2 ha.le)

/-- **Tail of the lattice minimal time.** -/
theorem hasTail_latticeSup {T : Vertex 2 → Configuration 2 → ℝ} {C s : ℝ} (hC : 0 < C)
    (hs : 0 < s) (htail : ∀ w, HasTail p (T w) C s) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ y : Vertex 2, HasTail p (latticeSup T y) C' s ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p,
        BddAbove (Set.range fun w => if latticeDist w y ≤ T w ω + 1 then T w ω else 0) := by
  obtain ⟨K, hK, hKb⟩ := exp_neg_rpow_le_inv_pow hs (by positivity : (0 : ℝ) < 2 * C)
  set Z := (2 * ∑' k : ℕ, (((k : ℝ) + 1) ^ 2)⁻¹) ^ 2
  have hZ : 0 ≤ Z := sq_nonneg _
  set A := C * K * 16 * Z
  -- the union bound
  have hunion : ∀ y : Vertex 2, ∀ a : ℝ, 0 < a →
      latticeBondLaw 2 p {ω | ∃ w, max a (latticeDist w y - 1) ≤ T w ω} ≤
        ENNReal.ofReal (A * Real.exp (-Real.rpow a s / (2 * C))) := by
    intro y a ha
    have hset : {ω | ∃ w, max a (latticeDist w y - 1) ≤ T w ω} =
        ⋃ w, {ω | max a (latticeDist w y - 1) ≤ T w ω} := by ext ω; simp
    rw [hset]
    refine (measure_iUnion_le _).trans ?_
    have hterm : ∀ w : Vertex 2, latticeBondLaw 2 p {ω | max a (latticeDist w y - 1) ≤ T w ω} ≤
        ENNReal.ofReal (C * K * 16 * Real.exp (-Real.rpow a s / (2 * C)) *
          ((1 + latticeDist w y) ^ 4)⁻¹) := by
      intro w
      refine (htail w _ (le_max_of_le_left ha.le)).trans (ENNReal.ofReal_le_ofReal ?_)
      obtain ⟨b, hb⟩ : ∃ b, b = max (latticeDist w y - 1) 0 := ⟨_, rfl⟩
      have hb0 : 0 ≤ b := hb ▸ le_max_right _ _
      have hb1 : latticeDist w y - 1 ≤ b := hb ▸ le_max_left _ _
      have hmab : max a (latticeDist w y - 1) = max a b := by
        rw [hb, max_comm (latticeDist w y - 1) 0, ← max_assoc, max_eq_left ha.le]
      rw [hmab]
      have hM0 : 0 ≤ max a b := le_max_of_le_left ha.le
      have hpow : (Real.rpow a s + Real.rpow b s) / 2 ≤ Real.rpow (max a b) s := by
        have h1 : Real.rpow a s ≤ Real.rpow (max a b) s :=
          Real.rpow_le_rpow ha.le (le_max_left _ _) hs.le
        have h2 : Real.rpow b s ≤ Real.rpow (max a b) s :=
          Real.rpow_le_rpow hb0 (le_max_right _ _) hs.le
        linarith
      have he : Real.exp (-Real.rpow (max a b) s / C) ≤
          Real.exp (-Real.rpow a s / (2 * C)) * Real.exp (-Real.rpow b s / (2 * C)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        rw [neg_div, neg_div, neg_div, ← neg_add, neg_le_neg_iff, ← add_div,
          div_le_div_iff₀ (by positivity) hC]
        nlinarith
      have hKb' := hKb b hb0
      have h1b : ((1 + b) ^ 4)⁻¹ ≤ 16 * ((1 + latticeDist w y) ^ 4)⁻¹ := by
        have hd0 := latticeDist_nonneg w y
        have h2 : (1 + latticeDist w y) / 2 ≤ 1 + b := by linarith
        have h3 : ((1 + latticeDist w y) / 2) ^ 4 ≤ (1 + b) ^ 4 :=
          pow_le_pow_left₀ (by positivity) h2 4
        have h4 : 0 < (1 + latticeDist w y) ^ 4 := by positivity
        rw [show ((1 + latticeDist w y) / 2) ^ 4 = (1 + latticeDist w y) ^ 4 / 16 by ring] at h3
        rw [← div_eq_mul_inv, le_div_iff₀ h4, inv_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith
      calc C * Real.exp (-Real.rpow (max a b) s / C)
          ≤ C * (Real.exp (-Real.rpow a s / (2 * C)) * Real.exp (-Real.rpow b s / (2 * C))) :=
            mul_le_mul_of_nonneg_left he hC.le
        _ ≤ C * (Real.exp (-Real.rpow a s / (2 * C)) * (K * ((1 + b) ^ 4)⁻¹)) := by
            gcongr
        _ ≤ C * (Real.exp (-Real.rpow a s / (2 * C)) *
              (K * (16 * ((1 + latticeDist w y) ^ 4)⁻¹))) := by
            gcongr
        _ = _ := by ring
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    have hsum : ∀ S : Finset (Vertex 2), ∑ w ∈ S, ((1 + latticeDist w y) ^ 4)⁻¹ ≤ Z :=
      fun S => sum_inv_one_add_pow_four_le y S
    have hsumm : Summable fun w : Vertex 2 => ((1 + latticeDist w y) ^ 4)⁻¹ :=
      summable_of_sum_le (fun w => by have := latticeDist_nonneg w y; positivity) hsum
    have hc0 : 0 ≤ C * K * 16 * Real.exp (-Real.rpow a s / (2 * C)) := by positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg hc0
      (by have := latticeDist_nonneg w y; positivity)) (hsumm.mul_left _)]
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_mul_left]
    have := hsumm.tsum_le_of_sum_le hsum
    calc C * K * 16 * Real.exp (-Real.rpow a s / (2 * C)) *
          ∑' w, ((1 + latticeDist w y) ^ 4)⁻¹
        ≤ C * K * 16 * Real.exp (-Real.rpow a s / (2 * C)) * Z :=
          mul_le_mul_of_nonneg_left this hc0
      _ = A * Real.exp (-Real.rpow a s / (2 * C)) := by ring
  set C' := max (max A 1) (2 ^ s * (2 * C))
  have hC'1 : 1 ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C', by linarith, fun y => ⟨?_, ?_⟩⟩
  · intro u hu
    rcases eq_or_lt_of_le hu with hu0 | hu0
    · subst hu0
      calc latticeBondLaw 2 p {ω | 0 ≤ latticeSup T y ω} ≤ 1 := prob_le_one
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            simp only [Real.rpow_eq_pow, Real.zero_rpow hs.ne', neg_zero, zero_div, Real.exp_zero,
              mul_one]
            exact hC'1
    · have hsub : {ω | u ≤ latticeSup T y ω} ⊆
          {ω | ∃ w, max (u / 2) (latticeDist w y - 1) ≤ T w ω} := by
        intro ω hω
        exact exists_le_of_lt_latticeSup (by linarith) (Or.inr (by simp only [Set.mem_setOf_eq] at hω; linarith))
      refine (measure_mono hsub).trans ((hunion y _ (by linarith)).trans
        (ENNReal.ofReal_le_ofReal ?_))
      have hu2 : Real.rpow (u / 2) s = Real.rpow u s / 2 ^ s := Real.div_rpow hu (by norm_num) s
      rw [hu2]
      have hw : 0 ≤ Real.rpow u s := Real.rpow_nonneg hu s
      have h2s : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      apply mul_le_mul ((le_max_left _ _).trans (le_max_left _ _)) _ (Real.exp_pos _).le
        (by linarith)
      apply Real.exp_le_exp.2
      rw [neg_div, neg_div, neg_le_neg_iff, div_div]
      exact div_le_div_of_nonneg_left hw (by positivity) (le_max_right _ _)
  · -- almost surely bounded
    have hnull : latticeBondLaw 2 p {ω | ¬ BddAbove (Set.range fun w =>
        if latticeDist w y ≤ T w ω + 1 then T w ω else 0)} = 0 := by
      have hbound : ∀ n : ℕ, latticeBondLaw 2 p {ω | ¬ BddAbove (Set.range fun w =>
          if latticeDist w y ≤ T w ω + 1 then T w ω else 0)} ≤
            ENNReal.ofReal (A * Real.exp (-Real.rpow ((n : ℝ) + 1) s / (2 * C))) := by
        intro n
        refine (measure_mono fun ω hω => ?_).trans (hunion y ((n : ℝ) + 1) (by positivity))
        exact exists_le_of_lt_latticeSup (by positivity) (Or.inl hω)
      have htend : Filter.Tendsto (fun n : ℕ =>
          ENNReal.ofReal (A * Real.exp (-Real.rpow ((n : ℝ) + 1) s / (2 * C))))
          Filter.atTop (nhds (ENNReal.ofReal (A * 0))) := by
        apply ENNReal.tendsto_ofReal
        apply Filter.Tendsto.const_mul
        have h1 : Filter.Tendsto (fun n : ℕ => Real.rpow ((n : ℝ) + 1) s / (2 * C))
            Filter.atTop Filter.atTop := by
          apply Filter.Tendsto.atTop_div_const (by positivity)
          exact (tendsto_rpow_atTop hs).comp
            (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
        refine this.congr fun n => ?_
        simp [neg_div]
      rw [mul_zero, ENNReal.ofReal_zero] at htend
      exact le_antisymm (ge_of_tendsto' htend hbound) (by simp)
    rw [ae_iff]
    simpa using hnull

end Rigidity.Green
