import Rigidity.Proofs.Green.DisplacementTailD
import Rigidity.Proofs.Green.TailD

/-!
# The minimal time of a lattice family of minimal times on `ℤ^d`

The `d`-dimensional form of `DarioGuLatticeSup.lean`, with the tails `HasTailD` of `TailD.lean`:

  `latticeSupD T y ω = sup_w {T w ω : |w - y| ≤ T w ω + 1}`:

for `t ≥ latticeSupD T y ω` (and a bounded family) every `w` with `|w - y| ≤ t + 1` has
`T w ω ≤ t` (`le_of_latticeSupD_le`). If the `T w` have a uniform tail `C exp(-u^s/C)`, a union
bound over `w`, with `Σ_w (1 + |w - y|)^{-2d} < ∞` (`summable_inv_one_add_pow`), gives
`latticeSupD T y` a tail of the same form, and the family is almost surely bounded
(`hasTail_latticeSupD`). This is the enlargement of the minimal times over the centres within
distance `t` used in the assembly of Theorem 1 of Dario–Gu on `ℤ^d`.
-/

open MeasureTheory Finset LatticeProb.Percolation
open scoped ENNReal

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

variable {d : ℕ} {p : unitInterval}

/-- `exp(-v^s / c) ≤ K (1 + v)^{-k}` for `v ≥ 0`. -/
theorem exp_neg_rpow_le_inv_pow_nat {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ v : ℝ, 0 ≤ v →
      Real.exp (-Real.rpow v s / c) ≤ K * ((1 + v) ^ k)⁻¹ := by
  set m := ⌈(k : ℝ) / s⌉₊
  have hm : (k : ℝ) ≤ s * m := by
    have := Nat.le_ceil ((k : ℝ) / s)
    rw [div_le_iff₀ hs] at this
    linarith
  refine ⟨2 ^ k * max 1 (m.factorial * c ^ m), by positivity, fun v hv => ?_⟩
  rcases le_or_gt v 1 with h1 | h1
  · have he : Real.exp (-Real.rpow v s / c) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div, neg_nonpos]
      exact div_nonneg (Real.rpow_nonneg hv s) hc.le
    have hp : 1 ≤ 2 ^ k * ((1 + v) ^ k)⁻¹ := by
      have h2 : (1 + v) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      linarith
    have hK1 : 1 ≤ max 1 ((m.factorial : ℝ) * c ^ m) := le_max_left _ _
    calc Real.exp (-Real.rpow v s / c) ≤ 1 := he
      _ ≤ 2 ^ k * ((1 + v) ^ k)⁻¹ := hp
      _ ≤ 2 ^ k * max 1 ((m.factorial : ℝ) * c ^ m) * ((1 + v) ^ k)⁻¹ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hK1)
            (by positivity)
  · set x := Real.rpow v s / c
    have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg hv s) hc.le
    have hexp := Real.pow_div_factorial_le_exp x hx0 m
    have hxm : x ^ m = Real.rpow v (s * m) / c ^ m := by
      show (v ^ s / c) ^ m = v ^ (s * (m : ℝ)) / c ^ m
      rw [div_pow, Real.rpow_mul hv, Real.rpow_natCast]
    have hvk : v ^ k ≤ Real.rpow v (s * m) := by
      have := Real.rpow_le_rpow_of_exponent_le h1.le hm
      rwa [Real.rpow_natCast] at this
    have h2k : (1 + v) ^ k ≤ 2 ^ k * v ^ k := by
      have : 1 + v ≤ 2 * v := by linarith
      calc (1 + v) ^ k ≤ (2 * v) ^ k := pow_le_pow_left₀ (by linarith) this k
        _ = 2 ^ k * v ^ k := by ring
    have hvpos : 0 < v ^ k := pow_pos (by linarith) k
    have hxpos : 0 < x ^ m := by
      rw [hxm]; exact div_pos (lt_of_lt_of_le hvpos hvk) (by positivity)
    have hexp' : Real.exp (-x) ≤ m.factorial / x ^ m := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos x) (div_pos (by positivity) hxpos), inv_div]
      exact hexp
    calc Real.exp (-Real.rpow v s / c) = Real.exp (-x) := by rw [neg_div]
      _ ≤ m.factorial / x ^ m := hexp'
      _ = m.factorial * c ^ m / Real.rpow v (s * m) := by rw [hxm]; field_simp
      _ ≤ m.factorial * c ^ m / v ^ k := div_le_div_of_nonneg_left (by positivity) hvpos hvk
      _ ≤ 2 ^ k * (m.factorial * c ^ m) * ((1 + v) ^ k)⁻¹ := by
          rw [div_eq_mul_inv]
          have : (v ^ k)⁻¹ ≤ 2 ^ k * ((1 + v) ^ k)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ hvpos]
            linarith
          calc (m.factorial : ℝ) * c ^ m * (v ^ k)⁻¹ ≤
              m.factorial * c ^ m * (2 ^ k * ((1 + v) ^ k)⁻¹) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)

/-- `Σ_{w ∈ ℤ^d} (1 + |w - y|)^{-2d} ≤ (Σ_n (1 + |n|)^{-2})^d`. -/
theorem summable_inv_one_add_pow (y : Vertex d) :
    Summable (fun w : Vertex d => ((1 + ldist w y) ^ (2 * d))⁻¹) ∧
      ∑' w : Vertex d, ((1 + ldist w y) ^ (2 * d))⁻¹ ≤
        (∑' n : ℤ, ((1 + |(n : ℝ)|) ^ 2)⁻¹) ^ d := by
  set f : ℤ → ℝ := fun n => ((1 + |(n : ℝ)|) ^ 2)⁻¹ with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hfs : Summable f := by
    have hb : Summable fun n : ℤ => (|(n : ℝ)| ^ 2)⁻¹ := by
      have := Real.summable_abs_int_rpow (b := 2) (by norm_num)
      refine this.congr fun n => ?_
      rw [← Real.rpow_natCast, Real.rpow_neg (abs_nonneg _)]; norm_num
    refine (hb.add (summable_of_ne_finset_zero (s := {0}) (f := fun n : ℤ => if n = 0 then (1 : ℝ)
      else 0) fun n hn => by simp at hn; simp [hn])).of_nonneg_of_le hf0 (fun n => ?_)
    by_cases hn : n = 0
    · subst hn; simp [hf]
    · simp only [hf, hn, if_false, add_zero]
      apply inv_anti₀ (by have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
                          positivity)
      have := abs_nonneg (n : ℝ)
      nlinarith
  have hprod := hasSum_prod_pi (g := f) hf0 hfs d
  have hpt : ∀ z : Vertex d, ((1 + ldist (z + y) y) ^ (2 * d))⁻¹ ≤ ∏ i, f (z i) := by
    intro z
    have hcoord : ∀ i, 1 + |((z i : ℤ) : ℝ)| ≤ 1 + ldist (z + y) y := fun i => by
      have := abs_coord_le_norm_edzD z y i
      rw [latticeDist_eq_norm_edzD]
      linarith
    simp only [hf]
    rw [Finset.prod_inv_distrib]
    have hp : ∏ i : Fin d, (1 + |((z i : ℤ) : ℝ)|) ^ 2 ≤ (1 + ldist (z + y) y) ^ (2 * d) := by
      calc ∏ i : Fin d, (1 + |((z i : ℤ) : ℝ)|) ^ 2 ≤ ∏ _i : Fin d, (1 + ldist (z + y) y) ^ 2 :=
            Finset.prod_le_prod (fun i _ => by positivity)
              (fun i _ => pow_le_pow_left₀ (by positivity) (hcoord i) 2)
        _ = (1 + ldist (z + y) y) ^ (2 * d) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    exact inv_anti₀ (Finset.prod_pos fun i _ => by positivity) hp
  have hs : Summable fun z : Vertex d => ((1 + ldist (z + y) y) ^ (2 * d))⁻¹ :=
    hprod.summable.of_nonneg_of_le (fun z => by
      have := Rigidity.WeakPoincare.latticeDist_nonneg (z + y) y; positivity) hpt
  have hs' : Summable fun w : Vertex d => ((1 + ldist w y) ^ (2 * d))⁻¹ :=
    (Equiv.addRight y).summable_iff.1 hs
  refine ⟨hs', ?_⟩
  calc ∑' w : Vertex d, ((1 + ldist w y) ^ (2 * d))⁻¹ =
      ∑' z : Vertex d, ((1 + ldist (z + y) y) ^ (2 * d))⁻¹ :=
        ((Equiv.addRight y).tsum_eq (fun w => ((1 + ldist w y) ^ (2 * d))⁻¹)).symm
    _ ≤ ∑' z : Vertex d, ∏ i, f (z i) := hs.tsum_le_tsum hpt hprod.summable
    _ = _ := hprod.tsum_eq

/-- The lattice minimal time. -/
noncomputable def latticeSupD (T : Vertex d → Configuration d → ℝ) (y : Vertex d)
    (ω : Configuration d) : ℝ :=
  ⨆ w : Vertex d, if ldist w y ≤ T w ω + 1 then T w ω else 0

theorem latticeSupD_nonneg {T : Vertex d → Configuration d → ℝ} (hT : ∀ w ω, 0 ≤ T w ω)
    (y : Vertex d) (ω : Configuration d) : 0 ≤ latticeSupD T y ω :=
  Real.iSup_nonneg fun w => by split_ifs <;> [exact hT w ω; exact le_rfl]

theorem measurable_latticeSupD {T : Vertex d → Configuration d → ℝ} (hT : ∀ w, Measurable (T w))
    (y : Vertex d) : Measurable (latticeSupD T y) :=
  Measurable.iSup fun w => Measurable.ite (measurableSet_le measurable_const ((hT w).add_const 1))
    (hT w) measurable_const

theorem le_of_latticeSupD_le {T : Vertex d → Configuration d → ℝ} {y : Vertex d}
    {ω : Configuration d}
    (hb : BddAbove (Set.range fun w => if ldist w y ≤ T w ω + 1 then T w ω else 0))
    {t : ℝ} (ht : latticeSupD T y ω ≤ t) {w : Vertex d} (hw : ldist w y ≤ t + 1) :
    T w ω ≤ t := by
  by_contra h
  push Not at h
  have hinc : ldist w y ≤ T w ω + 1 := by linarith
  have := le_ciSup hb w
  rw [if_pos hinc] at this
  exact absurd (this.trans ht) (not_le.2 h)

theorem exists_le_of_lt_latticeSupD {T : Vertex d → Configuration d → ℝ} {y : Vertex d}
    {ω : Configuration d} {a : ℝ} (ha : 0 < a)
    (h : ¬ BddAbove (Set.range fun w => if ldist w y ≤ T w ω + 1 then T w ω else 0) ∨
      2 * a ≤ latticeSupD T y ω) :
    ∃ w, max a (ldist w y - 1) ≤ T w ω := by
  have hex : ∃ w, a < (if ldist w y ≤ T w ω + 1 then T w ω else 0) := by
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
theorem hasTail_latticeSupD {T : Vertex d → Configuration d → ℝ} {C s : ℝ} (hC : 0 < C)
    (hs : 0 < s) (htail : ∀ w, HasTailD p (T w) C s) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ y : Vertex d, HasTailD p (latticeSupD T y) C' s ∧
      ∀ᵐ ω ∂latticeBondLaw d p,
        BddAbove (Set.range fun w => if ldist w y ≤ T w ω + 1 then T w ω else 0) := by
  obtain ⟨K, hK, hKb⟩ := exp_neg_rpow_le_inv_pow_nat hs (by positivity : (0 : ℝ) < 2 * C) (2 * d)
  set Z := (∑' n : ℤ, ((1 + |(n : ℝ)|) ^ 2)⁻¹) ^ d
  have hZ : 0 ≤ Z := pow_nonneg (tsum_nonneg fun n => by positivity) d
  set A := C * K * 2 ^ (2 * d) * Z
  -- the union bound
  have hunion : ∀ y : Vertex d, ∀ a : ℝ, 0 < a →
      latticeBondLaw d p {ω | ∃ w, max a (ldist w y - 1) ≤ T w ω} ≤
        ENNReal.ofReal (A * Real.exp (-Real.rpow a s / (2 * C))) := by
    intro y a ha
    have hset : {ω | ∃ w, max a (ldist w y - 1) ≤ T w ω} =
        ⋃ w, {ω | max a (ldist w y - 1) ≤ T w ω} := by ext ω; simp
    rw [hset]
    refine (measure_iUnion_le _).trans ?_
    have hterm : ∀ w : Vertex d, latticeBondLaw d p {ω | max a (ldist w y - 1) ≤ T w ω} ≤
        ENNReal.ofReal (C * K * 2 ^ (2 * d) * Real.exp (-Real.rpow a s / (2 * C)) *
          ((1 + ldist w y) ^ (2 * d))⁻¹) := by
      intro w
      refine (htail w _ (le_max_of_le_left ha.le)).trans (ENNReal.ofReal_le_ofReal ?_)
      obtain ⟨b, hb⟩ : ∃ b, b = max (ldist w y - 1) 0 := ⟨_, rfl⟩
      have hb0 : 0 ≤ b := hb ▸ le_max_right _ _
      have hb1 : ldist w y - 1 ≤ b := hb ▸ le_max_left _ _
      have hmab : max a (ldist w y - 1) = max a b := by
        rw [hb, max_comm (ldist w y - 1) 0, ← max_assoc, max_eq_left ha.le]
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
      have h1b : ((1 + b) ^ (2 * d))⁻¹ ≤ 2 ^ (2 * d) * ((1 + ldist w y) ^ (2 * d))⁻¹ := by
        have hd0 := Rigidity.WeakPoincare.latticeDist_nonneg w y
        have h2 : (1 + ldist w y) / 2 ≤ 1 + b := by linarith
        have h3 : ((1 + ldist w y) / 2) ^ (2 * d) ≤ (1 + b) ^ (2 * d) :=
          pow_le_pow_left₀ (by positivity) h2 (2 * d)
        have h4 : 0 < (1 + ldist w y) ^ (2 * d) := by positivity
        rw [div_pow] at h3
        rw [← div_eq_mul_inv, le_div_iff₀ h4, inv_mul_eq_div, div_le_iff₀ (by positivity)]
        have h5 : (1 + ldist w y) ^ (2 * d) ≤ 2 ^ (2 * d) * (1 + b) ^ (2 * d) := by
          rw [div_le_iff₀ (by positivity)] at h3; linarith
        linarith
      calc C * Real.exp (-Real.rpow (max a b) s / C)
          ≤ C * (Real.exp (-Real.rpow a s / (2 * C)) * Real.exp (-Real.rpow b s / (2 * C))) :=
            mul_le_mul_of_nonneg_left he hC.le
        _ ≤ C * (Real.exp (-Real.rpow a s / (2 * C)) * (K * ((1 + b) ^ (2 * d))⁻¹)) := by
            gcongr
        _ ≤ C * (Real.exp (-Real.rpow a s / (2 * C)) *
              (K * (2 ^ (2 * d) * ((1 + ldist w y) ^ (2 * d))⁻¹))) := by
            gcongr
        _ = _ := by ring
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    obtain ⟨hsumm, hsumle⟩ := summable_inv_one_add_pow (d := d) y
    have hc0 : 0 ≤ C * K * 2 ^ (2 * d) * Real.exp (-Real.rpow a s / (2 * C)) := by positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg hc0
      (by have := Rigidity.WeakPoincare.latticeDist_nonneg w y; positivity)) (hsumm.mul_left _)]
    apply ENNReal.ofReal_le_ofReal
    rw [tsum_mul_left]
    calc C * K * 2 ^ (2 * d) * Real.exp (-Real.rpow a s / (2 * C)) *
          ∑' w, ((1 + ldist w y) ^ (2 * d))⁻¹
        ≤ C * K * 2 ^ (2 * d) * Real.exp (-Real.rpow a s / (2 * C)) * Z :=
          mul_le_mul_of_nonneg_left hsumle hc0
      _ = A * Real.exp (-Real.rpow a s / (2 * C)) := by ring
  set C' := max (max A 1) (2 ^ s * (2 * C))
  have hC'1 : 1 ≤ C' := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨C', by linarith, fun y => ⟨?_, ?_⟩⟩
  · intro u hu
    rcases eq_or_lt_of_le hu with hu0 | hu0
    · subst hu0
      calc latticeBondLaw d p {ω | 0 ≤ latticeSupD T y ω} ≤ 1 := prob_le_one
        _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            simp only [Real.rpow_eq_pow, Real.zero_rpow hs.ne', neg_zero, zero_div, Real.exp_zero,
              mul_one]
            exact hC'1
    · have hsub : {ω | u ≤ latticeSupD T y ω} ⊆
          {ω | ∃ w, max (u / 2) (ldist w y - 1) ≤ T w ω} := by
        intro ω hω
        exact exists_le_of_lt_latticeSupD (by linarith)
          (Or.inr (by simp only [Set.mem_setOf_eq] at hω; linarith))
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
    have hnull : latticeBondLaw d p {ω | ¬ BddAbove (Set.range fun w =>
        if ldist w y ≤ T w ω + 1 then T w ω else 0)} = 0 := by
      have hbound : ∀ n : ℕ, latticeBondLaw d p {ω | ¬ BddAbove (Set.range fun w =>
          if ldist w y ≤ T w ω + 1 then T w ω else 0)} ≤
            ENNReal.ofReal (A * Real.exp (-Real.rpow ((n : ℝ) + 1) s / (2 * C))) := by
        intro n
        refine (measure_mono fun ω hω => ?_).trans (hunion y ((n : ℝ) + 1) (by positivity))
        exact exists_le_of_lt_latticeSupD (by positivity) (Or.inl hω)
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
