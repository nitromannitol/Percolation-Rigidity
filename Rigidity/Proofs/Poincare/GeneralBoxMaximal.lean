import Mathlib

/-!
# The centred box maximal function on `ℤ^d`

The extension of `BoxMaximal.lean` from `ℤ²` to `ℤ^d`. For `F : ℤ^d → ℝ` nonnegative and summable,
`boxMax F x = sup_{r ∈ ℕ} |Q_r(x)|⁻¹ Σ_{Q_r(x)} F` with `Q_r(x) = x + [-r, r]^d`. This is the lattice form of the maximal function of Armstrong, Kuusi and
Mourrat, Lemma D.4 (used in their Proposition D.2 and, through it, in Dario's Appendix A):

* `card_le_of_lt_boxMax`, `count_lt_boxMax_le`: the weak type `(1, 1)` bound
  `|{boxMax F > λ}| ≤ 3^d λ⁻¹ Σ F`, by the Vitali covering lemma of Mathlib
  (`Vitali.exists_disjoint_subfamily_covering_enlargement`) with enlargement factor `3`;
* `tsum_boxMax_rpow_le`: the strong type `(p, p)` bound, `1 < p`,
  `Σ (boxMax F)^p ≤ 2 · 3^d · 2^{p-1} p/(p-1) Σ F^p`, from the weak type bound applied to
  `F 1_{F > λ/2}` and the layer cake formula.
-/

open MeasureTheory Set

namespace Rigidity.Poincare.GeneralDim

variable {d : ℕ}

/-- The box `x + [-r, r]^d` of `ℤ^d`. -/
noncomputable def supBox (x : Fin d → ℤ) (r : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (x i - r) (x i + r)

theorem mem_supBox {x z : Fin d → ℤ} {r : ℕ} : z ∈ supBox x r ↔ ∀ i, |z i - x i| ≤ r := by
  simp only [supBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem self_mem_supBox (x : Fin d → ℤ) (r : ℕ) : x ∈ supBox x r :=
  mem_supBox.2 fun i => by simp

theorem card_supBox (x : Fin d → ℤ) (r : ℕ) : (supBox x r).card = (2 * r + 1) ^ d := by
  have : ∀ i, (Finset.Icc (x i - r) (x i + r)).card = 2 * r + 1 := fun i => by
    rw [Int.card_Icc]
    omega
  rw [supBox, Fintype.card_piFinset, Finset.prod_congr rfl fun i _ => this i, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The average of `F` over the box `x + [-r, r]^d`. -/
noncomputable def boxAvg (F : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) (r : ℕ) : ℝ :=
  (∑ z ∈ supBox x r, F z) / ((2 * r + 1) ^ d : ℕ)

/-- **The centred box maximal function** of `F` on `ℤ^d`. -/
noncomputable def boxMax (F : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) : ℝ :=
  ⨆ r : ℕ, boxAvg F x r

section

variable {F : (Fin d → ℤ) → ℝ}

theorem boxAvg_nonneg (hF : ∀ z, 0 ≤ F z) (x : Fin d → ℤ) (r : ℕ) : 0 ≤ boxAvg F x r :=
  div_nonneg (Finset.sum_nonneg fun z _ => hF z) (Nat.cast_nonneg _)

theorem boxAvg_le_tsum (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) (x : Fin d → ℤ) (r : ℕ) :
    boxAvg F x r ≤ ∑' z, F z := by
  have h1 : ∑ z ∈ supBox x r, F z ≤ ∑' z, F z := hFs.sum_le_tsum _ fun z _ => hF z
  have h2 : (1 : ℝ) ≤ ((2 * r + 1) ^ d : ℕ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have h3 : (0 : ℝ) ≤ ∑' z, F z := tsum_nonneg hF
  rw [boxAvg, div_le_iff₀ (by linarith)]
  nlinarith

theorem bddAbove_boxAvg (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) (x : Fin d → ℤ) :
    BddAbove (Set.range (boxAvg F x)) :=
  ⟨∑' z, F z, by rintro _ ⟨r, rfl⟩; exact boxAvg_le_tsum hF hFs x r⟩

theorem boxAvg_le_boxMax (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) (x : Fin d → ℤ) (r : ℕ) :
    boxAvg F x r ≤ boxMax F x :=
  le_ciSup (bddAbove_boxAvg hF hFs x) r

theorem boxMax_nonneg (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) (x : Fin d → ℤ) :
    0 ≤ boxMax F x :=
  (boxAvg_nonneg hF x 0).trans (boxAvg_le_boxMax hF hFs x 0)

/-- **Weak type `(1, 1)` on finite sets**: a finite set of points where the maximal function
exceeds `λ` has at most `3^d λ⁻¹ Σ F` points. -/
theorem card_le_of_lt_boxMax (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) {lam : ℝ} (hlam : 0 < lam)
    (E : Finset (Fin d → ℤ)) (hE : ∀ x ∈ E, lam < boxMax F x) :
    (E.card : ℝ) ≤ 3 ^ d / lam * ∑' z, F z := by
  classical
  have hex : ∀ x, ∃ r : ℕ, lam < boxMax F x → lam < boxAvg F x r := by
    intro x
    by_cases h : lam < boxMax F x
    · obtain ⟨r, hr⟩ := exists_lt_of_lt_ciSup h
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose r hr using hex
  have hrE : ∀ x ∈ E, lam * (2 * (r x : ℝ) + 1) ^ d < ∑ z ∈ supBox x (r x), F z := by
    intro x hx
    have h := hr x (hE x hx)
    rw [boxAvg, lt_div_iff₀ (by positivity)] at h
    push_cast at h
    exact h
  obtain ⟨u, huE, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x => ((supBox x (r x) : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))) (E : Set (Fin d → ℤ))
    (fun x => (r x : ℝ)) 2 (by norm_num) (fun _ _ => Nat.cast_nonneg _)
    ((E.sup r : ℕ) : ℝ) (fun x hx => Nat.cast_le.2 (Finset.le_sup (f := r) hx))
    (fun x _ => ⟨x, self_mem_supBox x (r x)⟩)
  have hufin : u.Finite := E.finite_toSet.subset huE
  set U := hufin.toFinset with hU
  have hUE : ∀ b ∈ U, b ∈ E := fun b hb => huE ((Set.Finite.mem_toFinset hufin).1 hb)
  -- covering by the enlarged boxes
  have hsub : E ⊆ U.biUnion fun b => supBox b (3 * r b) := by
    intro a ha
    obtain ⟨b, hbu, ⟨w, hwa, hwb⟩, hab⟩ := hcov a ha
    rw [Finset.mem_biUnion]
    refine ⟨b, (Set.Finite.mem_toFinset hufin).2 hbu, mem_supBox.2 fun i => ?_⟩
    have h1 := mem_supBox.1 (Finset.mem_coe.1 hwa) i
    have h2 := mem_supBox.1 (Finset.mem_coe.1 hwb) i
    have hab' : (r a : ℤ) ≤ 2 * r b := by exact_mod_cast hab
    have : |a i - b i| ≤ |w i - a i| + |w i - b i| := by
      rw [abs_sub_comm (w i) (a i)]
      exact abs_sub_le _ _ _
    push_cast
    linarith
  have hdisjU : (U : Set (Fin d → ℤ)).PairwiseDisjoint fun b => supBox b (r b) := by
    intro b hb c hc hbc
    have := hdisj ((Set.Finite.mem_toFinset hufin).1 hb) ((Set.Finite.mem_toFinset hufin).1 hc) hbc
    exact Finset.disjoint_coe.1 this
  have hcard : (E.card : ℝ) ≤ ∑ b ∈ U, 3 ^ d * (2 * (r b : ℝ) + 1) ^ d := by
    calc (E.card : ℝ) ≤ ((U.biUnion fun b => supBox b (3 * r b)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ b ∈ U, ((supBox b (3 * r b)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ b ∈ U, 3 ^ d * (2 * (r b : ℝ) + 1) ^ d := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [card_supBox, ← mul_pow]
          push_cast
          exact pow_le_pow_left₀ (by positivity)
            (by nlinarith [(Nat.cast_nonneg (r b) : (0 : ℝ) ≤ r b)]) d
  have hsum : ∑ b ∈ U, ∑ z ∈ supBox b (r b), F z ≤ ∑' z, F z := by
    rw [← Finset.sum_biUnion hdisjU]
    exact hFs.sum_le_tsum _ fun z _ => hF z
  calc (E.card : ℝ) ≤ ∑ b ∈ U, 3 ^ d * (2 * (r b : ℝ) + 1) ^ d := hcard
    _ ≤ ∑ b ∈ U, 3 ^ d / lam * ∑ z ∈ supBox b (r b), F z := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h := (hrE b (hUE b hb)).le
        rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
        have h3 : (0 : ℝ) < 3 ^ d := by positivity
        calc 3 ^ d * (2 * (r b : ℝ) + 1) ^ d * lam = 3 ^ d * (lam * (2 * (r b : ℝ) + 1) ^ d) := by
              ring
          _ ≤ 3 ^ d * ∑ z ∈ supBox b (r b), F z := mul_le_mul_of_nonneg_left h h3.le
    _ = 3 ^ d / lam * ∑ b ∈ U, ∑ z ∈ supBox b (r b), F z := by rw [Finset.mul_sum]
    _ ≤ 3 ^ d / lam * ∑' z, F z := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **Weak type `(1, 1)`**: `|{boxMax F > λ}| ≤ 3^d λ⁻¹ Σ F`. -/
theorem count_lt_boxMax_le (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) {lam : ℝ} (hlam : 0 < lam) :
    Measure.count {x | lam < boxMax F x} ≤ ENNReal.ofReal (3 ^ d / lam * ∑' z, F z) := by
  set E := {x | lam < boxMax F x}
  by_cases hfin : E.Finite
  · rw [Measure.count_apply_finite _ hfin, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal (card_le_of_lt_boxMax hF hFs hlam _ fun x hx => ?_)
    exact (Set.Finite.mem_toFinset hfin).1 hx
  · exfalso
    obtain ⟨N, hN⟩ := exists_nat_gt (3 ^ d / lam * ∑' z, F z)
    obtain ⟨s, hsE, hs⟩ := Set.Infinite.exists_subset_card_eq hfin N
    have h := card_le_of_lt_boxMax hF hFs hlam s fun x hx => hsE hx
    rw [hs] at h
    linarith

/-- **Weak type with truncation**: `|{boxMax F > λ}| ≤ 2 · 3^d λ⁻¹ Σ F 1_{F > λ/2}`. -/
theorem count_lt_boxMax_le_trunc (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) {lam : ℝ}
    (hlam : 0 < lam) :
    Measure.count {x | lam < boxMax F x} ≤
      ENNReal.ofReal (2 * 3 ^ d / lam * ∑' z, if lam < 2 * F z then F z else 0) := by
  classical
  set G : (Fin d → ℤ) → ℝ := fun z => if lam < 2 * F z then F z else 0 with hG
  have hG0 : ∀ z, 0 ≤ G z := fun z => by
    simp only [hG]
    split_ifs
    · exact hF z
    · exact le_rfl
  have hGF : ∀ z, G z ≤ F z := fun z => by
    simp only [hG]
    split_ifs
    · exact le_rfl
    · exact hF z
  have hGs : Summable G := hFs.of_nonneg_of_le hG0 hGF
  have hFG : ∀ z, F z ≤ G z + lam / 2 := fun z => by
    simp only [hG]
    split_ifs with h
    · linarith
    · linarith [not_lt.1 h]
  have hsub : {x | lam < boxMax F x} ⊆ {x | lam / 2 < boxMax G x} := by
    intro x hx
    obtain ⟨r, hr⟩ := exists_lt_of_lt_ciSup (Set.mem_setOf_eq ▸ hx)
    have hpos : (0 : ℝ) < ((2 * r + 1) ^ d : ℕ) := by positivity
    have h1 : boxAvg F x r ≤ boxAvg G x r + lam / 2 := by
      rw [boxAvg, boxAvg, div_add' _ _ _ hpos.ne', div_le_div_iff_of_pos_right hpos]
      calc ∑ z ∈ supBox x r, F z ≤ ∑ z ∈ supBox x r, (G z + lam / 2) :=
            Finset.sum_le_sum fun z _ => hFG z
        _ = ∑ z ∈ supBox x r, G z + lam / 2 * ((2 * r + 1) ^ d : ℕ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, card_supBox, nsmul_eq_mul]
            ring
    show lam / 2 < boxMax G x
    have h2 := boxAvg_le_boxMax hG0 hGs x r
    linarith
  calc Measure.count {x | lam < boxMax F x} ≤ Measure.count {x | lam / 2 < boxMax G x} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (3 ^ d / (lam / 2) * ∑' z, G z) := count_lt_boxMax_le hG0 hGs (by linarith)
    _ = ENNReal.ofReal (2 * 3 ^ d / lam * ∑' z, G z) := by
        congr 1
        field_simp

/-- `∫_0^c λ^{p-2} dλ = c^{p-1}/(p-1)` for `p > 1`, as a lower integral. -/
theorem lintegral_Ioo_rpow_sub_two {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) :
    ∫⁻ t in Ioo 0 c, ENNReal.ofReal (t ^ (p - 2)) = ENNReal.ofReal (c ^ (p - 1) / (p - 1)) := by
  have hr : -1 < p - 2 := by linarith
  have hint : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Ioc 0 c) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hr)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1 this
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc,
      integral_rpow (Or.inl hr)]
    congr 1
    rw [show p - 2 + 1 = p - 1 by ring, Real.zero_rpow (ne_of_gt (by linarith)), sub_zero]
  · exact hint.mono_set Ioo_subset_Ioc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _

/-- **Strong type `(p, p)`** of the box maximal function, `1 < p`:
`Σ (boxMax F)^p ≤ 2 · 3^d · 2^{p-1} p/(p-1) Σ F^p`. -/
theorem tsum_boxMax_rpow_le (hF : ∀ z, 0 ≤ F z) (hFs : Summable F) {p : ℝ} (hp : 1 < p) :
    ∑' x, ENNReal.ofReal (boxMax F x ^ p) ≤
      ENNReal.ofReal (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) * ∑' x, ENNReal.ofReal (F x ^ p) := by
  classical
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  -- the layer cake formula for the counting measure
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := Measure.count)
    (f := boxMax F) (Filter.Eventually.of_forall fun x => boxMax_nonneg hF hFs x)
    (Measurable.of_discrete).aemeasurable hp0
  rw [lintegral_count] at hlc
  rw [hlc]
  -- the truncated weak type bound under the integral
  set S : ℝ → (Fin d → ℤ) → ENNReal := fun t z =>
    ENNReal.ofReal (2 * 3 ^ d * F z) * (Set.Iio (2 * F z)).indicator
      (fun t => ENNReal.ofReal (t ^ (p - 2))) t with hS
  have hmeas : ∀ z, Measurable fun t : ℝ => (Set.Iio (2 * F z)).indicator
      (fun t : ℝ => ENNReal.ofReal (t ^ (p - 2))) t := fun z =>
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iio
  have hpt : ∀ t ∈ Ioi (0 : ℝ), Measure.count {x | t < boxMax F x} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ∑' z, S t z := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hGs : Summable fun z => if t < 2 * F z then F z else 0 :=
      hFs.of_nonneg_of_le (fun z => by split_ifs; exacts [hF z, le_rfl])
        (fun z => by split_ifs; exacts [le_rfl, hF z])
    refine (mul_le_mul_of_nonneg_right (count_lt_boxMax_le_trunc hF hFs ht0)
      zero_le).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by
      exact mul_nonneg (by positivity) (tsum_nonneg fun z => by split_ifs; exacts [hF z, le_rfl]))]
    have e1 : 2 * 3 ^ d / t * (∑' z, if t < 2 * F z then F z else 0) * t ^ (p - 1) =
        ∑' z, (if t < 2 * F z then 2 * 3 ^ d * F z * t ^ (p - 2) else 0) := by
      rw [mul_comm, ← mul_assoc, ← tsum_mul_left]
      refine tsum_congr fun z => ?_
      have ht2 : t ^ (p - 1) * (2 * 3 ^ d / t) = 2 * 3 ^ d * t ^ (p - 2) := by
        rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one ht0.ne']
        field_simp
      split_ifs
      · rw [ht2]
        ring
      · rw [mul_zero]
    rw [e1, ENNReal.ofReal_tsum_of_nonneg]
    · refine tsum_congr fun z => ?_
      simp only [hS, Set.indicator, Set.mem_Iio]
      split_ifs
      · rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (hF z))]
      · simp
    · intro z
      split_ifs
      · exact mul_nonneg (mul_nonneg (by positivity) (hF z)) (Real.rpow_nonneg ht0.le _)
      · exact le_rfl
    · refine (hGs.mul_left (2 * 3 ^ d * t ^ (p - 2))).congr fun z => ?_
      split_ifs <;> ring
  calc ENNReal.ofReal p *
        ∫⁻ t in Ioi 0, Measure.count {x | t < boxMax F x} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal p * ∫⁻ t in Ioi 0, ∑' z, S t z :=
        mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioi hpt) zero_le
    _ = ENNReal.ofReal p * ∑' z, ∫⁻ t in Ioi 0, S t z := by
        rw [lintegral_tsum fun z => ((hmeas z).const_mul _).aemeasurable]
    _ = ENNReal.ofReal p * ∑' z, ENNReal.ofReal (2 * 3 ^ d * 2 ^ (p - 1) / (p - 1) * F z ^ p) := by
        congr 1
        refine tsum_congr fun z => ?_
        simp only [hS]
        rw [lintegral_const_mul _ (hmeas z), lintegral_indicator measurableSet_Iio,
          Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi,
          lintegral_Ioo_rpow_sub_two hp (by linarith [hF z]),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (hF z))]
        congr 1
        rw [Real.mul_rpow (by norm_num) (hF z)]
        by_cases hz : F z = 0
        · rw [hz, Real.zero_rpow hp1.ne', Real.zero_rpow hp0.ne']
          ring
        · have hz' : 0 < F z := lt_of_le_of_ne (hF z) (Ne.symm hz)
          have : F z ^ p = F z * F z ^ (p - 1) := by
            rw [show p = 1 + (p - 1) by ring, Real.rpow_add hz', Real.rpow_one]
            ring_nf
          rw [this]
          field_simp
    _ = ENNReal.ofReal (2 * 3 ^ d * 2 ^ (p - 1) * p / (p - 1)) * ∑' x, ENNReal.ofReal (F x ^ p) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun z => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end

end Rigidity.Poincare.GeneralDim
