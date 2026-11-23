import Rigidity.Proofs.Corrector.DarioBoxMoments

/-!
# Steps 1–4 of the proof of Dario's Theorem 1

Dario (*Optimal corrector estimates on percolation clusters*, §5) upgrades the `L^q` bound of
Theorem 2 on the coarsened corrector `[χ_p]_𝒫` to a bound on its increments
`E|[χ_p]_𝒫(x) - [χ_p]_𝒫(0)|^q ≤ C^q q^{qk} m^{q/2}` for `3^m ≤ |x| < 3^{m+1}` (Steps 1–4).
The argument uses three properties of the fields `F_y = [χ_p]_{𝒫_y}`, coarsened with the
translated partitions `𝒫_y = y + 𝒫(τ_{-y} a)`, which we take as hypotheses
(`LinftyIterationData`):

* `thm2`: (step1LinftyLp), Theorem 2 for `F_0` on the box `□_m`, in moment form,
  `E[3^{-dm} Σ_{z ∈ □_m} |F_0(z) - (F_0)_{□_m}|^q] ≤ (A q^k)^q m^{q/2}`;
* `stat`: (e.stat.corr), `F_0(z) - F_0(w) = (F_y(z + y) - F_y(w + y)) ∘ τ` for a measure-preserving
  translation `τ` of the configurations;
* `comp`: (est.PPy) in moment form, `E|F_y(z) - F_0(z)|^q ≤ (B q^k)^q`.

Steps 1–3 compare `F_0(0)` and `F_0(x)` with the double average
`D_m(x) = 3^{-2dm} Σ_{y ∈ □_m} Σ_{z ∈ x + y + □_m} F_0(z)`; Step 3 uses `x + □_m ⊆ □_{m+2}`. The
moments are lower Lebesgue integrals, so no integrability hypothesis is needed.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter Set LatticeProb.Percolation
open scoped ENNReal

/-- The hypotheses of Steps 1–4 of the proof of Dario's Theorem 1 for the fields `F y`. -/
structure LinftyIterationData (p : unitInterval) (F : Vertex 2 → Vertex 2 → Configuration 2 → ℝ)
    (A B k : ℝ) : Prop where
  hA : 0 ≤ A
  hB : 0 ≤ B
  meas : ∀ y z, Measurable (F y z)
  thm2 : ∀ m : ℕ, 1 ≤ m → ∀ q : ℝ, 1 ≤ q →
    ∫⁻ ω, ENNReal.ofReal ((∑ z ∈ boxAt 0 m, |F 0 z ω - boxAvg (F 0) 0 m ω| ^ q) / 9 ^ m)
        ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((A * q ^ k) ^ q * (m : ℝ) ^ (q / 2))
  stat : ∀ y, ∃ T : Configuration 2 → Configuration 2,
    MeasurePreserving T (latticeBondLaw 2 p) (latticeBondLaw 2 p) ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ z w, F 0 z ω - F 0 w ω = F y (z + y) (T ω) - F y (w + y) (T ω)
  comp : ∀ y z, ∀ q : ℝ, 1 ≤ q →
    mom p (fun ω => F y z ω - F 0 z ω) q ≤ ENNReal.ofReal ((B * q ^ k) ^ q)

namespace LinftyIterationData

variable {p : unitInterval} {F : Vertex 2 → Vertex 2 → Configuration 2 → ℝ} {A B k : ℝ}

/-- The pointwise form of the stationarity for box averages. -/
theorem sub_boxAvg_transport {y : Vertex 2} {T : Configuration 2 → Configuration 2}
    {ω : Configuration 2}
    (hω : ∀ z w, F 0 z ω - F 0 w ω = F y (z + y) (T ω) - F y (w + y) (T ω))
    (a c : Vertex 2) (m : ℕ) :
    F 0 a ω - boxAvg (F 0) c m ω = F y (a + y) (T ω) - boxAvg (F y) (c + y) m (T ω) := by
  rw [sub_boxAvg_eq, sub_boxAvg_eq, ← sum_boxAt_add (fun z => F y (a + y) (T ω) - F y z (T ω))]
  congr 1
  exact Finset.sum_congr rfl fun w _ => hω a w

theorem sub_boxAvg2_transport {y : Vertex 2} {T : Configuration 2 → Configuration 2}
    {ω : Configuration 2}
    (hω : ∀ z w, F 0 z ω - F 0 w ω = F y (z + y) (T ω) - F y (w + y) (T ω))
    (a c : Vertex 2) (m : ℕ) :
    F 0 a ω - boxAvg2 (F 0) c m ω = F y (a + y) (T ω) - boxAvg2 (F y) (c + y) m (T ω) := by
  rw [sub_boxAvg2_eq, sub_boxAvg2_eq]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [sub_boxAvg_transport hω a (c + w) m, add_right_comm]

theorem measurable_sub_boxAvg (hD : LinftyIterationData p F A B k) (y a c : Vertex 2) (m : ℕ) :
    Measurable fun ω => F y a ω - boxAvg (F y) c m ω :=
  (hD.meas y a).sub (measurable_boxAvg (hD.meas y) c m)

theorem measurable_sub_boxAvg2 (hD : LinftyIterationData p F A B k) (y a c : Vertex 2) (m : ℕ) :
    Measurable fun ω => F y a ω - boxAvg2 (F y) c m ω :=
  (hD.meas y a).sub (measurable_boxAvg2 (hD.meas y) c m)

/-- Stationarity: `E|F_y(a + y) - (F_y)_{c + y + □_m}|^q = E|F_0(a) - (F_0)_{c + □_m}|^q`. -/
theorem mom_sub_boxAvg_transport (hD : LinftyIterationData p F A B k) (y a c : Vertex 2)
    (m : ℕ) (q : ℝ) :
    mom p (fun ω => F y (a + y) ω - boxAvg (F y) (c + y) m ω) q =
      mom p (fun ω => F 0 a ω - boxAvg (F 0) c m ω) q := by
  obtain ⟨T, hT, hTae⟩ := hD.stat y
  have hm := measurable_ofReal_abs_rpow (hD.measurable_sub_boxAvg y (a + y) (c + y) m) q
  unfold mom
  rw [← hT.lintegral_comp hm]
  refine lintegral_congr_ae ?_
  filter_upwards [hTae] with ω hω
  rw [sub_boxAvg_transport hω a c m]

theorem mom_sub_boxAvg2_transport (hD : LinftyIterationData p F A B k) (y a c : Vertex 2)
    (m : ℕ) (q : ℝ) :
    mom p (fun ω => F y (a + y) ω - boxAvg2 (F y) (c + y) m ω) q =
      mom p (fun ω => F 0 a ω - boxAvg2 (F 0) c m ω) q := by
  obtain ⟨T, hT, hTae⟩ := hD.stat y
  have hm := measurable_ofReal_abs_rpow (hD.measurable_sub_boxAvg2 y (a + y) (c + y) m) q
  unfold mom
  rw [← hT.lintegral_comp hm]
  refine lintegral_congr_ae ?_
  filter_upwards [hTae] with ω hω
  rw [sub_boxAvg2_transport hω a c m]

/-- Comparison of box averages: `E|(F_y)_{c + □_m} - (F_0)_{c + □_m}|^q ≤ (B q^k)^q`. -/
theorem mom_boxAvg_sub_le (hD : LinftyIterationData p F A B k) (y c : Vertex 2) (m : ℕ)
    {q : ℝ} (hq : 1 ≤ q) :
    mom p (fun ω => boxAvg (F y) c m ω - boxAvg (F 0) c m ω) q ≤
      ENNReal.ofReal ((B * q ^ k) ^ q) := by
  have heq : (fun ω => boxAvg (F y) c m ω - boxAvg (F 0) c m ω) =
      fun ω => (∑ z ∈ boxAt c m, (F y z ω - F 0 z ω)) / 9 ^ m := by
    funext ω
    rw [boxAvg, boxAvg, Finset.sum_sub_distrib, sub_div]
  rw [heq]
  exact mom_sum_div_le_of_le _ (fun z ω => F y z ω - F 0 z ω)
    (fun z => (hD.meas y z).sub (hD.meas 0 z)) (card_boxAt_real c m) (by positivity) hq
    (fun z _ => hD.comp y z q hq)

theorem mom_boxAvg2_sub_le (hD : LinftyIterationData p F A B k) (y c : Vertex 2) (m : ℕ)
    {q : ℝ} (hq : 1 ≤ q) :
    mom p (fun ω => boxAvg2 (F y) c m ω - boxAvg2 (F 0) c m ω) q ≤
      ENNReal.ofReal ((B * q ^ k) ^ q) := by
  have heq : (fun ω => boxAvg2 (F y) c m ω - boxAvg2 (F 0) c m ω) =
      fun ω => (∑ w ∈ boxAt 0 m, (boxAvg (F y) (c + w) m ω - boxAvg (F 0) (c + w) m ω)) /
        9 ^ m := by
    funext ω
    rw [boxAvg2, boxAvg2, Finset.sum_sub_distrib, sub_div]
  rw [heq]
  exact mom_sum_div_le_of_le _ (fun w ω => boxAvg (F y) (c + w) m ω - boxAvg (F 0) (c + w) m ω)
    (fun w => (measurable_boxAvg (hD.meas y) _ m).sub (measurable_boxAvg (hD.meas 0) _ m))
    (card_boxAt_real 0 m) (by positivity) hq (fun w _ => hD.mom_boxAvg_sub_le y (c + w) m hq)

/-- **The common part of Steps 1 and 3**: replacing `F_y` by `F_0` with the stationarity,
`E|F_0(0) - D_m(c)|^q ≤ 3^q (3^{-dm} Σ_{y ∈ □_m} E|F_0(-y) - (F_0)_{c + □_m}|^q + 2 (B q^k)^q)`. -/
theorem mom_sub_boxAvg2_le (hD : LinftyIterationData p F A B k) (c : Vertex 2) (m : ℕ)
    {q : ℝ} (hq : 1 ≤ q) :
    mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) c m ω) q ≤
      ENNReal.ofReal (3 ^ q) * ((∑ y ∈ boxAt 0 m, mom p (fun ω => F 0 (-y) ω -
        boxAvg (F 0) c m ω) q) * ENNReal.ofReal (1 / 9 ^ m) +
        2 * ENNReal.ofReal ((B * q ^ k) ^ q)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have heq : (fun ω => F 0 0 ω - boxAvg2 (F 0) c m ω) =
      fun ω => (∑ y ∈ boxAt 0 m, (F 0 0 ω - boxAvg (F 0) (c + y) m ω)) / 9 ^ m := by
    funext ω
    rw [sub_boxAvg2_eq]
  rw [heq]
  refine (mom_sum_div_le _ (fun y ω => F 0 0 ω - boxAvg (F 0) (c + y) m ω)
    (fun y => hD.measurable_sub_boxAvg 0 0 _ m) (card_boxAt_real 0 m) (by positivity) hq).trans ?_
  have hterm : ∀ y ∈ boxAt 0 m, mom p (fun ω => F 0 0 ω - boxAvg (F 0) (c + y) m ω) q ≤
      ENNReal.ofReal (3 ^ q) * (mom p (fun ω => F 0 (-y) ω - boxAvg (F 0) c m ω) q +
        2 * ENNReal.ofReal ((B * q ^ k) ^ q)) := by
    intro y _
    have h3 := mom_le_three (p := p) (f := fun ω => F 0 0 ω - boxAvg (F 0) (c + y) m ω)
      (g₁ := fun ω => F y 0 ω - boxAvg (F y) (c + y) m ω)
      (g₂ := fun ω => F y 0 ω - F 0 0 ω)
      (g₃ := fun ω => boxAvg (F y) (c + y) m ω - boxAvg (F 0) (c + y) m ω) hq0
      (hD.measurable_sub_boxAvg y 0 _ m) ((hD.meas y 0).sub (hD.meas 0 0))
      (Eventually.of_forall fun ω => by
        have : F 0 0 ω - boxAvg (F 0) (c + y) m ω = (F y 0 ω - boxAvg (F y) (c + y) m ω) -
            (F y 0 ω - F 0 0 ω) + (boxAvg (F y) (c + y) m ω - boxAvg (F 0) (c + y) m ω) := by ring
        rw [this]
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl))
    have ht := hD.mom_sub_boxAvg_transport y (-y) c m q
    rw [neg_add_cancel] at ht
    refine h3.trans ?_
    rw [ht, add_assoc, two_mul]
    gcongr
    · exact hD.comp y 0 q hq
    · exact hD.mom_boxAvg_sub_le y (c + y) m hq
  calc (∑ y ∈ boxAt 0 m, mom p (fun ω => F 0 0 ω - boxAvg (F 0) (c + y) m ω) q) *
        ENNReal.ofReal (1 / 9 ^ m)
      ≤ (∑ y ∈ boxAt 0 m, ENNReal.ofReal (3 ^ q) *
          (mom p (fun ω => F 0 (-y) ω - boxAvg (F 0) c m ω) q +
            2 * ENNReal.ofReal ((B * q ^ k) ^ q))) * ENNReal.ofReal (1 / 9 ^ m) := by
        gcongr with y hy
        exact hterm y hy
    _ = ENNReal.ofReal (3 ^ q) * ((∑ y ∈ boxAt 0 m, mom p (fun ω => F 0 (-y) ω -
          boxAvg (F 0) c m ω) q) * ENNReal.ofReal (1 / 9 ^ m) +
          2 * ENNReal.ofReal ((B * q ^ k) ^ q)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, card_boxAt, nsmul_eq_mul,
          mul_assoc, add_mul]
        congr 2
        rw [mul_comm ((9 ^ m : ℕ) : ℝ≥0∞), mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        push_cast
        rw [mul_one_div_cancel (by positivity), ENNReal.ofReal_one, mul_one]

/-- The averaged moment over the reflected box is the moment of the box oscillation. -/
theorem sum_mom_neg_eq (hD : LinftyIterationData p F A B k) (c : Vertex 2) (m : ℕ) (q : ℝ) :
    (∑ y ∈ boxAt 0 m, mom p (fun ω => F 0 (-y) ω - boxAvg (F 0) c m ω) q) *
        ENNReal.ofReal (1 / 9 ^ m) =
      ∫⁻ ω, ENNReal.ofReal ((∑ z ∈ boxAt 0 m, |F 0 z ω - boxAvg (F 0) c m ω| ^ q) / 9 ^ m)
        ∂latticeBondLaw 2 p := by
  unfold mom
  rw [← lintegral_finsetSum _ fun y _ =>
    measurable_ofReal_abs_rpow (hD.measurable_sub_boxAvg 0 (-y) c m) q,
    ← lintegral_mul_const _ (Finset.measurable_sum _ fun y _ =>
      measurable_ofReal_abs_rpow (hD.measurable_sub_boxAvg 0 (-y) c m) q)]
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun y _ => by positivity),
    sum_boxAt_neg (fun z => |F 0 z ω - boxAvg (F 0) c m ω| ^ q) m]
  congr 1
  ring

/-- The oscillation around a box average inside a larger box (Step 3):
`3^{-dm} Σ_{z ∈ □_m} |F_0(z) - (F_0)_{x + □_m}|^q ≤ 162 · 2^q 3^{-d(m+2)} Σ_{z ∈ □_{m+2}}
|F_0(z) - (F_0)_{□_{m+2}}|^q` for `|x|_∞ < 3^{m+1}`. -/
theorem sum_abs_sub_boxAvg_le (G : Vertex 2 → ℝ) {x : Vertex 2} {m : ℕ}
    (hx : ∀ i, |x i| < ((3 ^ (m + 1) : ℕ) : ℤ)) {q : ℝ} (hq : 1 ≤ q) :
    (∑ z ∈ boxAt 0 m, |G z - (∑ w ∈ boxAt x m, G w) / 9 ^ m| ^ q) / 9 ^ m ≤
      162 * 2 ^ q * ((∑ z ∈ boxAt 0 (m + 2),
        |G z - (∑ w ∈ boxAt 0 (m + 2), G w) / 9 ^ (m + 2)| ^ q) / 9 ^ (m + 2)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  set a' := (∑ w ∈ boxAt 0 (m + 2), G w) / 9 ^ (m + 2)
  set ax := (∑ w ∈ boxAt x m, G w) / 9 ^ m
  set S' := ∑ z ∈ boxAt 0 (m + 2), |G z - a'| ^ q
  have hS'0 : 0 ≤ S' := Finset.sum_nonneg fun z _ => by positivity
  have h9 : (0 : ℝ) < 9 ^ m := by positivity
  have hJ : |ax - a'| ^ q ≤ (∑ w ∈ boxAt x m, |G w - a'| ^ q) / 9 ^ m := by
    have : ax - a' = (∑ w ∈ boxAt x m, (G w - a')) / 9 ^ m := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_boxAt, nsmul_eq_mul]
      push_cast
      simp only [ax]
      field_simp
    rw [this]
    exact abs_sum_div_rpow_le _ _ (card_boxAt_real x m) h9 hq
  have hsub1 : ∑ w ∈ boxAt x m, |G w - a'| ^ q ≤ S' :=
    Finset.sum_le_sum_of_subset_of_nonneg (boxAt_subset_of_lt hx) fun _ _ _ => by positivity
  have hsub2 : ∑ z ∈ boxAt 0 m, |G z - a'| ^ q ≤ S' :=
    Finset.sum_le_sum_of_subset_of_nonneg (boxAt_subset_boxAt_add_two m) fun _ _ _ => by
      positivity
  have hpt : ∀ z, |G z - ax| ^ q ≤ 2 ^ q * (|G z - a'| ^ q + |ax - a'| ^ q) := by
    intro z
    calc |G z - ax| ^ q ≤ (|G z - a'| + |ax - a'|) ^ q := by
          refine Real.rpow_le_rpow (abs_nonneg _) ?_ hq0
          calc |G z - ax| = |(G z - a') - (ax - a')| := by ring_nf
            _ ≤ |G z - a'| + |ax - a'| := abs_sub _ _
      _ ≤ 2 ^ q * (|G z - a'| ^ q + |ax - a'| ^ q) :=
          add_rpow_le_two (abs_nonneg _) (abs_nonneg _) hq0
  have hsum : ∑ z ∈ boxAt 0 m, |G z - ax| ^ q ≤ 2 ^ q * (S' + 9 ^ m * |ax - a'| ^ q) := by
    calc ∑ z ∈ boxAt 0 m, |G z - ax| ^ q
        ≤ ∑ z ∈ boxAt 0 m, 2 ^ q * (|G z - a'| ^ q + |ax - a'| ^ q) :=
          Finset.sum_le_sum fun z _ => hpt z
      _ = 2 ^ q * (∑ z ∈ boxAt 0 m, |G z - a'| ^ q + 9 ^ m * |ax - a'| ^ q) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, card_boxAt,
            nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 2 ^ q * (S' + 9 ^ m * |ax - a'| ^ q) := by gcongr
  have hax : 9 ^ m * |ax - a'| ^ q ≤ S' := by
    calc 9 ^ m * |ax - a'| ^ q ≤ 9 ^ m * ((∑ w ∈ boxAt x m, |G w - a'| ^ q) / 9 ^ m) := by gcongr
      _ = ∑ w ∈ boxAt x m, |G w - a'| ^ q := by field_simp
      _ ≤ S' := hsub1
  have h2 : (0 : ℝ) ≤ 2 ^ q := by positivity
  calc (∑ z ∈ boxAt 0 m, |G z - ax| ^ q) / 9 ^ m ≤ 2 ^ q * (S' + S') / 9 ^ m := by
        gcongr
        exact hsum.trans (by gcongr)
    _ = 162 * 2 ^ q * (S' / 9 ^ (m + 2)) := by
        rw [pow_add]
        field_simp
        ring

/-- **Step 1** (`x = 0`): `E|F_0(0) - D_m(0)|^q ≤ 3^q ((A q^k)^q m^{q/2} + 2 (B q^k)^q)`. -/
theorem mom_step1 (hD : LinftyIterationData p F A B k) {m : ℕ} (hm : 1 ≤ m) {q : ℝ} (hq : 1 ≤ q) :
    mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) 0 m ω) q ≤
      ENNReal.ofReal (3 ^ q) * (ENNReal.ofReal ((A * q ^ k) ^ q * (m : ℝ) ^ (q / 2)) +
        2 * ENNReal.ofReal ((B * q ^ k) ^ q)) := by
  refine (hD.mom_sub_boxAvg2_le 0 m hq).trans ?_
  rw [hD.sum_mom_neg_eq 0 m q]
  gcongr
  exact hD.thm2 m hm q hq

/-- **Step 2**: `E|F_0(x) - D_m(x)|^q ≤ 3^q (E|F_0(0) - D_m(0)|^q + 2 (B q^k)^q)`. -/
theorem mom_step2 (hD : LinftyIterationData p F A B k) (x : Vertex 2) (m : ℕ) {q : ℝ}
    (hq : 1 ≤ q) :
    mom p (fun ω => F 0 x ω - boxAvg2 (F 0) x m ω) q ≤
      ENNReal.ofReal (3 ^ q) * (mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) 0 m ω) q +
        2 * ENNReal.ofReal ((B * q ^ k) ^ q)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have h3 := mom_le_three (p := p) (f := fun ω => F 0 x ω - boxAvg2 (F 0) x m ω)
    (g₁ := fun ω => F x x ω - boxAvg2 (F x) x m ω)
    (g₂ := fun ω => F x x ω - F 0 x ω)
    (g₃ := fun ω => boxAvg2 (F x) x m ω - boxAvg2 (F 0) x m ω) hq0
    (hD.measurable_sub_boxAvg2 x x x m) ((hD.meas x x).sub (hD.meas 0 x))
    (Eventually.of_forall fun ω => by
      have : F 0 x ω - boxAvg2 (F 0) x m ω = (F x x ω - boxAvg2 (F x) x m ω) -
          (F x x ω - F 0 x ω) + (boxAvg2 (F x) x m ω - boxAvg2 (F 0) x m ω) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl))
  have ht := hD.mom_sub_boxAvg2_transport x 0 0 m q
  rw [zero_add] at ht
  refine h3.trans ?_
  rw [ht, add_assoc, two_mul]
  gcongr
  · exact hD.comp x x q hq
  · exact hD.mom_boxAvg2_sub_le x x m hq

/-- **Step 3**: for `|x|_∞ < 3^{m+1}`,
`E|F_0(0) - D_m(x)|^q ≤ 3^q (162 · 2^q (A q^k)^q (m+2)^{q/2} + 2 (B q^k)^q)`. -/
theorem mom_step3 (hD : LinftyIterationData p F A B k) {x : Vertex 2} {m : ℕ}
    (hx : ∀ i, |x i| < ((3 ^ (m + 1) : ℕ) : ℤ)) {q : ℝ} (hq : 1 ≤ q) :
    mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) x m ω) q ≤
      ENNReal.ofReal (3 ^ q) * (ENNReal.ofReal (162 * 2 ^ q *
        ((A * q ^ k) ^ q * ((m + 2 : ℕ) : ℝ) ^ (q / 2))) +
        2 * ENNReal.ofReal ((B * q ^ k) ^ q)) := by
  refine (hD.mom_sub_boxAvg2_le x m hq).trans ?_
  rw [hD.sum_mom_neg_eq x m q]
  gcongr
  calc ∫⁻ ω, ENNReal.ofReal ((∑ z ∈ boxAt 0 m, |F 0 z ω - boxAvg (F 0) x m ω| ^ q) / 9 ^ m)
        ∂latticeBondLaw 2 p
      ≤ ∫⁻ ω, ENNReal.ofReal (162 * 2 ^ q) * ENNReal.ofReal ((∑ z ∈ boxAt 0 (m + 2),
          |F 0 z ω - boxAvg (F 0) 0 (m + 2) ω| ^ q) / 9 ^ (m + 2)) ∂latticeBondLaw 2 p := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (sum_abs_sub_boxAvg_le (fun z => F 0 z ω) hx hq)
    _ = ENNReal.ofReal (162 * 2 ^ q) * ∫⁻ ω, ENNReal.ofReal ((∑ z ∈ boxAt 0 (m + 2),
          |F 0 z ω - boxAvg (F 0) 0 (m + 2) ω| ^ q) / 9 ^ (m + 2)) ∂latticeBondLaw 2 p :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (162 * 2 ^ q) *
          ENNReal.ofReal ((A * q ^ k) ^ q * ((m + 2 : ℕ) : ℝ) ^ (q / 2)) := by
        gcongr
        exact hD.thm2 (m + 2) (by omega) q hq
    _ = ENNReal.ofReal (162 * 2 ^ q * ((A * q ^ k) ^ q * ((m + 2 : ℕ) : ℝ) ^ (q / 2))) :=
        (ENNReal.ofReal_mul (by positivity)).symm

/-- **Steps 1–4 of the proof of Dario's Theorem 1**: for `|x|_∞ < 3^{m+1}`, `m ≥ 1` and `q ≥ 1`,
`E|F_0(x) - F_0(0)|^q ≤ (K q^k)^q (m+2)^{q/2}` with `K = 6084 max(A, B)`. -/
theorem mom_sub_le (hD : LinftyIterationData p F A B k) {x : Vertex 2} {m : ℕ} (hm : 1 ≤ m)
    (hx : ∀ i, |x i| < ((3 ^ (m + 1) : ℕ) : ℤ)) {q : ℝ} (hq : 1 ≤ q) :
    mom p (fun ω => F 0 x ω - F 0 0 ω) q ≤
      ENNReal.ofReal ((6084 * max A B * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2)) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  set W : ℝ := (A * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) + (B * q ^ k) ^ q with hW
  have hqk : 0 ≤ q ^ k := Real.rpow_nonneg hq0 k
  have hAq : 0 ≤ (A * q ^ k) ^ q := Real.rpow_nonneg (mul_nonneg hD.hA hqk) q
  have hBq : 0 ≤ (B * q ^ k) ^ q := Real.rpow_nonneg (mul_nonneg hD.hB hqk) q
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hmq : (m : ℝ) ^ (q / 2) ≤ ((m : ℝ) + 2) ^ (q / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg m) (by linarith) (by positivity)
  have hm2q : (1 : ℝ) ≤ ((m : ℝ) + 2) ^ (q / 2) := Real.one_le_rpow hm1 (by positivity)
  have hcast : (((m + 2 : ℕ) : ℝ)) = (m : ℝ) + 2 := by push_cast; ring
  have hTW : (A * q ^ k) ^ q * (m : ℝ) ^ (q / 2) ≤ W := by
    have : (A * q ^ k) ^ q * (m : ℝ) ^ (q / 2) ≤ (A * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) :=
      mul_le_mul_of_nonneg_left hmq hAq
    linarith
  have hT2W : (A * q ^ k) ^ q * ((m + 2 : ℕ) : ℝ) ^ (q / 2) ≤ W := by rw [hcast]; linarith
  have hBW : (B * q ^ k) ^ q ≤ W := by
    have : 0 ≤ (A * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) := by positivity
    linarith
  have hW0 : 0 ≤ W := le_trans hBq hBW
  have h3q : (1 : ℝ) ≤ 3 ^ q := Real.one_le_rpow (by norm_num) hq0
  have h2q : (1 : ℝ) ≤ 2 ^ q := Real.one_le_rpow (by norm_num) hq0
  -- the three steps with the bound `W`
  have h2B : 2 * ENNReal.ofReal ((B * q ^ k) ^ q) ≤ ENNReal.ofReal (2 * W) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hs1 : mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) 0 m ω) q ≤
      ENNReal.ofReal (3 ^ q * (3 * W)) := by
    refine (hD.mom_step1 hm hq).trans ?_
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 ^ q by positivity)]
    gcongr
    calc ENNReal.ofReal ((A * q ^ k) ^ q * (m : ℝ) ^ (q / 2)) + 2 * ENNReal.ofReal ((B * q ^ k) ^ q)
        ≤ ENNReal.ofReal W + ENNReal.ofReal (2 * W) := add_le_add (ENNReal.ofReal_le_ofReal hTW) h2B
      _ = ENNReal.ofReal (3 * W) := by
          rw [← ENNReal.ofReal_add hW0 (by positivity)]
          ring_nf
  have hs2 : mom p (fun ω => F 0 x ω - boxAvg2 (F 0) x m ω) q ≤
      ENNReal.ofReal (3 ^ q * (3 ^ q * (3 * W) + 2 * W)) := by
    refine (hD.mom_step2 x m hq).trans ?_
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 ^ q by positivity)]
    gcongr
    calc mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) 0 m ω) q + 2 * ENNReal.ofReal ((B * q ^ k) ^ q)
        ≤ ENNReal.ofReal (3 ^ q * (3 * W)) + ENNReal.ofReal (2 * W) := add_le_add hs1 h2B
      _ = ENNReal.ofReal (3 ^ q * (3 * W) + 2 * W) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hs3 : mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) x m ω) q ≤
      ENNReal.ofReal (3 ^ q * (162 * 2 ^ q * W + 2 * W)) := by
    refine (hD.mom_step3 hx hq).trans ?_
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 ^ q by positivity)]
    gcongr
    calc ENNReal.ofReal (162 * 2 ^ q * ((A * q ^ k) ^ q * ((m + 2 : ℕ) : ℝ) ^ (q / 2))) +
          2 * ENNReal.ofReal ((B * q ^ k) ^ q)
        ≤ ENNReal.ofReal (162 * 2 ^ q * W) + ENNReal.ofReal (2 * W) :=
          add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hT2W (by positivity))) h2B
      _ = ENNReal.ofReal (162 * 2 ^ q * W + 2 * W) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  -- Step 4
  have h4 := mom_le_two (p := p) (f := fun ω => F 0 x ω - F 0 0 ω)
    (g₁ := fun ω => F 0 x ω - boxAvg2 (F 0) x m ω)
    (g₂ := fun ω => F 0 0 ω - boxAvg2 (F 0) x m ω) hq0 (hD.measurable_sub_boxAvg2 0 x x m)
    (Eventually.of_forall fun ω => by
      have : F 0 x ω - F 0 0 ω = (F 0 x ω - boxAvg2 (F 0) x m ω) -
          (F 0 0 ω - boxAvg2 (F 0) x m ω) := by ring
      rw [this]
      exact abs_sub _ _)
  refine h4.trans ?_
  calc ENNReal.ofReal (2 ^ q) * (mom p (fun ω => F 0 x ω - boxAvg2 (F 0) x m ω) q +
        mom p (fun ω => F 0 0 ω - boxAvg2 (F 0) x m ω) q)
      ≤ ENNReal.ofReal (2 ^ q) * (ENNReal.ofReal (3 ^ q * (3 ^ q * (3 * W) + 2 * W)) +
          ENNReal.ofReal (3 ^ q * (162 * 2 ^ q * W + 2 * W))) := by gcongr
    _ = ENNReal.ofReal (2 ^ q * (3 ^ q * (3 ^ q * (3 * W) + 2 * W) +
          3 ^ q * (162 * 2 ^ q * W + 2 * W))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((6084 * max A B * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        -- `2^q 3^q 3^q ≤ 18^q`, `2^q 3^q ≤ 18^q`, `2^q 3^q 2^q ≤ 18^q`
        have e18 : (2 : ℝ) ^ q * 3 ^ q * 3 ^ q = 18 ^ q := by
          rw [← Real.mul_rpow (by norm_num) (by norm_num), ← Real.mul_rpow (by norm_num)
            (by norm_num)]
          norm_num
        have e12 : (2 : ℝ) ^ q * 3 ^ q * 2 ^ q = 12 ^ q := by
          rw [← Real.mul_rpow (by norm_num) (by norm_num), ← Real.mul_rpow (by norm_num)
            (by norm_num)]
          norm_num
        have h12 : (12 : ℝ) ^ q ≤ 18 ^ q := Real.rpow_le_rpow (by norm_num) (by norm_num) hq0
        have h6 : (2 : ℝ) ^ q * 3 ^ q ≤ 18 ^ q := by
          rw [← Real.mul_rpow (by norm_num) (by norm_num)]
          exact Real.rpow_le_rpow (by norm_num) (by norm_num) hq0
        have hbound : 2 ^ q * (3 ^ q * (3 ^ q * (3 * W) + 2 * W) +
            3 ^ q * (162 * 2 ^ q * W + 2 * W)) ≤ 169 * 18 ^ q * W := by
          have h18 : 0 ≤ (18 : ℝ) ^ q := by positivity
          have : 2 ^ q * (3 ^ q * (3 ^ q * (3 * W) + 2 * W) + 3 ^ q * (162 * 2 ^ q * W + 2 * W)) =
              3 * (2 ^ q * 3 ^ q * 3 ^ q) * W + 2 * (2 ^ q * 3 ^ q) * W +
                162 * (2 ^ q * 3 ^ q * 2 ^ q) * W + 2 * (2 ^ q * 3 ^ q) * W := by ring
          rw [this, e18, e12]
          nlinarith [mul_le_mul_of_nonneg_right h12 hW0, mul_le_mul_of_nonneg_right h6 hW0]
        refine hbound.trans ?_
        -- `W ≤ 2 (max A B q^k)^q (m+2)^{q/2}`
        set M := max A B
        have hM0 : 0 ≤ M := le_trans hD.hA (le_max_left _ _)
        have hAM : (A * q ^ k) ^ q ≤ (M * q ^ k) ^ q :=
          Real.rpow_le_rpow (mul_nonneg hD.hA hqk) (mul_le_mul_of_nonneg_right (le_max_left _ _)
            hqk) hq0
        have hBM : (B * q ^ k) ^ q ≤ (M * q ^ k) ^ q :=
          Real.rpow_le_rpow (mul_nonneg hD.hB hqk) (mul_le_mul_of_nonneg_right (le_max_right _ _)
            hqk) hq0
        have hMq : 0 ≤ (M * q ^ k) ^ q := Real.rpow_nonneg (mul_nonneg hM0 hqk) q
        have hWle : W ≤ 2 * ((M * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2)) := by
          rw [hW]
          nlinarith [mul_le_mul_of_nonneg_right hAM (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 2) ^ (q / 2)),
            mul_le_mul_of_nonneg_left hm2q hMq]
        have h338 : (338 : ℝ) ≤ 338 ^ q := by
          calc (338 : ℝ) = 338 ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ 338 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
        have hK : (6084 * M * q ^ k) ^ q = 338 ^ q * 18 ^ q * (M * q ^ k) ^ q := by
          rw [show (6084 : ℝ) * M * q ^ k = 338 * 18 * (M * q ^ k) by ring,
            Real.mul_rpow (by norm_num) (mul_nonneg hM0 hqk),
            Real.mul_rpow (by norm_num) (by norm_num)]
        rw [hK]
        have h18 : 0 ≤ (18 : ℝ) ^ q := by positivity
        have hprod : 0 ≤ (M * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) := by positivity
        calc 169 * 18 ^ q * W ≤ 169 * 18 ^ q * (2 * ((M * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2))) :=
              by gcongr
          _ = 338 * 18 ^ q * ((M * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2)) := by ring
          _ ≤ 338 ^ q * 18 ^ q * ((M * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2)) := by gcongr
          _ = 338 ^ q * 18 ^ q * (M * q ^ k) ^ q * ((m : ℝ) + 2) ^ (q / 2) := by ring

end LinftyIterationData

end Rigidity.Corrector
