import Rigidity.Proofs.Green.GaussFlowTailD

/-!
# The displacement of the heat kernel on `ℤ^d` from the Carne–Varopoulos bound

If `p_u(w, x) ≤ C e^{-|x - w|²/(Cu)} + C e^{-|x - w|/C}` for every `x` (the two branches of the
Carne–Varopoulos bound, Dario–Gu, Proposition 2.15), then for `u ≥ 1` and `L ≥ 0`

  `Σ_{|x - w| ≥ L} p_u(w, x) ≤ C (2πCu)^{d/2} M_C e^{-L²/(2Cu)} + C E_C e^{-L/(2C)}`

(`tsum_far_vsrwHeat_le`), with the lattice sums `M_C` of the Gaussian (`gaussMassBoundD`) and
`E_C = (Σ_{n ∈ ℤ} e^{-|n|/(2Cd)})^d` of the exponential (`tsum_exp_neg_norm_edzD_le`).
-/

open scoped Classical
open LatticeProb.Percolation

namespace Rigidity.Green

local notation "ldist" => Rigidity.WeakPoincare.latticeDist

theorem summable_exp_neg_mul_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * |(n : ℝ)|) := by
  have hq : Real.exp (-c) < 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hg : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hq
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    ring

variable {d : ℕ}

theorem edzD_apply (x y : Vertex d) (i : Fin d) : edzD x y i = (x i : ℝ) - y i := by
  simp only [PiLp.sub_apply]
  rfl

theorem abs_coord_le_norm_edzD (z w : Vertex d) (i : Fin d) :
    |((z i : ℤ) : ℝ)| ≤ ‖edzD (z + w) w‖ := by
  have h := PiLp.norm_apply_le (edzD (z + w) w) i
  rw [edzD_apply, Real.norm_eq_abs] at h
  simpa using h

/-- The exponential sum over the lattice: `Σ_x e^{-c|x - w|} ≤ (Σ_n e^{-(c/d)|n|})^d`. -/
theorem tsum_exp_neg_norm_edzD_le [NeZero d] {c : ℝ} (hc : 0 < c) (w : Vertex d) :
    Summable (fun x => Real.exp (-c * ‖edzD x w‖)) ∧
      ∑' x, Real.exp (-c * ‖edzD x w‖) ≤
        (∑' n : ℤ, Real.exp (-(c / d) * |(n : ℝ)|)) ^ d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hcd : 0 < c / d := div_pos hc hd
  set g : ℤ → ℝ := fun n => Real.exp (-(c / d) * |(n : ℝ)|) with hg
  have hprod := hasSum_prod_pi (g := g) (fun n => (Real.exp_pos _).le)
    (summable_exp_neg_mul_abs_int hcd) d
  have hpt : ∀ z : Vertex d, Real.exp (-c * ‖edzD (z + w) w‖) ≤ ∏ i, g (z i) := by
    intro z
    simp only [hg]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [← Finset.mul_sum, neg_mul, neg_mul, neg_le_neg_iff]
    have hsum : ∑ i : Fin d, |((z i : ℤ) : ℝ)| ≤ d * ‖edzD (z + w) w‖ := by
      calc ∑ i : Fin d, |((z i : ℤ) : ℝ)| ≤ ∑ _i : Fin d, ‖edzD (z + w) w‖ :=
            Finset.sum_le_sum fun i _ => abs_coord_le_norm_edzD z w i
        _ = d * ‖edzD (z + w) w‖ := by simp
    calc c / d * ∑ i, |((z i : ℤ) : ℝ)| ≤ c / d * (d * ‖edzD (z + w) w‖) :=
          mul_le_mul_of_nonneg_left hsum hcd.le
      _ = c * ‖edzD (z + w) w‖ := by field_simp
  have hs : Summable fun z : Vertex d => Real.exp (-c * ‖edzD (z + w) w‖) :=
    hprod.summable.of_nonneg_of_le (fun z => (Real.exp_pos _).le) hpt
  have hs' : Summable fun x => Real.exp (-c * ‖edzD x w‖) :=
    (Equiv.addRight w).summable_iff.1 hs
  refine ⟨hs', ?_⟩
  calc ∑' x, Real.exp (-c * ‖edzD x w‖) = ∑' z : Vertex d, Real.exp (-c * ‖edzD (z + w) w‖) :=
        ((Equiv.addRight w).tsum_eq (fun x => Real.exp (-c * ‖edzD x w‖))).symm
    _ ≤ ∑' z : Vertex d, ∏ i, g (z i) := hs.tsum_le_tsum hpt hprod.summable
    _ = _ := hprod.tsum_eq

/-- `E_C = (Σ_{n ∈ ℤ} e^{-|n|/(2Cd)})^d`. -/
noncomputable def expMassBoundD (d : ℕ) (C : ℝ) : ℝ :=
  (∑' n : ℤ, Real.exp (-(1 / (2 * C) / d) * |(n : ℝ)|)) ^ d

theorem expMassBoundD_nonneg (d : ℕ) (C : ℝ) : 0 ≤ expMassBoundD d C :=
  pow_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le) d

variable [NeZero d] {ω : Configuration d}

/-- **The displacement of the heat kernel** from the two branches of the Carne–Varopoulos
bound. -/
theorem tsum_far_vsrwHeat_le {w : Vertex d} {u L C : ℝ} (hu : 1 ≤ u) (hL : 0 ≤ L) (hC : 0 < C)
    (hcv : ∀ x, vsrwHeat (openGraph ω) (2 * d) u w x ≤
      C * Real.exp (-(ldist x w ^ 2 / (C * u))) + C * Real.exp (-(ldist x w / C))) :
    ∑' x, (if L ≤ ldist x w then vsrwHeat (openGraph ω) (2 * d) u w x else 0) ≤
      C * (2 * Real.pi * C * u) ^ ((d : ℝ) / 2) * gaussMassBoundD d C *
          Real.exp (-(L ^ 2 / (2 * C * u))) +
        C * expMassBoundD d C * Real.exp (-(L / (2 * C))) := by
  have hD := two_mul_pos_d (d := d)
  have hdeg := openGraph_degree_le ω
  have hu0 : 0 < u := by linarith
  have hp0 : ∀ x, 0 ≤ vsrwHeat (openGraph ω) (2 * d) u w x :=
    fun x => vsrwHeat_nonneg hD hdeg hu0.le w x
  set K₁ : ℝ := (2 * Real.pi * C * u) ^ ((d : ℝ) / 2) with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  -- the Gaussian branch as a Gaussian kernel of variance `C`
  have hgauss : ∀ x, Real.exp (-(ldist x w ^ 2 / (2 * C * u))) =
      K₁ * gaussianHeatD d C u (edzD x w) := by
    intro x
    unfold gaussianHeatD
    rw [← mul_assoc, hK₁, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero,
      one_mul, latticeDist_eq_norm_edzD]
  have hbound : ∀ x, (if L ≤ ldist x w then vsrwHeat (openGraph ω) (2 * d) u w x else 0) ≤
      C * Real.exp (-(L ^ 2 / (2 * C * u))) * (K₁ * gaussianHeatD d C u (edzD x w)) +
        C * Real.exp (-(L / (2 * C))) * Real.exp (-(1 / (2 * C)) * ‖edzD x w‖) := by
    intro x
    have hr0 : 0 ≤ ldist x w := Rigidity.WeakPoincare.latticeDist_nonneg x w
    have hg0 : 0 ≤ gaussianHeatD d C u (edzD x w) :=
      gaussianHeatD_nonneg' C u (by positivity) _
    split_ifs with hLx
    · refine (hcv x).trans (add_le_add ?_ ?_)
      · rw [← hgauss, mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le
        have hL2 : L ^ 2 ≤ ldist x w ^ 2 := pow_le_pow_left₀ hL hLx 2
        have hCu : 0 < 2 * C * u := by positivity
        have e1 : ldist x w ^ 2 / (C * u) = 2 * (ldist x w ^ 2 / (2 * C * u)) := by
          field_simp
        have e3 : L ^ 2 / (2 * C * u) ≤ ldist x w ^ 2 / (2 * C * u) :=
          div_le_div_of_nonneg_right hL2 hCu.le
        rw [e1]
        linarith
      · rw [mul_assoc, ← Real.exp_add, ← latticeDist_eq_norm_edzD]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le
        have e1 : ldist x w / C = 2 * (ldist x w / (2 * C)) := by field_simp
        have e2 : -(1 / (2 * C)) * ldist x w = -(ldist x w / (2 * C)) := by ring
        have e3 : L / (2 * C) ≤ ldist x w / (2 * C) :=
          div_le_div_of_nonneg_right hLx (by positivity)
        rw [e1, e2]
        linarith
    · positivity
  obtain ⟨hes, hel⟩ := tsum_exp_neg_norm_edzD_le (d := d) (c := 1 / (2 * C)) (by positivity) w
  have hgs := summable_gaussianHeatD (d := d) hC hu0 w
  have hR : Summable fun x =>
      C * Real.exp (-(L ^ 2 / (2 * C * u))) * (K₁ * gaussianHeatD d C u (edzD x w)) +
        C * Real.exp (-(L / (2 * C))) * Real.exp (-(1 / (2 * C)) * ‖edzD x w‖) :=
    ((hgs.mul_left K₁).mul_left _).add (hes.mul_left _)
  have hT : Summable fun x => (if L ≤ ldist x w then vsrwHeat (openGraph ω) (2 * d) u w x else 0) :=
    hR.of_nonneg_of_le (fun x => by split_ifs; exacts [hp0 x, le_rfl]) hbound
  calc _ ≤ ∑' x, (C * Real.exp (-(L ^ 2 / (2 * C * u))) * (K₁ * gaussianHeatD d C u (edzD x w)) +
        C * Real.exp (-(L / (2 * C))) * Real.exp (-(1 / (2 * C)) * ‖edzD x w‖)) :=
        hT.tsum_le_tsum hbound hR
    _ = C * Real.exp (-(L ^ 2 / (2 * C * u))) * (K₁ * ∑' x, gaussianHeatD d C u (edzD x w)) +
        C * Real.exp (-(L / (2 * C))) * ∑' x, Real.exp (-(1 / (2 * C)) * ‖edzD x w‖) := by
        rw [((hgs.mul_left K₁).mul_left _).tsum_add (hes.mul_left _), tsum_mul_left, tsum_mul_left,
          tsum_mul_left]
    _ ≤ C * Real.exp (-(L ^ 2 / (2 * C * u))) * (K₁ * gaussMassBoundD d C) +
        C * Real.exp (-(L / (2 * C))) * expMassBoundD d C := by
        gcongr
        · exact tsum_gaussianHeatD_le hC hu w
        · exact hel
    _ = _ := by ring

end Rigidity.Green
