import Rigidity.Proofs.Green.GeneralTwoScaleSource

/-!
# Steps 3-4 of Proposition 4.3 of Dario–Gu on `ℤ^d`: the estimate of the source term

Step 3 of the proof of Proposition 4.3 of Dario–Gu (lines 2333-2412 of the source), (4.32) after
Young's inequality, on `ℤ^d`, `d ≥ 2`, with the weight one: the `d²` components of the centered flux
are estimated by `neg_tsum_flux_leD`, and

`-θ^{-1} Σ_x v ξ ≤ E(v)/4 + (8r)^{-1} Σ_x v² + Q_ξ r^{α - d/2 - 2}`

(`neg_tsum_xiD_le`). With Step 4 (`summable_tsum_sq_clusterFD_le`,
`summable_tsum_sq_clusterFluxD_le`) and the splitting `tsum_source_le_of_splitD` this gives the
estimate of the source term used by the energy argument of Step 5:

`Σ_x v G(r) ≤ E(v) + (2r)^{-1} Σ_x v² + Q r^{α - d/2 - 2}`

for every square summable `v` vanishing off the cluster (`tsum_clusterSourceD_le`), when the
corrector grows like `B (√r + |x - y| + 2)^α` on the cluster (Proposition 2.12) and the weak norms of
the centered flux on the dyadic balls `𝒞 ∩ B_{2^{m+2}√r}(y)` are at most `C_f (2^{m+2}√r)^α`
(Proposition 2.13).
-/

open scoped Classical
open LatticeProb LatticeProb.Percolation Rigidity.External

namespace Rigidity.Green.GeneralDim

variable {d : ℕ}

theorem rpow_mul_rpow_div_sq {r a b : ℝ} (hr : 0 < r) :
    r ^ a * r ^ b / r ^ 2 = r ^ (a + b - 2) := by
  rw [← Real.rpow_add hr, ← Real.rpow_natCast r 2, ← Real.rpow_sub hr]
  norm_num

/-- **Step 3**: the estimate of the term `ξ` of the source, with Young's inequality. -/
theorem neg_tsum_xiD_le (hd : 2 ≤ d) {σ : ℝ} (hσ : 0 < σ) : ∃ L : ℝ, 0 < L ∧
    ∀ (ω : Configuration d) (K : OpenComponent ω) (y : Vertex d) (χ : Fin d → Vertex d → ℝ)
      (θ Cf B α r : ℝ) (v : Vertex d → ℝ), 0 < θ → 0 ≤ Cf → 0 ≤ B → 0 < α → α ≤ 1 → 1 ≤ r →
      (∀ z ∈ K.supp, ∀ k, |χ k z| ≤ B * (Real.sqrt r + ‖edzD z y‖ + 2) ^ α) →
      (∀ k i : Fin d, ∀ m : ℕ, WeakNormLeD ω (dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r))
        (centeredFluxD ω σ χ k i) (Cf * (2 ^ (m + 2) * Real.sqrt r) ^ α)) →
      Summable (fun x => v x ^ 2) → (∀ x, x ∉ K.supp → v x = 0) →
      Summable (fun x => v x * clusterXiD K σ χ r y x) ∧
        -(θ⁻¹ * ∑' x, v x * clusterXiD K σ χ r y x) ≤ openEnergyD ω v / 4 +
          1 / (8 * r) * ∑' x, v x ^ 2 + 3 * (θ⁻¹ * d ^ 2 * L * Cf) ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) := by
  obtain ⟨L, hL, hbound⟩ := neg_tsum_flux_leD hd hσ
  refine ⟨L, hL, fun ω K y χ θ Cf B α r v hθ hCf hB hα hα1 hr hχ hW hv hvK => ?_⟩
  have hr0 : 0 < r := by linarith
  set Fl : Fin d → Fin d → Vertex d → ℝ := fun k i x => centeredFluxD ω σ χ k i x *
    (fwdDiffD i (fwdDiffD k fun z => latticeGaussianD σ r z y) x * v x) with hFl
  have hGs : ∀ k i : Fin d, Summable fun x => |Fl k i x| := by
    intro k i
    have hsq := summable_sq_flux_coeffD K hσ hB hα1 hr hχ k i
    have hm := summable_mul_of_sqD hsq hv
    refine hm.abs.congr fun x => ?_
    simp only [hFl]
    by_cases hx : x ∈ K.supp
    · rw [if_pos hx, mul_assoc]
    · rw [if_neg hx, hvK x hx]
      simp
  have hsumm : ∀ k i : Fin d, Summable (Fl k i) := fun k i => (hGs k i).of_abs
  have hpt : ∀ x, v x * clusterXiD K σ χ r y x = ∑ k, ∑ i, Fl k i x := by
    intro x
    simp only [hFl, clusterXiD]
    split_ifs with hx
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [hvK x hx]
      simp
  have hsumξ : Summable fun x => v x * clusterXiD K σ χ r y x := by
    simp only [hpt]
    exact summable_sum fun k _ => summable_sum fun i _ => hsumm k i
  refine ⟨hsumξ, ?_⟩
  have htsum : ∑' x, v x * clusterXiD K σ χ r y x = ∑ k, ∑ i, ∑' x, Fl k i x := by
    rw [tsum_congr hpt, Summable.tsum_finsetSum fun k _ =>
      summable_sum fun i _ => hsumm k i]
    exact Finset.sum_congr rfl fun k _ => Summable.tsum_finsetSum fun i _ => hsumm k i
  rw [htsum]
  set U := Real.sqrt (∑' x, v x ^ 2) with hU
  set E := Real.sqrt (openEnergyD ω v) with hE
  set ρ := r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) with hρ
  set Z := L * Cf * r ^ (α / 2) * r ^ (-((d : ℝ) / 4)) *
    (U / (r * Real.sqrt r) + E / r) with hZ
  have hFk : ∀ k i : Fin d, -(∑' x, Fl k i x) ≤ Z := fun k i =>
    hbound ω K y χ k i Cf α r v hCf hα hα1 hr hv hvK (hW k i) (hGs k i)
  have hsumall : -(∑ k, ∑ i, ∑' x, Fl k i x) ≤ (d : ℝ) ^ 2 * Z := by
    rw [← Finset.sum_neg_distrib]
    calc ∑ k, -(∑ i, ∑' x, Fl k i x) = ∑ k, ∑ i, -(∑' x, Fl k i x) :=
          Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_neg_distrib]
      _ ≤ ∑ _k : Fin d, ∑ _i : Fin d, Z :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => hFk k i
      _ = (d : ℝ) ^ 2 * Z := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hθ0 : 0 ≤ θ⁻¹ := inv_nonneg.2 hθ.le
  have hstep : -(θ⁻¹ * ∑ k, ∑ i, ∑' x, Fl k i x) ≤ θ⁻¹ * ((d : ℝ) ^ 2 * Z) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hsumall hθ0
  refine hstep.trans ?_
  set A := θ⁻¹ * d ^ 2 * L * Cf with hA
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hEE : E ^ 2 = openEnergyD ω v := Real.sq_sqrt (openEnergyD_nonneg ω v)
  have hUU : U ^ 2 = ∑' x, v x ^ 2 := Real.sq_sqrt (tsum_nonneg fun x => sq_nonneg _)
  have hρ2 : ρ ^ 2 / r ^ 2 = r ^ (α - (d : ℝ) / 2 - 2) := by
    have e1 : (r ^ (-((d : ℝ) / 4))) ^ 2 = r ^ (-((d : ℝ) / 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      congr 1
      push_cast
      ring
    rw [hρ, mul_pow, sq_rpow_half hr0, e1, rpow_mul_rpow_div_sq hr0]
    congr 1
  have hZe : θ⁻¹ * ((d : ℝ) ^ 2 * Z) = A * ρ * (U / (r * Real.sqrt r)) + A * ρ * (E / r) := by
    rw [hZ, hA, hρ]
    ring
  rw [hZe]
  -- Young's inequality for the two terms
  have y1 : A * ρ * (E / r) ≤ E ^ 2 / 4 + A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) := by
    set z := A * ρ / r with hz
    have hz2 : z ^ 2 = A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) := by
      rw [hz, div_pow, mul_pow, mul_div_assoc, hρ2]
    have h := sq_nonneg (E / 2 - z)
    have e2 : A * ρ * (E / r) = E * z := by
      rw [hz]
      ring
    rw [e2, ← hz2]
    nlinarith
  have y2 : A * ρ * (U / (r * Real.sqrt r)) ≤
      1 / (8 * r) * U ^ 2 + 2 * A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) := by
    set w := A * ρ / (r * Real.sqrt r) with hw
    have hr3 : (r * Real.sqrt r) ^ 2 = r ^ 2 * r := by
      rw [mul_pow, Real.sq_sqrt hr0.le]
    have key : U * w ≤ 1 / (8 * r) * U ^ 2 + 2 * r * w ^ 2 := by
      have h := sq_nonneg (U - 4 * r * w)
      have e : 1 / (8 * r) * U ^ 2 + 2 * r * w ^ 2 - U * w = (U - 4 * r * w) ^ 2 / (8 * r) := by
        field_simp
        ring
      have h0 : 0 ≤ (U - 4 * r * w) ^ 2 / (8 * r) := by positivity
      linarith
    have e1 : A * ρ * (U / (r * Real.sqrt r)) = U * w := by
      rw [hw]
      ring
    have e2 : 2 * r * w ^ 2 = 2 * A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) := by
      rw [hw, div_pow, hr3, ← hρ2, mul_pow]
      field_simp
    rw [e1, ← e2]
    exact key
  rw [← hEE, ← hUU]
  have e3 : 3 * A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) =
      A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) + 2 * A ^ 2 * r ^ (α - (d : ℝ) / 2 - 2) := by ring
  rw [e3]
  linarith

/-- **The estimate of the source term (Steps 3-4)** for one configuration. -/
theorem tsum_clusterSourceD_le (hd : 2 ≤ d) {σ θ : ℝ} (hσ : 0 < σ) (hθ : 0 < θ) {B Cf α : ℝ}
    (hB : 0 ≤ B) (hCf : 0 ≤ Cf) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ (ω : Configuration d) (K : OpenComponent ω) (y : Vertex d)
      (χ : Fin d → Vertex d → ℝ) (r : ℝ) (v : Vertex d → ℝ), 1 ≤ r →
      (∀ z ∈ K.supp, ∀ k, |χ k z| ≤ B * (Real.sqrt r + ‖edzD z y‖ + 2) ^ α) →
      (∀ k i : Fin d, ∀ m : ℕ, WeakNormLeD ω (dgClusterBallD K y (2 ^ (m + 2) * Real.sqrt r))
        (centeredFluxD ω σ χ k i) (Cf * (2 ^ (m + 2) * Real.sqrt r) ^ α)) →
      Summable (fun x => v x ^ 2) → (∀ x, x ∉ K.supp → v x = 0) →
      ∑' x, v x * clusterSourceD K σ θ χ y r x ≤
        openEnergyD ω v + 1 / (2 * r) * ∑' x, v x ^ 2 + Q * r ^ (α - (d : ℝ) / 2 - 2) := by
  obtain ⟨L, hL, hxi⟩ := neg_tsum_xiD_le hd hσ
  set G := growthConstD d σ with hG
  have hG0 : 0 ≤ G := growthConstD_nonneg hσ
  set Qf := (σ / 2 * d * gaussConstD d σ 3 * (1 + d * B)) ^ 2 * G with hQf
  set QF := d * ((gaussConstD d σ 2 * (1 + d * B)) ^ 2 * G) with hQF
  set Qξ := 3 * (θ⁻¹ * d ^ 2 * L * Cf) ^ 2 with hQξ
  have hQf0 : 0 ≤ Qf := by positivity
  have hQF0 : 0 ≤ QF := by positivity
  have hQξ0 : 0 ≤ Qξ := by positivity
  refine ⟨2 * θ⁻¹ ^ 2 * Qf + θ⁻¹ ^ 2 * QF + Qξ, by positivity,
    fun ω K y χ r v hr hχ hW hv hvK => ?_⟩
  have hr0 : 0 < r := by linarith
  obtain ⟨hfs, hfb⟩ := summable_tsum_sq_clusterFD_le K hσ hr hα0.le hα1 hB hχ
  have hFs := fun i => (summable_tsum_sq_clusterFluxD_le K hσ hr hα0.le hα1 hB hχ i).1
  have hFb : ∑ i, ∑' x, clusterFluxD K σ χ r y i x ^ 2 ≤ QF * r ^ (α - (d : ℝ) / 2 - 2) := by
    calc ∑ i, ∑' x, clusterFluxD K σ χ r y i x ^ 2
        ≤ ∑ _i : Fin d, (gaussConstD d σ 2 * (1 + d * B)) ^ 2 * G *
            r ^ (α - (d : ℝ) / 2 - 2) := Finset.sum_le_sum fun i _ =>
          (summable_tsum_sq_clusterFluxD_le K hσ hr hα0.le hα1 hB hχ i).2
      _ = QF * r ^ (α - (d : ℝ) / 2 - 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hQF]
          ring
  have hFo : ∀ i x, clusterFluxD K σ χ r y i x = openCondD ω i x * clusterFluxD K σ χ r y i x := by
    intro i x
    unfold clusterFluxD stepOneFD
    split_ifs
    · rw [← mul_assoc, ← sq, openCondD_sq]
    · rw [mul_zero]
  obtain ⟨hξs, hξ⟩ := hxi ω K y χ θ Cf B α r v hθ hCf hB hα0 hα1 hr hχ hW hv hvK
  have hfb' : ∑' x, clusterFD K σ χ r y x ^ 2 ≤ Qf * r ^ (α - (d : ℝ) / 2 - 2 - 1) := by
    rw [show α - (d : ℝ) / 2 - 2 - 1 = α - (d : ℝ) / 2 - 3 by ring]
    exact hfb
  have h := tsum_source_le_of_splitD ω (β := α - (d : ℝ) / 2 - 2) (Qξ := Qξ) hθ hr0 hv hfs hfb'
    hFs hFo hFb hξs hξ
  have e : ∑' x, v x * clusterSourceD K σ θ χ y r x =
      θ⁻¹ * ∑' x, v x * (clusterFD K σ χ r y x - ∑ i, (clusterFluxD K σ χ r y i (x - Pi.single i 1) -
        clusterFluxD K σ χ r y i x) - clusterXiD K σ χ r y x) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [clusterSourceD_eq_split]
    ring
  rw [e]
  exact h

end Rigidity.Green.GeneralDim
