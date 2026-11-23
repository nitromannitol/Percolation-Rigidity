import Rigidity.Proofs.Green.DarioGuTwoScaleEnergyDeriv

/-!
# The differential inequality of Step 2 of Proposition 4.3 of Dario–Gu

Step 2 of the proof of Proposition 4.3 of Dario–Gu (lines 2276-2331 of the source) tests the
equation `∂_s w = Δ w + G` against `ψ² w`. With `ψ' = ∂_s ψ`, the derivative of the weighted
energy `Σ_x (ψ w)²` (`hasDerivAt_tsum_sq_mul`) is bounded by
`2 Σ_x w² (ψ ψ' + κ) - 2 E(ψ w) + 2 Σ_x ψ² w G` (`tsum_energy_deriv_le`), where
`E(v) = Σ_x Σ_i a_i(x) (v(x + e_i) - v(x))²` is the energy of the open graph (`openEnergy`) and
`κ = edgeKappa ω ψ` collects the squared differences of `ψ` (the discrete product rule
`tsum_edge_energy_le`, in place of (4.27)). This is (4.28) before the terms of the source are
estimated.
-/

open LatticeProb LatticeProb.Percolation

namespace Rigidity.Green

/-- The energy `E(v) = Σ_x Σ_i a_i(x) (v(x + e_i) - v(x))²` of `v` on the open graph. -/
noncomputable def openEnergy (ω : Configuration 2) (v : Vertex 2 → ℝ) : ℝ :=
  ∑' x, ∑ i : Fin 2, openCond ω i x * (v (x + unit i) - v x) ^ 2

theorem summable_sq_mul_of_abs_le {c w : Vertex 2 → ℝ} {B : ℝ} (hc : ∀ x, |c x| ≤ B)
    (hw : Summable fun x => w x ^ 2) : Summable fun x => (c x * w x) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) (hw.mul_left (B ^ 2))
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← sq_abs (c x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hc x) 2

theorem summable_sq_openLaplacian (ω : Configuration 2) {w : Vertex 2 → ℝ}
    (hw : Summable fun x => w x ^ 2) : Summable fun x => openLaplacian ω w x ^ 2 := by
  have hD : Summable fun x => |w x| ^ 2 := by simpa only [sq_abs] using hw
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_) (summable_sq_nbrEnv hD)
  have h := abs_openLaplacian_le_nbrEnv ω (u := w) (D := fun x => |w x|) (fun _ => le_rfl) x
  rw [← sq_abs (openLaplacian ω w x)]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

theorem sq_sub_le_of_abs_le {ψ : Vertex 2 → ℝ} {B : ℝ} (hψ : ∀ x, |ψ x| ≤ B) (x z : Vertex 2) :
    (ψ z - ψ x) ^ 2 ≤ 4 * B ^ 2 := by
  have h1 := abs_le.1 (hψ x)
  have h2 := abs_le.1 (hψ z)
  nlinarith

theorem edgeKappa_nonneg (ω : Configuration 2) (ψ : Vertex 2 → ℝ) (x : Vertex 2) :
    0 ≤ edgeKappa ω ψ x := by
  unfold edgeKappa
  refine Finset.sum_nonneg fun i _ => ?_
  have := openCond_nonneg ω i x
  have := openCond_nonneg ω i (x - unit i)
  positivity

theorem edgeKappa_le_of_abs_le (ω : Configuration 2) {ψ : Vertex 2 → ℝ} {B : ℝ}
    (hψ : ∀ x, |ψ x| ≤ B) (x : Vertex 2) : edgeKappa ω ψ x ≤ 8 * B ^ 2 := by
  refine (edgeKappa_le ω ψ x).trans ?_
  simp only [Fin.sum_univ_two]
  have := sq_sub_le_of_abs_le hψ x (x + unit 0)
  have := sq_sub_le_of_abs_le hψ x (x - unit 0)
  have := sq_sub_le_of_abs_le hψ x (x + unit 1)
  have := sq_sub_le_of_abs_le hψ x (x - unit 1)
  linarith

/-- **The differential inequality of Step 2** (before the source terms are estimated): for `w`
and `G` square summable and `ψ`, `ψ'` bounded,
`Σ_x 2 (ψ w) (ψ' w + ψ (Δ w + G)) ≤ 2 Σ_x w² (ψ ψ' + κ) - 2 E(ψ w) + 2 Σ_x ψ² w G`. -/
theorem tsum_energy_deriv_le (ω : Configuration 2) {w ψ ψ' G : Vertex 2 → ℝ} {B B' : ℝ}
    (hw : Summable fun x => w x ^ 2) (hψ : ∀ x, |ψ x| ≤ B) (hψ' : ∀ x, |ψ' x| ≤ B')
    (hG : Summable fun x => G x ^ 2) :
    ∑' x, 2 * (ψ x * w x) * (ψ' x * w x + ψ x * (openLaplacian ω w x + G x)) ≤
      2 * ∑' x, w x ^ 2 * (ψ x * ψ' x + edgeKappa ω ψ x) -
        2 * openEnergy ω (fun x => ψ x * w x) + 2 * ∑' x, ψ x ^ 2 * w x * G x := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hψ 0)
  have hψw : Summable fun x => (ψ x * w x) ^ 2 := summable_sq_mul_of_abs_le hψ hw
  have hψ2 : ∀ x, |ψ x ^ 2| ≤ B ^ 2 := fun x => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hψ x) 2
  have hψ2w : Summable fun x => (ψ x ^ 2 * w x) ^ 2 := summable_sq_mul_of_abs_le hψ2 hw
  have hL := summable_sq_openLaplacian ω hw
  have s1 : Summable fun x => w x ^ 2 * (ψ x * ψ' x) := by
    refine Summable.of_norm_bounded (hw.mul_left (B * B')) fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (w x)), mul_comm (B * B')]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hψ x) (hψ' x) (abs_nonneg _) hB) (sq_nonneg _)
  have s2 : Summable fun x => openLaplacian ω w x * (ψ x ^ 2 * w x) := summable_mul_of_sq hL hψ2w
  have s3 : Summable fun x => ψ x ^ 2 * w x * G x := summable_mul_of_sq hψ2w hG
  have s4 : Summable fun x => w x ^ 2 * edgeKappa ω ψ x := by
    refine Summable.of_nonneg_of_le (fun x => mul_nonneg (sq_nonneg _) (edgeKappa_nonneg ω ψ x))
      (fun x => ?_) (hw.mul_left (8 * B ^ 2))
    rw [mul_comm (8 * B ^ 2)]
    exact mul_le_mul_of_nonneg_left (edgeKappa_le_of_abs_le ω hψ x) (sq_nonneg _)
  have sE : Summable fun x => ∑ i : Fin 2,
      openCond ω i x * (ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2 := by
    refine summable_sum fun i _ => ?_
    refine Summable.of_nonneg_of_le (fun x => mul_nonneg (openCond_nonneg ω i x) (sq_nonneg _))
      (fun x => mul_le_of_le_one_left (sq_nonneg _) (openCond_le_one ω i x))
      (summable_sq_sub (summable_sq_add_shift hψw (unit i)) hψw)
  have sK : Summable fun x => ∑ i : Fin 2, openCond ω i x *
      ((ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) := by
    refine summable_sum fun i _ => ?_
    refine Summable.of_nonneg_of_le (fun x => mul_nonneg (openCond_nonneg ω i x) (by positivity))
      (fun x => ?_) ((hw.add (summable_sq_add_shift hw (unit i))).mul_left (2 * B ^ 2))
    have hd := sq_sub_le_of_abs_le hψ x (x + unit i)
    have hw0 : 0 ≤ w x ^ 2 + w (x + unit i) ^ 2 := by positivity
    have hc0 := openCond_nonneg ω i x
    have hc1 := openCond_le_one ω i x
    have h1 : openCond ω i x * ((ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) ≤
        (ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2 :=
      mul_le_of_le_one_left (by positivity) hc1
    have h2 := mul_le_mul_of_nonneg_right hd hw0
    linarith
  have hE := tsum_edge_energy_le ω hw hψ
  have hK : ∑' x, ∑ i : Fin 2, openCond ω i x *
      ((ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) =
      ∑' x, w x ^ 2 * edgeKappa ω ψ x := tsum_edge_weight_eq ω hw hψ
  have hsplit : ∑' x, ∑ i : Fin 2, openCond ω i x *
        ((ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2 -
          (ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) =
      (∑' x, ∑ i : Fin 2,
        openCond ω i x * (ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2) -
      ∑' x, ∑ i : Fin 2, openCond ω i x *
        ((ψ (x + unit i) - ψ x) ^ 2 * (w x ^ 2 + w (x + unit i) ^ 2) / 2) := by
    rw [← sE.tsum_sub sK]
    refine tsum_congr fun x => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hEn : openEnergy ω (fun x => ψ x * w x) = ∑' x, ∑ i : Fin 2,
      openCond ω i x * (ψ (x + unit i) * w (x + unit i) - ψ x * w x) ^ 2 := rfl
  have hLHS : ∑' x, 2 * (ψ x * w x) * (ψ' x * w x + ψ x * (openLaplacian ω w x + G x)) =
      2 * ∑' x, w x ^ 2 * (ψ x * ψ' x) + 2 * ∑' x, openLaplacian ω w x * (ψ x ^ 2 * w x) +
        2 * ∑' x, ψ x ^ 2 * w x * G x := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
      ← (s1.mul_left 2).tsum_add (s2.mul_left 2),
      ← ((s1.mul_left 2).add (s2.mul_left 2)).tsum_add (s3.mul_left 2)]
    exact tsum_congr fun x => by ring
  have hRHS : ∑' x, w x ^ 2 * (ψ x * ψ' x + edgeKappa ω ψ x) =
      ∑' x, w x ^ 2 * (ψ x * ψ' x) + ∑' x, w x ^ 2 * edgeKappa ω ψ x := by
    rw [← s1.tsum_add s4]
    exact tsum_congr fun x => by ring
  rw [hLHS, hRHS]
  rw [hsplit, hK] at hE
  linarith

end Rigidity.Green
