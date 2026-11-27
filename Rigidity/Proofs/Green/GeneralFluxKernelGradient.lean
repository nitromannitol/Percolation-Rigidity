import Rigidity.Proofs.Green.DarioGuFluxKernelGradient
import Rigidity.Proofs.Poincare.GeneralHeatGradient

/-!
# The `ℓ¹` norm of the gradient of the heat kernel of `ℤ^d`

The extension of `DarioGuFluxKernelGradient.lean` from `ℤ²` to `ℤ^d`:

* `tsum_pi_prod`: `Σ_{x : Fin n → ℤ} Π_i f_i(x_i) = Π_i Σ_k f_i(k)` in `ℝ≥0∞`;
* `exists_tsum_ofReal_abs_zdHeat_grad_le`: `Σ_v |Φ_t(0, v + e_j) - Φ_t(0, v)| ≤ C/√t` for
  `t > 0`, by the product form `Φ_t(0, v) = Π_i q_{2t}(v_i)` (`zdHeat_eq_prod_lineKernel`) and the
  one-dimensional bound `exists_tsum_ofReal_abs_lineKernel_sub_le`;
* `heatGradKernelD j a b v = ∫_a^b |Φ_t(0, v + e_j) - Φ_t(0, v)| dt` and its total mass
  `(b - a) C/√a` (`tsum_heatGradKernelD_le`), or `2(b - a)` (`tsum_heatGradKernelD_le_two`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation LatticeProb.ContinuousTime
  Rigidity.Poincare.GeneralDim
open scoped ENNReal

namespace Rigidity.Green.GeneralFlux

/-- `Σ_{x : Fin n → ℤ} Π_i f_i(x_i) = Π_i Σ_k f_i(k)`. -/
theorem tsum_pi_prod : ∀ (n : ℕ) (f : Fin n → ℤ → ℝ≥0∞),
    ∑' x : Fin n → ℤ, ∏ i, f i (x i) = ∏ i, ∑' k, f i k
  | 0, f => by simp
  | n + 1, f => by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq]
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [ENNReal.tsum_prod (f := fun (a : ℤ) (b : Fin n → ℤ) => f 0 a * ∏ x, f x.succ (b x))]
      simp_rw [ENNReal.tsum_mul_left, tsum_pi_prod n (fun i => f i.succ), ENNReal.tsum_mul_right]

variable {d : ℕ} [NeZero d]

theorem zdHeat_zero_left_eq (t : ℝ) (v : Vertex d) :
    zdHeat d t 0 v = ∏ i, lineKernel (2 * t) (v i) := by
  rw [zdHeat_eq_prod_lineKernel, sub_zero]

/-- **The gradient of the heat kernel of `ℤ^d` has `ℓ¹` norm `≤ C/√t`.** -/
theorem exists_tsum_ofReal_abs_zdHeat_grad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ j : Fin d,
      ∑' v : Vertex d, ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| ≤
        ENNReal.ofReal (C / Real.sqrt t) := by
  obtain ⟨C₁, hC₁, h1⟩ := exists_tsum_ofReal_abs_lineKernel_sub_le
  refine ⟨max C₁ 2, by positivity, fun t ht j => ?_⟩
  have hst : Real.sqrt t ≤ Real.sqrt (2 * t) := Real.sqrt_le_sqrt (by linarith)
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hq0 : ∀ k, 0 ≤ lineKernel (2 * t) k := fun k =>
    Rigidity.Poincare.lineKernel_nonneg (by linarith) k
  have hm := tsum_ofReal_lineKernel_le_one (by linarith : 0 ≤ 2 * t)
  set F : Fin d → ℤ → ℝ≥0∞ := fun i n =>
    if i = j then ENNReal.ofReal |lineKernel (2 * t) (n + 1) - lineKernel (2 * t) n| else ENNReal.ofReal (lineKernel (2 * t) n) with hF
  -- the gradient as a product
  have hpt : ∀ v : Vertex d, ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| =
      ∏ i, F i (v i) := by
    intro v
    rw [zdHeat_zero_left_eq, zdHeat_zero_left_eq,
      ← Finset.mul_prod_erase _ (fun i => lineKernel (2 * t) ((v + unit j) i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun i => lineKernel (2 * t) (v i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun i => F i (v i)) (Finset.mem_univ j)]
    have hrest : ∏ i ∈ Finset.univ.erase j, lineKernel (2 * t) ((v + unit j) i) =
        ∏ i ∈ Finset.univ.erase j, lineKernel (2 * t) (v i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp [LatticeProb.unit, hij]
    have hj : (v + unit j) j = v j + 1 := by simp [LatticeProb.unit]
    have hFj : F j (v j) =
        ENNReal.ofReal |lineKernel (2 * t) (v j + 1) - lineKernel (2 * t) (v j)| := by
      simp [hF]
    have hFrest : ∏ i ∈ Finset.univ.erase j, F i (v i) =
        ENNReal.ofReal (∏ i ∈ Finset.univ.erase j, lineKernel (2 * t) (v i)) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ => hq0 _]
      refine Finset.prod_congr rfl fun i hi => ?_
      simp [hF, Finset.ne_of_mem_erase hi]
    rw [hrest, hj, hFj, hFrest]
    rw [← sub_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hq0 _),
      ENNReal.ofReal_mul (abs_nonneg _)]
  have hprod : ∑' v : Vertex d, ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| ≤
      ∑' n : ℤ, ENNReal.ofReal |lineKernel (2 * t) (n + 1) - lineKernel (2 * t) n| := by
    rw [tsum_congr hpt, tsum_pi_prod d F, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hFj : ∑' n, F j n = ∑' n : ℤ, ENNReal.ofReal |lineKernel (2 * t) (n + 1) - lineKernel (2 * t) n| := by simp [hF]
    have hle : ∏ i ∈ Finset.univ.erase j, ∑' n, F i n ≤ 1 := by
      refine Finset.prod_le_one' fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hF, if_neg hij]
      exact hm
    rw [hFj]
    calc (∑' n : ℤ, ENNReal.ofReal |lineKernel (2 * t) (n + 1) - lineKernel (2 * t) n|) * ∏ i ∈ Finset.univ.erase j, ∑' n, F i n
        ≤ (∑' n : ℤ, ENNReal.ofReal |lineKernel (2 * t) (n + 1) - lineKernel (2 * t) n|) * 1 :=
          mul_le_mul_right hle _
      _ = _ := mul_one _
  refine hprod.trans ?_
  rcases le_or_gt 1 (2 * t) with h2t | h2t
  · refine (h1 (2 * t) h2t).trans (ENNReal.ofReal_le_ofReal ?_)
    calc C₁ / Real.sqrt (2 * t) ≤ C₁ / Real.sqrt t :=
          div_le_div_of_nonneg_left hC₁.le hsq0 hst
      _ ≤ max C₁ 2 / Real.sqrt t :=
          div_le_div_of_nonneg_right (le_max_left _ _) hsq0.le
  · have hsh : ∑' n : ℤ, ENNReal.ofReal (lineKernel (2 * t) (n + 1)) = ∑' n : ℤ, ENNReal.ofReal (lineKernel (2 * t) n) :=
      (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => ENNReal.ofReal (lineKernel (2 * t) n))
    calc ∑' n : ℤ, ENNReal.ofReal |lineKernel (2 * t) (n + 1) - lineKernel (2 * t) n|
        ≤ ∑' n : ℤ, (ENNReal.ofReal (lineKernel (2 * t) (n + 1)) + ENNReal.ofReal (lineKernel (2 * t) n)) :=
          ENNReal.tsum_le_tsum fun n => by
            rw [← ENNReal.ofReal_add (hq0 _) (hq0 _)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_le]
            constructor <;> linarith [hq0 n, hq0 (n + 1)]
      _ = ∑' n : ℤ, ENNReal.ofReal (lineKernel (2 * t) (n + 1)) + ∑' n : ℤ, ENNReal.ofReal (lineKernel (2 * t) n) :=
          ENNReal.tsum_add
      _ ≤ 1 + 1 := by rw [hsh]; exact add_le_add hm hm
      _ = ENNReal.ofReal 2 := by norm_num
      _ ≤ ENNReal.ofReal (max C₁ 2 / Real.sqrt t) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 (by linarith)
          rw [le_div_iff₀ hsq0]
          nlinarith [le_max_right C₁ 2]

/-! ### The time-integrated kernel -/

/-- `∫_a^b |Φ_t(0, v + e_j) - Φ_t(0, v)| dt` on `ℤ^d`. -/
noncomputable def heatGradKernelD (j : Fin d) (a b : ℝ) (v : Vertex d) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioc a b, ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v|

theorem measurable_ofReal_abs_zdHeat_grad (j : Fin d) (v : Vertex d) :
    Measurable fun t => ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| :=
  ENNReal.measurable_ofReal.comp
    (((continuous_zdHeat 0 _).sub (continuous_zdHeat 0 _)).abs.measurable)

theorem tsum_heatGradKernelD_eq (j : Fin d) (a b : ℝ) :
    ∑' v, heatGradKernelD j a b v = ∫⁻ t in Set.Ioc a b, ∑' v : Vertex d,
      ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| :=
  (lintegral_tsum fun v => (measurable_ofReal_abs_zdHeat_grad j v).aemeasurable).symm

/-- **The mass of the time-integrated kernel**, `(b - a) C/√a`. -/
theorem tsum_heatGradKernelD_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∀ j : Fin d, ∑' v : Vertex d,
      ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| ≤
        ENNReal.ofReal (C / Real.sqrt t))
    {a b : ℝ} (ha : 0 < a) (j : Fin d) :
    ∑' v, heatGradKernelD j a b v ≤ ENNReal.ofReal ((b - a) * (C / Real.sqrt a)) := by
  rw [tsum_heatGradKernelD_eq]
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  calc ∫⁻ t in Set.Ioc a b, ∑' v : Vertex d,
        ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v|
      ≤ ∫⁻ _ in Set.Ioc a b, ENNReal.ofReal (C / Real.sqrt a) := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        have ht0 : 0 < t := ha.trans ht.1
        refine (hC t ht0 j).trans (ENNReal.ofReal_le_ofReal ?_)
        exact div_le_div_of_nonneg_left hC0 hsa (Real.sqrt_le_sqrt ht.1.le)
    _ = ENNReal.ofReal (C / Real.sqrt a) * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal ((b - a) * (C / Real.sqrt a)) := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_comm]

/-- **The mass of the time-integrated kernel**, `2(b - a)`. -/
theorem tsum_heatGradKernelD_le_two {a b : ℝ} (ha : 0 ≤ a) (j : Fin d) :
    ∑' v, heatGradKernelD j a b v ≤ ENNReal.ofReal (2 * (b - a)) := by
  rw [tsum_heatGradKernelD_eq]
  calc ∫⁻ t in Set.Ioc a b, ∑' v : Vertex d,
        ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v|
      ≤ ∫⁻ _ in Set.Ioc a b, (2 : ℝ≥0∞) := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        have ht0 : 0 ≤ t := ha.trans ht.1.le
        have hsh : ∑' v : Vertex d, ENNReal.ofReal (zdHeat d t 0 (v + unit j)) =
            ∑' v : Vertex d, ENNReal.ofReal (zdHeat d t 0 v) :=
          (Equiv.addRight (unit j)).tsum_eq (fun v => ENNReal.ofReal (zdHeat d t 0 v))
        have hm : ∑' v : Vertex d, ENNReal.ofReal (zdHeat d t 0 v) = 1 :=
          tsum_ofReal_zdHeat ht0 0
        calc ∑' v : Vertex d, ENNReal.ofReal |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v|
            ≤ ∑' v : Vertex d, (ENNReal.ofReal (zdHeat d t 0 (v + unit j)) +
                ENNReal.ofReal (zdHeat d t 0 v)) :=
              ENNReal.tsum_le_tsum fun v => by
                have h1 := zdHeat_nonneg ht0 0 (v + unit j)
                have h2 := zdHeat_nonneg ht0 (0 : Vertex d) v
                rw [← ENNReal.ofReal_add h1 h2]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [abs_le]
                constructor <;> linarith
          _ = 2 := by rw [ENNReal.tsum_add, hsh, hm]; norm_num
    _ = 2 * ENNReal.ofReal (b - a) := by rw [setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal (2 * (b - a)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

end Rigidity.Green.GeneralFlux
