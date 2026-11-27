import Rigidity.Proofs.Green.GeneralFluxHeatDifference
import Rigidity.Proofs.Green.GeneralFluxMoments
import Rigidity.Proofs.Corrector.GeneralPoincareMoments
import Rigidity.Proofs.Green.DarioGuFluxDyadic

/-!
# The dyadic heat decomposition of a pairing on `ℤ^d`

The lattice form, with dyadic heat times, of the multiscale Poincaré inequality (D.28) of
Armstrong, Kuusi and Mourrat that Dario–Gu use for the estimate (eq.gsmallH-1) (Appendix B). For
`f` summable against every heat kernel and `w` vanishing off a finite set `S`, with
`t_j = 2·4^j`,

`Σ_S f w = Σ_S Φ_{t_J} f w - Σ_{j<J} Σ_u Φ_{4^j} f(u) (Φ_{7·4^j} w - Φ_{4^j} w)(u)
  - Σ_u f(u) (Φ_2 w - w)(u)`,

and each term is bounded by the Cauchy–Schwarz inequality of `DarioGuFluxHeatDifference`
(`ofReal_abs_sum_mul_le_dyadic`): the pairing is at most `Y ‖w‖_{ℓ²(S)} + Z ‖∇w‖_{ℓ²(T)}` with
`Y = ‖Φ_{t_J} f‖_{ℓ²(S)}` and `Z` the sum over the dyadic times of the weighted `ℓ²` norms of the
heat averages of `f` times `√(6 C 2^j)` (and `2` for the first step).

Moments with polynomial growth (`GrowthMomentsD`) pass to the square root of a weighted sum of
squares (`growthMoments_sqrt_weighted_tsum`, by Jensen's inequality) and to finite sums
(`GrowthMomentsD.finsetSum`).
-/

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.Poincare.GeneralDim Rigidity.Corrector
open scoped ENNReal Classical

namespace Rigidity.Green.GeneralFlux

variable {d : ℕ} [NeZero d] {p : unitInterval}

/-! ### Moments -/

omit [NeZero d] in
/-- **Moments of the square root of a weighted sum of squares.** -/
theorem growthMoments_sqrt_weighted_tsum {X : Vertex d → Configuration d → ℝ}
    (hXm : ∀ u, Measurable (X u)) {B κ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hX : ∀ u, GrowthMomentsD p (fun ω => ENNReal.ofReal |X u ω|) B κ)
    {m : Vertex d → ℝ≥0∞} {M : ℝ} (hM : 0 ≤ M) (hm : ∑' u, m u ≤ ENNReal.ofReal M) :
    GrowthMomentsD p (fun ω => (∑' u, ENNReal.ofReal (X u ω ^ 2) * m u) ^ (1 / 2 : ℝ))
      (Real.sqrt M * B * 2 ^ κ) κ := by
  set μ := latticeBondLaw d p
  set W : Configuration d → ℝ≥0∞ := fun ω => ∑' u, ENNReal.ofReal (X u ω ^ 2) * m u with hW
  have hWm : Measurable W :=
    Measurable.tsum fun u => ((hXm u).pow_const 2).ennreal_ofReal.mul_const _
  have hmt : ∀ u, m u ≠ ⊤ := fun u =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((ENNReal.le_tsum u).trans hm)
  have hκ1 : ∀ q : ℝ, 1 ≤ q → 1 ≤ q ^ κ := fun q hq => Real.one_le_rpow hq hκ
  -- the moments of order `q ≥ 2`
  have hbig : ∀ q : ℝ, 2 ≤ q → ∫⁻ ω, W ω ^ (q / 2) ∂μ ≤
      ENNReal.ofReal ((Real.sqrt M * B * q ^ κ) ^ q) := by
    intro q hq
    have hq0 : 0 < q := by linarith
    have ha : 1 ≤ q / 2 := by linarith
    have hpt : ∀ ω, W ω ^ (q / 2) ≤
        (∑' u, ENNReal.ofReal |X u ω| ^ q * m u) * ENNReal.ofReal M ^ (q / 2 - 1) := by
      intro ω
      have h := lintegral_mul_rpow_le (μ := Measure.count)
        (g := fun u => ENNReal.ofReal (X u ω ^ 2)) (w := m)
        (Measurable.of_discrete).aemeasurable (Measurable.of_discrete).aemeasurable hmt ha
      simp only [lintegral_count] at h
      refine h.trans (mul_le_mul' (le_of_eq ?_) (ENNReal.rpow_le_rpow hm (by linarith)))
      refine tsum_congr fun u => ?_
      congr 1
      rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul]
      congr 1
      push_cast
      ring
    have hXq : ∀ u, Measurable fun ω => ENNReal.ofReal |X u ω| ^ q := fun u =>
      ((hXm u).abs.ennreal_ofReal).pow_const q
    calc ∫⁻ ω, W ω ^ (q / 2) ∂μ
        ≤ ∫⁻ ω, (∑' u, ENNReal.ofReal |X u ω| ^ q * m u) * ENNReal.ofReal M ^ (q / 2 - 1) ∂μ :=
          lintegral_mono hpt
      _ = (∑' u, (∫⁻ ω, ENNReal.ofReal |X u ω| ^ q ∂μ) * m u) *
            ENNReal.ofReal M ^ (q / 2 - 1) := by
          rw [lintegral_mul_const _ (Measurable.tsum fun u => (hXq u).mul_const _),
            lintegral_tsum fun u => ((hXq u).mul_const _).aemeasurable]
          congr 1
          exact tsum_congr fun u => lintegral_mul_const _ (hXq u)
      _ ≤ (∑' u, ENNReal.ofReal ((B * q ^ κ) ^ q) * m u) * ENNReal.ofReal M ^ (q / 2 - 1) :=
          mul_le_mul_left (ENNReal.tsum_le_tsum fun u => mul_le_mul_left (hX u q (by linarith))
            _) _
      _ = ENNReal.ofReal ((B * q ^ κ) ^ q) * (∑' u, m u) * ENNReal.ofReal M ^ (q / 2 - 1) := by
          rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal ((B * q ^ κ) ^ q) * ENNReal.ofReal M * ENNReal.ofReal M ^ (q / 2 - 1) :=
          mul_le_mul_left (mul_le_mul_right hm _) _
      _ = ENNReal.ofReal ((Real.sqrt M * B * q ^ κ) ^ q) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hM (by linarith), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have e1 : M * M ^ (q / 2 - 1) = M ^ (q / 2) := by
            rw [← Real.rpow_one_add' hM (ne_of_gt (by linarith))]
            congr 1
            ring
          have e2 : M ^ (q / 2) = Real.sqrt M ^ q := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hM]
            congr 1
            ring
          rw [show Real.sqrt M * B * q ^ κ = Real.sqrt M * (B * q ^ κ) by ring,
            Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), ← e2, ← e1]
          ring
  intro q hq
  have hq0 : 0 < q := by linarith
  have hY : ∀ ω, ((W ω) ^ (1 / 2 : ℝ)) ^ q = W ω ^ (q / 2) := fun ω => by
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  change ∫⁻ ω, (W ω ^ (1 / 2 : ℝ)) ^ q ∂μ ≤ _
  simp only [hY]
  rcases le_or_gt 2 q with h2 | h2
  · refine (hbig q h2).trans (ENNReal.ofReal_le_ofReal ?_)
    refine Real.rpow_le_rpow (by positivity) ?_ hq0.le
    have h1 : (1 : ℝ) ≤ 2 ^ κ := Real.one_le_rpow (by norm_num) hκ
    have h0 : 0 ≤ Real.sqrt M * B * q ^ κ := by positivity
    nlinarith
  · have hle := GeneralDim.lintegral_rpow_le_rpow_lintegral (p := p) hWm.aemeasurable (a := q / 2)
      (by linarith) (by linarith)
    have h22 := hbig 2 le_rfl
    simp only [div_self (two_ne_zero' ℝ), ENNReal.rpow_one] at h22
    refine hle.trans ((ENNReal.rpow_le_rpow h22 (by linarith)).trans ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.rpow_mul (by positivity), show (2 : ℝ) * (q / 2) = q by ring]
    refine Real.rpow_le_rpow (by positivity) ?_ hq0.le
    have h1 : (1 : ℝ) ≤ q ^ κ := hκ1 q hq
    have h0 : 0 ≤ Real.sqrt M * B * 2 ^ κ := by positivity
    nlinarith

omit [NeZero d] in
/-- **Moments of a finite sum.** -/
theorem GrowthMomentsD.finsetSum {ι : Type*} (s : Finset ι) {X : ι → Configuration d → ℝ≥0∞}
    (hXm : ∀ i, Measurable (X i)) {B κ : ℝ} (hB : 0 ≤ B)
    (hX : ∀ i ∈ s, GrowthMomentsD p (X i) B κ) :
    GrowthMomentsD p (fun ω => ∑ i ∈ s, X i ω) (s.card * B) κ := by
  intro q hq
  have hq0 : 0 < q := by linarith
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos hq0, lintegral_zero]
    exact bot_le
  have hc0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hcq : ((s.card : ℝ≥0∞)) ^ (q - 1) = ENNReal.ofReal ((s.card : ℝ) ^ (q - 1)) := by
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg hc0 (by linarith)]
  calc ∫⁻ ω, (∑ i ∈ s, X i ω) ^ q ∂latticeBondLaw d p
      ≤ ∫⁻ ω, (s.card : ℝ≥0∞) ^ (q - 1) * ∑ i ∈ s, X i ω ^ q ∂latticeBondLaw d p :=
        lintegral_mono fun ω => ENNReal.rpow_sum_le_const_mul_sum_rpow s (fun i => X i ω) hq
    _ = (s.card : ℝ≥0∞) ^ (q - 1) * ∑ i ∈ s, ∫⁻ ω, X i ω ^ q ∂latticeBondLaw d p := by
        rw [lintegral_const_mul' _ _ (by rw [hcq]; exact ENNReal.ofReal_ne_top),
          lintegral_finsetSum _ fun i _ => (hXm i).pow_const q]
    _ ≤ (s.card : ℝ≥0∞) ^ (q - 1) * ∑ i ∈ s, ENNReal.ofReal ((B * q ^ κ) ^ q) :=
        mul_le_mul_right (Finset.sum_le_sum fun i hi => hX i hi q hq) _
    _ = ENNReal.ofReal ((s.card * B * q ^ κ) ^ q) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcq, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hc1 : (1 : ℝ) ≤ s.card := by exact_mod_cast hne.card_pos
        have e : (s.card : ℝ) ^ q = (s.card : ℝ) ^ (q - 1) * s.card := by
          rw [← Real.rpow_add_one (ne_of_gt (by linarith)) (q - 1)]
          congr 1
          ring
        rw [show (s.card : ℝ) * B * q ^ κ = s.card * (B * q ^ κ) by ring,
          Real.mul_rpow hc0 (by positivity), e]
        ring

/-! ### The dyadic decomposition -/

/-- The weight `m(u) = Σ_j Σ_{x ∈ T} κ_j(a, b, x - u)`. -/
noncomputable def dyadicWeight (T : Finset (Vertex d)) (a b : ℝ) (u : Vertex d) : ℝ≥0∞ :=
  ∑ j : Fin d, ∑ x ∈ T, heatGradKernelD j a b (x - u)

/-- `‖∇w‖²_{ℓ²(T)}`. -/
noncomputable def gradSqSum (T : Finset (Vertex d)) (w : Vertex d → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin d, ∑ x ∈ T, ENNReal.ofReal ((w (x + unit j) - w x) ^ 2)

/-- `‖w‖²_{ℓ²(S)}`. -/
noncomputable def sqSum (S : Finset (Vertex d)) (w : Vertex d → ℝ) : ℝ≥0∞ :=
  ∑ x ∈ S, ENNReal.ofReal (w x ^ 2)

omit [NeZero d] in
theorem tsum_dyadicWeight_le (T : Finset (Vertex d)) {a b : ℝ} {K : ℝ≥0∞}
    (hK : ∀ j : Fin d, ∑' v, heatGradKernelD j a b v ≤ K) :
    ∑' u, dyadicWeight T a b u ≤ d * T.card * K := by
  unfold dyadicWeight
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  calc ∑ j : Fin d, ∑' u, ∑ x ∈ T, heatGradKernelD j a b (x - u)
      ≤ ∑ _j : Fin d, ∑ _x ∈ T, K := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine Finset.sum_le_sum fun x _ => ?_
        rw [show (∑' u, heatGradKernelD j a b (x - u)) = ∑' v, heatGradKernelD j a b v from
          (Equiv.subLeft x).tsum_eq (fun v => heatGradKernelD j a b v)]
        exact hK j
    _ = d * T.card * K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [NeZero d] in
theorem ofReal_abs_sum_mul_le_sqSum (S : Finset (Vertex d)) (F w : Vertex d → ℝ) :
    ENNReal.ofReal |∑ x ∈ S, F x * w x| ≤ sqSum S F ^ (1 / 2 : ℝ) * sqSum S w ^ (1 / 2 : ℝ) := by
  have h := ENNReal.inner_le_Lp_mul_Lq S (fun x => ENNReal.ofReal |F x|)
    (fun x => ENNReal.ofReal |w x|) Real.HolderConjugate.two_two
  have hsq : ∀ y : ℝ, ENNReal.ofReal |y| ^ (2 : ℝ) = ENNReal.ofReal (y ^ 2) := fun y => by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  simp only [hsq] at h
  refine (ofReal_abs_finset_sum_le _ _).trans ?_
  simp only [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  exact h

theorem sqrt_four_pow (j : ℕ) : Real.sqrt ((4 : ℝ) ^ j) = 2 ^ j := by
  rw [show (4 : ℝ) ^ j = (2 ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
    Real.sqrt_sq (by positivity)]

/-- **The dyadic heat decomposition of the pairing.** -/
theorem ofReal_abs_sum_mul_le_dyadic {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t : ℝ, 0 < t → ∀ j : Fin d, ∑' v : Vertex d, ENNReal.ofReal
      |zdHeat d t 0 (v + unit j) - zdHeat d t 0 v| ≤
        ENNReal.ofReal (C / Real.sqrt t))
    {f : Vertex d → ℝ} (hf : HeatSummableAllD f) {S T : Finset (Vertex d)} {w : Vertex d → ℝ}
    (hw : ∀ y ∉ S, w y = 0) (hT : ∀ x ∉ T, ∀ j : Fin d, w (x + unit j) = w x) (J : ℕ) :
    ENNReal.ofReal |∑ x ∈ S, f x * w x| ≤
      sqSum S (heatAvgD (2 * 4 ^ J) f) ^ (1 / 2 : ℝ) * sqSum S w ^ (1 / 2 : ℝ) +
        (∑ j ∈ Finset.range J, (∑' u, ENNReal.ofReal (heatAvgD (4 ^ j) f u ^ 2) *
            dyadicWeight T (4 ^ j) (7 * 4 ^ j) u) ^ (1 / 2 : ℝ) *
              ENNReal.ofReal (6 * C * 2 ^ j) ^ (1 / 2 : ℝ) +
          (∑' u, ENNReal.ofReal (f u ^ 2) * dyadicWeight T 0 2 u) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal 4 ^ (1 / 2 : ℝ)) * gradSqSum T w ^ (1 / 2 : ℝ) := by
  set G : ℝ → Vertex d → ℝ := fun t => heatAvgD t f with hG
  -- the telescoping identity
  have htel : ∀ x, ∑ j ∈ Finset.range J, (G (2 * 4 ^ (j + 1)) x - G (2 * 4 ^ j) x) =
      G (2 * 4 ^ J) x - G 2 x := by
    intro x
    rw [Finset.sum_range_sub (fun j => G (2 * 4 ^ j) x)]
    simp
  have hid : ∑ x ∈ S, f x * w x = ∑ x ∈ S, G (2 * 4 ^ J) x * w x -
      ∑ j ∈ Finset.range J, ∑ x ∈ S, (G (2 * 4 ^ (j + 1)) x - G (2 * 4 ^ j) x) * w x -
        ∑ x ∈ S, (G 2 x - f x) * w x := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, htel, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  -- the dyadic steps
  have hstep : ∀ j : ℕ, ∑ x ∈ S, (G (2 * 4 ^ (j + 1)) x - G (2 * 4 ^ j) x) * w x =
      ∑' u, heatAvgD (4 ^ j) f u * (heatF S w (7 * 4 ^ j) u - heatF S w (4 ^ j) u) := by
    intro j
    have h := sum_heatAvgD_sub_mul_eq hf S w (a := 4 ^ j) (b := 7 * 4 ^ j) (c := 4 ^ j)
      (by positivity) (by positivity) (by positivity)
    have e1 : (7 : ℝ) * 4 ^ j + 4 ^ j = 2 * 4 ^ (j + 1) := by ring
    have e2 : (4 : ℝ) ^ j + 4 ^ j = 2 * 4 ^ j := by ring
    rw [e1, e2] at h
    exact h
  have hinit : ∑ x ∈ S, (G 2 x - f x) * w x =
      ∑' u, f u * (heatF S w 2 u - heatF S w 0 u) := by
    have h := sum_heatAvgD_sub_mul_eq hf S w (a := 0) (b := 2) (c := 0) le_rfl (by norm_num) le_rfl
    simp only [add_zero, show (heatAvgD 0 f) = f from funext (heatAvgD_zero f)] at h
    exact h
  have hstepK : ∀ j : ℕ, ∀ i : Fin d, ∑' v, heatGradKernelD i (4 ^ j) (7 * 4 ^ j) v ≤
      ENNReal.ofReal (6 * C * 2 ^ j) := by
    intro j i
    refine (tsum_heatGradKernelD_le hC0 hC (by positivity) i).trans (le_of_eq ?_)
    have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
    rw [sqrt_four_pow, h4]
    congr 1
    field_simp
    ring
  have hinitK : ∀ i : Fin d, ∑' v, heatGradKernelD i 0 2 v ≤ ENNReal.ofReal 4 := by
    intro i
    refine (tsum_heatGradKernelD_le_two le_rfl i).trans (le_of_eq ?_)
    norm_num
  have hsplit : ∀ (K X : ℝ≥0∞), (K * X) ^ (1 / 2 : ℝ) = K ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
    fun K X => ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hstepB : ∀ j ∈ Finset.range J,
      ENNReal.ofReal |∑ x ∈ S, (G (2 * 4 ^ (j + 1)) x - G (2 * 4 ^ j) x) * w x| ≤
        (∑' u, ENNReal.ofReal (heatAvgD (4 ^ j) f u ^ 2) *
          dyadicWeight T (4 ^ j) (7 * 4 ^ j) u) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (6 * C * 2 ^ j) ^ (1 / 2 : ℝ) * gradSqSum T w ^ (1 / 2 : ℝ) := by
    intro j _
    rw [hstep j]
    refine (ofReal_abs_tsum_mul_heatF_sub_leD _ hw hT (by
      have : (0 : ℝ) ≤ 4 ^ j := by positivity
      linarith) (hstepK j)).trans (le_of_eq ?_)
    rw [hsplit]
    exact (mul_assoc _ _ _).symm
  have hinitB : ENNReal.ofReal |∑ x ∈ S, (G 2 x - f x) * w x| ≤
      (∑' u, ENNReal.ofReal (f u ^ 2) * dyadicWeight T 0 2 u) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal 4 ^ (1 / 2 : ℝ) * gradSqSum T w ^ (1 / 2 : ℝ) := by
    rw [hinit]
    refine (ofReal_abs_tsum_mul_heatF_sub_leD _ hw hT (by norm_num) hinitK).trans (le_of_eq ?_)
    rw [hsplit]
    exact (mul_assoc _ _ _).symm
  have hend : ENNReal.ofReal |∑ x ∈ S, G (2 * 4 ^ J) x * w x| ≤
      sqSum S (heatAvgD (2 * 4 ^ J) f) ^ (1 / 2 : ℝ) * sqSum S w ^ (1 / 2 : ℝ) :=
    ofReal_abs_sum_mul_le_sqSum S _ w
  rw [hid]
  have habs : ∀ a b c : ℝ, ENNReal.ofReal |a - b - c| ≤
      ENNReal.ofReal |a| + ENNReal.ofReal |b| + ENNReal.ofReal |c| := by
    intro a b c
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := abs_sub (a - b) c
    have h2 := abs_sub a b
    linarith
  refine (habs _ _ _).trans ?_
  rw [add_mul, Finset.sum_mul, add_assoc]
  refine add_le_add hend (add_le_add ?_ hinitB)
  exact (ofReal_abs_finset_sum_le _ _).trans (Finset.sum_le_sum hstepB)

end Rigidity.Green.GeneralFlux
